/* ==============================================================
 * mymalloc.c -- 用 sbrk 实现自己的 malloc / free
 * 特性：
 *   1. 线程安全 -- 全局互斥锁保护
 *   2. 块标记 -- 用于检测野指针、双重释放、块头损坏等安全问题
 *
 * 编译: cc -Wall -Wextra -O2 mymalloc.c -o mymalloc -lpthread
 * ============================================================== */
#include <pthread.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

// 块标记 (magic number)
#define MAGIC_ALLOC 0xA110CA7EU // 块已分配
#define MAGIC_FREE 0xF4EEF4EEU // 块空闲

/* 16 字节对齐，足以满足 x86-64 上 max_align_t 的要求 */
#define ALIGNMENT 16
#define ALIGN_UP(x) (((x) + (ALIGNMENT - 1)) & ~(size_t)(ALIGNMENT - 1))

/* ===================== 块头 =========================
 * 每个块 = [header][payload]
 * 所有块按地址顺序串成一条双向链表（隐式空闲链表）
 * ==================================================== */
typedef struct block {
    size_t size; // payload 字节数（不含头部）
    int free; // 0：已分配，1：空闲
    uint32_t magic; // 块标记：MAGIC_ALLOC / MAGIC_FREE
    struct block* prev;
    struct block* next;
} block_t;

#define HEADER_SIZE ALIGN_UP(sizeof(block_t))

static block_t* head = NULL; /* 堆里第一个块 */
static block_t* tail = NULL; /* 堆里最后一个块 */

// 堆边界：free时，用于检查范围合法性
static char* heap_lo = NULL;
static char* heap_hi = NULL;

// 全局锁：静态初始化
static pthread_mutex_t g_lock = PTHREAD_MUTEX_INITIALIZER;

// 调试开关：检测到非法指针时是否打印信息
static int g_verbose = 1;

/* ==========================================================
 *                      内部工具函数
 * ========================================================== */
static block_t* request_memory(size_t payload)
{
    size_t total = ALIGN_UP(HEADER_SIZE + payload);

    void* p = sbrk((intptr_t)total);
    if (p == (void*)-1) {
        return NULL; // 堆耗尽
    }

    // 维护堆边界
    char* lo = (char*)p;
    char* hi = lo + total;
    if (!heap_lo) {
        heap_lo = lo;
        heap_hi = hi;
    } else {
        if (lo < heap_lo) {
            heap_lo = lo;
        }
        if (hi > heap_hi) {
            heap_hi = hi;
        }
    }

    // 如果新拿到的内存紧挨着最后一个空闲块，直接合并进去，减少碎片
    if (tail && tail->free && (char*)tail + HEADER_SIZE + tail->size == (char*)p) {
        tail->size += total;
        return tail;
    }

    block_t* b = (block_t*)p;
    b->size = total - HEADER_SIZE;
    b->free = 1;
    b->magic = MAGIC_FREE;
    b->prev = tail;
    b->next = NULL;

    if (tail) {
        tail->next = b;
    } else {
        head = b;
    }
    tail = b;

    return b;
}

// 把 b 分裂成 [header + payload(size)][剩余], 剩余部分成为新的空闲块
static void split_block(block_t* b, size_t size)
{
    // 剩余部分至少要能装下一个头部 + 最小可用载荷，否则不值得分裂
    if (b->size < size + HEADER_SIZE + ALIGNMENT) {
        return;
    }

    block_t* nb = (block_t*)((char*)b + HEADER_SIZE + size);
    nb->size = b->size - size - HEADER_SIZE;
    nb->free = 1;
    nb->magic = MAGIC_FREE;
    nb->prev = b;
    nb->next = b->next;

    if (b->next) {
        b->next->prev = nb;
    } else {
        tail = nb;
    }

    b->next = nb;
    b->size = size;
}

// 把空闲块 b 与相邻的空闲块合并 (b 必须已标记为free)
static void coalesce(block_t* b)
{
    // 向后合并
    if (b->next && b->next->free) {
        block_t* n = b->next;
        b->size += HEADER_SIZE + n->size;
        b->next = n->next;
        if (n->next) {
            n->next->prev = b;
        } else {
            tail = b;
        }
        n->magic = 0; // 抹除被吸收块的 magic，避免残留
    }
    // 向前合并
    if (b->prev && b->prev->free) {
        block_t* p = b->prev;
        p->size += HEADER_SIZE + b->size;
        p->next = b->next;
        if (b->next) {
            b->next->prev = p;
        } else {
            tail = p;
        }
        b->magic = 0; // 抹除被吸收块的 magic，避免残留
    }
}

// 校验：指针ptr是否是由本分配器分配的，且当前处于[已分配]状态
static int validate_ptr(void* ptr, const char* who)
{
    if (!ptr) {
        return 0;
    }

    // uintptr_t 是一个无符号整数类型，C标准保证它可以完整容纳一个 void* 的值
    // 两个指针只有在指向同一个数组对象 (或数组尾后位置) 时，比较才有意义，否则是未定义行为。
    uintptr_t up = (uintptr_t)ptr;
    uintptr_t lo = (uintptr_t)heap_lo;
    uintptr_t hi = (uintptr_t)heap_hi;

    // 1) 范围检查：必须落在堆区间内
    if (up < lo || up >= hi) {
        if (g_verbose) {
            fprintf(stderr, "[%s] %p is not from my_malloc\n", who, ptr);
        }
        return 0;
    }
    // 2) 头部位置检查
    block_t* b = (block_t*)((char*)ptr - HEADER_SIZE);
    if ((uintptr_t)b < lo || (uintptr_t)b + HEADER_SIZE > hi) {
        if (g_verbose) {
            fprintf(stderr, "[%s] header of %p out of heap\n", who, ptr);
        }
        return 0;
    }
    // 3) magic检查：区分[已释放] [已分配] [已损坏]
    if (b->magic == MAGIC_FREE) {
        if (g_verbose) {
            fprintf(stderr, "[%s] double free detected @%p\n", who, ptr);
        }
        return 0;
    }
    if (b->magic != MAGIC_ALLOC) {
        if (g_verbose) {
            fprintf(stderr, "[%s] bad magic 0x%08X @%p (header corrupted?)\n", who, b->magic, ptr);
        }
        return 0;
    }
    return 1;
}

// 内部 malloc，不加锁
static void* malloc_nolock(size_t size)
{
    if (size == 0 || size > SIZE_MAX - ALIGNMENT - HEADER_SIZE) {
        return NULL;
    }

    size = ALIGN_UP(size);

    block_t* b = head;
    while (b && !(b->free && b->size >= size)) {
        b = b->next;
    }

    if (!b) {
        b = request_memory(size);
        if (!b) {
            return NULL;
        }
    }

    split_block(b, size);
    b->free = 0;
    b->magic = MAGIC_ALLOC;
    return (char*)b + HEADER_SIZE;
}

// 内部free，不加锁
void free_nolock(void* ptr)
{
    if (!validate_ptr(ptr, "free")) {
        return;
    }

    block_t* b = (block_t*)((char*)ptr - HEADER_SIZE);
    b->free = 1;
    b->magic = MAGIC_FREE;
    coalesce(b); // 立即和相邻的块合并，减少内存碎片
}

/* ======================================================
 *                    对外接口 (加锁)
 * ====================================================== */

void* my_malloc(size_t size)
{
    pthread_mutex_lock(&g_lock);
    void* p = malloc_nolock(size);
    pthread_mutex_unlock(&g_lock);
    return p;
}

void my_free(void* ptr)
{
    if (!ptr) {
        return;
    }
    pthread_mutex_lock(&g_lock);
    free_nolock(ptr);
    pthread_mutex_unlock(&g_lock);
}

void* my_calloc(size_t n, size_t size)
{
    if (n == 0 || size == 0) {
        return NULL;
    }
    if (size > SIZE_MAX / n) {
        return NULL;
    }
    size_t total = n * size;
    void* p = my_malloc(total);
    if (p) {
        memset(p, 0, total);
    }
    return p;
}

void* my_realloc(void* ptr, size_t size)
{
    if (!ptr) {
        return my_malloc(size);
    }
    if (size == 0) {
        my_free(ptr);
        return NULL;
    }

    pthread_mutex_lock(&g_lock);

    if (!validate_ptr(ptr, "realloc")) {
        pthread_mutex_unlock(&g_lock);
        return NULL;
    }

    block_t* b = (block_t*)((char*)ptr - HEADER_SIZE);
    size_t need = ALIGN_UP(size);

    // 1) 原地缩小
    if (b->size >= need) {
        split_block(b, need);
        pthread_mutex_unlock(&g_lock);
        return ptr;
    }
    // 2) 合并后面紧邻的空闲块
    if (b->next && b->next->free && b->size + HEADER_SIZE + b->next->size >= need) {
        block_t* n = b->next;
        b->size += HEADER_SIZE + n->size;
        b->next = n->next;
        if (n->next) {
            n->next->prev = b;
        } else {
            tail = b;
        }
        n->magic = 0; // 抹除被吸收块的 magic，避免残留
        split_block(b, need);
        pthread_mutex_unlock(&g_lock);
        return ptr;
    }

    size_t oldsize = b->size;
    pthread_mutex_unlock(&g_lock);

    // 3) 搬家：锁外调用公开接口，避免自锁
    void* np = my_malloc(size);
    if (!np) {
        return NULL;
    }
    memcpy(np, ptr, oldsize);
    my_free(ptr);
    return np;
}

/* ======================================================
 *                     测试
 * ====================================================== */
static void heap_dump(const char* tag)
{
    printf("=== %s ===\n", tag);
    size_t total = 0;
    for (block_t* b = head; b; b = b->next) {
        printf("  payload@%p  size=%5zu  %s magic=0x%08X\n",
            (void*)((char*)b + HEADER_SIZE), b->size,
            b->free ? "FREE" : "USED",
            b->magic);
        total += HEADER_SIZE + b->size;
    }
    printf("  heap total = %zu bytes\n\n", total);
}

static void* start_routine(void* arg)
{
    long id = (long)arg;
    for (int i = 0; i < 1000; ++i) {
        size_t sz = (size_t)(16 + (i * 37) % 512);
        void* p = my_malloc(sz);
        if (p) {
            // 用一用，确认真的可写
            memset(p, (int)id, sz);
            my_free(p);
        }
    }
    return NULL;
}

int main(void)
{
    // 1) 基本功能
    int* a = my_malloc(100);
    char* b = my_malloc(1000);
    int* c = my_malloc(50);
    heap_dump("3 次分配之后");

    // 用一用，确认真的可写
    memset(a, 0xAA, 100);
    memset(b, 0xBB, 1000);
    memset(c, 0xCC, 50);

    my_free(b);
    heap_dump("free(b)");

    my_free(a);
    heap_dump("free(a) -- a与b合并");

    my_free(c);
    heap_dump("free(c) -- 整个堆合成一个空闲块");

    // 复用刚释放的空间，不应该再向内核要内存
    void* d = my_malloc(1000);
    heap_dump("malloc(1000) -- 复用已释放区域");

    my_free(d);

    // 2) magic 保护测试
    int* e = my_malloc(100);
    char* f = my_malloc(1000);
    puts("--- magic保护测试 ---");
    my_free(e);
    heap_dump("free(e)");
    my_free(e); // double free: 应被 magic 检测拦截
    my_free((void*)0x123456); // 野指针：应被范围检查拦截

    my_free(f);
    heap_dump("free(f)");

    // 3) 多线程压测
    puts("--- 多线程压测 (8 threads × 1000 ops) ---");
    pthread_t tids[8];
    for (long i = 0; i < 8; ++i) {
        pthread_create(&tids[i], NULL, start_routine, (void*)i);
    }
    for (int i = 0; i < 8; ++i) {
        pthread_join(tids[i], NULL);
    }
    puts("DONE");
    return 0;
}
