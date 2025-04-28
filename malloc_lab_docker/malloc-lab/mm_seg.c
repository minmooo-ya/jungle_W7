#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <stdbool.h>


#include "mm.h"
#include "memlib.h"

#define WSIZE 8             // Word size (8 bytes)
#define DSIZE 16            // Double word size (16 bytes)
#define CHUNKSIZE (1<<12)   // Heap 확장 단위 (그대로 두어도 OK)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

// Pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

// Read and write a word at address p
#define GET(p) (*(unsigned long *)(p))  
#define PUT(p, val) (*(unsigned long *)(p) = (val))

// Read the size and allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~(size_t)0xF) // 0xF로 하자 (하위 4비트 사용)
#define GET_ALLOC(p) (GET(p) & 0x1)

// Given block ptr bp, compute address of its header and footer
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// Given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define PRED(bp) (*(void **)(bp))                        // 이전 free block 포인터
#define SUCC(bp) (*(void **)((char *)(bp) + WSIZE))       // 다음 free block 포인터
/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "puddingjelly",
    /* First member's full name */
    "sweetpotatooo",
    /* First member's email address */
    "sehyun5004@naver.com",
    /* Second member's full name (leave blank if none) */
    "minmoooya",
    /* Second member's email address (leave blank if none) */
    "minhyay01@gmail.com"};

#define ALIGNMENT 16
#define NUM_CLASSES 10

#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0xF)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void insert_node(void *bp);
static void remove_node(void *bp);

void *heap_listp;   // 항상 heap의 첫 payload를 가리키는 포인터 (heap base)
static void *segregated_free_lists[NUM_CLASSES];

// find size class
static int find_size_class(size_t size) {
    if (size <= 9) return 0;
    else if (size <= 16) return 1;
    else if (size <= 32) return 2;
    else if (size <= 64) return 3;
    else if (size <= 128) return 4;
    else if (size <= 256) return 5;
    else if (size <= 512) return 6;
    else if (size <= 1024) return 7;
    else if (size <= 2048) return 8;
    else return 9;
}

// static void insert_node(void *bp) {
//     int class_idx = find_size_class(GET_SIZE(HDRP(bp)));
//     void *cur = segregated_free_lists[class_idx];
//     void *prev = NULL;

//     while (cur != NULL && GET_SIZE(HDRP(cur)) < GET_SIZE(HDRP(bp))) {
//         prev = cur;
//         cur = SUCC(cur);
//     }

//     if (prev == NULL) {
//         // 맨 앞에 삽입
//         segregated_free_lists[class_idx] = bp;
//         PRED(bp) = NULL;
//     } else {
//         SUCC(prev) = bp;
//         PRED(bp) = prev;
//     }

//     if (cur != NULL) {
//         PRED(cur) = bp;
//     }
//     SUCC(bp) = cur;
// }

static void insert_node(void *bp) {
    int class_idx = find_size_class(GET_SIZE(HDRP(bp)));
    
    SUCC(bp) = segregated_free_lists[class_idx];
    PRED(bp) = NULL;
    if (segregated_free_lists[class_idx] != NULL)
        PRED(segregated_free_lists[class_idx]) = bp;
    segregated_free_lists[class_idx] = bp;
}

// remove node
static void remove_node(void *bp) {
    int class_idx = find_size_class(GET_SIZE(HDRP(bp)));

    if (PRED(bp))
        SUCC(PRED(bp)) = SUCC(bp);
    else
        segregated_free_lists[class_idx] = SUCC(bp);

    if (SUCC(bp))
        PRED(SUCC(bp)) = PRED(bp);
}

// coalesce
static void *coalesce(void *bp) {
    bool prev_alloc = (PREV_BLKP(bp) < (void *)mem_heap_lo()) || GET_ALLOC(HDRP(PREV_BLKP(bp)));
    bool next_alloc = (NEXT_BLKP(bp) > (void *)mem_heap_hi()) || GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        insert_node(bp);
        return bp;
    }
    else if (prev_alloc && !next_alloc) {
        remove_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {
        remove_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {
        remove_node(PREV_BLKP(bp));
        remove_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    insert_node(bp);
    return bp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    return coalesce(bp);
}

int mm_init(void)
{
    //  1. 힙을 위한 최소 공간 16바이트 확보 (padding + prologue header/footer + epilogue header)
    heap_listp = mem_sbrk(4 * WSIZE);
    if (heap_listp == (void *)-1) {
        return -1;  //  sbrk 실패 시 에러 리턴
    }
    //  2. 초기 블록들 구성하는 단계
    PUT(heap_listp, 0);                                 //  Alignment padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));      //  Prologue header (8바이트, 할당됨)
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));      //  Prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));          //  Epilogue header (0바이트, 할당됨)

    //  3. payload 기준 위치로 이동 (Prologue 블록의 payload 포인터)
    heap_listp += (2 * WSIZE);

    for (int i = 0; i < NUM_CLASSES; i++)
    segregated_free_lists[i] = NULL;

    void *bp = extend_heap(CHUNKSIZE/WSIZE);
    //  4. 살제 usable한 free block 확보
    if (bp == NULL)
        return -1;
    if (extend_heap(4) == NULL)   // 자주 사용되는 작은 블럭이 잘 처리되어 점수가 오름
        return -1;

    return 0;
}

static void *find_fit(size_t asize) {
    for (int i = find_size_class(asize); i < NUM_CLASSES; i++) {
        void *bp = segregated_free_lists[i];
        while (bp != NULL) {
            if (GET_SIZE(HDRP(bp)) >= asize)
                return bp;
            bp = SUCC(bp);
        }
    }
    return NULL;
}

// 주어진 위치에 메모리를 배치 (필요 시 분할)
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    remove_node(bp);

    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        void *next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(csize - asize, 0));
        PUT(FTRP(next_bp), PACK(csize - asize, 0));
        insert_node(next_bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0) {
        return NULL;
    }

    if (size <= DSIZE) {
        asize = 2*DSIZE;
    }
    else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE -1)) / DSIZE);
    }

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    if (ptr == NULL)
        return;
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/* mm_realloc - in-place 최적화 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)
        return mm_malloc(size);
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    size_t oldsize = GET_SIZE(HDRP(ptr));
    size_t asize = (size <= DSIZE) ? (2 * DSIZE) : DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    if (asize <= oldsize)
        return ptr;

    void *next = NEXT_BLKP(ptr);
    if (!GET_ALLOC(HDRP(next)) && (oldsize + GET_SIZE(HDRP(next))) >= asize) {
        remove_node(next);
        size_t newsize = oldsize + GET_SIZE(HDRP(next));
        PUT(HDRP(ptr), PACK(newsize, 1));
        PUT(FTRP(ptr), PACK(newsize, 1));
        return ptr;
    }

    void *newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    size_t copySize = oldsize - DSIZE;
    if (size < copySize)
        copySize = size;
    memcpy(newptr, ptr, copySize);
    mm_free(ptr);
    return newptr;
}