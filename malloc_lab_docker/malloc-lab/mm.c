#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <stdbool.h>


#include "mm.h"
#include "memlib.h"

// 기본 상수 정의
#define WSIZE 8             // Word size: 8 bytes (header, footer 크기)
#define DSIZE 16            // Double word size: 16 bytes (최소 블록 크기)
#define CHUNKSIZE (1 << 12) // 초기 및 힙 확장 시 요청하는 크기: 4KB (2^12)

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 두 값 중 더 큰 값을 반환

// 블록의 크기(size)와 할당 여부(alloc bit)를 하나의 word에 패킹
#define PACK(size, alloc) ((size) | (alloc))

// 메모리 p가 가리키는 위치에서 8바이트 읽기
#define GET(p) (*(unsigned long *)(p))  

// 메모리 p가 가리키는 위치에 8바이트 값 쓰기
#define PUT(p, val) (*(unsigned long *)(p) = (val))

// 포인터 p로부터 size(상위 비트들) 추출 (하위 4비트는 무시)
#define GET_SIZE(p) (GET(p) & ~(size_t)0xF) 

// 포인터 p로부터 할당 상태(하위 1비트) 추출
#define GET_ALLOC(p) (GET(p) & 0x1)

// 블록 포인터 bp로부터 header 주소 계산
#define HDRP(bp) ((char *)(bp) - WSIZE)

// 블록 포인터 bp로부터 footer 주소 계산
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 블록 포인터 bp로부터 다음 블록의 포인터 계산
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))

// 블록 포인터 bp로부터 이전 블록의 포인터 계산
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// 가용 리스트(free list)에서 현재 블록 bp의 이전 블록 포인터 접근
#define PRED(bp) (*(void **)(bp)) 

// 가용 리스트(free list)에서 현재 블록 bp의 다음 블록 포인터 접근
#define SUCC(bp) (*(void **)((char *)(bp) + WSIZE))

// 메모리 정렬 관련 상수 및 매크로
#define ALIGNMENT 16 // 16바이트 단위로 정렬 (x86-64 규약 때문)

#define NUM_CLASSES 10 // segregated free list를 위한 크기 클래스 개수

// 주어진 size를 16바이트로 올림 (16의 배수로 맞춤)
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0xF)

// size_t 자료형을 저장할 때 필요한 공간 크기 (16바이트로 정렬)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

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

static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void insert_node(void *bp);
static void remove_node(void *bp);

void *heap_listp;   // 항상 heap의 첫 payload를 가리키는 포인터 (heap base)
static void *segregated_free_lists[NUM_CLASSES];

// 주어진 크기에 맞는 size class를 반환하는 함수
static int find_size_class(size_t size) {
    if (size <= 32) return 0;
    else if (size <= 64) return 1;
    else if (size <= 128) return 2;
    else if (size <= 256) return 3;
    else if (size <= 512) return 4;
    else if (size <= 1024) return 5;
    else if (size <= 2048) return 6;
    else if (size <= 4096) return 7;
    else if (size <= 8192) return 8;
    else return 9;
}

// //정렬 ver
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

// segregated free list에 새 free 블록을 삽입하는 함수 (정렬 X 버전)
static void insert_node(void *bp) {
    int class_idx = find_size_class(GET_SIZE(HDRP(bp)));
    
    SUCC(bp) = segregated_free_lists[class_idx]; // 현재 리스트의 첫 번째 노드를 successor로 설정
    PRED(bp) = NULL; // predecessor는 NULL
    if (segregated_free_lists[class_idx] != NULL)
        PRED(segregated_free_lists[class_idx]) = bp; // 기존 첫 번째 노드가 있으면 그 노드의 predecessor를 bp로 설정
    segregated_free_lists[class_idx] = bp; // 리스트의 첫 번째에 bp를 삽입
}

// segregated free list에서 free 블록을 제거하는 함수
static void remove_node(void *bp) {
    int class_idx = find_size_class(GET_SIZE(HDRP(bp)));
    void *prev = PRED(bp);
    void *succ = SUCC(bp);

    if (prev)
        SUCC(prev) = succ; // 이전 노드가 있으면, 이전 노드의 successor를 갱신
    else
        segregated_free_lists[class_idx] = succ; // 없으면 리스트의 시작 노드를 successor로 변경

    if (succ)
        PRED(succ) = prev; // 다음 노드가 있으면, 다음 노드의 predecessor를 갱신
}

// 인접한 free 블록들과 병합(coalescing)하는 함수
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  // 이전 블록 할당 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));  // 다음 블록 할당 여부
    size_t size = GET_SIZE(HDRP(bp));                    // 현재 블록 크기
    void *next = NEXT_BLKP(bp);
    void *prev = PREV_BLKP(bp);

    if (prev_alloc && next_alloc) { // case 1: 둘 다 할당됨
        insert_node(bp);
        return bp;
    }
    else if (prev_alloc && !next_alloc) { // case 2: 다음 블록만 free
        remove_node(next);
        size += GET_SIZE(HDRP(next));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) { // case 3: 이전 블록만 free
        remove_node(prev);
        size += GET_SIZE(HDRP(prev));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(prev), PACK(size, 0));
        bp = prev;
    }
    else { // case 4: 이전, 다음 모두 free
        remove_node(prev);
        remove_node(next);
        size += GET_SIZE(HDRP(prev)) + GET_SIZE(HDRP(next));
        PUT(HDRP(prev), PACK(size, 0));
        PUT(FTRP(next), PACK(size, 0));
        bp = prev;
    }
    insert_node(bp);
    return bp;
}


// 힙을 words * 4bytes 만큼 확장하고 새 free 블록을 만들어 반환하는 함수
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 짝수 단위로 정렬
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));            // 새 free 블록 header
    PUT(FTRP(bp), PACK(size, 0));            // 새 free 블록 footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));    // 새로운 epilogue header
    return coalesce(bp);
}

// allocator 초기화 함수
int mm_init(void)
{
    // 1. 힙 생성 (초기 padding + prologue header/footer + epilogue header)
    heap_listp = mem_sbrk(4 * WSIZE);
    if (heap_listp == (void *)-1) {
        return -1;
    }

    PUT(heap_listp, 0);                                 // 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));       // prologue header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));       // prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));           // epilogue header

    heap_listp += (2 * WSIZE); // payload 영역으로 이동

    for (int i = 0; i < NUM_CLASSES; i++)
        segregated_free_lists[i] = NULL; // segregated list 초기화

    void *bp = extend_heap(CHUNKSIZE/WSIZE); // 초기 힙 확장
    if (bp == NULL)
        return -1;
    if (extend_heap(4) == NULL) // 추가로 작은 블록 확보
        return -1;

    return 0;
}


// static void *find_fit(size_t asize) {
//     for (int i = find_size_class(asize); i < NUM_CLASSES; i++) {
//         void *bp = segregated_free_lists[i];
//         while (bp != NULL) {
//             if (GET_SIZE(HDRP(bp)) >= asize)
//                 return bp;
//             bp = SUCC(bp);
//         }
//     }
//     return NULL;
// }

// segregated free list에서 크기에 맞는 블록을 찾는 함수 (best-fit 방식)
static void *find_fit(size_t asize) {
    for (int i = find_size_class(asize); i < NUM_CLASSES; i++) {
        void *bp = segregated_free_lists[i];
        void *best_bp = NULL;
        size_t best_size = (size_t)-1;

        while (bp != NULL) {
            size_t bsize = GET_SIZE(HDRP(bp));
            if (bsize >= asize) {
                if (bsize == asize)
                    return bp; // 완벽한 fit이면 바로 리턴
                if (bsize < best_size) {
                    best_size = bsize;
                    best_bp = bp;
                }
            }
            bp = SUCC(bp);
        }
        if (best_bp != NULL)
            return best_bp;
    }
    return NULL;
}


// 메모리 블록을 할당 요청 크기에 맞게 배치하고, 남으면 분할하는 함수
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    remove_node(bp);

    if ((csize - asize) >= (2 * DSIZE)) { // 남은 크기가 최소 블록 크기 이상이면 분할
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        void *next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(csize - asize, 0));
        PUT(FTRP(next_bp), PACK(csize - asize, 0));
        insert_node(next_bp); // 남은 블록은 free list에 다시 삽입
    }
    else { // 남은 크기가 작으면 그냥 통째로 할당
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

// 메모리 블록을 할당하는 함수
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

// 메모리 블록을 해제하는 함수
void mm_free(void *ptr)
{
    if (ptr == NULL)
        return;
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0)); // header 수정
    PUT(FTRP(ptr), PACK(size, 0)); // footer 수정
    coalesce(ptr); // 병합 시도
}


// 메모리 블록을 재할당하는 함수 (in-place 최적화)
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
        return ptr; // 기존 블록이 충분히 크면 그대로 사용
    
    void *next = NEXT_BLKP(ptr);
    if (!GET_ALLOC(HDRP(next)) && (oldsize + GET_SIZE(HDRP(next))) >= asize) { // 다음 블록과 합칠 수 있으면
        remove_node(next);
        size_t newsize = oldsize + GET_SIZE(HDRP(next));
        PUT(HDRP(ptr), PACK(newsize, 1));
        PUT(FTRP(ptr), PACK(newsize, 1));
        return ptr;
    }

    // 새 블록 할당 후 데이터 복사
    void *newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    size_t copySize = oldsize - DSIZE;
    if (size < copySize)
        copySize = size;
    memcpy(newptr, ptr, copySize); // 데이터 복사
    mm_free(ptr); // 기존 블록 해제
    return newptr;
}