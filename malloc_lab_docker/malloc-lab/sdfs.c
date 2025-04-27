#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"     // mdriver가 호출할 함수들 시그니처 제공 (mm_malloc, mm_free, etc.)
#include "memlib.h" // 가상 Heap을 확장하기 위한 함수 정의 (mem_sbrk, mem_heap_lo 등)

/* ==========================================
 * 정렬/기본 단위
 * ========================================== */
/* 메모리 정렬 기준: 8바이트 (double word) */
#define ALIGNMENT 8
/* 정렬을 위한 매크로: size를 8의 배수로 올림 */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) // ~0x7은 2진수로 1111...1000
/* size_t의 크기를 ALIGN 단위로 맞춘 값 */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* ==========================================
 * 기본 상수 및 매크로 정의 / Constants & Macros
 * ========================================== */
/* 워드 및 더블워드 크기 (단위: 바이트) */
#define WSIZE 4 /* 워드 크기 (header/footer용) */
#define DSIZE 8 /* 더블워드 크기 (payload 최소 단위) */
/* 기본 힙 확장 크기 (초기 힙 요청 및 fit 실패 시) */
#define CHUNKSIZE (1 << 12) /* 4096 bytes = 4KB */

/* 두 값 중 큰 값 반환 */
#define MAX(x, y) ((x) > (y) ? (x) : (y))
/* size와 할당 여부(alloc)를 묶어 하나의 워드로 패킹 */
#define PACK(size, alloc) ((size) | (alloc))

/* 포인터 p가 가리키는 주소의 값을 읽거나 저장 (header/footer 직접 조작용) */
#define GET(p) (*(unsigned int *)(p))              // 값 읽기 → (((포인터 p가 가리키는 메모리 주소)에서 4바이트 크기)를 읽어옴)
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 값 쓰기 → (((포인터 p가 가리키는 메모리 주소)에 4바이트 크기)로 val 값을 저장함)

/* 주소 p에서 블록 크기와 할당 여부 추출 (블록 메타데이터 읽기) */
#define GET_SIZE(p) (GET(p) & ~0x7) // 하위 3비트를 제외한 크기
#define GET_ALLOC(p) (GET(p) & 0x1) // 하위 1비트가 할당 여부

/* 블록 포인터 bp로부터 header/footer 주소 계산 */
#define HDRP(bp) ((char *)(bp) - WSIZE)                      // header 위치
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // footer 위치

/* 블록 포인터 bp로부터 이전/다음 블록의 주소 계산 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp))) // 다음 블록
// → ((블록포인터 bp를 char 포인터로 변환)하고, ((bp의 헤더 주소 안)에 들어있는 현재 블록의 전체 크기)를 더해 다음 블록의 payload 시작 주소를 구함)
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록
// → ((블록포인터 bp를 char 포인터로 변환)하고, ((bp에서 8바이트 만큼 뒤로 이동한 주소(= 이전 블록의 푸터))의 전체 크기)를 빼서 이전 블록의 payload 시작 주소를 구함)

/* ==========================================
 * 전역 변수 정의 / Global Variables
 * ========================================== */
static char *heap_listp = 0;    // 힙의 시작 위치를 가리키는 전역 포인터
static char *last_fitp;         // 마지막 탐색 위치를 기록

/* ==========================================
 * 내부 함수 선언 / Internal Function Prototypes
 * ========================================== */
static void *extend_heap(size_t words); // 힙 확장 함수
static void *coalesce(void *bp);        // 인접 블록 병합 함수

/* ==========================================
 * 초기화 함수 / Initialization
 * ========================================== */
/*
 * mm_init - 초기 힙 생성 / Initialize the heap
 * 1. 4워드 공간을 확보하여 기본 힙 구조를 설정한다.
 *    - 패딩 (alignment padding)
 *    - 프롤로그 헤더 (prologue header)
 *    - 프롤로그 푸터 (prologue footer)
 *    - 에필로그 헤더 (epilogue header)
 * 2. 프롤로그/에필로그를 설정하여 힙 일관성을 유지한다.
 * 3. 이후 첫 번째 가용 블록을 만들기 위해 CHUNKSIZE만큼 힙을 확장한다.
 */
int mm_init(void)
{
    // 4워드 만큼 가상 힙 공간을 확장 요청해 (mem_sbrk(4 * WSIZE))
    // 성공하면, 확장된 메모리의 시작 주소를 heap_listp에 저장하고
    // 만약 mem_sbrk()가 실패하면, (void *)-1을 반환함.
    // 따라서 만약 메모리 확보에 실패했다면, -1을 반환하라는 코드
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    // 블록 메타데이터 설정
    PUT(heap_listp, 0);                            // 패딩 (Unused Alignment Padding)
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 헤더 (size = 8, alloc = 1)
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 푸터 (size = 8, alloc = 1)
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // 에필로그 헤더 (size = 0, alloc = 1)

    heap_listp += (2 * WSIZE);  // 프롤로그 블록의 payload 시작 위치로 이동
    last_fitp = heap_listp;     // last_fitp 초기화

    // 첫 가용 블록을 만들기 위해 CHUNKSIZE만큼 힙 확장
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    // if (extend_heap(4) == NULL) return -1;  // 자주 사용되는 작은 블럭이 잘 처리되도록

    return 0;
}

/* ==========================================
 * 힙 확장 및 병합 / Heap Extension & Coalescing
 * ========================================== */
/*
 * extend_heap - 힙을 size 워드 만큼 확장하고 새 가용 블록 생성 / Extend heap
 * 1. 요청한 워드 수(words)를 짝수로 맞춰 double word alignment를 유지한다.
 * 2. mem_sbrk(size) 호출로 힙을 확장한다.
 * 3. 새 가용 블록의 header와 footer를 초기화하고,
 * 4. 새로운 에필로그 헤더를 추가한다.
 * 5. 확장된 블록이 앞 블록과 연결 가능하면 coalesce(병합)한다.
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 워드 수를 짝수로 맞춰 더블워드 정렬 유지
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    // 힙 공간 요청 (memlib.c에서 정의된 mem_sbrk 사용)
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));         // 새로운 가용블록의 header 초기화
    PUT(FTRP(bp), PACK(size, 0));         // 새로운 가용블록의 footer 초기화
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새로운 epilogue header 생성
    return coalesce(bp);                  // 직전 블록이 가용 상태면 병합
}

/* ==========================================
 * 가용 블록 탐색 / Find Available Block
 * ========================================== */
/*
 * find_fit - Next-fit 방식으로 가용 블록 탐색
 * 1. 마지막 탐색 지점(last_bp)부터 힙 끝까지 순차적으로 탐색
 * 2. 가용 && 요청 크기 이상인 블록을 발견하면 해당 블록을 반환하고,
 *    last_bp를 해당 블록으로 갱신
 * 3. 힙 끝까지 못 찾으면, heap_listp부터 last_bp까지 다시 탐색
 * 4. 두 번 순회해도 못 찾으면 NULL을 반환한다.
 *  ➔ First-fit과 다르게, 매번 heap_listp부터 처음부터 찾지 않고
 *    직전 탐색 위치(last_bp) 이후부터 찾음
 */
static void *find_fit(size_t asize)
{
    void *bp = last_fitp;

    // 1. last_fitp부터 에필로그까지 탐색
    for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            last_fitp = bp; // 찾으면 last_fitp 갱신
            return bp;
        }
    }

    // 2. 못 찾으면 처음부터 last_fitp까지 다시 탐색
    //for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0 && bp != last_fitp; bp = NEXT_BLKP(bp))
    for (bp = heap_listp; bp < last_fitp; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            last_fitp = bp; // 찾으면 last_fitp 갱신
            return bp;
        }
    }
    return NULL; // No fit - NULL 반환
}

/* ==========================================
 * 가용 블록에 메모리 할당 / Place Block
 * ========================================== */
/*
 * place - 탐색된 가용 블록에 메모리 할당
 * 1. 필요한 크기만큼 앞쪽 블록을 할당
 * 2. 남은 공간이 충분하면 새로운 가용 블록 생성
 * 3. 남은 공간이 작으면 전체 블록을 할당
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    if ((csize - asize) >= (2 * DSIZE))
    { // 블록을 할당하고 남은 공간이 최소 블록 크기(16B) 이상이면 분할
        // 앞쪽 블록 할당
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // 남은 블록 주소로 이동 & 새 가용 블록 생성
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else
    {
        // 분할할 수 없는 크기면 전체 블록 할당
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* ==========================================
 * 메모리 블록 할당 및 해제 / Malloc & Free
 * ========================================== */
/*
 * mm_malloc - 요청한 size만큼 메모리 블록 할당
 * 1. 요청 크기 조정 (정렬 및 최소 블록 크기 충족)
 * 2. find_fit으로 가용 블록 탐색
 * 3. 없으면 extend_heap으로 힙 확장 후 배치
 * 4. 예외 free block 병합 후 place
 */
void *mm_malloc(size_t size)
{
    size_t asize;      // 조정된 블록 크기 (payload + header/footer + 정렬)
    size_t extendsize; // fit 실패 시 heap을 얼마나 확장할지
    char *bp;

    if (size == 0)
        return NULL; // 잘못된 요청은 무시

    // 최소 블록 크기(16B) 충족하도록 조정
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // 가용 블록 탐색
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize); // 블록 배치 및 분할 가능
        last_fitp = bp;     // 추가함
        return bp;
    }

    // 적합한 블록이 없으면 힙 확장 후 배치
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    // bp = coalesce(bp); // 예외 free block 병합해 관리 개선
    place(bp, asize);  // 확장된 블록에 배치
    last_fitp = bp;
    return bp;
}

/* ==========================================
 * 메모리 블록 해제 / Free Block
 * ========================================== */
/*
 * mm_free - 블록을 해제하여 가용 상태로 변경
 * 1. header/footer를 free로 설정
 * 2. 주변 가용 블록들과 병합(coalesce)
 */
void mm_free(void *ptr)
{
    void *bp = ptr;
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0)); // header: free
    PUT(FTRP(bp), PACK(size, 0)); // footer: free
    coalesce(bp);                 // 주변 가용블록과 병합 시도
}

/* ==========================================
 * 가용 블록 병합 / Coalesce Free Blocks
 * ========================================== */
/*
 * coalesce - 인접한 가용 블록들을 하나로 병합
 * 1. 앞/뒤 블록의 할당 여부 확인
 * 2. 경우(case 1~4)에 따라 병합 처리
 * 3. 병합된 블록의 포인터 반환
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 앞 블록 할당 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 뒷 블록 할당 여부
    size_t size = GET_SIZE(HDRP(bp));                   // 현재 블록 크기

    if (prev_alloc && next_alloc)
    { // Case 1: 양쪽 모두 할당 - 병합 없음
        last_fitp = bp;
        return bp;
    }
    else if (prev_alloc && !next_alloc)
    { // Case 2: 뒤만 free
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    { // Case 3: 앞만 free
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else
    { // Case 4: 양쪽 모두 free - 양쪽 병합
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))
                + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더에 새 사이즈 저장
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록 푸터에 새 사이즈 저장
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/* ==========================================
 * 메모리 블록 재할당 / Reallocate Block
 * ========================================== */
/*
 * mm_realloc - 블록 재할당
 * 1. ptr이 NULL이면 malloc(size)로 새로 할당한다.
 * 2. size가 0이면 free(ptr) 후 NULL을 반환한다.
 * 3. 요청 크기가 기존 블록보다 작거나 같으면 in-place로 사용하거나 분할한다.
 * 4. 오른쪽 블록이 가용 상태이고, 합쳐서 충분하면 확장하여 사용하고 필요시 분할한다.
 * 5. 위 방법으로 불가능하면 새 블록을 malloc하고, 기존 데이터를 복사한 후 free한다.
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)
        return mm_malloc(size);

    if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }

    size_t old_block = GET_SIZE(HDRP(ptr)); // 기존 블록의 전체 크기 (헤더+푸터 포함)
    size_t old_payload = old_block - DSIZE; // 기존 블록의 payload 크기만 추출 (헤더+푸터 제외)
    size_t new_asize;                       // 새로운 요청 크기를 정렬+오버헤드 포함해서 계산

    if (size <= DSIZE)
        new_asize = 2 * DSIZE;
    else
        new_asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // [Case 1] 새 요청이 기존 블록 크기보다 작거나 같으면
    //          현재 블록을 분할하거나 그대로 사용 (in-place)
    if (new_asize <= old_block)
    {
        place(ptr, new_asize); // 필요하면 분할
        return ptr;            // 주소 그대로 반환
    }

    // [Case 2] 오른쪽 블록이 가용 상태이고,
    //          합쳐서 충분한 크기가 되면 in-place 확장하고, 필요시 분할
    if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) &&
        old_block + GET_SIZE(HDRP(NEXT_BLKP(ptr))) >= new_asize)
    {
        size_t total = old_block + GET_SIZE(HDRP(NEXT_BLKP(ptr))); // 합친 블록 크기
        PUT(HDRP(ptr), PACK(total, 1));                            // 새로운 header 설정
        PUT(FTRP(ptr), PACK(total, 1));                            // 새로운 footer 설정
        place(ptr, new_asize);                                     // 오른쪽 확장 후 split
        return ptr;
    }

    // [Case 3] 위 방법으로도 안되면
    // => 새 블록을 malloc해서 데이터 복사 후 기존 블록 free
    void *new_ptr = mm_malloc(size);
    if (new_ptr == NULL)
        return NULL; // 기존 ptr은 살아 있음 free하지 않음)

    // 복사할 크기는 기존 payload vs 요청 size 중 작은 쪽
    size_t copy = old_payload < size ? old_payload : size;
    memmove(new_ptr, ptr, copy); // 새 블록에 데이터 복사 (memmove: 겹칠 수도 있으니 안전 복사)

    mm_free(ptr);   // 기존 블록 해제
    return new_ptr; // 새 블록 주소 반환
}