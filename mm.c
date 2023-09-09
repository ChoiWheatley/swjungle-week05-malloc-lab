/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include "mm.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"

typedef char *byte_p;

int mm_init(void);
void *mm_malloc(size_t size);
void *mm_realloc(void *ptr, size_t size);
static void *extend_heap(size_t words);
static void *coalesce(byte_p bp);

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "swjungle-week05-team08",
    /* First member's full name */
    "ChoiWheatley",
    /* First member's email address */
    "chltmdgus604@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/**
 * SECTION Constants and Macros
 * Figure 9.43 코드가 누락되어 추가함.
 */
#define WSIZE 4  //  워드 사이즈 (헤더, 푸터 사이즈) in bytes
#define DSIZE WSIZE * 2      // 더블 워드 사이즈 in bytes
#define CHUNKSIZE (1 << 12)  // 힙 추가 시 요청할 크기 in bytes
#define MAX(x, y) ((x) > (y))

// header, footer에 들어갈 정보 (blocksize, allocated)를 묶는다.
#define PACK(size, alloc) ((size) | (alloc))

// read and write a word at address p
#define GET(p) (*(size_t *)(p))
#define PUT(p, val) (*(size_t *)(p) = (val))

// Unpack and Read specific field from address p
#define GET_SIZE(p) (size_t)(GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x01)

// 헤더 포인터의 주소를 가리킨다. p는 payload의 첫번째 주소를 가리킨다.
#define HEADER_PTR(bp) (void *)((byte_p)(bp)-WSIZE)
// 푸터 포인터의 주소를 가리킨다. p는 payload의 첫번째 주소를 가리킨다.
#define FOOTER_PTR(bp) (void *)((byte_p)(bp) + GET_SIZE(HEADER_PTR(bp)) - DSIZE)

// 다음 블럭의 bp(base pointer)를 가리킨다.
#define NEXT_BLOCK_PTR(bp) \
  (void *)((byte_p)(bp) + GET_SIZE(((byte_p)(bp)-WSIZE)))
// 이전 블럭의 bp(base pointer)를 가리킨다.
#define PREV_BLOCK_PTR(bp) (void *)((byte_p)(bp)-GET_SIZE(((byte_p)(bp)-DSIZE)))

void *heap_listp;
///!SECTION

/*
 * # mm_init - initialize the malloc package.
 *
 * Figure 9.42에 따르면, 힙 시작 첫번째 워드는 정렬을 위해 사용하지 않으며,
 * 0으로 초기화 되어있다. 바로 뒤에는 프롤로그 블록이 나오며, 페이로드 없이
 * 헤더와 푸터만 존재한다. 힙 영역 마지막 워드는 에필로그 블록으로, 블록사이즈가
 * 0으로 초기화 되어있다.
 */
int mm_init(void) {
  // 비어있는 힙 생성
  if (((heap_listp) = mem_sbrk(4 * WSIZE)) == (void *)-1) {
    return -1;
  }
  PUT(heap_listp, 0);                             // alignment padding
  PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));  // prologue header
  PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));  // prologue footer
  PUT(heap_listp + (3 * WSIZE), PACK(0, 1));      // epilogue header
  heap_listp += (2 * WSIZE);

  // Extend the empty heap with a free block of CHUNKSIZE bytes
  if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
    return -1;
  }
  return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
  int newsize = ALIGN(size + SIZE_T_SIZE);
  void *p = mem_sbrk(newsize);
  if (p == (void *)-1)
    return NULL;
  else {
    *(size_t *)p = size;
    return (void *)((char *)p + SIZE_T_SIZE);
  }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr) {
  size_t size = GET_SIZE(HEADER_PTR(ptr));

  PUT(HEADER_PTR(ptr), PACK(size, 0));
  PUT(FOOTER_PTR(ptr), PACK(size, 0));
  coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
  void *oldptr = ptr;
  void *newptr;
  size_t copySize;

  newptr = mm_malloc(size);
  if (newptr == NULL) return NULL;
  copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
  if (size < copySize) copySize = size;
  memcpy(newptr, oldptr, copySize);
  mm_free(oldptr);
  return newptr;
}

/**
 * # extend_heap - 지정한 블록 개수만큼 힙 영역을 추가한다.
 */
void *extend_heap(size_t words) {
  byte_p bp;
  size_t size = words * WSIZE;

  // 정렬을 유지하기 위해 words를 2의 배수로 반올림한다.
  if (words % 2 != 0) {
    size = (words + 1) * WSIZE;
  }
  if ((bp = mem_sbrk(size)) == (void *)-1) {
    return NULL;
  }
  // 늘어난 힙 영역대로 헤더 푸터 에필로그 헤더를 재설정한다.
  PUT(HEADER_PTR(bp), PACK(size, 0));               // free block header
  PUT(FOOTER_PTR(bp), PACK(size, 0));               // free block footer
  PUT(HEADER_PTR(NEXT_BLOCK_PTR(bp)), PACK(0, 1));  // new epilogue header

  // 기존 블럭이 해제되었더라면 병합해주어야지
  return coalesce(bp);
}

/**
 * # coalesce - prev, next 블럭과 병합을 시도한다.
 *
 * cases:
 *
 * - none is freed
 * - prev is freed
 * - next is freed
 * - prev & next is freed
 *
 * @return coalesced block pointer
 */
void *coalesce(byte_p bp) {
  byte_p prev_bp = PREV_BLOCK_PTR(bp);
  byte_p next_bp = NEXT_BLOCK_PTR(bp);

  if (GET_ALLOC(prev_bp) && GET_ALLOC(next_bp)) {
    // none is freed, do nothing?
    return bp;
  }

  if (GET_ALLOC(prev_bp)) {
    // next is freed, 내 헤더와 next의 푸터의 값을 바꾼다.
    size_t extended_blocksize = GET_SIZE(bp) + GET_SIZE(next_bp);
    size_t packed = PACK(extended_blocksize, 0);

    PUT(HEADER_PTR(bp), packed);
    PUT(FOOTER_PTR(next_bp), packed);

    return bp;
  }

  if (GET_ALLOC(next_bp)) {
    // prev is freed, prev의 헤더와 내 푸터의 값을 바꾼다.
    size_t extended_blocksize = GET_SIZE(bp) + GET_SIZE(prev_bp);
    size_t packed = PACK(extended_blocksize, 0);

    PUT(HEADER_PTR(prev_bp), packed);
    PUT(FOOTER_PTR(bp), packed);

    return prev_bp;
  }

  // prev, next is freed, prev의 헤더와 next의 푸터의 값을 바꾼다.
  size_t extended_blocksize =
      GET_SIZE(prev_bp) + GET_SIZE(bp) + GET_SIZE(next_bp);
  size_t packed = PACK(extended_blocksize, 0);

  PUT(HEADER_PTR(prev_bp), packed);
  PUT(FOOTER_PTR(next_bp), packed);

  return prev_bp;
}
