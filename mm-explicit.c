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
#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

typedef char *byte_p;

int mm_init(void);
void *mm_malloc(size_t size);
void *mm_realloc(void *ptr, size_t size);
static void *extend_heap(size_t words);
static void *coalesce(byte_p bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
inline static size_t adjust_size(size_t size);
void *first_fit(size_t asize);
void *next_fit(size_t asize);
void insert_front(void *elem);
void *pop_front(void *elem);
void pop(void *elem);

void *g_prologue;  // 이중연결리스트의 마지막 노드를 의미
void *g_cur;
void *g_top;

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
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/**
 * SECTION Constants and Macros
 * Figure 9.43 코드가 누락되어 추가함.
 */
#define WSIZE 4  //  워드 사이즈 (헤더, 푸터 사이즈) in bytes
#define DSIZE 8  // 더블 워드 사이즈 in bytes
#define CHUNKSIZE (1 << 12)     // 힙 추가 시 요청할 크기 in bytes
#define MIN_BLK_SIZE WSIZE * 4  // header, footer

#define MAX(x, y) ((x) > (y) ? (x) : (y))

// header, footer에 들어갈 정보 (blocksize, allocated)를 묶는다.
#define PACK(size, alloc) ((size) | (alloc))

// read and write a word at address p
#define GET(p) (*(size_t *)(p))
#define PUT(p, val) (*(size_t *)(p) = (val))
#define GETADDR(p) (*(byte_p *)(p))
#define PUTADDR(p, addr) (*(byte_p *)(p) = (byte_p)(addr))

// Unpack and Read specific field from address p
#define GET_SIZE(p) (size_t)(GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x01)

// 헤더 포인터의 주소를 가리킨다. p는 payload의 첫번째 주소를 가리킨다.
#define HEADER_PTR(bp) (void *)((byte_p)(bp)-WSIZE)
// 푸터 포인터의 주소를 가리킨다. p는 payload의 첫번째 주소를 가리킨다.
#define FOOTER_PTR(bp) ((byte_p)(bp) + GET_SIZE(HEADER_PTR(bp)) - DSIZE)

// 다음 블럭의 bp(base pointer)를 가리킨다.
#define NEXT_BLOCK_PTR(bp) (void *)((byte_p)(bp) + GET_SIZE(HEADER_PTR(bp)))
// 이전 블럭의 bp(base pointer)를 가리킨다.
#define PREV_BLOCK_PTR(bp) (void *)((byte_p)(bp)-GET_SIZE(((byte_p)(bp)-DSIZE)))

///!SECTION

/**
 * Helper Functions
 */
static size_t __offset(void *p);
inline static bool __is_prologue(void *bp);
inline static bool __is_epilogue(void *bp);
static size_t __get_size(void *p) { return GET_SIZE(p); }
static bool __get_alloc(void *p) { return GET_ALLOC(p); }
static byte_p __header_ptr(void *bp) { return HEADER_PTR(bp); }
static byte_p __footer_ptr(void *bp) { return FOOTER_PTR(bp); }
static void *__next_block_ptr(void *bp) { return NEXT_BLOCK_PTR(bp); }
static void *__prev_block_ptr(void *bp) { return PREV_BLOCK_PTR(bp); }
static void *__prev_free_ptr(void *bp) { return bp; }
static void *__next_free_ptr(void *bp) {
  return (void *)((byte_p *)bp + WSIZE);
}
static void *__getaddr(void *p) { return GETADDR(p); }
static void __putaddr(void *p, void *addr) { PUTADDR(p, addr); }

/*
 * # mm_init - initialize the malloc package.
 *
 * alignment를 16으로, WSIZE를 4로 주었기 때문에 정렬을 위해 첫 3워드는
 * 패딩바이트로, 그 뒤부터 각각 header, prev, next, footer, header 순으로
 * 들어온다.
 *
 * pipe(|): alignment
 *
 * |                          |                               |
 * +-----+-----+-----+--------+------+------+--------+--------+
 * | pad | pad | pad | header | prev | next | footer | header |
 * +-----+-----+-----+--------+------+------+--------+--------+
 * |                          ^                               ^
 *                         prologue                           |
 *                                                         epilogue
 */
int mm_init(void) {
  // 비어있는 힙 생성
  if (((g_prologue) = mem_sbrk(2 * MIN_BLK_SIZE)) == (void *)-1) {
    return -1;
  }
  PUT(g_prologue + (0 * WSIZE), 0);                      // alignment padding
  PUT(g_prologue + (1 * WSIZE), 0);                      // alignment padding
  PUT(g_prologue + (2 * WSIZE), 0);                      // alignment padding
  PUT(g_prologue + (3 * WSIZE), PACK(MIN_BLK_SIZE, 1));  // prologue header
  PUT(g_prologue + (4 * WSIZE), (size_t)g_top);          // previous pointer
  PUT(g_prologue + (5 * WSIZE), (size_t)NULL);           // next pointer
  PUT(g_prologue + (6 * WSIZE), PACK(MIN_BLK_SIZE, 1));  // prologue footer
  PUT(g_prologue + (7 * WSIZE), PACK(0, 1));             // epilogue header

  g_prologue += (4 * WSIZE);  // go to prologue header
  g_cur = g_prologue;
  g_top = g_prologue;

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
  size_t asize;       // adjusted block size
  size_t extendsize;  // amount to extend heap if no fit
  byte_p bp;

  // ignore spurious requests
  if (size == 0) {
    return NULL;
  }

  // adjust block size to include overhead and alignment requirements
  asize = adjust_size(size);

  // search the free list for a fit
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }

  // no fit found. get more memory and place the block
  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
    return NULL;
  }
  place(bp, asize);
  return bp;
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

/**
 * @brief minimize unnecessary allocation
 */
void *mm_realloc(void *bp, size_t size) {
  void *oldptr = bp;
  void *newptr;
  size_t copySize;

  void *next_bp = NEXT_BLOCK_PTR(bp);
  size_t my_size = GET_SIZE(HEADER_PTR(bp));
  size_t next_size = GET_SIZE(HEADER_PTR(next_bp));
  size_t asize = adjust_size(size);
  if (!GET_ALLOC(HEADER_PTR(next_bp)) &&
      asize <= my_size + next_size - MIN_BLK_SIZE) {
    // no need to call malloc
    size_t packed = PACK(asize, 1);
    PUT(HEADER_PTR(bp), packed);
    PUT(FOOTER_PTR(bp), packed);
    // refresh free block
    next_size = my_size + next_size - asize;
    next_bp = NEXT_BLOCK_PTR(bp);
    packed = PACK(next_size, 0);
    PUT(HEADER_PTR(next_bp), packed);
    PUT(FOOTER_PTR(next_bp), packed);
    return bp;
  }

  newptr = mm_malloc(size);
  if (newptr == NULL) return NULL;
  copySize = *(size_t *)((char *)oldptr - WSIZE) - 1;
  if (size < copySize) copySize = size;
  memcpy(newptr, oldptr, copySize);
  mm_free(oldptr);
  return newptr;
}

/**
 * # extend_heap - 지정한 블록 개수만큼 힙 영역을 추가한다.
 *
 */
void *extend_heap(size_t words) {
  void *bp;
  size_t size = words * WSIZE;

  // 정렬을 유지하기 위해 words를 2의 배수로 반올림한다.
  if (words % 2 != 0) {
    size = (words + 1) * WSIZE;
  }
  // sbrk는 이전 힙 영역의 마지막 위치를 리턴한다.
  if ((long)(bp = mem_sbrk(size)) == -1) {
    return NULL;
  }
  // 늘어난 힙 영역대로 헤더 푸터 에필로그 헤더를 재설정한다.
  PUT(HEADER_PTR(bp), PACK(size, 0));               // free block header
  PUT(FOOTER_PTR(bp), PACK(size, 0));               // free block footer
  PUT(HEADER_PTR(NEXT_BLOCK_PTR(bp)), PACK(0, 1));  // new epilogue header

  // add to linked list
  insert_front(bp);

  // 기존 블럭이 해제되었더라면 병합해주어야지
  return coalesce(bp);
}

/**
 * coalesce - prev, next 블럭과 병합을 시도한다.
 *
 * cases:
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

  if (GET_ALLOC(HEADER_PTR(prev_bp)) && GET_ALLOC(HEADER_PTR(next_bp))) {
    // none is freed, do nothing?
    return bp;
  }

  // ∵ bp will be merged and be re-pushed into the list soon!
  pop(bp);

  if (!GET_ALLOC(HEADER_PTR(prev_bp)) && GET_ALLOC(HEADER_PTR(next_bp))) {
    // prev is freed, prev의 헤더와 내 푸터의 값을 바꾼다.
    size_t extended_blocksize =
        GET_SIZE(HEADER_PTR(bp)) + GET_SIZE(HEADER_PTR(prev_bp));
    size_t packed = PACK(extended_blocksize, 0);

    pop(prev_bp);

    // make prev_bp the bigger chunk
    PUT(HEADER_PTR(prev_bp), packed);
    PUT(FOOTER_PTR(bp), packed);

    insert_front(prev_bp);
    g_cur = prev_bp;
    return prev_bp;
  }

  if (!GET_ALLOC(HEADER_PTR(next_bp)) && GET_ALLOC(HEADER_PTR(prev_bp))) {
    // next is freed, 내 헤더와 next의 푸터의 값을 바꾼다.
    size_t extended_blocksize =
        GET_SIZE(HEADER_PTR(bp)) + GET_SIZE(HEADER_PTR(next_bp));
    size_t packed = PACK(extended_blocksize, 0);

    pop(next_bp);

    // make bp the bigger chunk
    PUT(HEADER_PTR(bp), packed);
    PUT(FOOTER_PTR(next_bp), packed);

    insert_front(bp);

    g_cur = bp;
    return bp;
  }

  // prev, next is freed, prev의 헤더와 next의 푸터의 값을 바꾼다.
  size_t extended_blocksize = GET_SIZE(HEADER_PTR(prev_bp)) +
                              GET_SIZE(HEADER_PTR(bp)) +
                              GET_SIZE(HEADER_PTR(next_bp));
  size_t packed = PACK(extended_blocksize, 0);

  pop(prev_bp);
  pop(next_bp);

  // make prev_bp the bigger chunk
  PUT(HEADER_PTR(prev_bp), packed);
  PUT(FOOTER_PTR(next_bp), packed);

  insert_front(prev_bp);

  g_cur = prev_bp;
  return prev_bp;
}

/**
 * @brief find_fit - first fit을 기준으로 찾아라
 *
 * @return asize <= BLOCK_SIZE - 2WSIZE를 만족하는 블럭 포인터 | NULL
 */
void *find_fit(size_t asize) { return first_fit(asize); }

void *first_fit(size_t asize) {
  for (void *cur = g_prologue; GET_SIZE(HEADER_PTR(cur)) > 0;
       cur = NEXT_BLOCK_PTR(cur)) {
    if (!GET_ALLOC(HEADER_PTR(cur)) && (asize <= GET_SIZE(HEADER_PTR(cur)))) {
      return cur;
    }
  }

  return NULL;
}

void *next_fit(size_t asize) {
  // g_cur -> epilogue
  for (void *cur = g_cur; GET_SIZE(HEADER_PTR(cur)) > 0;
       cur = NEXT_BLOCK_PTR(cur)) {
    void *p = HEADER_PTR(cur);
    if (!GET_ALLOC(p) && asize <= GET_SIZE(p)) {
      g_cur = cur;
      return cur;
    }
  }

  // prologue -> g_cur
  for (void *cur = g_prologue; cur < g_cur; cur = NEXT_BLOCK_PTR(cur)) {
    void *p = HEADER_PTR(cur);
    if (!GET_ALLOC(p) && asize <= GET_SIZE(p)) {
      g_cur = cur;
      return cur;
    }
  }
  return NULL;
}

/**
 * @brief place requested block at the beginning of the free block
 *
 * find_fit, extend_heap의 리턴값은 `asize`가 들어갈 공간이 주어진 블럭의
 * 주소값이다. 우리가 할 건 bp에 헤더와 푸터를 달고 쪼개진 free block에 헤더와
 * 푸터를 다는 것이다.
 */
void place(void *bp, size_t asize) {
  size_t old_size = GET_SIZE(HEADER_PTR(bp));
  size_t free_size = old_size - asize;
  size_t pack_alloc = PACK(asize, 1);  // 새로이 할당한 블럭의 헤더/푸터 값
  size_t pack_free = PACK(free_size, 0);  // 쪼개진 블럭의 헤더/푸터 값

  pop(bp);

  // set header and footer for splitted block
  // minimum block size <= asize
  if (MIN_BLK_SIZE <= free_size) {
    // set header and footer for my block
    PUT(HEADER_PTR(bp), pack_alloc);
    PUT(FOOTER_PTR(bp), pack_alloc);
    // set header and footer for free block
    byte_p splitted_bp = NEXT_BLOCK_PTR(bp);
    PUT(HEADER_PTR(splitted_bp), pack_free);
    PUT(FOOTER_PTR(splitted_bp), pack_free);
  } else {
    // intentional internal fragmentation with padding bytes
    size_t pack_all = PACK(old_size, 1);
    PUT(HEADER_PTR(bp), pack_all);
    PUT(FOOTER_PTR(bp), pack_all);
  }

  g_cur = bp;
}

/**
 * @brief size that can cover additional DWORDs, align 8-byte
 */
inline size_t adjust_size(size_t size) {
  size_t asize;
  if (size <= DSIZE) {
    asize = 2 * DSIZE;  // for header and footer
  } else {
    // size + header + footer + padding 포함한 DSIZE 기준으로 정렬된 블럭의 크기
    // (bytes)
    asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
  }
  return asize;
}

inline bool __is_prologue(void *bp) {
  return GET_SIZE(HEADER_PTR(bp)) == DSIZE && GET_ALLOC(HEADER_PTR(bp));
}

inline bool __is_epilogue(void *bp) {
  return GET_SIZE(HEADER_PTR(bp)) == 0 && GET_ALLOC(HEADER_PTR(bp));
}

size_t __offset(void *p) { return (size_t)((byte_p)p - (byte_p)g_prologue); }

/**
 * @brief top과 top의 next 사이에 elem을 추가한다.
 */
void insert_front(void *bp) {
  PUTADDR(__next_free_ptr(bp), g_top);
  PUTADDR(__prev_free_ptr(g_top), bp);
  PUTADDR(g_top, bp);
}

/**
 * @brief g_top 위치를 변경하고 리턴할 원소와의 연결을 끊는다.
 */
void *pop_front(void *elem) {
  void *ret = g_top;
  PUTADDR(__prev_free_ptr(GETADDR(__next_free_ptr(g_top))), NULL);
  PUTADDR(__next_free_ptr(g_top), NULL);
  g_top = GETADDR(__next_free_ptr(g_top));
  return ret;
}

/**
 * @brief elem을 리스트에서 꺼낸다. 앞, 뒤 적절하게 연결한다.
 */
void pop(void *elem) {
  void *prev = __prev_free_ptr(__getaddr(elem));
  void *next = __next_free_ptr(__getaddr(elem));
  if (prev != NULL) {
    __putaddr(__next_free_ptr(prev), next);
  }
  if (next != NULL) {
    __putaddr(__next_free_ptr(next), prev);
  }
}
