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

typedef unsigned long dword_t;

int mm_init(void);
void *mm_malloc(size_t size);
void *mm_realloc(void *bp, size_t size);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
inline static size_t adjust_size(size_t size);
inline static bool is_prologue(void *bp);
inline static bool is_epilogue(void *bp);
void *first_fit(size_t asize);
static void *first_fit_explicit(size_t asize);
static void insert_in_free_list(void *bp);
static void remove_from_free_list(void *bp);

void *g_prologue;
static void *g_free_list_head;

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

/**Global Variables*/
#define WSIZE sizeof(void *)
#define DSIZE (2 * WSIZE)
#define CHUNKSIZE (1 << 12)  // minimum size that can be extend

#define ALIGNMENT DSIZE
#define MINIMUM_BLOCK_SIZE (2 * ALIGNMENT)

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~(ALIGNMENT - 1))
#define SIZE_T_SIZE \
  (ALIGN(sizeof(size_t)))  // returns nearest multiple of ALIGNMENT

#define MAX(x, y) ((x) > (y) ? (x) : (y))

// header, footer에 들어갈 정보 (blocksize, allocated)를 묶는다.
#define PACK(size, alloc) ((size) | (alloc))

// read and write a word at address p
#define GET(p) (*(uintptr_t *)(p))
#define PUT(p, val) (*(uintptr_t *)(p) = (val))

// Unpack and Read specific field from address p
#define GET_SIZE(p) (GET(p) & ~(ALIGNMENT - 1))
#define GET_ALLOC(p) (GET(p) & 0x01)

// 헤더 포인터의 주소를 가리킨다. p는 payload의 첫번째 주소를 가리킨다.
#define HEADER(bp) ((void *)(bp)-WSIZE)
// 푸터 포인터의 주소를 가리킨다. p는 payload의 첫번째 주소를 가리킨다.
#define FOOTER(bp) ((void *)(bp) + GET_SIZE(HEADER(bp)) - DSIZE)

// 다음 블럭의 bp(base pointer)를 가리킨다.
#define NEXT_ADJ(bp) ((void *)(bp) + GET_SIZE(HEADER(bp)))
// 이전 블럭의 bp(base pointer)를 가리킨다.
#define PREV_ADJ(bp) ((void *)(bp)-GET_SIZE(((void *)(bp)-DSIZE)))

// get next pointer in the list, NULLable
#define NEXT_FREE(bp) (*(char **)(bp + WSIZE))
// get prev pointer in the list, NULLable
#define PREV_FREE(bp) (*(char **)(bp))

#define SET_NEXT_FREE(bp, qp) (NEXT_FREE(bp) = qp)
#define SET_PREV_FREE(bp, qp) (PREV_FREE(bp) = qp)

/**
 * Helper Functions
 */
static dword_t __offset(void *p);
static size_t __get_size(void *p) { return GET_SIZE(p); }
static bool __get_alloc(void *p) { return GET_ALLOC(p); }
static void *__header(void *bp) { return HEADER(bp); }
static void *__footer(void *bp) { return FOOTER(bp); }
static void *__next_adj(void *bp) { return NEXT_ADJ(bp); }
static void *__prev_adj(void *bp) { return PREV_ADJ(bp); }
static void *__next_free(void *bp) { return NEXT_FREE(bp); }
static void *__prev_free(void *bp) { return PREV_FREE(bp); }
// simple composite function that calls `__get_alloc(__header(bp))`
static bool __alloc_bp(void *bp) { return __get_alloc(__header(bp)); }
// simple composite function that calls `__get_size(__header(bp))`
static size_t __size_bp(void *bp) { return __get_size(__header(bp)); }

#ifdef DEBUG
/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp);
#endif  // DEBUG

/*
 * # mm_init - initialize the malloc package.
 *
 * Figure 9.42에 따르면, 힙 시작 첫번째 워드는 정렬을 위해 사용하지 않으며,
 * 0으로 초기화 되어있다. 바로 뒤에는 프롤로그 블록이 나오며, 페이로드 없이
 * 헤더와 푸터만 존재한다. 힙 영역 마지막 워드는 에필로그 블록으로,
 * 블록사이즈가 0으로 초기화 되어있다.
 */
int mm_init(void) {
  // 비어있는 힙 생성
  if (((g_prologue) = mem_sbrk(8 * WSIZE)) == (void *)-1) {
    return -1;
  }
  PUT(g_prologue + (0 * WSIZE), 0);               // alignment padding
  PUT(g_prologue + (1 * WSIZE), PACK(DSIZE, 1));  // prologue header
  PUT(g_prologue + (2 * WSIZE), PACK(DSIZE, 1));  // prologue footer
  PUT(g_prologue + (3 * WSIZE), PACK(0, 1));      // epilogue header

  g_prologue += (2 * WSIZE);  // points to 0-sized payload (=footer)
  g_free_list_head = g_prologue;

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
  void *bp;

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
void mm_free(void *bp) {
  if (bp == NULL) {
    return;
  }
  size_t size = GET_SIZE(HEADER(bp));
  PUT(HEADER(bp), PACK(size, 0));
  PUT(FOOTER(bp), PACK(size, 0));
  coalesce(bp);
}

/**
 * @brief minimize unnecessary allocation
 */
void *mm_realloc(void *bp, size_t size) {
  void *oldptr = bp;
  void *newptr;
  size_t copySize;
  void *next_bp = NEXT_ADJ(bp);
  size_t my_size = GET_SIZE(HEADER(bp));
  size_t next_size = GET_SIZE(HEADER(next_bp));
  size_t asize = adjust_size(size);

  if (size == 0) {
    mm_free(bp);
    return NULL;
  }

  if (!GET_ALLOC(HEADER(next_bp)) &&
      asize <= my_size + next_size - MINIMUM_BLOCK_SIZE) {
    // no need to call malloc
    dword_t packed = PACK(asize, 1);
    PUT(HEADER(bp), packed);
    PUT(FOOTER(bp), packed);
    // refresh free block
    next_size = my_size + next_size - asize;
    next_bp = NEXT_ADJ(bp);
    packed = PACK(next_size, 0);
    PUT(HEADER(next_bp), packed);
    PUT(FOOTER(next_bp), packed);
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
 */
void *extend_heap(size_t words) {
  void *old_epilogue;
  size_t size = words * WSIZE;

  // 정렬을 유지하기 위해 words를 2의 배수로 반올림한다.
  if (words & 1) {
    size = (words + 1) * WSIZE;
  }
  if ((uintptr_t)(old_epilogue = mem_sbrk(size)) == -1) {
    // sbrk returns last block and extend heap size
    return NULL;
  }

  /**
   * previous epilogue block is now free block
   * header of new block will be new epilogue
   */

  // 늘어난 힙 영역대로 헤더 푸터 에필로그 헤더를 재설정한다.
  PUT(HEADER(old_epilogue), PACK(size, 0));         // free block header
  PUT(FOOTER(old_epilogue), PACK(size, 0));         // free block footer
  PUT(HEADER(NEXT_ADJ(old_epilogue)), PACK(0, 1));  // new epilogue header

  // 기존 블럭이 해제되었더라면 병합해주어야지
  return coalesce(old_epilogue);
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
void *coalesce(void *bp) {
  void *prev_bp = PREV_ADJ(bp);
  void *next_bp = NEXT_ADJ(bp);
  const bool next_alloc = __alloc_bp(next_bp);
  const bool prev_alloc = __alloc_bp(prev_bp) || prev_bp == bp;
  size_t size = __size_bp(bp);

  if (prev_alloc && !next_alloc) {
    // next is only freed, change my header and footer
    size += __size_bp(next_bp);

    remove_from_free_list(next_bp);

    PUT(HEADER(bp), PACK(size, 0));
    PUT(FOOTER(next_bp), PACK(size, 0));
  } else if (!prev_alloc && next_alloc) {
    // prev is only freed, change prev's header and footer
    size += __size_bp(prev_bp);
    bp = prev_bp;

    remove_from_free_list(bp);

    PUT(HEADER(bp), PACK(size, 0));
    PUT(FOOTER(bp), PACK(size, 0));
  } else if (!prev_alloc && !next_alloc) {
    // both are freed
    size += __size_bp(prev_bp) + __size_bp(next_bp);

    remove_from_free_list(prev_bp);
    remove_from_free_list(next_bp);

    bp = prev_bp;

    PUT(HEADER(bp), PACK(size, 0));
    PUT(FOOTER(bp), PACK(size, 0));
  }

  insert_in_free_list(bp);

  return bp;
}

/**
 * @brief find_fit - first fit을 기준으로 찾아라
 *
 * @return asize <= BLOCK_SIZE - 2WSIZE를 만족하는 블럭 포인터 | NULL
 */
void *find_fit(size_t asize) { return first_fit(asize); }

void *first_fit(size_t asize) {
  for (void *cur = g_prologue; GET_SIZE(HEADER(cur)) > 0; cur = NEXT_ADJ(cur)) {
    if (!GET_ALLOC(HEADER(cur)) && (asize <= GET_SIZE(HEADER(cur)))) {
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
  size_t old_size = GET_SIZE(HEADER(bp));
  size_t free_size = old_size - asize;
  dword_t pack_alloc = PACK(asize, 1);  // 새로이 할당한 블럭의 헤더/푸터 값
  dword_t pack_free = PACK(free_size, 0);  // 쪼개진 블럭의 헤더/푸터 값

  // set header and footer for splitted block
  // minimum block size <= asize
  if (MINIMUM_BLOCK_SIZE <= free_size) {
    // set header and footer for my block
    PUT(HEADER(bp), pack_alloc);
    PUT(FOOTER(bp), pack_alloc);

    remove_from_free_list(bp);

    // set header and footer for free block
    bp = NEXT_ADJ(bp);
    PUT(HEADER(bp), pack_free);
    PUT(FOOTER(bp), pack_free);

    coalesce(bp);
  } else {
    // intentional internal fragmentation with padding bytes
    dword_t pack_all = PACK(old_size, 1);
    PUT(HEADER(bp), pack_all);
    PUT(FOOTER(bp), pack_all);

    remove_from_free_list(bp);
  }
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
    // size + (WSIZE) + (WSIZE) of aligned by ALIGNMENT
    asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
  }
  return asize;
}

inline bool is_prologue(void *bp) {
  return GET_SIZE(HEADER(bp)) == DSIZE && GET_ALLOC(HEADER(bp));
}

inline bool is_epilogue(void *bp) {
  return GET_SIZE(HEADER(bp)) == 0 && GET_ALLOC(HEADER(bp));
}

dword_t __offset(void *p) {
  return (dword_t)((uintptr_t)p - (uintptr_t)g_prologue);
}

/**
 * @brief finds a fit for a block with `asize` bytes from the free list
 * @improvement: special case that expand heap size in itself
 */
static void *first_fit_explicit(size_t asize) {
  for (void *bp = g_free_list_head; __alloc_bp(bp) == 0; bp = __next_free(bp)) {
    if (asize <= (size_t)__size_bp(bp)) {
      return bp;
    }
  }
  return NULL;
}

/// @brief inserts the free block pointer into the free list
static void insert_in_free_list(void *bp) {
  SET_NEXT_FREE(bp, g_free_list_head);  // bp.next = head
  SET_PREV_FREE(g_free_list_head, bp);  // head.prev = bp
  SET_PREV_FREE(bp, NULL);              // bp.prev = NULL
  g_free_list_head = bp;
}

/// @brief removes the free block pointer from the free list
static void remove_from_free_list(void *bp) {
  if (PREV_FREE(bp)) {
    // bp.prev.next = bp.next
    SET_NEXT_FREE(PREV_FREE(bp), NEXT_FREE(bp));
  } else {
    // head = bp.next
    g_free_list_head = NEXT_FREE(bp);
  }
  // bp.next.prev = bp.prev
  SET_PREV_FREE(NEXT_FREE(bp), PREV_FREE(bp));
}

#ifdef DEBUG

/*
 * The remaining routines are heap consistency checker routines.
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void checkblock(void *bp) {
  if ((uintptr_t)bp % DSIZE)
    printf("Error: %p is not doubleword aligned\n", bp);
  if (GET(HDRP(bp)) != GET(FTRP(bp)))
    printf("Error: header does not match footer\n");
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency.
 */
void checkheap(bool verbose) {
  void *bp;

  if (verbose) printf("Heap (%p):\n", heap_listp);

  if (GET_SIZE(HDRP(heap_listp)) != DSIZE || !GET_ALLOC(HDRP(heap_listp)))
    printf("Bad prologue header\n");
  checkblock(heap_listp);

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = (void *)NEXT_BLKP(bp)) {
    if (verbose) printblock(bp);
    checkblock(bp);
  }

  if (verbose) printblock(bp);
  if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
    printf("Bad epilogue header\n");
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void printblock(void *bp) {
  bool halloc, falloc;
  size_t hsize, fsize;

  checkheap(false);
  hsize = GET_SIZE(HDRP(bp));
  halloc = GET_ALLOC(HDRP(bp));
  fsize = GET_SIZE(FTRP(bp));
  falloc = GET_ALLOC(FTRP(bp));

  if (hsize == 0) {
    printf("%p: end of heap\n", bp);
    return;
  }

  printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, hsize,
         (halloc ? 'a' : 'f'), fsize, (falloc ? 'a' : 'f'));
}
#endif  // DEBUG