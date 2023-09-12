/*
 * code from
 * https://github.com/Ashwin0794/15-213_malloc_lab_explicit_list/blob/master/mm.c
 *
 * mm.c - explicit free list malloc package for 32-bit. Implemented
 * using first fit in free list.
 *
 * HEADER-> 4 BYTES
 *          It will keep note of asize(asize which is multiple of 8)
 *          of allocated block. Because the asize is multiple of 8, using last
 *          3 bits(which will always be 0's) to maintain the allocation status.
 *          last bit -> current block is allocated or not.
 *          second last bit -> previous block is alloc or not.
 *
 * FOOTER-> 4 BYTES (exists only for free blocks)
 *          Same as header but only used when heap block is free. When block
 *          is free, then footer is used to find the size of previous block
 *          to get the starting of block. One of the reason to choose min block
 *          size as 16.
 *
 * Free list -> Finding first free block in the free list rather than in
 *              the complete list of blocks. Maintaining 2 pointers (8 bytes)
 *              in free block using the unwanted data space. Using doubly
 *              linked list and free list insertion at the head(free_list_head).
 *              Reason to choose min block size as 16 bytes.
 *
 * min block size is 16 bytes -
 * 4 bytes (header)
 * 4 bytes (free_list_prev_ptr)
 * 4 bytes (free_list_next_ptr)
 * 4 bytes (footer when in free_list)
 *
 * Padding -> 4 bytes
 *
 * Prologue header -> 4 bytes (8/1)
 *
 * Prologue footer -> 4 bytes (8/1)
 *
 * Allocated Block -> Pointer returned to user. It contains only header.
 *
 * Free Block -> It will conatin  header, 2 pointers and footer.
 *
 * Epilogue -> 4 bytes (0/1) or (0/3)
 *
 */

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "explicit_free_list_dynamic_allocator",
    /* First member's full name */
    "Ashwin",
    /* First member's email address */
    "ashwinmeenameiyappan@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 16
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((unsigned int)(size) + (ALIGNMENT - 1)) & ~0x7)

/* returns nearest multiple of ALIGNMENT */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = val)

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC_STATUS(p) (GET(p) & 0x7)
/* To get the allocated feilds  */
#define GET_ALLOC(p) (GET(p) & 0x1)            // current block
#define PREV_ALLOC(p) (((GET(p)) >> 1) & 0x1)  // prev block

// we have static free_list_head pointer which points to first free node
// get prev and next free block payload address

// members of free_list must be only 4 byte each.
typedef struct free_list {
  char *prev;
  char *next;
} free_list;

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and prev blocks
 *
 * PREV_BLKP macro(uses footer to fetch) can only be used to fetch prev_bp
 * if prev blk is free blk otherwise allocated prev block cannot be
 * fetched because it wil not have footer.
 * */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp)-WSIZE))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE((char *)(bp)-DSIZE))

#define PREV_FREE_CURR_FREE 0
#define PREV_FREE_CURR_ALLOC 1
#define PREV_ALLOC_CURR_FREE 2
#define PREV_ALLOC_CURR_ALLOC 3

/* private gloabal static variable which will always point to prologue block */
static char *heap_listp;
static free_list *free_list_head;
static unsigned int free_blocks; /* Not using. Just in case */

static void *extend_heap(size_t words);
// static void print_free_list();
static void *find_fit(size_t asize);
static void free_list_insertion(void *bp);
static void remove_from_free_list(void *bp);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
// static void print_heap();
int mm_check(void);

#ifdef DEBUG
#define MM_CHECK() mm_check()
#else
#define MM_CHECK()
#endif

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
  /* Create the initial empty heap */
  free_list_head = NULL;
  if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) {
    return -1;
  }
  PUT(heap_listp, 0);                             // padding
  PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));  // prologue header
  PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));  // prologue footer
  PUT(heap_listp + (3 * WSIZE), PACK(0, PREV_ALLOC_CURR_ALLOC));  // epilogue
  heap_listp += (2 * WSIZE);  // points to prologe footer

  if (!extend_heap(CHUNKSIZE / WSIZE)) {
    return -1;
  }
#ifdef DEBUG
  MM_CHECK();
#endif
  return 0;
}

static void *extend_heap(size_t words) {
  char *new_heap_block;
  size_t size;

  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if ((long)(new_heap_block = mem_sbrk(size)) == -1) {
    return NULL;
  }

  /* updating header and footer of extended heap block of size chunksize.
   * Header of new block will be epilogue of previous heap block
   * */

  if (PREV_ALLOC(HDRP(new_heap_block))) {
    /* This is the case where epilogue->status prev block allocated
     * and next block will be new epilogue block. So need not coalesce.*/
    PUT(HDRP(new_heap_block), PACK(size, PREV_ALLOC_CURR_FREE));
    PUT(FTRP(new_heap_block), PACK(size, PREV_ALLOC_CURR_FREE));

    /* new epilogue */
    PUT(HDRP(NEXT_BLKP(new_heap_block)), PACK(0, PREV_FREE_CURR_ALLOC));

  } else {
    /* This is the case where prev blkp is free and requires coalescing */
    PUT(HDRP(new_heap_block), PACK(size, PREV_FREE_CURR_FREE));
    PUT(FTRP(new_heap_block), PACK(size, PREV_FREE_CURR_FREE));

    /* new epilogue */
    PUT(HDRP(NEXT_BLKP(new_heap_block)), PACK(0, PREV_FREE_CURR_ALLOC));

    new_heap_block = coalesce(new_heap_block);
  }

  free_list_insertion(new_heap_block);

  return new_heap_block;
}

/* Can use for debugging pursoses if necessary */
// static void print_heap() {
//
//   int block_number = 1;
//   char *block = NEXT_BLKP(heap_listp);
//   unsigned int header_value = *(unsigned int *)(HDRP(block));
//
//   /* header_value will be 1 or 3 for epilogue */
//   while ((block) <= ((char *)mem_heap_hi())) {
//     printf("%d header_value is %u\n",block_number, header_value);
//     block = NEXT_BLKP(block);
//     header_value = *((unsigned int *)(HDRP(block)));
//     block_number++;
//     if (header_value == 1u || header_value == 3u) {
//       printf("epilogue block \n");
//     }
//   }
// }

/* Can use for debugging purposes if necessary */
// static void print_free_list() {
//
//   int free_block_number = 1;
//   if (free_list_head == NULL) {
//     printf("free_list_head is NULL\n");
//     return;
//   }
//   free_list *traverse = (free_list *)free_list_head;
//   while (traverse != NULL) {
//     printf("header of %d free block ptr %u\n",
//                 free_block_number, *((unsigned int *)(HDRP(traverse))));
//     printf("footer of %d free block ptr %u\n",
//                 free_block_number, *((unsigned int *)(FTRP(traverse))));
//     traverse = (free_list *)(traverse->next);
//     free_block_number++;
//     if (traverse == NULL)
//       printf("traverse is NULL\n");
//   }
// }

static void *find_fit(size_t asize) {
  if (free_list_head == NULL) {
    return NULL;
  }
  free_list *free_list_traversal = free_list_head;
  while (free_list_traversal != NULL) {
    if (GET_SIZE(HDRP(free_list_traversal)) >= asize) {
      return free_list_traversal;
    }
    free_list_traversal = (free_list *)(free_list_traversal->next);
  }
  return NULL;
}

/* free_list_insertion is inserting a block at the head of free list
 * not manipulating header and footer of free blocks
 * linked list (stack implementation) */

static void free_list_insertion(void *free_block) {
  if (!free_block) {
    printf("null ptr in free_list_insertion\n");
    return;
  }

  free_list *new_free_block = (free_list *)free_block;

  if (free_list_head == NULL) {
    new_free_block->prev = NULL;
    new_free_block->next = NULL;
    free_list_head = new_free_block;
    free_blocks = 1;

  } else {
    new_free_block->next = (char *)free_list_head;
    new_free_block->prev = NULL;
    free_list_head->prev = (char *)new_free_block;
    free_list_head = new_free_block;
    free_blocks++;
  }
}

/* bp is a free block address
 * removing free block bp from free_list
 * not manipulating header and footer of free block*/

static void remove_from_free_list(void *free_block_ptr) {
  free_list *curr = (free_list *)free_block_ptr;
  free_list *curr_prev = (free_list *)(curr->prev);
  free_list *curr_next = (free_list *)(curr->next);

  if ((curr->prev == NULL) && (curr->next == NULL)) {
    /* one free block in free_list which is free_list_head */
    free_list_head = NULL;

  } else if ((curr->prev == NULL) && (curr->next)) {
    /* 2 free blocks in free_list and want to remove 1st block */
    curr_next->prev = NULL;
    free_list_head = curr_next;

  } else if ((curr->next == NULL) && (curr->prev)) {
    /* last block in free_list removal */
    curr_prev->next = NULL;

  } else if ((curr->prev) && (curr->next)) {
    /* middle block in free_list */
    curr_next->prev = curr->prev;
    curr_prev->next = curr->next;
  }
  free_blocks -= 1;
}

/*  Packing the header with allocation bits mean:
 *  (size|0) -> prev blk free and curr blk free
 *  (size|1) -> prev blk free and curr blk alloc
 *  (size|2) -> prev blk alloc and curr blk free
 *  (size|3) -> prev blk alloc and curr blk alloc
 *
 *  */

static void place(void *free_block_ptr, size_t asize) {
  if (free_block_ptr == NULL) {
    printf("free_block_ptr is NULL in place()\n");
    return;
  }
  size_t free_block_size = GET_SIZE(HDRP(free_block_ptr));

  remove_from_free_list(free_block_ptr);

  if (free_block_size - asize >= (2 * DSIZE)) {
    if (PREV_ALLOC(HDRP(free_block_ptr))) {
      PUT(HDRP(free_block_ptr), PACK(asize, PREV_ALLOC_CURR_ALLOC));

    } else {
      PUT(HDRP(free_block_ptr), PACK(asize, PREV_FREE_CURR_ALLOC));
    }

    /* updating header and footer of the remaining space */
    size_t new_size = free_block_size - asize;
    PUT(HDRP(NEXT_BLKP(free_block_ptr)), PACK(new_size, PREV_ALLOC_CURR_FREE));
    PUT(FTRP(NEXT_BLKP(free_block_ptr)), PACK(new_size, PREV_ALLOC_CURR_FREE));

    /* Need not update header of next block as it would have been
     * updated previously.*/
    free_block_ptr = NEXT_BLKP(free_block_ptr);
    free_list_insertion(free_block_ptr);

  } else {
    /* Updating header of allocating block */
    if (PREV_ALLOC(HDRP(free_block_ptr))) {
      PUT(HDRP(free_block_ptr), PACK(free_block_size, PREV_ALLOC_CURR_ALLOC));
    } else {
      PUT(HDRP(free_block_ptr), PACK(free_block_size, PREV_FREE_CURR_ALLOC));
    }

    /* Updating next block's previous alloc bit in header */
    unsigned int next_blk_hdr = GET(HDRP(NEXT_BLKP(free_block_ptr)));
    PUT(HDRP(NEXT_BLKP(free_block_ptr)), PACK(next_blk_hdr, 2));
  }
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

void *mm_malloc(size_t size) {
  size_t asize;
  size_t extendsize;
  char *free_block_ptr;

  // Ignore spurious requests
  if (size == 0) {
    return NULL;
  }

  /* adjust block size to include overhead and alignment reqs */
  if (size <= (DSIZE + WSIZE)) {
    asize = 2 * DSIZE;

  } else {
    asize = (DSIZE - ((size - (DSIZE + WSIZE)) % DSIZE)) + size + WSIZE;
  }

  if ((free_block_ptr = find_fit(asize)) != NULL) {
    place(free_block_ptr, asize);
#ifdef DEBUG
    if (!MM_CHECK()) {
      printf("func() mm_malloc ->error in mm_check\n");
      exit(1);
    }
#endif
    return free_block_ptr;
  }
  /* extend new heap block which will be inserted into free_list by
   * extend_heap function */

  extendsize = MAX(asize, CHUNKSIZE);
  if ((free_block_ptr = extend_heap(extendsize / WSIZE)) == NULL) {
    printf("NULL returned by extend_heap() in mm_malloc()\n");
    return NULL;
  }

  /* place function will update header and footer and will put the
   * remaining space if available in free_list */

  place(free_block_ptr, asize);

#ifdef DEBUG
  if (!MM_CHECK()) {
    printf("func() mm_malloc-> error in mm_check\n");
    exit(1);
  }
#endif

  return free_block_ptr;
}

void mm_free(void *free_the_allocated_ptr) {
  if (free_the_allocated_ptr == NULL) {
    return;
  } else if ((((unsigned long int)free_the_allocated_ptr) % 8) != 0) {
    printf("mm_free() didn't recieve 8 byte aligned ptr\n");
    return;
  } else if (free_the_allocated_ptr < mem_heap_lo()) {
    printf("free_the_allocated_ptr is than heap in mm_free()\n");
    return;
  } else if (free_the_allocated_ptr > mem_heap_hi()) {
    printf("free_the_allocated_ptr is greater than heap in mm_free()\n");
    return;
  }

  free_the_allocated_ptr = coalesce(free_the_allocated_ptr);
  free_list_insertion(free_the_allocated_ptr);

#ifdef DEBUG
  if (!MM_CHECK()) {
    printf("func() mm_free->error in mm_check\n");
    exit(1);
  }
#endif
}

/* coalesce and updating header and footer of free block bp */

static void *coalesce(void *alloc_ptr) {
  if (alloc_ptr == NULL) {
    printf("null ptr in coalesce \n");
    return NULL;
  }
  size_t alloc_size = GET_SIZE(HDRP(alloc_ptr));

  int prev_alloc = PREV_ALLOC(HDRP(alloc_ptr));
  int next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(alloc_ptr)));

  if (prev_alloc && next_alloc) {
    PUT(HDRP(alloc_ptr), PACK(alloc_size, PREV_ALLOC_CURR_FREE));
    PUT(FTRP(alloc_ptr), PACK(alloc_size, PREV_ALLOC_CURR_FREE));

    void *next_alloc_ptr = NEXT_BLKP(alloc_ptr);
    size_t next_size = GET_SIZE(HDRP(next_alloc_ptr));
    PUT(HDRP(next_alloc_ptr), PACK(next_size, PREV_FREE_CURR_ALLOC));

  } else if ((!prev_alloc) && next_alloc) {
    // prev is free and next is allocated
    void *prev_ptr = PREV_BLKP(alloc_ptr);
    remove_from_free_list(prev_ptr);
    size_t tsize = GET_SIZE(HDRP(prev_ptr)) + alloc_size;

    alloc_ptr = prev_ptr;
    PUT(HDRP(alloc_ptr), PACK(tsize, GET_ALLOC_STATUS(HDRP(alloc_ptr))));
    PUT(FTRP(alloc_ptr), PACK(tsize, GET_ALLOC_STATUS(HDRP(alloc_ptr))));

    /* Header of next block's prev_alloc bit has to be set to 0
     * and need not update footer for next block as it is allocated  */

    void *next_alloc_ptr = NEXT_BLKP(alloc_ptr);
    PUT(HDRP(next_alloc_ptr),
        PACK(GET_SIZE(HDRP(next_alloc_ptr)), PREV_FREE_CURR_ALLOC));

  } else if (prev_alloc && (!next_alloc)) {
    // prev allocated and next is free
    void *next_ptr = NEXT_BLKP(alloc_ptr);
    remove_from_free_list(next_ptr);
    size_t tsize = GET_SIZE(HDRP(next_ptr)) + alloc_size;

    PUT(HDRP(alloc_ptr), PACK(tsize, PREV_ALLOC_CURR_FREE));
    PUT(FTRP(alloc_ptr), PACK(tsize, PREV_ALLOC_CURR_FREE));

    /* Need not update Header of next block's prev_alloc bit */

  } else {
    void *prev_ptr = PREV_BLKP(alloc_ptr);
    remove_from_free_list(prev_ptr);
    void *next_ptr = NEXT_BLKP(alloc_ptr);
    remove_from_free_list(next_ptr);
    size_t tsize =
        GET_SIZE(HDRP(prev_ptr)) + alloc_size + GET_SIZE(HDRP(next_ptr));

    alloc_ptr = prev_ptr;
    PUT(HDRP(alloc_ptr), PACK(tsize, GET_ALLOC_STATUS(HDRP(alloc_ptr))));
    PUT(FTRP(alloc_ptr), PACK(tsize, GET_ALLOC_STATUS(HDRP(alloc_ptr))));
  }
  return alloc_ptr;
}

void *mm_realloc(void *ptr, size_t size) {
  void *newptr;
  if (ptr == NULL) {
    newptr = mm_malloc(size);
    return newptr;
  }

  void *oldptr = ptr;
  unsigned int copySize;
  newptr = mm_malloc(size);
  if (newptr == NULL) {
    return NULL;
  }
  // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
  copySize = GET_SIZE(HDRP(oldptr));
  if (size < copySize) {
    copySize = size;
  }
  memcpy(newptr, oldptr, copySize);
  mm_free(oldptr);
#ifdef DEBUG
  if (!MM_CHECK()) {
    printf("error in mm_check in func() realloc\n");
    exit(1);
  }
#endif
  return newptr;
}

/* checking heap consistency ie. checking every block in heap
 * after mm_init(), mm_malloc(), mm_free() and realloc() function calls. */

int mm_check(void) {
  void *mem_block = NEXT_BLKP(heap_listp);

  /* checking for prologue header */
  unsigned int prologue_header = *((unsigned int *)heap_listp - 1);
  assert(prologue_header == 9u);

  /* checking for prologue footer */
  unsigned int prologue_footer = *((unsigned int *)heap_listp);
  assert(prologue_footer == 9u);

  /* checking for epilogue */
  int epilogue_value = *(int *)(((char *)mem_heap_hi()) - 3);
  assert((epilogue_value == 1) || (epilogue_value == 3));

  for (; mem_block < mem_heap_hi(); mem_block = NEXT_BLKP(mem_block)) {
    /* valid heap address */
    assert(mem_block <= mem_heap_hi());

    /* valid heap address */
    assert(mem_block > mem_heap_lo());

    /* heap address must be 8 byte aligned */
    assert((((unsigned long int)mem_block) % 8u) == 0u);

    /* if heap block is allocated */
    if (GET_ALLOC(HDRP(mem_block))) {
      if (!PREV_ALLOC(HDRP(NEXT_BLKP(mem_block)))) {
        printf("allocated heap block's NEXT_BLKP's prev alloc is not set\n");
        return 0;
      }
    } else {
      /* if heap block is free then*/

      /* next-block's prev alloc bit must be 0 */
      if (PREV_ALLOC(HDRP(NEXT_BLKP(mem_block)))) {
        printf("free heap block's NEXT_BLKP's prev alloc is set\n");
        return 0;
      }

      /* free block's header must be equal to footer */
      unsigned int header = *(unsigned int *)(HDRP(mem_block));
      unsigned int footer = *(unsigned int *)(FTRP(mem_block));
      assert(header == footer);

      /* prev ad next ptr's shouldn't be equal */
      free_list *free_mem_block = (free_list *)mem_block;
      free_list *free_mem_block_prev = (free_list *)(free_mem_block->prev);
      free_list *free_mem_block_next = (free_list *)(free_mem_block->next);

      if (!((free_mem_block_prev == NULL) && (free_mem_block_next == NULL)) &&
          (free_mem_block_prev == free_mem_block_next)) {
        printf("free_block_loop asssertion failed\n");
        return 0;
      }

      /* checking if free block is part of free list */
      free_list *traverse_free_list = free_list_head;
      int free_block_present = 0;

      while (traverse_free_list != NULL) {
        if (((free_list *)mem_block) == traverse_free_list) {
          free_block_present = 1;
        }
        traverse_free_list = (free_list *)(traverse_free_list->next);
      }
      if (!free_block_present) {
        printf("free block is not part of free_list\n");
        return 0;
      }

      /* checking for mem_block->prev 's header's alloc bit must be 0 */
      if (((free_list *)mem_block)->prev) {
        if (GET_ALLOC(HDRP(((free_list *)mem_block)->prev))) {
          printf("free mem_block->prev' header's alloc bit is set to 1\n");
          return 0;
        }
      }
      if (((free_list *)mem_block)->next) {
        if (GET_ALLOC(HDRP(((free_list *)mem_block)->next))) {
          printf("free mem_block->next' header's alloc bit is set to 1\n");
          return 0;
        }
      }

      /* checking for missed coalescing */
      if (!GET_ALLOC(HDRP(NEXT_BLKP(mem_block)))) {
        printf("get_alloc of hdrp of next blkp's mem_block is %d\n",
               GET_ALLOC(HDRP(NEXT_BLKP(mem_block))));
        printf("alloc status of current free block is  %d\n",
               GET_ALLOC_STATUS(HDRP(mem_block)));
        printf("alloc status of next block is  %d\n",
               GET_ALLOC_STATUS(HDRP(NEXT_BLKP(mem_block))));
      }
      assert(GET_ALLOC(HDRP(NEXT_BLKP(mem_block))) == 1);
      assert(PREV_ALLOC(HDRP(mem_block)) == 1);

    } /* end of else(free_block checking) */
  }   /* end of for loop */
  return 1;
} /* end of mm_check */