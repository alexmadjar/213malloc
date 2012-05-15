/*
 * mm.c
 *
 * Provides a b-trie based implementation of malloc similar to Doug Leigh's malloc
 *
 * In my convention the size stored in the header / footer is the size of the
 * allocatable block area and doesn't include the size of the header / footer
 * 
 * 
 * Important notes about this implementation:
 *    - There is no error checking without debug turned on
 *    - "int" is assumed to be 1 word
 *  
 * For a more complete description, see the comment at the end of the file.
 *
 * Author: Alex Madjar
 * License:  Don't use this for anything besides grading me (yet because it's not ready!)
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "amm668",
    /* First member's full name */
    "Alexander Madjar",
    /* First member's email address */
    "AlexanderMadjar2012@u.northwestern.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};




// Global Variable
char* heap_listp;  // Pointer to the start of the implicit heap list

//  Turn debugging code on
//     0 -> no debugging checks or output
//     1 -> low level checks
//     2 -> verbose output
//  All debug output is sent to stderr
#define DEBUG (2)

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT 
    NOTE: ALIGNMENT must be a multiple of two
 */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~(ALIGNMENT-1))

/* Basic constants*/
#ifndef NULL
#define NULL ((void *)(0))
#endif
#define WSIZE       (4)       /* Word and header/footer size (bytes) */
#define WTYPE       unsigned int  // type to use for word sized ints
#define DSIZE       (8)       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */
#define POINTER_SIZE (sizeof(void *)) /* size of pointers */
#define MIN_SIZE ((size_t)(ALIGN(4*POINTER_SIZE)))
#define MAX_SIZE ((size_t)((1<<18)-1))
#define BIT_OFFSET (__builtin_clzl(MAX_SIZE))
#define BIT_COUNT  ((size_t)(1 + (__builtin_clzl(MIN_SIZE)) - BIT_OFFSET))
#define BINS_SIZE ((size_t)(BIT_COUNT * POINTER_SIZE))
#define BIN_OFFSET ((size_t)(BINS_SIZE + WSIZE))

#define MAX(x, y) ((x) > (y)? (x) : (y))
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))
/* Read and write a word at address p */
#define GET(p)       (*(WTYPE *)(p))
#define PUT(p, val)  (*(WTYPE *)(p) = ((WTYPE)(val)))
/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define IS_ALLOC(p) (GET(p) & 0x1)

#define HEADER(bp) ((char *)(bp) - WSIZE)
#define FOOTER(bp) ((char *)(bp) + GET_SIZE(HEADER(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + DSIZE + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - DSIZE - GET_SIZE(((char *)(bp) - DSIZE)))

static inline void *extend_heap(size_t bytes);
static inline void *coalesce(void *bp);
static inline void place(void* bp, size_t asize);
static inline void *find_fit(size_t asize);
#if DEBUG
int mm_check(void);
#endif
// freelist functions
static void freelist_add(void *bp);
static void freelist_remove(void *bp);
static void *freelist_bestfit(size_t sz);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
#if DEBUG>1
   fprintf(stderr, "Initializing heap with %lu BINS_SIZE\n", BINS_SIZE);
#endif
   /* Create the initial empty heap */
   if ((heap_listp = mem_sbrk((4*WSIZE) + BINS_SIZE)) == (void *)-1)
     return -1;
   if (ALIGN(BINS_SIZE) == BINS_SIZE) {
     PUT(heap_listp, 0); /* Alignment padding */
     heap_listp += WSIZE;
   }
   memset(heap_listp, NULL, BINS_SIZE);
   heap_listp += BINS_SIZE;
   PUT(heap_listp, PACK(0, 1)); /* Prologue header */
   heap_listp += WSIZE;
   PUT(heap_listp, PACK(0, 1)); /* Prologue footer */
   PUT(heap_listp + WSIZE, PACK(0, 1)); /* Epilogue header */
  
   /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extend_heap(CHUNKSIZE) == NULL)
    return -1;
  return 0;
}

static inline void *extend_heap(size_t bytes) {
#if DEBUG>1
  fprintf(stderr, "extending the heap by %lu bytes\n", bytes);
#endif
  char *bp;
  size_t size;
#if DEBUG
  if (bytes < MIN_SIZE) {
    fprintf(stderr, "!!! Tried to extend heap by %lu bytes!\n", bytes);
    return NULL;
  }
#endif
  /* Allocate an even number of words to maintain alignment */
  size = ALIGN(bytes)
  if ((long)(bp = mem_sbrk(size)) == -1)
      return NULL;
  size -= DSIZE;
  /* Initialize free block header/footer and the epilogue header */
  PUT(HEADER(bp), PACK(size, 0)); /* Free block header */
  PUT(FOOTER(bp), PACK(size, 0)); /* Free block footer */
  // TODO: Understand how this doesn't seg fault
  //  I don't think it does cause it was in the starter code, but...
  PUT(HEADER(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

  /* Coalesce if the previous block was free */
  return coalesce(bp);
}

void mm_free(void *bp){
  size_t size = GET_SIZE(HEADER(bp));
#if DEBUG>1
  fprintf(stderr, "Call to free with pointer %p (size: %lu)\n", bp, size);
#endif
  PUT(HEADER(bp),PACK(size, 0));
  PUT(FOOTER(bp),PACK(size, 0)); 
  coalesce(bp);
#if DEBUG
  if (!mm_check()) {
    fprintf(stderr, "!!!!!!!!!mm_check failed!!!!!!!!\n");
  }
#endif
}


/////// REWRITTEN THROUGH HERE

// coalesce takes a pointer to a block
// that is NOT in the free list
// tries to merge it with its neighbors
// and then adds the new block to the freelist
// returning a pointer to that newly added block
static inline void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(FOOTER(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HEADER(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HEADER(bp));
  if (prev_alloc && next_alloc) {
    return bp;
  }
  else if (prev_alloc && !next_alloc) {
    size += GET_SIZE(HEADER(NEXT_BLKP(bp)));
    PUT(HEADER(bp), PACK(size, 0));
    PUT(FOOTER(bp), PACK(size,0));
  }
  else if (!prev_alloc && next_alloc) {
    size += GET_SIZE(HEADER(PREV_BLKP(bp)));
    PUT(FOOTER(bp), PACK(size, 0));
    PUT(HEADER(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  else {
    size += GET_SIZE(HEADER(PREV_BLKP(bp))) +
    GET_SIZE(FOOTER(NEXT_BLKP(bp)));
    PUT(HEADER(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FOOTER(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  return bp; 
}

void *mm_malloc(size_t size)
{
  size_t asize;
  size_t extendsize;
  char *bp;
  if (size == 0)
    return NULL;
  /* Adjust block size to include overhead and alignment reqs. */
  if (size <= DSIZE)
    asize = 2*DSIZE;
  else
    asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
  /* Search the free list for a fit */
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }
  /* No fit found. Get more memory and place the block */
  extendsize = MAX(asize,CHUNKSIZE);
  if ((bp = extend_heap(extendsize)) == NULL)
    return NULL;
  place(bp, asize);
  if (!mm_check()) {
    fprintf(stderr, "mm_check failed\n");
  }
  return bp;
}


static inline void *find_fit(size_t asize)
{
  void *bp;
  for (bp = heap_listp; GET_SIZE(HEADER(bp))>0; bp = NEXT_BLKP(bp)) {
    if (!GET_ALLOC(HEADER(bp)) && (asize <= GET_SIZE(HEADER(bp))))
      return bp;
  }
  return NULL;
}

static inline void place(void* bp, size_t asize) {
  size_t csize = GET_SIZE(HEADER(bp));

  if ((csize - asize) >= (2*DSIZE)) {
    PUT(HEADER(bp), PACK(asize, 1));
    PUT(FOOTER(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HEADER(bp), PACK(csize-asize, 0));
    PUT(FOOTER(bp), PACK(csize-asize, 0));
  } else {
    PUT(HEADER(bp), PACK(csize, 1));
    PUT(FOOTER(bp), PACK(csize, 1));
  }

}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * HINT: this will always work, so save making this more efficient for later
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - 8);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

// DEBUG ONLY CODE
#if DEBUG

int uncoalesced(void);

// returns 0 IFF problem
int mm_check(void) {
  if(uncoalesced()) {
    fprintf(stderr, "Some blocks escaped coalescing!\n");
    return 0;
  }
  return 1;
  //return !(uncoalesced());
}

// returns the number of uncoalesced, neighboring blocks
int uncoalesced(void) {
  void *bp;
  int previous_free = 0;
  int number = 0;
  for (bp = heap_listp; GET_SIZE(HEADER(bp))>0; bp = NEXT_BLKP(bp)) {
    if (!GET_ALLOC(HEADER(bp))) {
      if (previous_free) {
        number++;
      }
      previous_free = 1;
    } else {
      previous_free = 0;
    }
  }
  return number;
}

// END DEBUG CODE
#endif














