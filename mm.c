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

/*  Experiments to run:
 *  - inline keyword
 *  - which node in trie for bestfit
 *  - go left / right based on math vs logic
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

// My Global Variable
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

/* Basic constants and types*/
#ifndef NULL
#define NULL ((void *)(0))
#endif
/* struct freenode
 *
 * This is the structure _inside_ the freespace (doesn't include header/footer)
 *
 */
struct freenode 
{
  struct freenode *next;  // next freenode of the same size (stack)
  // NOTE: left and right _must_ be in order and next to eachother
  struct freenode *children[2]; 
  struct freenode **prev; // pointer to the _only_ pointer that points here
};
#define WSIZE       (4)       /* Word and header/footer size (bytes) */
#define WTYPE       unsigned int  // type to use for word sized ints
#define NTYPE       unsigned long
#define DSIZE       (2*WSIZE)       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */
#define POINTER_SIZE (sizeof(void *)) /* size of pointers */
#define BITNESS  (8*sizeof(NTYPE))
#define MIN_SIZE ((size_t)(ALIGN(sizeof(struct freenode))))
#define MAX_SIZE ((size_t)((1<<18)-ALIGNMENT))
#define BIT_OFFSET (__builtin_clzl(MAX_SIZE))
#define BIT_COUNT  (1 + (__builtin_clzl(MIN_SIZE)) - BIT_OFFSET)
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



// Basic internal implicit list / heap operations
static inline void *extend_heap(size_t bytes); /* grow heap bytes size */
static inline void *coalesce(void *bp); /* merge newly free block with neighbors 
                                             and add to freelist */
/* allocate asize at bp (possibly spliting) and remove from freelist */
static inline void place(void* bp, size_t asize); 
/* finds best fit in the free list or allocates new space if not */
static inline void *find_fit(size_t asize);

#if DEBUG
int mm_check(void);
#endif

// explicit freelist functions
static void *freelist_add(void *bp);
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
  if ((long)(bp = mem_sbrk(DSIZE+size)) == -1)
      return NULL;
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

// coalesce takes a pointer to a block
// that is NOT in the free list
// tries to merge it with its neighbors
// and then adds the new block to the freelist
// returning a pointer to that newly added block
static inline void *coalesce(void *bp)
{
  WTYPE prev_alloc = IS_ALLOC(FOOTER(PREV_BLKP(bp)));
  WTYPE next_alloc = IS_ALLOC(HEADER(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HEADER(bp));
  if (prev_alloc && next_alloc) {
    // no op
  }
  else if (prev_alloc && !next_alloc) {
    #if DEBUG>1
      fprintf(stderr, "Coalescing %p with next block\n", bp);
    #endif
    freelist_remove(NEXT_BLKP(bp));
    size += DSIZE + GET_SIZE(HEADER(NEXT_BLKP(bp)));
    PUT(HEADER(bp), PACK(size, 0));
    PUT(FOOTER(bp), PACK(size, 0));
  }
  else if (!prev_alloc && next_alloc) {
    #if DEBUG>1
      fprintf(stderr, "Coalescing %p with previous block\n", bp);
    #endif
    freelist_remove(PREV_BLKP(bp));
    size += DSIZE + GET_SIZE(HEADER(PREV_BLKP(bp)));
    PUT(FOOTER(bp), PACK(size, 0));
    PUT(HEADER(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  else {
    #if DEBUG>1
      fprintf(stderr, "Coalescing %p with neighboring blocks\n", bp);
    #endif
    freelist_remove(PREV_BLKP(bp));
    freelist_remove(NEXT_BLKP(bp));
    size += GET_SIZE(HEADER(PREV_BLKP(bp))) +
    GET_SIZE(FOOTER(NEXT_BLKP(bp))) + (DSIZE*2);
    PUT(HEADER(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FOOTER(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  return freelist_add(bp); 
}

void *mm_malloc(size_t size)
{
  #if DEBUG>1
    fprintf(stderr, "+malloc called with size=%lu\n", size);
  #endif
  size_t extendsize;
  char *bp;
  // Ignore spurious requests
  if (size == 0)
    return NULL;
  /* Adjust block size to include overhead and alignment reqs. */
  if (size < MIN_SIZE)
    size = MIN_SIZE;
  else
    size = ALIGN(size);
  /* Search the free list for a fit */
  if ((bp = find_fit(size)) != NULL) {
    place(bp, size);
  }
  #if DEBUG
    if (!mm_check()) {
      fprintf(stderr, "!!!!!!!!! mm_check failed !!!!!!!!!!\n");
      return NULL;
    }
  #endif
  return bp;
}

// finds best fit or allocates new space if needed
// NOTE: asize is pre-aligned
static inline void *find_fit(size_t asize)
{
  size_t extendsize;
  void *bp;
  if ((bp = freelist_bestfit(asize)) != NULL) {
    return bp;
  }

  /* No fit found. Get more memory and place the block */
  extendsize = MAX(asize,CHUNKSIZE);
  // TODO: Remove possible inefficiency of adding then immediately removing noew space
  return extend_heap(extendsize)
}

// actually allocate this block with size asize
static inline void place(void* bp, size_t asize) {
  size_t csize = GET_SIZE(HEADER(bp));
  freelist_remove(bp);
  if ((csize - asize) >= MIN_SIZE + DSIZE) {
    PUT(HEADER(bp), PACK(asize, 1));
    PUT(FOOTER(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HEADER(bp), PACK(csize - asize - DSIZE, 0));
    PUT(FOOTER(bp), PACK(csize - asize - DSIZE, 0));
    freelist_add(bp);
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

/////////////////////
// freelist code
////////////////////

/* Note: No coalescing etc needs to happen here, nor checking of free bit
 *
 */

// zero indexed from most significant bit bit-accessor for unsigned long 
#define BIT_N(s,n) ((((NTYPE)(s))>>((BITNESS - 1) - (n))) & ((NTYPE)(1)))
// Gets the bin number for a size: note larger sizes -> smaller bin number
#define BIN_FOR(asize) ((__builtin_clzl(asize))-BIT_OFFSET)
#define BINP_AT(n) (&(((struct freenode **)((heap_listp)-BIN_OFFSET))[n]))

#define NEXT_TNODE(p,b) (&((p)->children[b]))

static struct freenode * rmost(struct freenode * n, NTYPE r);

static struct freenode * rmost(struct freenode * n, NTYPE r) {
  if (n->children[r] == NULL) {
    return NULL;
  }
  do {
    n = n->children[r];
  } while (n->children[r]);
  return n;
}

static void *freelist_add(void *bp) {
  size_t asize = GET_SIZE(FOOTER(bp));
  size_t bit = BIN_FOR(asize);
  struct freenode ** bin = BINP_AT(bit); // bin has the address of the bin pointer
  struct freenode * fn = (struct freenode *)bp;
  while(1) {
    if (*bin == NULL) {
      *bin = fn;
      fn->prev = bin;
      fn->next = fn->children[0] = fn->children[1] = NULL;
      return bp;
    }
    if (GET_SIZE(FOOTER(*bin)) == (WTYPE)(asize)) {
      fn->prev = bin;
      fn->next = *bin;
      fn->children[0] = (*bin)->children[0];
      (*bin)->children[0] = NULL;
      fn->children[1] = (*bin)->children[1];
      (*bin)->children[1] = NULL;
      *bin = fn;
      return bp;
    }
    bin = NEXT_TNODE(*bin, BIT_N(asize,++bit));
    #if DEBUG
      if (bit > 64) {
        fprintf(stderr, "!! Infinite loop in freelist_add!\n");
        return NULL;
      }
    #endif
  }
}

static void freelist_remove(void *bp) {
  struct freenode * fn = (struct freenode *)bp;
  // if part of LL
  if (fn->next) {
    fn->next->prev = fn->prev;
    *(fn->prev) = fn->next;
    fn->next->children[0] = fn->children[0];
    fn->next->children[1] = fn->children[1];
    return;
  }
  struct freenode * ance;
  // else if part of trie
  if (fn->children[0] != NULL) {
    ance = rmost(fn,0);
    *(ance->prev) = NULL;
    ance->children[0] = fn->children[0];
    ance->children[1] = fn->children[0];
  } else {
    // 0-most is definately NULL 
    ance = rmost(fn,1);
    if (ance) {
      *(ance->prev) = NULL;
      ance->children[0] = fn->children[0];
      ance->children[1] = fn->children[0];
    }
  }
  *(fn->prev) = ance;
}

static void *freelist_bestfit(size_t sz) {
  
}


//////////////////
// DEBUG ONLY CODE
//////////////////
#if DEBUG

int uncoalesced(void);
int inconsistant_footer(void);
int ends_in_epilogue(void);

// returns 0 IFF problem
int mm_check(void) {
  if(!ends_in_epilogue()) {
    fprintf(stderr, "!! The heap doesn't end in an epilogue!\n");
    return 0;
  }
  if(inconsistant_footer()) {
    fprintf(stderr, "!! Some blocks have inconsistant headers and footers!\n");
    return 0;
  }
  if(uncoalesced()) {
    fprintf(stderr, "!! Some blocks escaped coalescing!\n");
    return 0;
  }
  return 1;
}

int ends_in_epilogue(void) {
  void* ep = mem_heap_hi() + 1 - WSIZE;
  if (GET(ep) != PACK(0,1)) {
    return 0;
  } else {
    return 1;
  }
}

// returns the number of uncoalesced, neighboring blocks
int uncoalesced(void) {
  void *bp;
  int previous_free = 0;
  int number = 0;
  for (bp = heap_listp; GET_SIZE(HEADER(bp))>0; bp = NEXT_BLKP(bp)) {
    if (!IS_ALLOC(HEADER(bp))) {
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

int inconsistant_footer(void) {
  void *bp;
  int number = 0;
  for (bp = heap_listp; GET_SIZE(HEADER(bp))>0; bp = NEXT_BLKP(bp)) {
    if (HEADER(bp) != FOOTER(bp)) {
      number++;
    }
  }
  return number;
}

// END DEBUG CODE
#endif















