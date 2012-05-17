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
 *    - Should work on a wide array of machines (32/64 bit, embedded etc)
 *      because I tried to avoid type size assumptions. 
 *      This goal is however NOT THOROUGHLY TESTED and shouldn't be blindly relied on
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
 *  - no assert.h etc
 *  - extend heap right away
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

//  Turn debugging code on
//     0 -> no debugging checks or output
//     1 -> low level checks
//     2 -> verbose output
//  All debug output is sent to stderr
#define DEBUG (2)

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT 
    NOTE: ALIGNMENT must be a power of two
 */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~(ALIGNMENT-1))

/* Basic constants and types*/
#ifndef NULL
#  define NULL ((void *)(0))
#endif
/* struct freenode_t
 *
 * This is the structure _inside_ the freespace (doesn't include header/footer)
 *
 */
struct freenode_t 
{
  struct freenode_t *next;  // next freenode_t of the same size (stack)
  // NOTE: left and right _must_ be in order and next to eachother
  struct freenode_t *children[2]; 
  struct freenode_t **prev; // pointer to the _only_ pointer that points here
};
#define POINTER_SIZE (sizeof(void *)) /* size of pointers */
#define WSIZE (sizeof(size_t))
#define DSIZE (2*(WSIZE))
#define BITNESS  (8*POINTER_SIZE)
#define MIN_SIZE ((size_t)(ALIGN(sizeof(struct freenode_t))))
#define MAX_SIZE ((size_t)((1<<18)-ALIGNMENT))
#define BIT_OFFSET (__builtin_clzl(MAX_SIZE))
#define LSIG_BIT_OF_SIZE  (__builtin_clzl(ALIGNMENT))
#define BIT_COUNT  (1 + (__builtin_clzl(MIN_SIZE)) - BIT_OFFSET)

struct heaphead_t
{
  struct freenode_t *bins[BIT_COUNT];
  size_t prologue[2];
  size_t head[1];
};

// Our global heap pointer
struct heaphead_t * heap;

#define MAX(x, y) ((x) > (y)? (x) : (y))
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size_t)((size) | (alloc)))
/* Read the size and allocated fields from address p */
#define PACK_SIZE(packed)  ((packed) & ~(ALIGNMENT-1))
#define PACK_IS_ALLOC(packed) ((packed) & 0x1)
#define HEADER(bp) (((size_t *)(bp))[-1])
#define PREV_FOOTER(bp) (((size_t *)(bp))[-2])
#define GET_SIZE(p)  PACK_SIZE(HEADER(p))
#define IS_ALLOC(p)  PACK_IS_ALLOC(HEADER(p))
#define FOOTER(bp) (*((size_t *)(((char *)(bp)) + GET_SIZE(bp))))
#define NEXT_BLKP(bp) ((char *)(bp) + DSIZE + GET_SIZE(bp))
#define PREV_BLKP(bp) ((char *)(bp) - DSIZE - PACK_SIZE(PREV_FOOTER(bp)))



// Basic internal implicit list / heap operations
static inline void *extend_heap(size_t bytes); /* grow heap bytes size */
static inline void *coalesce(void *bp); /* merge newly free block with neighbors 
                                             and add to freelist */
/* allocate asize at bp (possibly spliting) and remove from freelist */
static inline void place(void* bp, size_t asize); 

#if DEBUG
int mm_check(void);
int check_defines(void);
#endif

// explicit freelist functions
static void *freelist_add(void *bp);
static void freelist_remove(void *bp);
static void *freelist_bestfit(size_t sz);

// redone through here

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
   #if DEBUG>1
      fprintf(stderr, "Initializing heap with %d bins\n", BIT_COUNT);
   #endif
   void * space;
   /* Create the initial empty heap */
   if ((space = mem_sbrk(ALIGN(sizeof(struct heaphead_t)))) == (void *)-1) {
    #if DEBUG
       fprintf(stderr, "!! unable to sbrk the header!\n");
    #endif
     return -1;
   }
   heap = (space + ALIGN(sizeof(struct heaphead_t)) - sizeof(struct heaphead_t));
   int a;
   for (a = 0; a < BIT_COUNT; a++) {
     heap->bins[a] = NULL;
   }
   heap->head[0] = heap->prologue[0] = heap->prologue[1] = PACK(0,1);

   #if DEBUG
      if(check_defines()) {
        fprintf(stderr, "!!  DEFINES are wack!\n");
        return -1;
      }
   #endif
  
   /* Extend the empty heap with a free block of CHUNKSIZE bytes */
 // if (extend_heap(CHUNKSIZE) == NULL)
 //   return -1;
  return 0;
}


// rewritten through here

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
  size = ALIGN(bytes);
  if ((long)(bp = mem_sbrk(DSIZE+size)) == -1)
      return NULL;
  /* Initialize free block header/footer and the epilogue header */
  HEADER(bp) = PACK(size, 0); /* Free block header */
  FOOTER(bp) = PACK(size, 0); /* Free block footer */
  HEADER(NEXT_BLKP(bp)) = PACK(0, 1); /* New epilogue header */
  // TODO: Not coellescing here could fragment space a bit
  return bp;
}

void mm_free(void *bp){
  size_t size = GET_SIZE(bp);
  #if DEBUG>1
    fprintf(stderr, "Call to free with pointer %p (size: %lu)\n", bp, size);
  #endif
  HEADER(bp) = PACK(size, 0);
  FOOTER(bp) = PACK(size, 0); 
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
  void *next = NEXT_BLKP(bp);
  int prev_alloc = PACK_IS_ALLOC(PREV_FOOTER(bp));
  int next_alloc = IS_ALLOC(next);
  size_t size = GET_SIZE(bp);
  if (prev_alloc && next_alloc) {
    // no op
  }
  else if (prev_alloc && !next_alloc) {
    #if DEBUG>1
      fprintf(stderr, "Coalescing %p with next block\n", bp);
    #endif
    freelist_remove(next);
    size += DSIZE + GET_SIZE(next);
    HEADER(bp) = PACK(size, 0);
    FOOTER(bp) = PACK(size, 0);
  }
  else if (!prev_alloc && next_alloc) {
    #if DEBUG>1
      fprintf(stderr, "Coalescing %p with previous block\n", bp);
    #endif
    freelist_remove(PREV_BLKP(bp));
    size += DSIZE + PACK_SIZE(PREV_FOOTER(bp));
    FOOTER(bp) = PACK(size, 0);
    bp = PREV_BLKP(bp);
    HEADER(bp) = PACK(size, 0);
  }
  else {
    #if DEBUG>1
      fprintf(stderr, "Coalescing %p with neighboring blocks\n", bp);
    #endif
    bp = PREV_BLKP(bp);
    freelist_remove(bp);
    freelist_remove(next);
    size += GET_SIZE(bp) +
    GET_SIZE(next) + (DSIZE*2);
    HEADER(bp) = PACK(size, 0);
    FOOTER(next) = PACK(size, 0);
  }
  bp = freelist_add(bp); 
  #if DEBUG
    if (!mm_check()) {
      fprintf(stderr, "!!!!!!!!!mm_check failed!!!!!!!!\n");
    }
  #endif
  return bp;
}

void *mm_malloc(size_t size)
{
  #if DEBUG>1
    fprintf(stderr, "+malloc called with size=%lu\n", size);
  #endif
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
  if ((bp = freelist_bestfit(size)) != NULL) {
    freelist_remove(bp);
    place(bp, size);
  } else {
    // TODO: play with this
    // size_t extendsize;
    // extendsize = MAX(CHUNKSIZE,size);
    if ((bp = extend_heap(size)) != NULL) {
      place(bp, size);
    }
  #if DEBUG
    else {
      fprintf(stderr, "!!! MALLOC FAILED!!! !!!!\n");
    }
  }
  if (!mm_check()) {
    fprintf(stderr, "!!!!!!!!! mm_check failed !!!!!!!!!!\n");
  }
  #endif
  return bp;
}

// actually allocate this block with size asize
static inline void place(void* bp, size_t asize) {
  size_t csize = GET_SIZE(bp);
  if ((csize - asize) >= MIN_SIZE + DSIZE) {
    HEADER(bp) = PACK(asize, 1);
    FOOTER(bp) = PACK(asize, 1);
    bp = NEXT_BLKP(bp);
    csize = csize - asize - DSIZE;
    HEADER(bp) = PACK(csize, 0);
    FOOTER(bp) = PACK(csize, 0);
    freelist_add(bp);
  } else {
    HEADER(bp) = PACK(csize, 1);
    FOOTER(bp) = PACK(csize, 1);
  }
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * HINT: this will always work, so save making this more efficient for later
 * TODO: More efficient version
 */
void *mm_realloc(void *ptr, size_t size)
{
    #if DEBUG>1
      fprintf(stderr, "reallocing block %p (size %lu) with new size %lu\n", ptr, GET_SIZE(ptr), size);
    #endif
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
#define BIT_N(s,n) ((((size_t)(s))>>((BITNESS - 1) - (n))) & ((size_t)(1)))
// Gets the bin number for a size: note larger sizes -> smaller bin number
#define BIN_FOR(asize) ((__builtin_clzl(asize))-BIT_OFFSET)

static struct freenode_t * rmost(struct freenode_t * n, size_t r);

static struct freenode_t * rmost(struct freenode_t * n, size_t r) {
  if (n->children[r] == NULL) {
    return NULL;
  }
  do {
    n = n->children[r];
  } while (n->children[r]);
  return n;
}

static void *freelist_add(void *bp) {
  size_t asize = GET_SIZE(bp);
  size_t bit = BIN_FOR(asize);
  struct freenode_t ** bin = &(heap->bins[bit]); // bin has the address of the bin pointer
  struct freenode_t * fn = (struct freenode_t *)bp;
  while(1) {
    if (*bin == NULL) {
      *bin = fn;
      fn->prev = bin;
      fn->next = fn->children[0] = fn->children[1] = NULL;
      return bp;
    }
    if (GET_SIZE(*bin) == asize) {
      fn->prev = bin;
      fn->next = *bin;
      fn->children[0] = (*bin)->children[0];
      (*bin)->children[0] = NULL;
      fn->children[1] = (*bin)->children[1];
      (*bin)->children[1] = NULL;
      *bin = fn;
      return bp;
    }
    bin = &((*bin)->children[BIT_N(asize,++bit)]);
    #if DEBUG
      if (bit > 64) {
        fprintf(stderr, "!! Infinite loop in freelist_add!\n");
        return NULL;
      }
    #endif
  }
}

static void freelist_remove(void *bp) {
  struct freenode_t * fn = (struct freenode_t *)bp;
  // if part of LL
  if (fn->next) {
    fn->next->prev = fn->prev;
    *(fn->prev) = fn->next;
    fn->next->children[0] = fn->children[0];
    fn->next->children[1] = fn->children[1];
    return;
  }
  struct freenode_t * ancestor;
  // else if part of trie
  if (fn->children[0] != NULL) {
    ancestor = rmost(fn,0);
    *(ancestor->prev) = NULL;
    ancestor->children[0] = fn->children[0];
    ancestor->children[1] = fn->children[1];
  } else {
    // 0-most is definately NULL 
    ancestor = rmost(fn,1);
    if (ancestor != NULL) {
      *(ancestor->prev) = NULL;
      ancestor->children[0] = fn->children[0];
      ancestor->children[1] = fn->children[1];
    }
  }
  *(fn->prev) = ancestor;
}

static void *freelist_bestfit(size_t sz) {
  struct freenode_t * bestfit = NULL;
  size_t bit = BIN_FOR(sz);
  struct freenode_t * bin = heap->bins[bit]; // bin has the address of the bin pointer
  // try "bin" first
  while (bin) {
    #if DEBUG
      if (bit > LSIG_BIT_OF_SIZE) {
        fprintf(stderr, "!! bestfit went beyond normal trie depth!\n");
        break;
      }
    #endif
    size_t s = GET_SIZE(bin);
    if (s == sz) {
      return bin;
    }
    if (s > sz) {
      if ((bestfit == NULL) || (s < GET_SIZE(bestfit))) {
        bestfit = bin;
      }
    }
    ++bit;
    bin = bin->children[BIT_N(sz,bit)];
  }
  if (bestfit != NULL) {
    return bestfit;
  }
  // if that doesn't work find anything larger
  for (bit = BIN_FOR(sz)-1; bit >= 0; bit--) {
    bin = heap->bins[bit];
    if (bin != NULL) {
      return bin;
    }
  }
  return NULL;
}


//////////////////
// DEBUG ONLY CODE
//////////////////
#if DEBUG

int check_bins();

int check_defines(void) {
  int problems = 0;
  if(ALIGN(ALIGNMENT*3 - 1) != ALIGNMENT*3) {
    fprintf(stderr, "!!ALIGN is whack!!\n");
    problems++;
  }
  if (sizeof(long) != WSIZE) {
    fprintf(stderr, "!!! WTYPE is whack!!\n");
    problems++;
  }
  if (sizeof(size_t) != sizeof(void *)) {
    fprintf(stderr, "!!! NTYPE and BITNESS are whack!!\n");
    problems++;
  }
  if (!BIT_N(MAX_SIZE,BIT_OFFSET) || BIT_N(MAX_SIZE,BIT_OFFSET-1) || BIT_N(MIN_SIZE,LSIG_BIT_OF_SIZE+1) || !BIT_N(ALIGNMENT,LSIG_BIT_OF_SIZE)) {
    fprintf(stderr, "!!! BIT_N is whack!!\n");
    problems++;
  }
  if (check_bins()) {
    fprintf(stderr, "!!! THE BINS is whack!!\n");
    problems++;
  }
  if (MAX(2,1) != 2 || MAX(1,2) != 2) {
    fprintf(stderr, "!!! MAX is whack!!\n");
    problems++;
  }
  return problems;
}

int check_bins() {
  int s;
  long unsigned c = 0;
  for(s = MAX_SIZE; s >= MIN_SIZE; s = s >> 1) {
    size_t b = BIN_FOR(s);
    heap->bins[b] = (void *)(c++);
  }
  struct freenode_t **l = (mem_heap_lo() + WSIZE);
  for (c = 0; c < BIT_COUNT; c++) {
    if (l[c] != (void *)(c)) {
      fprintf(stderr, "!!! There's a serious bins problem!\n");
      return 1;
    }
  }
  memset(l, 0, sizeof(struct freenode_t *)*BIT_COUNT);
  return 0;
}

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
  size_t *ep = (mem_heap_hi() + 1 - WSIZE);
  if (*ep != PACK(0,1)) {
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
  for (bp = &(heap->head[1]); GET_SIZE(bp)>0; bp = NEXT_BLKP(bp)) {
    if (!IS_ALLOC(bp)) {
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
  for (bp = &(heap->head[1]); GET_SIZE(bp)>0; bp = NEXT_BLKP(bp)) {
    if (HEADER(bp) != FOOTER(bp)) {
      number++;
    }
  }
  return number;
}

// END DEBUG CODE
#endif


