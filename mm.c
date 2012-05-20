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
 *      This goal is however NOT THOROUGHLY TESTED and shouldn't be relied on
 *    - It assumes that DSIZE is aligned
 *  
 * For a more complete description, see the comment at the end of the file.
 *
 * Author: Alex Madjar
 * License:  Don't use this for anything besides grading me ;)
 */


#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <limits.h>

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

// The following 3 defines are the only setable constants in my code:

//  Turn debugging code on
//     0 -> no debugging checks or output
//     1 -> low level checks
//     2 -> verbose output
//  All debug output is sent to stderr
#define DEBUG (0)

/* byte alignment (must be power of two and evenly divide DSIZE) */
#define ALIGNMENT 8

// the largest size a block is allowed to be (must be aligned)
#define MAX_SIZE ((size_t)((1<<28)-ALIGNMENT))

// The rest of the definitions are computed values

/* rounds up to the nearest multiple of ALIGNMENT 
    NOTE: ALIGNMENT must be a power of two
 */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~(ALIGNMENT-1))


/* Basic constants and types*/
#ifndef NULL
#  define NULL ((void *)(0))
#endif
#ifndef TRUE
#  define TRUE  (1)
#  define FALSE (0)
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
#define BITNESS  (CHAR_BIT*POINTER_SIZE)
#define MIN_SIZE ((size_t)(ALIGN(sizeof(struct freenode_t))))
// bit position of the first bin
#define BIT_OFFSET (__builtin_clzl(MAX_SIZE))
#define LSIG_BIT_OF_SIZE  (__builtin_clzl(ALIGNMENT))
// number of bins is bit pos of smallest - that of the largest plus one
#define BIT_COUNT  (1 + (__builtin_clzl(MIN_SIZE)) - BIT_OFFSET)
/* struct heaphead_t
 * 
 * This structure occures exactly once at the start of the heap.
 * It stores all the initial size bins, the prologue bytes
 * and (via &ptr->head[1]) points to first block on the heap
 *
 */
struct heaphead_t
{
  struct freenode_t *bins[BIT_COUNT];
  size_t prologue[2];
  size_t head[1];
};

// The global heap pointer (NOTE: the only global variable in the system)
struct heaphead_t * heap;


/* Basic macro functions */
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size_t)((size) | (alloc)))
/* Read the size and allocated fields from an int */
#define PACK_SIZE(packed)  ((packed) & ~(ALIGNMENT-1))
#define PACK_IS_ALLOC(packed) ((packed) & 0x1)
/* point us to bp's header */
#define HEADER(bp) (((size_t *)(bp))[-1])
// or previous footer (for efficiency, because HEADER(PREV_BLKP) is hard)
#define PREV_FOOTER(bp) (((size_t *)(bp))[-2])
// gets size/alloc from a pointer
#define GET_SIZE(p)  PACK_SIZE(HEADER(p))
#define IS_ALLOC(p)  PACK_IS_ALLOC(HEADER(p))
// slower functions
#define FOOTER(bp) (*((size_t *)(((char *)(bp)) + GET_SIZE(bp))))
#define NEXT_BLKP(bp) ((char *)(bp) + DSIZE + GET_SIZE(bp))
#define PREV_BLKP(bp) ((char *)(bp) - DSIZE - PACK_SIZE(PREV_FOOTER(bp)))


/////////////////
// Basic internal implicit list / heap operations
///////////////

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

/* 
 * mm_init - initialize the malloc package.
 *   makes the bins and initial prologue / epilogue
 *   allocates _no_ initial free space
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
  
  return 0;
}

// extends the heap by bytes. NOTE: doesn't change the freelist
static inline void *extend_heap(size_t bytes) {
  #if DEBUG>1
    fprintf(stderr, "extending the heap by %lx bytes\n", bytes);
  #endif
  char *bp;
  size_t size;
  #if DEBUG
    if (bytes < MIN_SIZE) {
      fprintf(stderr, "!!! Tried to extend heap by %lx bytes!\n", bytes);
      return NULL;
    }
  #endif
  /* Allocate an even number of words to maintain alignment */
  size = ALIGN(bytes);
  if ((long)(bp = mem_sbrk(DSIZE+size)) == -1)
      return NULL;
  /* Initialize free block header/footer and the epilogue header */
  HEADER(bp) = PACK(size, 0); /* Free block header */
  FOOTER(bp) = HEADER(bp);     /* Free block footer */
  HEADER(NEXT_BLKP(bp)) = PACK(0, 1); /* New epilogue header */
  // coallescing here didn't help efficiency in testing
  return bp;
}

void mm_free(void *bp){
  size_t size = GET_SIZE(bp);
  #if DEBUG>1
    fprintf(stderr, "Call to free with pointer %p (size: %lx)\n", bp, size);
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

// mm_malloc: this is the primary malloc call
// it only allocates new space on the heap as a last resort
// and then only does it as much as necessary
void *mm_malloc(size_t size)
{
  #if DEBUG>1
    fprintf(stderr, "+malloc called with size=%lx\n", size);
  #endif
  char *bp;
  // Ignore spurious requests
  if (size == 0)
    return NULL;
  if (size > MAX_SIZE) {
    #if DEBUG
      fprintf(stderr, "!! malloc called with size %lx > %lx\n", size, MAX_SIZE);
    #endif
    return NULL;
  }
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
    // if one wasn't found, create new space
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
  #endif
  }
  #if DEBUG>1
  fprintf(stderr, "+malloc returning %p (size=%lu)\n", bp, GET_SIZE(bp));
  #endif
  return bp;
}

// actually allocate this block with size asize
// splitting off freespace on the end if necessary
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

// a simple realloc that only allocates new space and copies
void *dumb_realloc(void *ptr, size_t size) {
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(oldptr);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

// smart realloc that attempts to leave the block in place if at all possible
void *mm_realloc(void *ptr, size_t size)
{
    #if DEBUG>1
      fprintf(stderr, "reallocing block %p (size %lx) with new size %lx\n", ptr, GET_SIZE(ptr), size);
    #endif
    size = ALIGN(size);
    long diff = size - GET_SIZE(ptr);
    if (diff <= 0) {
      place(ptr, size);
    } else {
      void *nxt_block = NEXT_BLKP(ptr);
      if ((!IS_ALLOC(nxt_block)) && (DSIZE + GET_SIZE(nxt_block) >= diff)) {
          freelist_remove(nxt_block);
          size_t csize = DSIZE + GET_SIZE(nxt_block) + GET_SIZE(ptr);
          HEADER(ptr) = PACK(csize, 1);
          FOOTER(ptr) = PACK(csize, 1);
          place(ptr, size);
      } else {
          ptr = dumb_realloc(ptr, size);
      }
    }
    #if DEBUG
    if (!mm_check()) {
      fprintf(stderr, "!!!!!!!!! mm_check failed !!!!!!!!!!\n");
    }
    #endif
    #if DEBUG>1
    fprintf(stderr, "+realloc returning %p (size=%lx)\n", ptr, GET_SIZE(ptr));
    #endif
    return ptr;
}

/////////////////////
// freelist code
////////////////////

/* Note: No coalescing etc needs to happen here, nor checking of free bit
 *
 */

// zero indexed from most significant bit bit-accessor 
#define BIT_N(s,n) ((((size_t)(s))>>((BITNESS - 1) - (n))) & ((size_t)(1)))
// Gets the bin number for a size: note larger sizes -> smaller bin number
#define BIN_FOR(asize) ((__builtin_clzl(asize))-BIT_OFFSET)
// safely sets a freenode pointer and its back pointer
#define SAFE_SET(dest, source) if (((dest) = (source))!=NULL) (dest)->prev = &(dest)
// copies the child pointers from source to dest
#define SET_CHILDREN(dest, source) \
          SAFE_SET((dest)->children[0], (source)->children[0]); \
          SAFE_SET((dest)->children[1], (source)->children[1])
// turns [size:xxxxxx..] into [xxxxxx[bit]00000...]
#define set_n_bit(size, bitp, bit) ((((~((size_t)(1))) & ((size) >> (BITNESS-(bitp)))) | (size_t)(bit)) << (BITNESS-(bitp)))

// finds the rightmost leaf of the trie
// NOTE: rightmost is more efficient than leftmost in trials
// Also note: this is best implemented using goto, trust me
static struct freenode_t * leaf(struct freenode_t * n) {
  leaf_loop:
  if (n->children[1] != NULL) {
    n = n->children[1];
    goto leaf_loop;
  }
  if (n->children[0] != NULL) {
    n = n->children[0];
    goto leaf_loop;
  }
  return n;
}

static void *freelist_add(void *bp) {
  #if DEBUG>1
    fprintf(stderr, "adding node %p (size=%lx) to the trie\n", bp, GET_SIZE(bp));
  #endif
  size_t asize = GET_SIZE(bp);
  if (asize > MAX_SIZE) {
    #if DEBUG
    fprintf(stderr, "!! attempting to add block size %lx > %lx to freelist!\n", asize, MAX_SIZE);
    #endif
    return NULL;
  }
  size_t bit = BIN_FOR(asize);
  struct freenode_t ** node = &(heap->bins[bit]); // node has the address of the bin pointer
  bit += BIT_OFFSET;
  struct freenode_t * fn = (struct freenode_t *)bp;
  while(1) {
    if (*node == NULL) {
      *node = fn;
      fn->prev = node;
      fn->next = fn->children[0] = fn->children[1] = NULL;
      return bp;
    }
    if (GET_SIZE(*node) == asize) {
      fn->prev = node;
      fn->next = *node;
      SET_CHILDREN(fn, *node);
      (*node)->children[0] = NULL;
      (*node)->children[1] = NULL;
      (*node)->prev = &(fn->next);
      *node = fn;
      return bp;
    }
    ++bit;
    #if DEBUG>1
    fprintf(stderr, "bit=%lu, size=%lx, bit_n=%lu\n", bit, asize, BIT_N(asize,bit));
    #endif
    node = &((*node)->children[BIT_N(asize,bit)]);
    #if DEBUG
      if (bit > 64) {
        fprintf(stderr, "!! Infinite loop in freelist_add!\n");
        return NULL;
      }
    #endif
  }
}

static void freelist_remove(void *bp) {
  #if DEBUG>1
    fprintf(stderr, "removing node %p (size=%lx) from the trie\n", bp, GET_SIZE(bp));
  #endif
  struct freenode_t * fn = (struct freenode_t *)bp;
  // if part of LL
  if (fn->next != NULL) {
    fn->next->prev = fn->prev;
    *(fn->prev) = fn->next;
    SET_CHILDREN(fn->next, fn);
    return;
  }
  struct freenode_t * ancestor = leaf(fn);
  if (ancestor == fn) {
    *(fn->prev) = NULL;
  } else {
    *(ancestor->prev) = NULL;
    SET_CHILDREN(ancestor, fn);
    ancestor->prev = fn->prev;
    *(fn->prev) = ancestor;
  }
}

static void *freelist_bestfit(size_t sz) {
  struct freenode_t * bestfit = NULL;
  size_t bit = BIN_FOR(sz);
  struct freenode_t * node = heap->bins[bit]; // node has the address of the bin pointer
  // try the correct bin first
  while (node) {
    #if DEBUG
      if (bit > LSIG_BIT_OF_SIZE) {
        fprintf(stderr, "!! bestfit went beyond normal trie depth!\n");
        break;
      }
    #endif
    size_t s = GET_SIZE(node);
    if (s == sz) {
      return node;
    }
    if (s > sz) {
      if ((bestfit == NULL) || (s < GET_SIZE(bestfit))) {
        bestfit = node;
      }
    }
    ++bit;
    node = node->children[BIT_N(sz,bit)];
  }
  if (bestfit != NULL) {
    return bestfit;
  }
  // if that doesn't work find anything larger
  for (bit = BIN_FOR(sz)-1; bit > 0; bit--) {
    node = heap->bins[bit];
    if (node != NULL) {
      return node;
    }
  }
  // once more for bit = 0
  node = heap->bins[bit];
  if (node != NULL) {
    return node;
  }
  // guess we got nothing for you
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
  if (!BIT_N(MAX_SIZE,BIT_OFFSET) || BIT_N(MAX_SIZE,BIT_OFFSET-1) || BIT_N(MIN_SIZE,LSIG_BIT_OF_SIZE+1) || !BIT_N(ALIGNMENT,LSIG_BIT_OF_SIZE)) {
    fprintf(stderr, "!!! BIT_N is whack!!\n");
    problems++;
  }
  if (check_bins()) {
    fprintf(stderr, "!!! THE BINS is whack!!\n");
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
  struct freenode_t **l = heap->bins;
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
int triecrawl(void);

extern int err(char * message);

int err(char * message) {
  fprintf(stderr, "%s\n", message);
  return 0;
}

// returns 0 IFF problem
int mm_check(void) {
  if(!ends_in_epilogue()) {
    return err("!! The heap doesn't end in an epilogue!");
  }
  if(inconsistant_footer()) {
    return err("!! Some blocks have inconsistant headers and footers!");
  }
  if(uncoalesced()) {
    return err("!! Some blocks escaped coalescing!");
  }
  if(triecrawl()) {
    exit(1);
    return err("!!! The trie is messed up!");
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

// returns the number of blocks with inconsistant headers and footers
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

int first_n_bits_the_same(size_t a, size_t b, size_t n);
int test_free_and_unvisitted(struct freenode_t *n);
int recursive_trie_node_test(struct freenode_t *n, size_t psize, size_t bit);

int first_n_bits_the_same(size_t a, size_t b, size_t n) {
  if (n == 0) return TRUE;
  if (n >= BITNESS) return (a == b);
  n = BITNESS - n;
  n = ((size_t)(1)) << n; // 000...1000..
  n--;        // 000...0111..
  n = ~n;     // 111...1000..
  return ((n & a) == (n & b));
}

#define assert_true(t, errormessage, args...) ((!(t)) ? fprintf(stderr, errormessage , ## args), (1) : (0))

// this is out primary testing function
// it crawls the entire freelist tree checking for consistancy
// see the long comments at the end for full documentation
int triecrawl(void) {
  int bin_number;
  int ret = 0;
  size_t largest_size_for_bin  =  MAX_SIZE;
  // trie crawl to visit all
  for (bin_number = 0; bin_number < BIT_COUNT; bin_number++) {
    struct freenode_t *bin = heap->bins[bin_number];
    #if DEBUG>1
      fprintf(stderr, "Bin %d (size=%lx)\n", bin_number, largest_size_for_bin);
    #endif
    ret += recursive_trie_node_test(bin, largest_size_for_bin, bin_number + 1 + BIT_OFFSET);
    largest_size_for_bin  >>= 1; 
  }
  // normal crawl to undo visits
  void *bp;
  for (bp = &(heap->head[1]); GET_SIZE(bp)>0; bp = NEXT_BLKP(bp)) {
    if (!IS_ALLOC(bp)) {
      if (PACK_IS_ALLOC(FOOTER(bp))) {
        // was visitted
        FOOTER(bp) = PACK(GET_SIZE(bp), 0);
      } else {
        // wasn't visitted!
        fprintf(stderr, "!! node at %p (size=%lx) is not in the trie!\n", bp, GET_SIZE(bp));
        ret++;
      }
    }
  }
  return ret;
}

int recursive_trie_node_test(struct freenode_t *n, size_t psize, size_t bit) {
  #if DEBUG>1
    fprintf(stderr, "node %p\n", n);
  #endif
  if (n == NULL) return 0;
  #if DEBUG>1
    fprintf(stderr, " (size=%lx)\n", GET_SIZE(n));
  #endif
  int ret = assert_true(first_n_bits_the_same(psize, GET_SIZE(n), bit), "!! node at %p (size=%lx) has the wrong size for its spot in the trie!\n", n, GET_SIZE(n));
  ret += test_free_and_unvisitted(n);
  #if DEBUG>1
    fprintf(stderr, "next: \n");
  #endif
  ret += recursive_trie_node_test(n->next, GET_SIZE(n), BITNESS);
  bit++;
  size_t zb = set_n_bit(psize, bit, 0);
  size_t ob = set_n_bit(psize, bit, 1);
  #if DEBUG>1
    fprintf(stderr, "left (size=%lx):\n ", zb);
  #endif
  ret += recursive_trie_node_test(n->children[0], zb, bit);
  #if DEBUG>1
    fprintf(stderr, "right (size=%lx):\n ", ob);
  #endif
  ret += recursive_trie_node_test(n->children[1], ob, bit);
  return ret;
}

int test_free_and_unvisitted(struct freenode_t *n) {
  int ret = 0;
  ret += assert_true(!IS_ALLOC(n), "!! freenode %p (size=%lx) is not free!\n", n, GET_SIZE(n));
  ret += assert_true(!PACK_IS_ALLOC(FOOTER(n)), "!! freenode %p (size=%lx) is in the trie multiple times!\n", n, GET_SIZE(n));
  ret += assert_true((*(n->prev) == n), "!! freenode %p (size=%lx) has a bad prev pointer!\n", n, GET_SIZE(n));
  FOOTER(n) = PACK(GET_SIZE(n), 1);
  return ret;
}

// END DEBUG CODE
#endif

/**************************************
******* DOCUMENTATION *****************
***************************************

I hope you find this interesting.


///////////////////////
// Heap structure
///////////////////////


max alloc size is 268,435,448 Bytes (256 MB or 0b1111111111111111111111111000 or 4 0's, 25 1's and 3 0's)
because 256MB and larger are best done using mmap

every block (whether free or allocated) has a 1 WSIZE (from here on WSIZE is defined as sizeof(size_t)) header and footer:
isAllocated = 0 or 1
size = 8 byte aligned byte-size of the block (not including the header / footer)
header/footer = size BITWISEOR isAllocated

in addition, free blocks contain (inside their data segment):
node* next  // a pointer to the next node in the stack of the same size
node* left  // a pointer to the left child in the trie
node* right // a pointer to the right child in the trie
node** prev // a pointer to the node* that points here
NOTE: left and right are stored in an array in order to make access easier without using a branch statement. children[0] -> left [1] -> right

because freenodes must contain this info, the min alloc size is 4*sizeof(void*)

NOTE: The total space this takes up is size + DSIZE  where DSIZE is 2*WSIZE

We create 24 bins of sizes by the number of zeros before the first 1 in the size 
(calculated using the clz function which returns the number of 0's)
because clz(max_size) = 4 and clz(min_size) = 27
clz(size)-4 = bin number (0 through 23 inclusive)

We divide the heap space as such: (key: *=pointer, not a size; in increasing address space)
*heap base*
unused padding bytes for alignment +
* "heap" pointer *
24 WORDs for the size buckets
1 WORD set to "1"
*official heap start pointer*
1 WORD set to "1" - prologue
X BLOCKS OF FREE AND ALLOCATED MEMORY
1 WORD set to "1" - epilog
usused padding bytes - "the wilderness" <- in this implementation this is size 0
*brk pointer / end of heap*

+ NOTE: in a production malloc we would use this padding to ensure that all valid pointers are 8 byte aligned and discard all free calls with non-aligned pointers. Perhaps in the future we'll add this level of robustness.

/////////////////
// Free List data structure
////////////////


Each bin contains a root pointer to a bitwise trie for blocks in that size range, and each node in the bitwise trie points to a stack of blocks of the same size.

Below is a discussion of how a bitwise trie generally works.
--------
Bitwise Trie
--------


Trie Structure

The root of the trie contains a single pointer to the first node. There are no
requirements about the key of this first node.


Trie Node

Each trie node contains two pointers to a left an right child node. All the
nodes in the left subtree are guaranteed to be less than the nodes in the
right subtree; however, the value of the parent node has no relation with any
of the children. This seems counter-intuitive at first, but it will make sense
as we go through the algorithms.

The key for each node is the size of the free chunk. The value is a pointer to
the beginning of the free chunk. Given the pointer to a free chunk, we should
be able to get it's size.


Insert Operation

insert(size_t size, void *value)

Check if the root pointer is NULL. Insert that new node as the head of the
trie, and return.

Otherwise, we need to scan the bits of 'size' from left-to-right, starting
with what we will denote bit 0. We get a pointer to the head node, what we
will call the current node. Using bit 0, we take either the left or right
child node (0 corresponds to left, 1 corresponds to right). If this child node
is NULL, then we create a new node and attach it as the left/right child.

Otherwise, we set the current node to the proper non-NULL left/right child. We
then iterate the above process using the next bit (now bit 1). We continue
this process until we find a NULL node.

Note: If we try to insert a node that already exists, bad things will happen.
You should prefix each iteration with a check to verify that our key (the
size) does not exactly match the key of the current node.


Find Operation

Check if the root pointer is NULL. If so, return NULL.

Otherwise, we scan the bits of 'size' from left-to-right, starting with what
we will denote as bit 0. We obtain a pointer to the head node, which we will
call the current node.

Check if the current node's key and the desired key match. If so, return the
current node value. Otherwise, using bit 0, we take either the left or right
child node. If this child is NULL, then the desired node does not exist, and
return NULL.

Otherwise, we set the current node to the proper non-NULL left/right child. We
then iterate the above process using the next bit (now bit 1). We continue
this process until we reach a NULL or find the node we want.


Best-Fit Operation

void *bestfit(size_t size)

Check if the root pointer is NULL. If so, return NULL.

Otherwise, we scan the bits of 'size' from left-to-right, starting with what
we will denote as bit 0. We obtain a pointer to the head node, which we will
call the current node. We set a pointer, which we will call the best-fit
pointer, to NULL.

We check the current node's size, if it is larger than the desired size. If
so, then we have a possible best fit. If the best-fit pointer is NULL, then it
is our best fit; otherwise, if the current node's size is less than the
best-fit pointer's size, then we have a new best fit and update the best-fit
pointer accordingly.


Remove Operation

void remove(size_t size)

Find the node using the find operation. Replace the node with any child node.
Since there is no requirement on ordering of the parent with respect to it's
children, it does not matter which child you pick. It also guarantees that the
left subtree is still strictly less than the right subtree.

(The code I have suggests using the right-most child node, it offset places
where the left-most node is preferred)

------
stack
------

Note that a bitwise trie cannot contain multiple nodes of the same size yet our freelist must be able to do so.

We do this by making each node in the bitwise trie the head of a stack, where all members of the stack are the same size.

consistant use of the "prev" pointer pointer makes both the trie and the stack doubly linked, which allows efficient and somewhat agnostic node insertion and removal.


*********************************/
