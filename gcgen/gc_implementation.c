/*
  Copyright (C) 2006 Adam C. Wick
  See LICENSE for licensing information.
*/
#include "gc_interface.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdarg.h>

#define MAGPIE_PAD_ALLOCATIONS

#ifdef EXEC_TEST
# define INIT_NURSERY_SIZE (2 * 1024 * 1024)
# define GEN0_GROW_FACTOR 0.5
# define GEN0_GROW_ADDITION (0.5 * 1024 * 1024)
# define LOG_PAGE_SIZE 14
#else
# include "gc_tuning.h"
#endif

/*****************************************************************************/
/*                                                                           */
/* Assertions                                                                */
/*                                                                           */
/*****************************************************************************/

/* ADAM: If you ever decide to ditch this for speed trials, you must still 
   include the test. So switch it to define GC_assert(x,y,z,a) x */
void GC_assert(int test, char* file, unsigned long line, char *errstr)
{
  if(!test) {
    fprintf(stderr, "ASSERTION FAILURE(%s,%u): %s\n", file, line, errstr);
    abort();
  }
}

/*****************************************************************************/
/* Low(er)-Level Memory Routines                                             */
/*****************************************************************************/

#include "vm_osx.c" /* Apple OS X */
#include "vm_linux.c" /* Linux */
#include "vm_freebsd.c" /* FreeBSD */
#include "vm_win.c" /* Windows */
#include "vm_solaris.c" /* Solaris */

static unsigned long gcint_memory_use = 0;
#define gcint_malloc(x) (gcint_memory_use += x, malloc(x))
#define gcint_free(x, y) (gcint_memory_use -= y, free(x))

/* 
   Of the above include files, exactly one should actually define anything.
   Each of the above checks to make sure that there isn't more than one 
   firing, and we check that at least one fired below. When done, the above
   routines expect the following function to be defined below:

        static void dirty_page(void *p)

   And they provide the following functions:

        static void *malloc_pages(unsigned long len, unsigned long alignment)
	static void free_pages(void *p, unsigned long len)
	static void flush_freed_pages()
	static void protect_pages(void *p, unsigned long len, int writeable)
	static void init_vm_subsystem()
	static void gcint_malloc(size)
	static void gcint_free(ptr, size)

   The goal of this collector is to require only the above five functions 
   from the host system. This allows more easy porting to other systems. 
   Drivers above may feel free to make the assumption that alignment will
   always be at 4k or larger and that allocations will always be 4k or
   larger. Low-level interface implementations may feel free to use alignments
   larger than the passed alignment if they prefer, but they must not use 
   alignments smaller than given.

   Driver implementers should feel free to cache if they thing system 
   performance suggests it. However, please note that the internal allocator
   already caches (in a sense), so it is suggested that only blocks of
   MPAGE_SIZE be cached.
*/

#ifndef VM_SYSTEM_DEFINED
#error "Couldn't find an OS-level VM system I could use."
#endif

/*****************************************************************************/
/*                                                                           */
/* Some useful high-level #defines and structures we define here for         */
/* convenience								     */
/*                                                                           */
/*****************************************************************************/

#define PTR(x)                               ((void*)(x))
#define PPTR(x)                              ((void**)(x))
#define NUM(x)                               ((unsigned long)(x))
#define gcBYTES_TO_WORDS(x)                  (((x) + 3) >> 2)
#define gcWORDS_TO_BYTES(x)                  ((x) << 2)
#define MPAGE_SIZE                           (1 << LOG_PAGE_SIZE)
#define MAX_OBJECT_SIZE                      (MPAGE_SIZE - 8)
#define MAX_OBJECT_SIZEW                     gcBYTES_TO_WORDS(MAX_OBJECT_SIZE)
#define NUM_INFO_BITS                        2
#define PAGE_SIZE_TO_INFO_SIZE(x)            ((((x) / 4) / 8) * NUM_INFO_BITS)
#define INFO_SIZE                            PAGE_SIZE_TO_INFO_SIZE(MPAGE_SIZE)

struct gcpage {                /* SIZE: DESCRIPTION:                        */
  struct gcpage *next, *prev;  /* 8     Linked list pointers.               */
  void **page;                 /* 4     The data actually on this page      */
  u_int8_t *info;              /* 4     The mark/start info for the objects */
  gc_tag tag;                  /* 4     The tag for data on this page       */
  u_int32_t size;              /* 4     The amount of data on the page      */
  u_int32_t previous_size;     /* 4     How much used to be on this page    */
  u_int8_t generation;         /* 1     The page's generation               */
  u_int8_t dirty;              /* 1     FLAG (page is dirty or not)         */
  u_int8_t big_page;           /* 1     FLAG (page is bigpage or not)       */
  u_int8_t marked_on;          /* 1     0 = NO, 1 = YES, 2 = YES & MOVED    */
};                             /* 32                                        */

#define PAGE_UNMARKED			    0
#define PAGE_MARKED			    1
#define PAGE_MARKED_AND_MOVED		    3 /* for bit processing */

/*****************************************************************************/
/*                                                                           */
/* Routines dealing with tags                                                */
/*                                                                           */
/*****************************************************************************/

static unsigned long allocated_tags = 0;

gc_tag GC_init_tag(void (mark)(void *ptr), void (repair)(void *ptr))
{
  gc_tag newtag = gcint_malloc(sizeof(struct gc_tag_struct));
  GC_ASSERT(newtag, "Failure allocating space for tag.");
  newtag->mark = mark;
  newtag->repair = repair;
  allocated_tags += 1;
  return newtag;
}

/*****************************************************************************/
/*                                                                           */
/* Routines for mapping arbitrary value to near-arbitrary values, with fast  */
/* lookup, insert and remove. The structure is basically a trie on nibbles   */
/* within a word. So it's a 16-ary try where the current least significant   */
/* nibble tells you where to find the item, and you shift as you recurse.    */
/*                                                                           */
/*****************************************************************************/

typedef struct ptrmapper {
  void *ptr, *val;
  struct ptrmapper **subtrees;
} ptrmapper;

#define NOT_FOUND ((void*)0xffffffff)

static void *get_ptrmapped_val(ptrmapper *map, void *ptr)
{
  int new_index;
  void *new_ptr;

  if(!map)
    return NOT_FOUND;
  if(map->ptr == ptr)
    return map->val;
  if(!map->subtrees)
    return NOT_FOUND;
  
  new_index = NUM(ptr) & 0xf;
  new_ptr = PTR(NUM(ptr) >> 4);
  return get_ptrmapped_val(map->subtrees[new_index], new_ptr);
}

static ptrmapper *set_ptrmapped_val(ptrmapper *map, void *ptr, void *val)
{
  if(!map) {
    map = gcint_malloc(sizeof(ptrmapper));
    bzero(map, sizeof(ptrmapper));
    map->ptr = ptr;
    map->val = val;
  } else if(map->ptr == ptr) {
    map->val = val;
  } else if(map->ptr == NOT_FOUND) {
    map->ptr = ptr;
    map->val = val;
  } else {
    int new_index = NUM(ptr) & 0xf;
    void *new_ptr  = PTR(NUM(ptr) >> 4);

    if(!map->subtrees) {
      map->subtrees = gcint_malloc(16 * sizeof(ptrmapper *));
      bzero(map->subtrees, 16 * sizeof(ptrmapper *));
    }

    map->subtrees[new_index] = 
      set_ptrmapped_val(map->subtrees[new_index], new_ptr, val);
  }
  return map;
}

static ptrmapper *remove_ptrmapped_val(ptrmapper *map, void *ptr)
{
  if(!map) {
    return NULL;
  } else if(map->ptr == ptr) {
    map->ptr = NOT_FOUND;
    map->val = NULL;
  } else if(!map->subtrees) {
    return map;
  } else {
    int new_index = NUM(ptr) & 0xf;
    void *new_ptr  = PTR(NUM(ptr) >> 4);
    
    map->subtrees[new_index] =
      remove_ptrmapped_val(map->subtrees[new_index], new_ptr);
  }

  /* See if we can get rid of the subtrees, if they exist */
  if(map->subtrees) {
    int i, can_delete_subtrees = 1;
    for(i = 0; i < 16; i++)
      can_delete_subtrees = can_delete_subtrees && !map->subtrees[i];
    if(can_delete_subtrees) {
      gcint_free(map->subtrees, 16 * sizeof(ptrmapper*));
      map->subtrees = NULL;
    }
  }

  /* Now see if we can get rid of the whole node */
  if((map->ptr == NOT_FOUND) && !map->subtrees) {
    gcint_free(map, sizeof(ptrmapper));
    map = NULL;
  }

  return map;
}

/*****************************************************************************/
/*                                                                           */
/* Routines dealing with page management                                     */
/*                                                                           */
/*****************************************************************************/

#define LOG_WORD_SIZE                    2
#define USEFUL_ADDR_BITS                 ((8 << LOG_WORD_SIZE) - LOG_PAGE_SIZE)
#define ADDR_BITS(x)                     (NUM(x) >> LOG_PAGE_SIZE)

/* the page map makes a nice mapping from addresses to pages, allowing
   fairly fast lookup. this is useful. */
static struct gcpage *page_map[1 << USEFUL_ADDR_BITS];

/* These procedures modify or use the page map. The page map provides us very
   fast mappings from pointers to the page the reside on, if any. The page 
   map itself serves two important purposes:

   Between collections, it maps pointers to write-protected pages, so that 
     the write-barrier can identify what page a write has happened to and
     mark it as potentially containing pointers from gen 1 to gen 0. 

   During collections, it maps pointers to "from" pages. */
#define modify_page_map(page, val) {                                  \
    long size_left = page->big_page ? page->size : MPAGE_SIZE;         \
    void *p = page->page;                                             \
                                                                      \
    while(size_left > 0) {                                            \
      page_map[ADDR_BITS(p)] = val;                                   \
      size_left -= MPAGE_SIZE;                                         \
      p = (char *)p + MPAGE_SIZE;                                      \
    }                                                                 \
  }

/*inline*/ static void pagemap_add(struct gcpage *page)
{
  modify_page_map(page, page);
}

/*inline*/ static void pagemap_remove(struct gcpage *page)
{
  modify_page_map(page, NULL);
}

/*inline*/ static struct gcpage *find_page(void *p)
{
  return page_map[ADDR_BITS(p)];
}



/*****************************************************************************/
/*                                                                           */
/* Routines for dealing with the nursery. We have to define them here due to */
/* the fact that we use these in the bitmap stuff.                           */
/*                                                                           */
/*****************************************************************************/

static /*inline*/ void set_object_start(void *base, u_int8_t *info, void *ptr);

static void **nursery_start = NULL;
static void **nursery_end = NULL;
static void **nursery_current = NULL;
static u_int8_t *nursery_info = NULL;

static u_int32_t nursery_info_size = 0;
static u_int32_t nursery_used = 0;
static u_int32_t nursery_max = 0;
static u_int32_t memory_in_use = 0;

static void reset_nursery(void)
{
  unsigned long new_gen0_size;

  if(nursery_start) {
    new_gen0_size = NUM((GEN0_GROW_FACTOR * (float)memory_in_use)
			+ GEN0_GROW_ADDITION);
    /* now we want to make sure that this is divisible by the page size. 
       we do this by chopping some amount off the end */
    new_gen0_size = new_gen0_size & (0xffffffff << LOG_PAGE_SIZE);
  } else {
    new_gen0_size = INIT_NURSERY_SIZE;
  }

  if ( new_gen0_size < INIT_NURSERY_SIZE ){
	  new_gen0_size = INIT_NURSERY_SIZE;
  }

  /* Free all the old stuff */
  if(nursery_start) {
    free_pages(nursery_start, NUM(nursery_end) - NUM(nursery_start));
    gcint_free(nursery_info, nursery_info_size);
    nursery_used = 0;
  }

  /* Allocate the new nursery */
  nursery_start = malloc_pages(new_gen0_size, 4096); 
  nursery_end = PPTR(NUM(nursery_start) + new_gen0_size);
  nursery_current = nursery_start;
  nursery_max = NUM(nursery_end) - NUM(nursery_start);

  /* ... and the new nursery information */
  nursery_info_size = PAGE_SIZE_TO_INFO_SIZE(new_gen0_size);
  nursery_info = gcint_malloc(nursery_info_size);

  /* zero these out */
  bzero(nursery_start, new_gen0_size);
  bzero(nursery_info, nursery_info_size);
}

#define OBJ_IN_NURSERY(x) ((NUM(x) >= NUM(nursery_start)) && \
			   (NUM(x) < NUM(nursery_current)))

#define LOG_HASH_SIZE                8
#define HASH_SHIFT                   4
#define HASH_SIZE                    (1 << LOG_HASH_SIZE)
#define HASH_OBJ(x)                  ((NUM(x) >> HASH_SHIFT) & (HASH_SIZE - 1))

static struct gcpage *pages[HASH_SIZE];
static struct gcpage *nursery_bigs = NULL;
static u_int8_t gc_top_generation = 0;

#define VALID_PAGE_FOR_OBJ(page,tag,size)			\
  ((page->tag == tag) &&					\
   !page->big_page &&						\
   ((page->size + size) < (MPAGE_SIZE - 4)))

#define FOR_EACH_PAGE(page,i)				    \
  struct gcpage *page;					    \
  int i;						    \
                                                            \
  for(i = 0; i < HASH_SIZE; i++)                            \
    for(page = pages[i]; page; page = page->next)          

/*****************************************************************************/
/*                                                                           */
/* Routines for root sets (global variables)                                 */
/*                                                                           */
/*****************************************************************************/

struct gc_root{
	void * ptr;
	gc_tag tag;
};

static struct gc_root * roots = 0;
static unsigned long roots_count = 0;
static unsigned long roots_size = 0;

void GC_add_root_tagged( void * pptr, gc_tag tag ){
	GC_ASSERT(pptr, "Passed null root?!");
	GC_ASSERT(!OBJ_IN_NURSERY(pptr), "Root source in nursery?!");
	GC_ASSERT(!find_page(pptr), "Root source in gc heap?!");

	if ( roots_count ){
		unsigned long i;

		for(i = 0; i < roots_count; i++)
			if(roots[i].ptr == pptr)
				return;
	}

	if ( roots_count >= roots_size ){
		unsigned long new_roots_size = roots_size ? 2 * roots_size : 500;
		struct gc_root *new_roots = gcint_malloc(sizeof(struct gc_root) * new_roots_size);
		if(roots) { 
			memcpy(new_roots, roots, roots_size * sizeof(struct gc_root)); 
			free(roots);
		}
		bzero(PTR(NUM(new_roots) + (roots_size * sizeof(struct gc_root))), 
				(new_roots_size - roots_size) * sizeof(struct gc_root));
		roots = new_roots;
		roots_size = new_roots_size;
	}

	roots[roots_count].ptr = pptr;
	roots[roots_count].tag = tag;
	roots_count += 1;
}

static gc_tag __gcstandard_pointer_tag;
void GC_add_root( void * pptr ){
	GC_add_root_tagged( pptr, __gcstandard_pointer_tag );
}

/*
static void **roots = 0;
static unsigned long roots_count = 0;
static unsigned long roots_size = 0;

void GC_add_root(void *pptr)
{
  GC_ASSERT(pptr, "Passed null root?!");
  GC_ASSERT(!OBJ_IN_NURSERY(pptr), "Root source in nursery?!");
  GC_ASSERT(!find_page(pptr), "Root source in gc heap?!");

  if(roots_count) {
    unsigned long i;

    for(i = 0; i < roots_count; i++)
      if(roots[i] == pptr)
	return;
  }

  if(roots_count >= roots_size) {
    unsigned long new_roots_size = roots_size ? 2 * roots_size : 500;
    void **new_roots = gcint_malloc(sizeof(void*) * new_roots_size);
    if(roots) { 
      memcpy(new_roots, roots, roots_size * sizeof(void*)); 
      free(roots);
    }
    bzero(PTR(NUM(new_roots) + (roots_size * sizeof(void*))), 
	  (new_roots_size - roots_size) * sizeof(void*));
    roots = new_roots;
    roots_size = new_roots_size;
  }

  roots[roots_count] = pptr;
  roots_count += 1;
}
*/

/*inline*/ static void mark_roots() 
{
  unsigned long i;

  for(i = 0; i < roots_count; i++) {
	  /*
    GC_mark(*(void**)(roots[i]));
    */
	  roots[i].tag->mark( roots[i].ptr );
  }
}

/*inline*/ static void repair_roots()
{
  unsigned long i;

  for(i = 0; i < roots_count; i++) {
    // GC_repair(roots[i]);
	  roots[i].tag->repair( roots[i].ptr );
  }
}

/*****************************************************************************/
/*                                                                           */
/* Routines for dealing with the bitmaps associated with every non-big GC    */
/* page.								     */
/*                                                                           */
/*****************************************************************************/

/*

   Outside GC
   00 - Nothing
   01 - Autotagged
   10 - Start
   11 - Dead
   
   During GC:
   11 - Marked

*/

/* Outside GC */
#define FLAG_AUTOTAGGED_OBJ		0x1 /* binary 0b01 */
#define FLAG_START_OBJ			0x2 /* binary 0b10 */
/* During GC */
#define FLAG_MARKED_OBJ			0x3 /* binary 0b11 */
#define ALL_MARKS_CLEAR1	       0x55 /* binary 0b01010101 */
#define ALL_MARKS_CLEAR2	       0xaa /* binary 0b10101010 */
#define CLEAR_MARKS(x) (ALL_MARKS_CLEAR1 & x) ^ (ALL_MARKS_CLEAR2 & x)

#define COMPUTE_WORD_NUMBER(base,ptr) ((NUM(ptr) - NUM(base)) >> 2)

static /*inline*/ u_int8_t get_info(u_int8_t *info, unsigned int word_no)
{
  unsigned int index = word_no >> 2;
  unsigned int mod = (word_no - (index << 2));
  u_int8_t quadword_info = info[index];

  switch(mod) {
    case 0: return quadword_info >> 6;
    case 1: return (quadword_info >> 4) & 0x3;
    case 2: return (quadword_info >> 2) & 0x3;
    case 3: return quadword_info & 0x3;
  }
  GC_ASSERT(0, "Internal consistency error.");
}

static /*inline*/ void set_info(u_int8_t *info, u_int32_t word_no, u_int8_t value)
{
  u_int32_t index = word_no >> 2;
  u_int32_t mod = (word_no - (index << 2));
  u_int8_t quadword_info = info[index];

  GC_ASSERT((mod >= 0) && (mod <= 3), "Internal consistency error");
  GC_ASSERT((value == FLAG_AUTOTAGGED_OBJ) ||
	    (value == FLAG_START_OBJ) ||
	    (value == FLAG_MARKED_OBJ), "Bad value for set_info");
  switch(mod) {
    case 0: info[index] = (quadword_info & 0x3f) | (value << 6); break;
    case 1: info[index] = (quadword_info & 0xcf) | (value << 4); break;
    case 2: info[index] = (quadword_info & 0xf3) | (value << 2); break;
    case 3: info[index] = (quadword_info & 0xfc) | value; break;
  }
}

static /*inline*/ void set_object_start(void *base, u_int8_t *info, void *ptr)
{
  GC_ASSERT(ptr >= base, "Internal consistency error. (ptr < base)");
  set_info(info, COMPUTE_WORD_NUMBER(base, ptr), FLAG_START_OBJ);
}

static /*inline*/ void *find_object_start(void *base, u_int8_t *info, void *ptr)
{
  int word_no = COMPUTE_WORD_NUMBER(base, ptr);
  GC_ASSERT(ptr >= base, "Internal consistency error. (ptr < base)");
  while(!(get_info(info, word_no) & 0x2)) {
    word_no--;
  }
  /* this gives a word offset from the start, which we now translate to
     a return pointer */
  return PPTR(base) + word_no;
}

static void dump_info_starts( void * base, u_int8_t * info, int max ){
	int word;
	for ( word = 0; word < max; word++ ){
		if ( get_info( info, word ) & 0x2 ){
			printf( "- %p\n", PPTR(base) + word );
		}
	}
}

static /*inline*/ void *find_object_end(void *base, u_int8_t *info, void *ptr)
{
  int word_no = COMPUTE_WORD_NUMBER(base, ptr) + 1;
  GC_ASSERT(ptr >= base, "Internal consistency error. (ptr < base)");
  while(!(get_info(info, word_no) & 0x2)) {
    word_no++;
  }
  /* this gives a word offset from the start, which we now translate to
     a return pointer */
  return PPTR(base) + word_no;
}

static /*inline*/ void set_object_marked(void *base, u_int8_t *info, void *ptr)
{
  GC_ASSERT(ptr >= base, "Internal consistency error. (ptr < base)");
  set_info(info, COMPUTE_WORD_NUMBER(base, ptr), FLAG_MARKED_OBJ);
}

static /*inline*/ void clear_object_marks(u_int8_t *info, u_int32_t size)
{
  u_int32_t *fake_info = (u_int32_t*)info;
  u_int32_t fake_size = size >> 2, i;
  
  GC_ASSERT(size = ((size >> 2) << 2), "Bad info size!");
  for(i = 0; i < fake_size; i++) {
    u_int32_t val = fake_info[i];
    /* Thanks to Jed Davis for this */
    fake_info[i] = val & ~((val >> 1) & 0x55555555);
  }
}

static /*inline*/ u_int8_t object_marked(void *base, u_int8_t *info, void *ptr)
{
  GC_ASSERT(ptr >= base, "Internal consistency error. (ptr < base)");
  return get_info(info, COMPUTE_WORD_NUMBER(base,ptr)) == FLAG_MARKED_OBJ;
}

static /*inline*/ u_int8_t set_object_autotagged(void *base, u_int8_t *info, void*p)
{
  u_int32_t word_no = COMPUTE_WORD_NUMBER(base,p);
  u_int8_t my_info = get_info(info, word_no);

  GC_ASSERT(p >= base, "Internal consistency error. (p < base)");
  if(my_info & FLAG_START_OBJ)
    set_info(info, word_no + 1, FLAG_AUTOTAGGED_OBJ);
  else
    set_info(info, word_no, FLAG_AUTOTAGGED_OBJ);
}

static /*inline*/ u_int8_t object_autotagged(void *base, u_int8_t *info, void *ptr)
{
  u_int32_t word_no = COMPUTE_WORD_NUMBER(base, ptr);
  u_int8_t my_info = get_info(info, word_no);

  GC_ASSERT(ptr >= base, "Internal consistency error. (p < base)");
  if(my_info & FLAG_START_OBJ)
    return object_autotagged(base, info, ptr + 4);
  else
    return my_info == FLAG_AUTOTAGGED_OBJ;
}

#define object_size(base,info,ptr) \
  (NUM(find_object_end(base,info,ptr) - NUM(ptr)))

void *GC_find_end_of_object(void *obj){
  void *page_start;
  u_int8_t *info;

#ifdef MAGPIE_PAD_ALLOCATIONS
#define REAL_END 4
#else
#define REAL_END 0
#endif

  if(OBJ_IN_NURSERY(obj)) {
    page_start = nursery_start;
    info = nursery_info;
  } else {
    struct gcpage *page = find_page(obj);
    GC_ASSERT(page, "Couldn't find page for object in GC_find_end_of_obj");

    if(page->big_page)
      return PTR(NUM(page->page) + page->size) - REAL_END;

    page_start = page->page;
    info = page->info;
  }

  return find_object_end(page_start, info, obj) - REAL_END;

#undef REAL_END
}

int GC_test_object_type(void *obj, gc_tag type)
{
  if(OBJ_IN_NURSERY(obj)) {
    void *start_obj = find_object_start(nursery_start, nursery_info, obj);
    gc_tag tag = *(gc_tag*)PTR(NUM(start_obj) - 4);
    return tag == type;
  } else {
    struct gcpage *page = find_page(obj);
    GC_ASSERT(page, "Couldn't find page for object in GC_test_object_type");
    return page->tag == type;
  }
}

/*****************************************************************************/
/*                                                                           */
/* Routines for debugging the collector.                                     */
/*                                                                           */
/*****************************************************************************/
//#define GC_INTERNAL_DEBUG

#ifdef GC_INTERNAL_DEBUG

static FILE *dumpfile = NULL;

static void gcdump_print_memblock(void **start, void **end, u_int8_t *info)
{
  unsigned long word_no = 0;
  void **work = start;
  int cycle = 0;

  while(work < end) {
    u_int8_t info_val = info ? get_info(info, word_no) : 0;

    if(cycle == 0) {
      fprintf(dumpfile, "%p: ", work);
    }

    fprintf(dumpfile, "%.8lx(%i%i) ", 
	    *work, (info_val >> 1) & 0x1, info_val & 0x1);

    if(cycle == 3) {
      fprintf(dumpfile, "\n");
      cycle = 0;
    } else cycle++;
    work++, word_no++;
  }
  fprintf(dumpfile, "\n");
}

static void gcdump_print_page(struct gcpage *page)
{
  fprintf(dumpfile, "Page %p (gen %u, dirty %u, big %u, marked %u)\n", page,
	  page->generation, page->dirty, page->big_page, page->marked_on);
  fprintf(dumpfile, "  size = %u (%u)\n", page->size, page->previous_size);
  fprintf(dumpfile, "   tag = %p\n", page->tag);
  gcdump_print_memblock(page->page, PTR(NUM(page->page) + page->size), 
			page->info);
}


static void gcdump_heap(int show_nursery)
{
  struct gcpage *page;
  int i;

  if(show_nursery) {
    fprintf(dumpfile, "Nursery %p - %p (current = %p)\n", 
	    nursery_start, nursery_end, nursery_current);
    gcdump_print_memblock(nursery_start, nursery_end, nursery_info);
  }
  
  for(page = nursery_bigs; page; page = page->next)
    gcdump_print_page(page);

  for(i = 0; i < HASH_SIZE; i++)
    for(page = pages[i]; page; page = page->next)
      gcdump_print_page(page);
}

static void GCDUMP_START(unsigned long number)
{
  char *filename = NULL;

  asprintf(&filename, "gcdump_%u", number);
  dumpfile = fopen(filename, "w");
  fprintf(dumpfile, "Starting garbage collection %u\n", number);
  gcdump_heap(1);
}

static void GCDUMP_END(void)
{
  fprintf(dumpfile, "Ending garbage collection %u\n");
  gcdump_heap(0);
  fclose(dumpfile);
}

static void GCDUMP_RECORD_TRAVSTACK(void *ptr, unsigned long size,
				    unsigned long tag)
{
  char *tagstr;

  switch(tag) {
    case 0: tagstr = "simple"; break;
    case 1: tagstr = "array"; break;
    case 2: tagstr = "complex"; break;
    case 3: tagstr = "tagged"; break;
    default: tagstr = "unknown"; break;
  }

  fprintf(dumpfile, "Traversing stack frame %p (type %s, size %u)\n",
	  ptr, tagstr, size);
  fflush(dumpfile);
}

static void GCDUMP_RECORD_MARK(void *ptr)
{
  fprintf(dumpfile, "GC_mark(%p)\n", ptr);
  fflush(dumpfile);
}

static void GCDUMP_RECORD_MARKMOVE(void *ptr, void *newptr, 
				   unsigned long objsize, gc_tag tag)
{
  fprintf(dumpfile, "Marked/moved %u byte object %p to %p (tag %p)\n",
	  objsize, ptr, newptr, tag);
  fflush(dumpfile);
}

static void GCDUMP_RECORD_MARKBIG(void *ptr, struct gcpage *page)
{
  fprintf(dumpfile, "Marked bigpage object %p on page %p\n", ptr, page);
  fflush(dumpfile);
}

static void GCDUMP_RECORD_MARKOLD(void *ptr, struct gcpage *page)
{
  fprintf(dumpfile, "Marked old object %p on page %p\n", ptr, page);
  fflush(dumpfile);
}

static void GCDUMP_RECORD_PROP(void *ptr, struct gcpage *page)
{
  fprintf(dumpfile, "Propogating from object %p on page %p (tag %p)\n", 
	  ptr, page, page->tag);
  fflush(dumpfile);
}

static void GCDUMP_RECORD_COPYAUTO(void *from, void *to, void *val)
{
  fprintf(dumpfile, "Moving autotag information from %p to %p (%p)\n", 
	  from, to, val);
  fflush(dumpfile);
}

static void GCDUMP_RECORD_REPAIR(void *ptr)
{
  fprintf(dumpfile, "Repairing object at %p\n", ptr);
  fflush(dumpfile);
}
#else
#define GCDUMP_START(num) /* */
#define GCDUMP_END() /* */
#define GCDUMP_RECORD_TRAVSTACK(ptr, size, kind) /* */
#define GCDUMP_RECORD_MARK(ptr) /* */
#define GCDUMP_RECORD_MARKMOVE(ptr,newptr,size,tag) /* */
#define GCDUMP_RECORD_MARKBIG(ptr,page) /* */
#define GCDUMP_RECORD_MARKOLD(ptr,page) /* */
#define GCDUMP_RECORD_PROP(ptr,page) /* */
#define GCDUMP_RECORD_COPYAUTO(from,to,val) /* */
#define GCDUMP_RECORD_REPAIR(ptr) /* */
#endif

/*****************************************************************************/
/*                                                                           */
/* Routines dealing with the stack                                           */
/*                                                                           */
/*****************************************************************************/

// void **GC_variable_stack = NULL;

typedef void (*gc_complex_trav)(void (*)(void*), void*, void*);

#define FRAME_GET_TYPE(x) ((unsigned long)(x) & 0x3)
#define FRAME_GET_SIZE(x) ((unsigned long)(x) >> 2)
#define FRAME_TYPE_SIMPLE 0x0
#define FRAME_TYPE_ARRAY 0x1
#define FRAME_TYPE_COMPLEX 0x2
#define FRAME_TYPE_TAGGED 0x3

#define traverse_stack(mucker, cmucker, tmucker, stack) {		\
    while(stack) {							\
      void **prev_stack = *(void**)stack;				\
      unsigned long finfo = *(unsigned long*)(stack + 1);		\
									\
      GCDUMP_RECORD_TRAVSTACK(stack, FRAME_GET_SIZE(finfo),		\
			      FRAME_GET_TYPE(finfo));			\
      switch(FRAME_GET_TYPE(finfo)) {					\
        case FRAME_TYPE_SIMPLE: {					\
	  unsigned long size = FRAME_GET_SIZE(finfo), i;		\
	  								\
          stack += 2;                                                   \
	  for(i = 0; i < size; i++) 					\
	    if(stack[i])						\
	      mucker(*(void**)(stack[i]));				\
	  break;							\
	}								\
									\
        case FRAME_TYPE_ARRAY: {					\
	  int i, j, size = FRAME_GET_SIZE(finfo);			\
									\
	  for(i = 0; i < size; i++) {					\
	    void **array;						\
	    unsigned long asize;					\
									\
	    stack += 2;							\
	    array = *(void***)stack;					\
	    asize = *(unsigned long*)(stack + 1);			\
	    for(j = 0; j < asize; j++)					\
	      if(array[j])						\
		mucker(array[j]);					\
	  }								\
	  break;							\
	}								\
									\
        case FRAME_TYPE_COMPLEX: {					\
          int i, size = FRAME_GET_SIZE(finfo);                          \
          stack += 2;							\
          for ( i = 0; i < size; i++ ){                                 \
	  void *ptr = *(void**)stack;	           			\
	  if(ptr) {							\
	    gc_complex_trav trav = *(gc_complex_trav*)(stack + 1);	\
	    trav((void (*)(void*))cmucker, ptr, 0 );     		\
	  }								\
		  stack += 4;                                           \
	  }                                                             \
	  break;							\
	}								\
									\
        case FRAME_TYPE_TAGGED: {					\
	  int i, size = FRAME_GET_SIZE(finfo);				\
									\
          stack += 2;							\
	  for(i = 0; i < size; i++) {					\
	    void *ptr;							\
	    gc_tag tag;							\
									\
	    ptr = *(void**)stack;					\
	    if(ptr) {							\
	      tag = *(gc_tag*)(stack + 1);				\
	      tmucker(ptr);						\
	    }								\
	    stack += 4;							\
	  }								\
	  break;							\
	}								\
      }									\
									\
      stack = prev_stack;						\
    }									\
  }

static void gcint_mark_stack(void **stack) {
  // traverse_stack(gcMARK, GC_mark, tag->mark, stack);

	while(stack) {
      void **prev_stack = *(void**)stack;				
      unsigned long finfo = *(unsigned long*)(stack + 1);		
									
      GCDUMP_RECORD_TRAVSTACK(stack, FRAME_GET_SIZE(finfo),		
			      FRAME_GET_TYPE(finfo));			
      switch(FRAME_GET_TYPE(finfo)) {					
        case FRAME_TYPE_SIMPLE: {					
	  unsigned long size = FRAME_GET_SIZE(finfo), i;		
	  								
	  stack += 2;
	  for(i = 0; i < size; i++) 					
	    if(stack[i])						
	      gcMARK(*(void**)(stack[i]));				
	  break;							
	}								
									
        case FRAME_TYPE_ARRAY: {					
	  int i, j, size = FRAME_GET_SIZE(finfo);			
									
	  for(i = 0; i < size; i++) {					
	    void **array;						
	    unsigned long asize;					
									
	    stack += 2;							
	    array = *(void***)stack;					
	    asize = *(unsigned long*)(stack + 1);			
	    for(j = 0; j < asize; j++)					
	      if(array[j])						
		gcMARK(array[j]);					
	  }								
	  break;							
	}								
									
        case FRAME_TYPE_COMPLEX: {					
          int i, size = FRAME_GET_SIZE(finfo);                          
          stack += 2;							
          for ( i = 0; i < size; i++ ){                                 
	  void *ptr = *(void**)stack;	           			
	  if(ptr) {							
	    gc_complex_trav trav = *(gc_complex_trav*)(stack + 1);	
	    trav((void (*)(void*))GC_mark, ptr, 0 );     		
	  }								
		  stack += 4;                                           
	  }                                                             
	  break;							
	}								
									
        case FRAME_TYPE_TAGGED: {					
	  int i, size = FRAME_GET_SIZE(finfo);				
									
          stack += 2;							
	  for(i = 0; i < size; i++) {					
	    void *ptr;							
	    gc_tag tag;							
									
	    ptr = *(void**)stack;					
	    if(ptr) {							
	      tag = *(gc_tag*)(stack + 1);				
	      tag->mark(ptr);						
	    }								
	    stack += 4;							
	  }								
	  break;							
	}								
      }									
									
      stack = prev_stack;						
    }									
}

static void gcint_repair_stack(void **stack)
{
  // traverse_stack(gcREPAIR, GC_repair, tag->repair, stack);
  while(stack) {
      void **prev_stack = *(void**)stack;				
      unsigned long finfo = *(unsigned long*)(stack + 1);		
									
      GCDUMP_RECORD_TRAVSTACK(stack, FRAME_GET_SIZE(finfo),		
			      FRAME_GET_TYPE(finfo));			
      switch(FRAME_GET_TYPE(finfo)) {					
        case FRAME_TYPE_SIMPLE: {					
	  unsigned long size = FRAME_GET_SIZE(finfo), i;		
	  								
	  stack += 2;
	  for(i = 0; i < size; i++) 					
	    if(stack[i])						
	      gcREPAIR(*(void**)(stack[i]));				
	  break;							
	}								
									
        case FRAME_TYPE_ARRAY: {					
	  int i, j, size = FRAME_GET_SIZE(finfo);			
									
	  for(i = 0; i < size; i++) {					
	    void **array;						
	    unsigned long asize;					
									
	    stack += 2;							
	    array = *(void***)stack;					
	    asize = *(unsigned long*)(stack + 1);			
	    for(j = 0; j < asize; j++)					
	      if(array[j])						
		gcREPAIR(array[j]);					
	  }								
	  break;							
	}								
									
        case FRAME_TYPE_COMPLEX: {					
          int i, size = FRAME_GET_SIZE(finfo);                          
          stack += 2;							
          for ( i = 0; i < size; i++ ){                                 
	  void *ptr = *(void**)stack;	           			
	  if(ptr) {							
	    gc_complex_trav trav = *(gc_complex_trav*)(stack + 1);	
	    trav((void (*)(void*))GC_repair, ptr, 0 );     		
	  }								
		  stack += 4;                                           
	  }                                                             
	  break;							
	}								
									
        case FRAME_TYPE_TAGGED: {					
	  int i, size = FRAME_GET_SIZE(finfo);				
									
          stack += 2;							
	  for(i = 0; i < size; i++) {					
	    void *ptr;							
	    gc_tag tag;							
									
	    ptr = *(void**)stack;					
	    if(ptr) {							
	      tag = *(gc_tag*)(stack + 1);				
	      tag->repair(ptr);						
	    }								
	    stack += 4;							
	  }								
	  break;							
	}								
      }									
									
      stack = prev_stack;						
    }
}

/*****************************************************************************/
/*                                                                           */
/* The routines we use to implement the internal mark stack.                 */
/*                                                                           */
/*****************************************************************************/

#define STACK_PART_SIZE       (1 * 1024 * 1024)

/* We allocate our internal stack in fixed-sized chunks, given in the
   previous #define. The first word is a pointer to the next stack, all
   the rest are data in that stack frame. */
static void **stack_part_start = NULL;
static void **stack_part_current = NULL;
static void **stack_part_end = NULL;

/*inline*/ static void push_ptr(void *ptr)
{
  if(!stack_part_end) {
    stack_part_start = malloc_pages(STACK_PART_SIZE, 4096);
    *stack_part_start = NULL;
    stack_part_end = PPTR(NUM(stack_part_start) + STACK_PART_SIZE);
    stack_part_current = stack_part_start + 1;
  } else if(stack_part_current == stack_part_end) {
    void **new_chunk = malloc_pages(STACK_PART_SIZE, 4096);
    *new_chunk = stack_part_start;
    stack_part_start = new_chunk;
    stack_part_end = PPTR(NUM(stack_part_start) + STACK_PART_SIZE);
    stack_part_current = stack_part_start + 1;
  }
  *stack_part_current++ = ptr;
}

/*inline*/ static int pop_ptr(void **ptr)
{
  if(stack_part_current == (stack_part_start + 1)) {
    void **prev_chunk = *stack_part_start;
    free_pages(stack_part_start, STACK_PART_SIZE);
    stack_part_start = prev_chunk;
    if(prev_chunk) 
      stack_part_end = PPTR(NUM(stack_part_start) + STACK_PART_SIZE);
    else
      stack_part_end = NULL;
    stack_part_current = stack_part_end;
  }
  
  if(stack_part_current) {
    *ptr = *(--stack_part_current);
    return 1;
  } else return 0;
}

/*****************************************************************************/
/*                                                                           */
/* Routines to deal with immobility.                                         */
/*                                                                           */
/*****************************************************************************/

/*inline*/ static void *find_new_place_for_object(gc_tag tag, unsigned long size);

struct immobile {
  struct immobile *next; /* 4 */
  gc_tag tag;            /* 4 */
  void *ptr;             /* 4 */
  int initialized;       /* 4 */
};                       /* 16 */

static struct gcpage *immobile_pages = NULL;
static struct immobile *immobiles = NULL;

void GC_immobilize(int num, ...)
{
  int force_full = 0;
  va_list args;
  int i;

  va_start(args, num);
  for(i = 0; i < num; i++) {
    void *p = va_arg(args, void*);
    struct immobile *imm = gcint_malloc(sizeof(struct immobile));
    gc_tag tag = NULL;

    if(OBJ_IN_NURSERY(p)) {
      p = find_object_start(nursery_start, nursery_info, p);
      tag = *(gc_tag*)(NUM(p) - 4);
    } else {
      struct gcpage *page = find_page(p);
      p = find_object_start(page->page, page->info, p);
      tag = page->tag;
      force_full = 1;
    }

    imm->next = immobiles;
    imm->tag = tag;
    imm->ptr = p;
    imm->initialized = 0;
    immobiles = imm;
  }
  va_end(args);

  garbage_collect(force_full);
}

static /*inline*/ void *alloc_new_immobile(void *p)
{
  struct gcpage *page;
  void *endp, *newp;
  unsigned int objsize;
  void *data;
  u_int8_t *info;

  if(OBJ_IN_NURSERY(p)) {
    data = nursery_start;
    info = nursery_info;
  } else {
    page = find_page(p);
    data = page->page;
    info = page->info;
    GC_ASSERT(0, "Figure out immobilization of old ptr case.");
  }

  endp = find_object_end(data, info, p);
  objsize = NUM(endp) - NUM(p);
  newp = find_new_place_for_object(NULL, objsize);
  GC_ASSERT(newp, "Couldn't find new place for object?!");
  memcpy(newp, p, objsize);
  set_object_marked(data, info, p);
  *(void**)p = newp;

  return newp;
}

static void mark_immobiles()
{
  struct immobile *imm;

  for(imm = immobiles; imm; imm = imm->next) 
    if(imm->initialized) {
      imm->tag->mark(imm->ptr);
    } else {
      imm->ptr = alloc_new_immobile(imm->ptr);
      imm->initialized = 1;
      imm->tag->mark(imm->ptr);
    }
}

static void repair_immobiles()
{
  struct immobile *imm;

  for(imm = immobiles; imm; imm = imm->next) 
    imm->tag->repair(imm->ptr);
}

/*****************************************************************************/
/*                                                                           */
/* Routines to deal with autotagging.                                        */
/*                                                                           */
/*****************************************************************************/

static ptrmapper *autotag_entries = NULL;

void * find_autotag_stack( void ** stack, void * obj ){
	// printf( "Search in stack %p\n", stack );
	while ( stack != 0 ){
		void ** prev_stack = *stack;
		unsigned long finfo = *(unsigned long*)(stack + 1);
		switch ( FRAME_GET_TYPE(finfo) ){
			case FRAME_TYPE_TAGGED :
			case FRAME_TYPE_COMPLEX : {
				int i;
				stack += 2;
				for ( i = 0; i < FRAME_GET_SIZE( finfo ); i++ ){
					void ** start = *stack;
					unsigned int length = *(unsigned int *)(stack + 3);
					// printf( "Search for %p from %p to %p\n", obj, start, PTR(NUM(start) + length) );
					if ( NUM(obj) >= NUM(start) &&
					     NUM(obj) < NUM(start) + length ){
						return PTR(NUM(*(stack + 2)) + NUM(obj) - NUM(start));
					}
				}
			}
		}
		stack = prev_stack;
	}
	return 0;
}

void GC_autotag_union(void **ptr, int tag)
{
  struct gcpage *page;

  if(OBJ_IN_NURSERY(ptr)) {
    autotag_entries = set_ptrmapped_val(autotag_entries, ptr, (void*)tag);
    set_object_autotagged(nursery_start, nursery_info, ptr);
  } else if(page = find_page(ptr)) {
    autotag_entries = set_ptrmapped_val(autotag_entries, ptr, (void*)tag);
    if(!page->big_page)
      set_object_autotagged(page->page, page->info, ptr);
  } else {
	  void * info = find_autotag_stack( GC_get_variable_stack(), (void *) ptr );
	  if ( info ){
		  *(int *) info = tag;
	  }
  }
}

int GC_get_autotagged_case(void **ptr){
  if(OBJ_IN_NURSERY(ptr) || find_page(ptr) ) {
	  return (int)get_ptrmapped_val(autotag_entries, ptr);
  } else {
	  void * info = find_autotag_stack( GC_get_variable_stack(), (void *) ptr );
	  if ( info ){
		return *(int *) info;
	  }
  }
  return -1;
}

static /*inline*/ void copy_autotag_info(void *base, u_int8_t *info, void *old,
				     void *new_base, u_int8_t *new_info, 
				     void *new)
{
  void *old_end = find_object_end(base, info, old);
  unsigned long word_num = 0;
  void *current;

  /* The first word of an object is a little tricky, because the tag will
     be on the next word. Of course, that could just be talking about the
     next word ... */
  if(object_autotagged(base, info, old + 4)) {
    void *val = get_ptrmapped_val(autotag_entries, old);
    if(val != NOT_FOUND) {
      autotag_entries = remove_ptrmapped_val(autotag_entries, old);
      autotag_entries = set_ptrmapped_val(autotag_entries, new, val);
      GCDUMP_RECORD_COPYAUTO(old, new, val);
    }
  }

  for(current = old + 4, word_num = 1; 
      current < old_end; 
      current += 4, word_num++)
    {
      if(object_autotagged(base, info, current)) {
	void *val = get_ptrmapped_val(autotag_entries, current);
	void *newptr = new + (current - old);

	set_object_autotagged(new_base, new_info, newptr);
	if(val != NOT_FOUND) {
	  autotag_entries = remove_ptrmapped_val(autotag_entries, current);
	  autotag_entries = set_ptrmapped_val(autotag_entries, newptr, val);
	  GCDUMP_RECORD_COPYAUTO(current, newptr, val);
#ifdef EXEC_TEST
	}
#else
	} else GC_ASSERT(word_num == 1, "No value for autotagged word?!");
#endif
      }
    }
}

/*
  u_int32_t old_word_no = COMPUTE_WORD_NUMBER(base, old) + 1;
  u_int32_t new_word_no = COMPUTE_WORD_NUMBER(new_base, new) + 1;
  u_int32_t old_index = old_word_no >> 2;
  u_int32_t new_index = new_word_no >> 2;
  u_int32_t old_mod = (old_word_no - (old_index << 2));
  u_int32_t new_mod = (new_word_no - (new_index << 2));
  u_int8_t curval, first_run = 1;
  
  while(1) { // We do explicit breaks to get out of this
    switch(old_mod) {
      case 0: curval = info[old_index] >> 6; break;
      case 1: curval = (info[old_index] >> 4) & 0x3; break;
      case 2: curval = (info[old_index] >> 2) & 0x3; break;
      case 3: curval = info[old_index] & 0x3; break;
    }

    if(curval & FLAG_START_OBJ)
      break;
    
    if(curval & FLAG_AUTOTAGGED_OBJ) {
      u_int32_t val = new_info[new_index];
      void *ptr, *tagval;

      switch(new_mod) {
        case 0: new_info[new_index] = (val & 0x3f) | (FLAG_AUTOTAGGED_OBJ<<6);
	  break;
        case 1: new_info[new_index] = (val & 0xcf) | (FLAG_AUTOTAGGED_OBJ<<4); 
	  break;
        case 2: new_info[new_index] = (val & 0xf3) | (FLAG_AUTOTAGGED_OBJ<<2);
	  break;
        case 3: new_info[new_index] = (val & 0xfc) | FLAG_AUTOTAGGED_OBJ;
	  break;
      }

      ptr = base + (old_index << 4) + (old_mod << 2);
      tagval = get_ptrmapped_val(autotag_entries, ptr);
      if(tagval != NOT_FOUND) {
	GCDUMP_RECORD_COPYAUTO(ptr, new_base + (new_index<<4) + (new_mod<<2));
	autotag_entries = remove_ptrmapped_val(autotag_entries, ptr);
	ptr = new_base + (new_index << 4) + (new_mod << 2);
	autotag_entries = set_ptrmapped_val(autotag_entries, ptr, tagval);
      } else if(ptr == (old + 4)) {
	tagval = get_ptrmapped_val(autotag_entries, old);
	autotag_entries = remove_ptrmapped_val(autotag_entries, old);
	autotag_entries = set_ptrmapped_val(autotag_entries, new, tagval);
      }
    }

    old_mod += 1;
    if(old_mod > 3) old_mod = 0, old_index++;
    new_mod += 1;
    if(new_mod > 3) new_mod = 0, new_index++;
  }
}
*/

static ptrmapper *clean_up_ptrmapper(ptrmapper *map, 
				     u_int32_t shift, 
				     u_int32_t add_val)
{
  if(!map) 
    return NULL;

  if(map->subtrees) {
    int i;

    for(i = 0; i < 16; i++) 
      map->subtrees[i] = 
	clean_up_ptrmapper(map->subtrees[i], shift + 4, add_val + (i << shift));

  }

  if(map->ptr != NOT_FOUND) {
    struct gcpage *page;
    void *actual_ptr = PTR((NUM(map->ptr) << shift) + add_val);

    if(OBJ_IN_NURSERY(actual_ptr)) {
      /* If the pointer was not updated by the copy, then the object was
	 collected */
      map = remove_ptrmapped_val(map, map->ptr);
    } else if(page = find_page(actual_ptr)) {
      if(page->big_page) {
	if(page->marked_on == PAGE_UNMARKED)
	  map = remove_ptrmapped_val(map, actual_ptr);
      } else {
	void *objptr = find_object_start(page->page, page->info, actual_ptr);

	/* At this point in the process, a mark means the object is dead */
	if(object_marked(page->page, page->info, objptr))
	  map = remove_ptrmapped_val(map, map->ptr);
      }
    }
  }

  return map;
}

static void repair_autotag_entries(void)
{
  autotag_entries = clean_up_ptrmapper(autotag_entries, 0, 0);
}

/*****************************************************************************/
/*                                                                           */
/* Routines for generation 1 and marking.                                    */
/*                                                                           */
/*****************************************************************************/

/*inline*/ static void *find_new_place_for_object(gc_tag tag, unsigned long size)
{
  struct gcpage *top = tag ? pages[HASH_OBJ(tag)] : immobile_pages;
  struct gcpage *work = top;

  while(work && !VALID_PAGE_FOR_OBJ(work, tag, size))
    work = work->next;

  if(work) {
    /* Yay. Found a pre-existing page. */
    void *retval = PTR(NUM(work->page) + work->size);
    work->size += size;
    work->marked_on = PAGE_MARKED;
    /* Again, we need to mark the start of the next object, so that we
       can properly compute the end of the current object */
    set_object_start(work->page, work->info, PTR(NUM(retval) + size));
    // bzero( retval, size );
    return retval;
  } else {
    /* We need to allocate a new page */
    work = gcint_malloc(sizeof(struct gcpage));
    work->next = top;
    work->prev = NULL;
    work->page = malloc_pages(MPAGE_SIZE, MPAGE_SIZE);
    work->info = gcint_malloc(INFO_SIZE);
    work->tag = tag;
    work->size = size;
    work->previous_size = 0;
    work->generation = work->marked_on = 1;
    work->dirty = work->big_page = 0;
    /* Link this in with the rest of the items */
    if(work->next) work->next->prev = work;
    if(tag) 
      pages[HASH_OBJ(tag)] = work;
    else
      immobile_pages = work;
    /* Add this item to the page map */
    pagemap_add(work);
    /* Clear out the info */
    bzero(work->info, INFO_SIZE);
    /* We need to set both both the start and end for this first allocation */
    set_object_start(work->page, work->info, work->page);
    set_object_start(work->page, work->info, PTR(NUM(work->page) + work->size));
    /* return the new value */
    return work->page;
  } 
}

void gc_mark_for_type( void * x, struct gc_tag_struct * tag ){
	if ( x && OBJ_IN_NURSERY(x) || find_page(x) ) {
		tag->mark( x );
	}
}

void gc_repair_for_type( void * x, struct gc_tag_struct * tag ){
	// x = *(void **) x;
	if ( x && OBJ_IN_NURSERY(x) || find_page(x) ) {
		tag->repair( x );
	}
}

void GC_mark2( const void * c_ptr ){
  void *ptr = (void*)c_ptr;
  struct gcpage *page;

  if(!ptr) return;

  GCDUMP_RECORD_MARK(ptr);
  if(OBJ_IN_NURSERY(ptr)) {
    ptr = find_object_start(nursery_start, nursery_info, ptr);
    if(!object_marked(nursery_start, nursery_info, ptr)) {
	    /* warning: 32bit assumption */
      /* when looking this up in gdb do **(struct gc_tag_struct **) ((unsigned int)ptr - 4) */
      gc_tag tag = *(gc_tag*)(NUM(ptr) - 4);
      void *endp = find_object_end(nursery_start, nursery_info, (void*)c_ptr);
      unsigned int objsize = NUM(endp) - NUM(ptr);
      void *newplace = find_new_place_for_object(tag, objsize);
      
      /* Set it as marked and move it over */
      set_object_marked(nursery_start, nursery_info, ptr);
      memcpy(newplace, ptr, objsize);

      /* store the new place in the region of memory the pointer points to
       * so that the repair procedure can calculate the final resting place
       * for any pointer that has ptr as a value.
       * i.e. ptr becomes a forwarding pointer
       */
      *(void**)ptr = newplace;

      /* Transfer any autotagging information */
      page = find_page(newplace);
      GC_ASSERT(page, "Couldn't find page for new object?!");
      copy_autotag_info(nursery_start, nursery_info, ptr,
			page->page, page->info, newplace);

      /* Push the new propagation pointer */
      GCDUMP_RECORD_MARKMOVE(ptr, newplace, objsize, tag);
      push_ptr(newplace);

      /* If this is a full collection, we have to make sure that the
	 new place is denoted as marked, so that we don't accidentally
	 mark it as dead. */
      if(gc_top_generation) {
	struct gcpage *page = find_page(newplace);
	set_object_marked(page->page, page->info, newplace);
      }
    }
  } else if(page = find_page(ptr)) {
    /* Just die if this is in a high generation and we're only collecting
       gen 0, or if this is an immobile object (tag 0) */
    if( /*! force_mark &&*/ ((page->generation > gc_top_generation) || !page->tag))
      return;

    if(page->big_page) {
      if(page->marked_on == PAGE_UNMARKED) {
	if(page->generation == 0) {
	  page->generation = 1;

	  if(page->prev) page->prev->next = page->next; else
	    nursery_bigs = nursery_bigs->next;
	  if(page->next) page->next->prev = page->prev;

	  page->next = pages[HASH_OBJ(page->tag)];
	  page->prev = NULL;
	  if(page->next) page->next->prev = page;
	  pages[HASH_OBJ(page->tag)] = page;
	}
	/* Mark this object and add it to the propagation stack */
	page->marked_on = PAGE_MARKED;
	GCDUMP_RECORD_MARKBIG(ptr, page);
	push_ptr(page->page);
      }
    } else {
      ptr = find_object_start(page->page, page->info, ptr);
      if(!object_marked(page->page, page->info, ptr)) {
	set_object_marked(page->page, page->info, ptr);
	push_ptr(ptr);
	page->marked_on = PAGE_MARKED;
	GCDUMP_RECORD_MARKOLD(ptr,page);
      }
    }
  }
}

void GC_mark(const void *c_ptr){
	GC_mark2( c_ptr );
}


/*inline*/ static void internal_mark(void *p)
{
  struct gcpage *page = find_page(p);
  GC_ASSERT(page, "Couldn't find page for internal_mark?!?!");
  GCDUMP_RECORD_PROP(p,page);
  page->tag->mark(p);
}

static void propagate_marks(void)
{
  void *ptr;
  while(pop_ptr(&ptr)) 
    internal_mark(ptr);
}

/*****************************************************************************/
/*                                                                           */
/* Allocation                                                                */
/*                                                                           */
/*****************************************************************************/

static void *park = NULL;

static void *allocate_big(gc_tag tag, unsigned long sizeb)
{
  struct gcpage *page;

#ifdef MAGPIE_PAD_ALLOCATIONS
  sizeb += 4;
#endif
 alloc_retry:
  /* Never garbage collect if this is our first allocation with a new 
     nursery. */
  if(nursery_used != 0 && (nursery_used + sizeb > nursery_max)) {
    garbage_collect(0);
  }
  nursery_used += sizeb;
  /* Allocate the new page */
  page = gcint_malloc(sizeof(struct gcpage));
  page->next = nursery_bigs;
  page->prev = NULL;
  page->info = NULL;
  page->tag = tag;
  page->size = sizeb;
  page->previous_size = 0;
  page->generation = page->dirty = page->marked_on = 0;
  page->big_page = 1;
  page->page = malloc_pages(sizeb, MPAGE_SIZE);
  /* Link it up with the rest of the list */
  if(page->next) 
    page->next->prev = page;
  nursery_bigs = page;
  /* and add it to the page map, zero out the return val and return */
  pagemap_add(page);
  bzero(page->page, sizeb);
  return page->page;
}

void *GC_malloc(gc_tag tag, unsigned long size)
{
  unsigned int sizew;

  size = size ? size : 16;
#ifdef MAGPIE_PAD_ALLOCATIONS
  sizew = gcBYTES_TO_WORDS(size) + 2;
#else
  sizew = gcBYTES_TO_WORDS(size) + 1;
#endif
  if(sizew < MAX_OBJECT_SIZEW) {
    unsigned int sizeb = gcWORDS_TO_BYTES(sizew);
    unsigned int newsize;
    void *retval;

  alloc_retry:
    newsize = nursery_used + sizeb;
    if(newsize >= nursery_max) {
      garbage_collect(0);
      goto alloc_retry;
    }
    
    retval = PTR(NUM(nursery_current) + 4);
    *(gc_tag*)nursery_current = tag;
    nursery_current += sizew;
    nursery_used = newsize;
    /* Note that we need to throw in two object starts, here. The first
       because the previous ended at where the tag is now, so it doesn't
       correctly denote where the object start is. The second because we
       always mark the end of objects. */
    set_object_start(nursery_start, nursery_info, retval);
    set_object_start(nursery_start, nursery_info, nursery_current);
    /*
    if(retval == (void*)0x552218) {
      printf("HERE!\n");
    }
    */
    // return retval + 4;
    memset( retval, 0, size );
    return retval;
  } else return allocate_big(tag, size);
}

static void GC_break_case_realloc( void * ptr ){
}

void *GC_realloc(gc_tag tag, void *ptr, unsigned long size)
{
  unsigned long alloc_size = gcWORDS_TO_BYTES(gcBYTES_TO_WORDS(size));
  unsigned long previous_size = 0, copy_size = 0;
  void *retval = NULL;
  
  /* A little sanity check / early escape */
  if(!ptr)  return GC_malloc(tag, size);

#ifdef MAGPIE_PAD_ALLOCATIONS
  alloc_size += 4;
#endif

  if(OBJ_IN_NURSERY(ptr)) {
    ptr = find_object_start(nursery_start, nursery_info, ptr);
    previous_size = object_size(nursery_start, nursery_info, ptr);
    if(alloc_size >= MAX_OBJECT_SIZE) {
      /* The old pointer is in the nursery, but the new one needs to
	 be on a big page */
      struct gcpage *page = gcint_malloc(sizeof(struct gcpage));
      page->next = nursery_bigs;
      page->prev = NULL;
      page->info = NULL;
      page->tag = tag;
      page->size = alloc_size;
      page->previous_size = 0;
      page->generation = page->dirty = page->marked_on = 0;
      page->big_page = 1;
      page->page = malloc_pages(alloc_size, MPAGE_SIZE);
      if(page->next) page->next->prev = page;
      nursery_bigs = page;
      pagemap_add(page);
      retval = page->page;
    } else if((nursery_used + alloc_size + 12) < nursery_max) {
      /* Our new pointer is not a big page, and will not cause a
	 garbage collection opon allocation */
      retval = GC_malloc(tag, alloc_size);
    } else {
      /* Our new pointer is not a big page, but if we allocated it,
	 it will trigger a garbage collection. So we put it into the
	 older generation, with the thought that it will survive 
	 collection */
      retval = find_new_place_for_object(tag, alloc_size);
      find_page(retval)->dirty = 1;
    }
  } else {
    struct gcpage *page = find_page(ptr);
    int old_dirty;

    if ( ! page ){
	    GC_break_case_realloc( ptr );
    }
    GC_ASSERT(page, "Couldn't find page for realloc.");
    old_dirty = page->dirty;
    if(page->big_page) {
      ptr = page->page;
      previous_size = page->size;
      if(alloc_size >= MAX_OBJECT_SIZE) {
	/* The old page was a big page, and the new one needs to be one,
	   too */
	struct gcpage *new_page = gcint_malloc(sizeof(struct gcpage));
	new_page->info = NULL;
	new_page->tag = tag;
	new_page->size = alloc_size;
	new_page->previous_size = 0;
	new_page->generation = page->generation;
	new_page->dirty = page->dirty;
	new_page->marked_on = 0;
	new_page->big_page = 1;
	new_page->page = malloc_pages(alloc_size, MPAGE_SIZE);
	if(page->generation) {
	  new_page->next = pages[HASH_OBJ(tag)];
	  new_page->prev = NULL;
	  if(new_page->next) new_page->next->prev = new_page;
	  pages[HASH_OBJ(tag)] = new_page;
	} else {
	  new_page->next = nursery_bigs;
	  new_page->prev = NULL;
	  if(new_page->next) new_page->next->prev = new_page;
	  nursery_bigs = new_page;
	}
	pagemap_add(new_page);
	retval = new_page->page;
      } else {
	/* The old page was a big page, but the new one doesn't need
	   to be one. Just to simplify my life enormously, this just
	   ignores the generation of the page the data was on and just
	   allocates it in the older generation */
	retval = find_new_place_for_object(tag, alloc_size);
      }
    } else {
      /* This is an older generation object that's not a big page */
      ptr = find_object_start(page->page, page->info, ptr);
      previous_size = object_size(page->page, page->info, ptr);
      if(alloc_size >= MAX_OBJECT_SIZE) {
	struct gcpage *new_page = gcint_malloc(sizeof(struct gcpage));
	new_page->info = NULL;
	new_page->tag = tag;
	new_page->size = alloc_size;
	new_page->previous_size = 0;
	new_page->generation = new_page->big_page = 1;
	new_page->dirty = new_page->marked_on = 0;
	new_page->page = malloc_pages(alloc_size, MPAGE_SIZE);
	new_page->next = pages[HASH_OBJ(tag)];
	new_page->prev = NULL;
	if(new_page->next) new_page->next->prev = new_page;
	pages[HASH_OBJ(tag)] = new_page;
	pagemap_add(new_page);
	retval = new_page->page;
      } else {
	retval = find_new_place_for_object(tag, alloc_size);
      }
    }

    page = find_page(retval);
    page->dirty = old_dirty;
  }

  /* At this point, previous_size and retval are set to their correct
     values */
  GC_ASSERT(previous_size, "Invariant error");
  GC_ASSERT(retval, "Invariant error");

  /* Now that we've got the location to put this, we need to copy the
     information. The realloc() spec, according to the OS/X man page,
     says "copies as much of the old data pointed to by ptr as will fit
     in the new allocation." */
  if(previous_size > size)
    copy_size = size;
  else
    copy_size = previous_size;
  
  /* Do the copy and return*/
  memcpy(retval, ptr, copy_size);
  return retval;
}

int GC_find_size( void * obj ){
	struct gcpage * page;
	if ( OBJ_IN_NURSERY( obj ) ){
		void * start = find_object_start( nursery_start, nursery_info, obj );
		void * end = find_object_end( nursery_start, nursery_info, obj ) - 4;
		return end - start;
	} else if ( page = find_page( obj ) ){
		if ( page->big_page ){
			return page->size;
		} else {
			void * start = find_object_start(page->page, page->info, obj );
			void * end = find_object_end(page->page, page->info, obj ) - 4;
			return end - start;
		}
	} else {
		return -1;
	}
}

void *GC_kmalloc(gc_tag tag, unsigned long size, int priority)
{
  return GC_malloc(tag, size);
}

/*****************************************************************************/
/*                                                                           */
/* Routines for repairing modified pointers.                                 */
/*                                                                           */
/*****************************************************************************/

void GC_repair(void **pptr)
{
  struct gcpage *page;
  void *ptr;

  GC_ASSERT(pptr, "Null pointer given to GC_repair");
  ptr = *pptr;

  if(OBJ_IN_NURSERY(ptr)) {
    void *startp = find_object_start(nursery_start, nursery_info, ptr);
    GC_ASSERT( find_page(PTR(NUM(*(void**)startp) + (NUM(ptr) - NUM(startp)))), "Can't find new page for nursery object?" );
    *(void**)pptr = PTR(NUM(*(void**)startp) + (NUM(ptr) - NUM(startp)));
    GC_ASSERT( find_page( *pptr ), "Can't find new page for nursery object?" );
  } else if(page = find_page(ptr)) {
    if(page->marked_on == PAGE_MARKED_AND_MOVED) {
      void *startp = find_object_start(page->page, page->info, ptr);
      *(void**)pptr = PTR(NUM(*(void**)startp) + (NUM(ptr) - NUM(startp)));
      GC_ASSERT( find_page( *pptr ), "Can't find new page?" );
    }
  }
}

static void repair_heap(void)
{
  FOR_EACH_PAGE(page, i)
    if(page->marked_on) {
      gc_tag tag = page->tag;

      if(page->big_page) {
	tag->repair(page->page);
      } else {
	void *position = page->page;
	void *end = PTR(NUM(page->page) + page->size);

	while(position < end) {
	  GCDUMP_RECORD_REPAIR(position);
	  if(gc_top_generation) {
	    /* If this is a full collection, a mark here means that the
	       object is live. So essentially we now want to flip the
	       meanings of these items. 11 (marked) goes to 10 (start), 
	       and 10 (start) goes to 11 (dead). */
	    if(object_marked(page->page, page->info, position)) {
	      /* This object is live. so repair it and set it as live */
	      tag->repair(position);
	      set_object_start(page->page, page->info, position);
	    } else {
	      /* This object is dead. so just set it as so. */
	      set_object_marked(page->page, page->info, position);
	    }
	  } else {
	    /* If this is not a full collection, a mark in the older 
	       generation means that the object is dead. This is a 
	       little tricky, I know */
	    if(!object_marked(page->page, page->info, position))
	      tag->repair(position);
	  }
	  position = find_object_end(page->page, page->info, position);
	}
      }

      page->marked_on = 0;
    }
}

/*****************************************************************************/
/*                                                                           */
/* The internal mark / repair procedures.                                    */
/*                                                                           */
/*****************************************************************************/

gc_tag __gcstandard_atomic_tag;
gc_tag __gcstandard_array_tag;

void atomic_MARK(void *obj)
{
}

void pointer_MARK( void * obj ){
	GC_mark( *(void **) obj );
}

void pointer_REPAIR( void * obj ){
	GC_repair( (void **) obj );
}

void array_MARK(void *obj)
{
  void **start = obj;
  void **end = GC_END_OF_OBJECT(obj);

  while(start < end)
    gcMARK(*start++);
}

void array_REPAIR(void *obj)
{
  void **start = obj;
  void **end = GC_END_OF_OBJECT(obj);

  while(start < end)
    GC_repair(start++);
}

static void mark_dirty_pages(void)
{
  FOR_EACH_PAGE(page, i)
    if(page->dirty) {
      gc_tag tag = page->tag;

      page->marked_on = 1;
      if(page->big_page) {
	tag->mark(page->page);
      } else {
	void *position = page->page;
	void *end = PTR(NUM(page->page) + page->size);
	
	while(position < end) {
	  if(!object_marked(page->page, page->info, position))
	    /* In this particular situation, "outside" of normal
	       garbage collection, an object being "marked" means that
	       it's dead. */
	    tag->mark(position);
	  position = find_object_end(page->page, page->info, position);
	}
      }
    }
}

/*****************************************************************************/
/*                                                                           */
/* Garbage Collection                                                        */
/*                                                                           */
/*****************************************************************************/

#ifdef EXEC_TEST
void initialize_tags(void);
#endif

void GC_initialize()
{
  bzero(&page_map, sizeof(page_map));
  init_vm_subsystem();
  reset_nursery();
  __gcstandard_atomic_tag = GC_init_tag(atomic_MARK, atomic_MARK);
  __gcstandard_array_tag = GC_init_tag(array_MARK, array_REPAIR);
  __gcstandard_pointer_tag = GC_init_tag(pointer_MARK, pointer_REPAIR);
  initialize_tags();
}

void dirty_page(void *p) { 
  struct gcpage *page = find_page(p);
  GC_ASSERT(page, "Dirty write to unknown page.");
  protect_pages(page->page, page->size, 1);
  page->dirty = 1;
}

static void prepare_pages_for_collection(void)
{
  FOR_EACH_PAGE(page, i) {
    page->marked_on = 0;
    page->previous_size = page->size;
    if(gc_top_generation && page->info)
      clear_object_marks(page->info, INFO_SIZE);
  }
}

static void do_heap_compact(void)
{
  /* We have to do these page walks manually, because we're going to mess
     with the heap in ways that would confuse our standard FOR_EACH_PAGE */
  struct gcpage *page, *next;
  int i;

  if(gc_top_generation) {
    for(i = 0; i < HASH_SIZE; i++)
      for(page = pages[i]; page; page = next) {
	next = page->next;
	if(!page->marked_on) {
	  int page_size = page->big_page ? page->size : MPAGE_SIZE;
	  
	  if(page->next) page->next->prev = page->prev;
	  if(page->prev) page->prev->next = page->next; else
	    pages[i] = page->next;
	  
	  memset( page->page, 0xff, page_size );
	  
	  if(!page->dirty) protect_pages(page->page, page_size, 1);
	  pagemap_remove(page);
	  if(!page->big_page) gcint_free(page->info, INFO_SIZE);
	  free_pages(page->page, page_size);
	  gcint_free(page, sizeof(struct gcpage));
	}
      }
  }

  /* Always free any free gen0 big pages */
  while(nursery_bigs) {
    next = nursery_bigs->next;
    pagemap_remove(nursery_bigs);
    free_pages(nursery_bigs->page, nursery_bigs->size);
    gcint_free(nursery_bigs, sizeof(struct gcpage));
    nursery_bigs = next;
  }
  nursery_bigs = NULL;
}

static void clean_up_heap(void)
{
}

static void protect_old_pages(void)
{
  FOR_EACH_PAGE(page, i) {
    memory_in_use += page->size;
    if(page->tag != __gcstandard_atomic_tag)
      protect_pages(page->page, page->size, 0);
  }
}

void garbage_collect(int force_full)
{
  static unsigned long number = 0;
  static unsigned int since_last_full = 0;
  static unsigned long last_full_mem_use = (20 * 1024 * 1024);
  unsigned long old_mem_use = memory_in_use;

  static FILE * save;
  if ( ! save ){
	  save = fopen( "gc.log", "w" );
  }

  gc_top_generation = force_full || (since_last_full > 20) ||
    (memory_in_use > (2 * last_full_mem_use));
  number++;

  /*
     printf("Garbage collection #%u (nursery %p - %p, top %i)\n",
     number, nursery_start, nursery_end, gc_top_generation);
     */
     fprintf(save,"Garbage collection #%u (nursery %p - %p, top %i)\n",
     number, nursery_start, nursery_end, gc_top_generation);
     fflush(save);

  GCDUMP_START(number);
  /* Step #1: Prepare */
  prepare_pages_for_collection();
  /* Step #2: Mark the roots */
  if(!gc_top_generation) mark_dirty_pages();
  mark_roots();
  gcMARK(park);
  gcint_mark_stack(GC_get_variable_stack());
  mark_immobiles();
  /* Step #3: Propagate the marks */
  propagate_marks();
  /* Step #4: Compact the heap */
  do_heap_compact();
  /* Step #5: Repair all the pointers */
  repair_heap();
  repair_immobiles();
  repair_autotag_entries();
  gcint_repair_stack(GC_get_variable_stack());
  repair_roots();
  gcREPAIR(park);
  /* Step #6: Final clean-up */
  clean_up_heap();
  memory_in_use = 0;
  protect_old_pages();
  reset_nursery();
  flush_freed_pages();
  /* Step #7; Compute some last statistics */
  if(gc_top_generation) {
    since_last_full = 0;
    last_full_mem_use = memory_in_use;
  } else since_last_full++;
  GCDUMP_END();
}

/*****************************************************************************/
/*                                                                           */
/* Routines for doing internal testiong.                                     */
/*                                                                           */
/*****************************************************************************/

#ifdef EXEC_TEST
#include <assert.h>
#include <fcntl.h>

void *value = (void*)0x12345678;
unsigned long base_mem_use = 0;

void test_ptrmapper_for_file(char *filename)
{
  ptrmapper *map = NULL;
  void *buffer;
  int self;

  self = open(filename, O_RDONLY, 0);
  while(read(self, &buffer, 4) == 4) {
    if(buffer!= NOT_FOUND) map = set_ptrmapped_val(map, buffer, value);
  }
  close(self);
  self = open(filename, O_RDONLY, 0);
  while(read(self, &buffer, 4) == 4) {
    if(buffer!= NOT_FOUND) assert(get_ptrmapped_val(map, buffer) == value);
  }
  close(self);
  self = open(filename, O_RDONLY, 0);
  while(read(self, &buffer, 4) == 4) {
    if(buffer!= NOT_FOUND)
      if(get_ptrmapped_val(map, buffer) != NOT_FOUND)
	map = remove_ptrmapped_val(map, buffer);
  }
  close(self);
  assert(!map);
}

void test_ptrmapper(void)
{
  ptrmapper *map = NULL, *temp;
  u_int32_t i, j;
  
  /* TEST NUMBER ONE */
  printf("  Test #1\n");
  map = set_ptrmapped_val(map, value, value);
  assert(get_ptrmapped_val(map, value) == value);
  map = remove_ptrmapped_val(map, value);
  assert(!map);

  /* TEST NUMBER TWO */
  printf("  Test #2\n");
  for(i = 0, j = 1; i < 8; i++, j = (j << 4) + 1)
    map = set_ptrmapped_val(map, (void*)j, value+i);
  for(temp = map; temp && temp->subtrees; temp = temp->subtrees[1])
    for(i = 0; i < 16; i++)
      if((i != 1) && temp->subtrees)
      assert(temp->subtrees[i] == NULL);
  for(i = 0, j = 1; i < 8; i++, j = (j << 4) + 1)
    assert(get_ptrmapped_val(map, (void*)j) == (value + i));
  for(i = 0, j = 1; i < 8; i++, j = (j << 4) + 1)
    map = remove_ptrmapped_val(map, (void*)j);
  assert(!map);

  /* TEST NUMBER THREE */
  printf("  Test #3\n");
  for(i = 0, j = 1; i < 8; i++, j = (j << 4) + 1)
    map = set_ptrmapped_val(map, (void*)j, value+i);
  assert(get_ptrmapped_val(map, (void*)0x21111111) == NOT_FOUND);
  assert(get_ptrmapped_val(map, (void*)0x11112111) == NOT_FOUND);
  assert(get_ptrmapped_val(map, (void*)0x2) == NOT_FOUND);
  for(i = 0, j = 1; i < 8; i++, j = (j << 4) + 1)
    assert(get_ptrmapped_val(map, (void*)j) == (value + i));
  assert(get_ptrmapped_val(map, (void*)0x21111111) == NOT_FOUND);
  assert(get_ptrmapped_val(map, (void*)0x11112111) == NOT_FOUND);
  assert(get_ptrmapped_val(map, (void*)0x2) == NOT_FOUND);
  for(i = 0, j = 1; i < 8; i++, j = (j << 4) + 1)
    map = remove_ptrmapped_val(map, (void*)j);
  assert(!map);

  /* TEST NUMBER FOUR */
  printf("  Test #4\n");
  for(i = 0, j = 1; i < 8; i++, j = (j << 4) + 1)
    map = set_ptrmapped_val(map, (void*)j, value+i);
  for(i = 0, j = 1; i < 8; i++, j = (j << 4) + 1)
    assert(get_ptrmapped_val(map, (void*)j) == (value + i));
  for(i = 0, j = 0x11111111; i < 8; i++, j >>= 4)
    map = remove_ptrmapped_val(map, (void*)j);
  assert(!map);

  /* TEST NUMBER FIVE */
  printf("  Test #5\n");
  test_ptrmapper_for_file("gc_implementation.o");
   
  /* TEST NUMBER SIX */
  printf("  Test #6\n");
  test_ptrmapper_for_file("/Users/awick/Desktop/05NovemberSYSmap.pdf");

  /* TEST NUMBER SEVEN */
  printf("  Test #7\n");
  test_ptrmapper_for_file("/usr/lib/libcrypto.0.9.7.dylib");
}

void bitmap_test_basics(void *ptr, u_int8_t *info)
{
  /* Check that the starts were set correctly */
  assert(ptr == find_object_start(ptr, info, ptr));
  assert((ptr + 124) == find_object_start(ptr, info, ptr + 124));
  assert((ptr + 320) == find_object_start(ptr, info, ptr + 320));
  assert((ptr + 632) == find_object_start(ptr, info, ptr + 632));

  /* Check that the autotags were set correctly*/
  assert(object_autotagged(ptr, info, ptr + 320));
  assert(object_autotagged(ptr, info, ptr + 550));
  assert(object_autotagged(ptr, info, ptr + 820));

  /* Check that we can find the starts correctly */
  assert(ptr == find_object_start(ptr, info, ptr + 32));
  assert((ptr + 124) == find_object_start(ptr, info, ptr + 124 + 32));
  assert((ptr + 320) == find_object_start(ptr, info, ptr + 320 + 64));
  assert((ptr + 632) == find_object_start(ptr, info, ptr + 632 + 96));
  assert((ptr + 320) == find_object_start(ptr, info, ptr + 550));
  assert((ptr + 632) == find_object_start(ptr, info, ptr + 820));

  /* Check that we can find the ends correctly */
  assert((ptr + 124) == find_object_end(ptr, info, ptr + 32));
  assert((ptr + 320) == find_object_end(ptr, info, ptr + 124 + 32));
  assert((ptr + 632) == find_object_end(ptr, info, ptr + 320 + 64));
  assert((ptr + 1024) == find_object_end(ptr, info, ptr + 632 + 96));
}

void bitmap_basic_test(void *ptr)
{
  u_int8_t *info = gcint_malloc(PAGE_SIZE_TO_INFO_SIZE(4096));
  bzero(info, PAGE_SIZE_TO_INFO_SIZE(4096));

  /* Set the object starts */
  set_object_start(ptr, info, ptr);
  set_object_start(ptr, info, ptr + 124);
  set_object_start(ptr, info, ptr + 320);
  set_object_start(ptr, info, ptr + 632);
  set_object_start(ptr, info, ptr + 1024);

  /* Set some of these as autotagged */
  set_object_autotagged(ptr, info, ptr + 320);
  set_object_autotagged(ptr, info, ptr + 550);
  set_object_autotagged(ptr, info, ptr + 820);

  /* Check that the basic stuff works */
  bitmap_test_basics(ptr, info);

  /* Set the marks on some of these */
  set_object_marked(ptr, info, ptr + 124);
  set_object_marked(ptr, info, ptr + 320);

  /* Make sure they're still marked */
  assert(!object_marked(ptr, info, ptr));
  assert(object_marked(ptr, info, ptr + 124));
  assert(object_marked(ptr, info, ptr + 320));
  assert(!object_marked(ptr, info, ptr + 632));

  /* Check that the basic stuff works */
  bitmap_test_basics(ptr, info);

  /* Now clear all the marks */
  clear_object_marks(info, PAGE_SIZE_TO_INFO_SIZE(4096));

  /* And make sure nothing's marked, and the basic stuff still works */
  assert(!object_marked(ptr, info, ptr));
  assert(!object_marked(ptr, info, ptr + 124));
  assert(!object_marked(ptr, info, ptr + 320));
  assert(!object_marked(ptr, info, ptr + 632));
  bitmap_test_basics(ptr, info);

  gcint_free(info, PAGE_SIZE_TO_INFO_SIZE(4096));
}

void bitmap_copy_autotag_test(void *ptr)
{
  u_int8_t *old_info = gcint_malloc(PAGE_SIZE_TO_INFO_SIZE(4096));
  u_int8_t *new_info = gcint_malloc(PAGE_SIZE_TO_INFO_SIZE(4096));

  bzero(old_info, PAGE_SIZE_TO_INFO_SIZE(4096));
  bzero(new_info, PAGE_SIZE_TO_INFO_SIZE(4096));

  set_object_start(NULL, old_info, NULL);
  set_object_start(NULL, old_info, PTR(128));
  set_object_autotagged(NULL, old_info, PTR(32));
  set_object_autotagged(NULL, old_info, PTR(48));
  set_object_autotagged(NULL, old_info, PTR(112));

  /* Test if they're exactly matching */
  copy_autotag_info(NULL, old_info, NULL, ptr, new_info, ptr);
  assert(object_autotagged(ptr, new_info, ptr + 32));
  assert(object_autotagged(ptr, new_info, ptr + 48));
  assert(object_autotagged(ptr, new_info, ptr + 112));
  bzero(new_info, PAGE_SIZE_TO_INFO_SIZE(4096));

  /* Test if they're off by one word */
  copy_autotag_info(NULL, old_info, NULL, ptr, new_info, ptr + 4);
  assert(object_autotagged(ptr, new_info, ptr + 4 + 32));
  assert(object_autotagged(ptr, new_info, ptr + 4 + 48));
  assert(object_autotagged(ptr, new_info, ptr + 4 + 112));
  bzero(new_info, PAGE_SIZE_TO_INFO_SIZE(4096));

  /* Test if they're off by two words */
  copy_autotag_info(NULL, old_info, NULL, ptr, new_info, ptr + 8);
  assert(object_autotagged(ptr, new_info, ptr + 8 + 32));
  assert(object_autotagged(ptr, new_info, ptr + 8 + 48));
  assert(object_autotagged(ptr, new_info, ptr + 8 + 112));
  bzero(new_info, PAGE_SIZE_TO_INFO_SIZE(4096));

  /* Test if they're off by three words */
  copy_autotag_info(NULL, old_info, NULL, ptr, new_info, ptr + 12);
  assert(object_autotagged(ptr, new_info, ptr + 12 + 32));
  assert(object_autotagged(ptr, new_info, ptr + 12 + 48));
  assert(object_autotagged(ptr, new_info, ptr + 12 + 112));
  bzero(new_info, PAGE_SIZE_TO_INFO_SIZE(4096));

  gcint_free(old_info, PAGE_SIZE_TO_INFO_SIZE(4096));
  gcint_free(new_info, PAGE_SIZE_TO_INFO_SIZE(4096));
}

void test_bitmap(void)
{
  void *ptr = gcint_malloc(4096);

  printf("  Test #1\n");
  bitmap_basic_test(NULL);
  printf("  Test #2\n");
  bitmap_basic_test(ptr);
  printf("  Test #3\n");
  bitmap_copy_autotag_test(ptr);
  gcint_free(ptr, 4096);
}

void test_internal_stack(void)
{
  void *popval;
  int i;

  printf("  Test #1\n");
  push_ptr(PTR(0x12345678));
  assert(pop_ptr(&popval));
  assert(popval == PTR(0x12345678));
  assert(stack_part_current = (stack_part_start + 1));
  assert(!(*stack_part_start));

  printf("  Test #2\n");
  for(i = 0; i < STACK_PART_SIZE + 1; i++)
    push_ptr(PTR(0x12345678 + i));
  for(i = STACK_PART_SIZE; i >= 0; i--) {
    assert(pop_ptr(&popval));
    assert(popval == PTR(0x12345678 + i));
  }
  assert(stack_part_current = (stack_part_start + 1));
  assert(!(*stack_part_start));

  printf("  Test #3\n");
  for(i = 0; i <= (STACK_PART_SIZE / 4) - 2; i++)
    push_ptr(PTR(0x12345678 + i));
  for(i = 0; i < 8; i++) {
    push_ptr(PTR(0x12345679));
    push_ptr(PTR(0x1234567a));
    push_ptr(PTR(0x1234567b));
    push_ptr(PTR(0x1234567c));
    assert(pop_ptr(&popval));
    assert(popval = PTR(0x1234567c));
    assert(pop_ptr(&popval));
    assert(popval = PTR(0x1234567b));
    assert(pop_ptr(&popval));
    assert(popval = PTR(0x1234567a));
    assert(pop_ptr(&popval));
    assert(popval = PTR(0x12345679));
  }
  for(i = (STACK_PART_SIZE / 4) - 2; i >= 0; i--) {
    assert(pop_ptr(&popval));
    assert(popval == PTR(0x12345678 + i));
  }
  assert(stack_part_current = (stack_part_start + 1));
  assert(!(*stack_part_start));
  assert(!pop_ptr(&popval));
  assert(!stack_part_start);
  assert(!stack_part_current);
  assert(!stack_part_end);

  printf("  Test #4\n");
  assert(!pop_ptr(&popval));
  assert(!pop_ptr(&popval));
  assert(!pop_ptr(&popval));
}

void test_reset_nursery(void)
{
  nursery_start = malloc_pages(4096, MPAGE_SIZE);
  nursery_end = PPTR(NUM(nursery_start) + 4096);
  nursery_current = nursery_start;
  nursery_max = 4096;
  nursery_info_size = PAGE_SIZE_TO_INFO_SIZE(4096);
  nursery_info = gcint_malloc(nursery_info_size);
  bzero(nursery_start, 4096);
  bzero(nursery_info, nursery_info_size);
}

void test_cleanup_nursery(void)
{
  free_pages(nursery_start, 4096);
  gcint_free(nursery_info, nursery_info_size);
  nursery_max = nursery_info_size = 0;
  nursery_start = nursery_current = nursery_end = NULL;
  nursery_info = NULL;
}

void test_allocation(void)
{
  void *ptrs[7] = { 0, 0, 0, 0, 0, 0 };

  test_reset_nursery();

  printf("  Test #1\n");
  ptrs[0] = GC_malloc(PTR(1), 16);
  assert(ptrs[0] == PTR(NUM(nursery_start) + 4));
  assert(*PPTR(ptrs[0] - 4) == PTR(1));
  ptrs[1] = GC_malloc(PTR(2), 16);
  assert(ptrs[1] == PTR(NUM(ptrs[0] + 20)));
  assert(*PPTR(ptrs[1] - 4) == PTR(2));
  ptrs[2] = GC_malloc(PTR(3), 16);
  assert(ptrs[2] == PTR(NUM(ptrs[1] + 20)));
  assert(*PPTR(ptrs[2] - 4) == PTR(3));
  ptrs[3] = GC_malloc(PTR(4), 16);
  assert(ptrs[3] == PTR(NUM(ptrs[2] + 20)));
  assert(*PPTR(ptrs[3] - 4) == PTR(4));
  /* check that the start items got in right if we start at the start*/
  assert(ptrs[0] == find_object_start(nursery_start, nursery_info, ptrs[0]));
  assert(ptrs[1] == find_object_start(nursery_start, nursery_info, ptrs[1]));
  assert(ptrs[2] == find_object_start(nursery_start, nursery_info, ptrs[2]));
  assert(ptrs[3] == find_object_start(nursery_start, nursery_info, ptrs[3]));
  /* check that the start items got in right if we start in the middle */
  assert(ptrs[0] == find_object_start(nursery_start, nursery_info, ptrs[0]+8));
  assert(ptrs[1] == find_object_start(nursery_start, nursery_info, ptrs[1]+8));
  assert(ptrs[2] == find_object_start(nursery_start, nursery_info, ptrs[2]+8));
  assert(ptrs[3] == find_object_start(nursery_start, nursery_info, ptrs[3]+8));
  /* check that the object ends got in right */
  assert(ptrs[0] + 16 == find_object_end(nursery_start, nursery_info, ptrs[0]));
  assert(ptrs[1] + 16 == find_object_end(nursery_start, nursery_info, ptrs[1]));
  assert(ptrs[2] + 16 == find_object_end(nursery_start, nursery_info, ptrs[2]));
  assert(ptrs[3] + 16 == find_object_end(nursery_start, nursery_info, ptrs[3]));

  printf("  Test #2\n");
  *(unsigned long*)(ptrs[0] +  0) = 0x12345678;
  *(unsigned long*)(ptrs[0] +  8) = 0x87654321;
  *(unsigned long*)(ptrs[0] + 12) = 0x13579ace;
  ptrs[4] = GC_realloc(PTR(4), ptrs[0], 8);
  assert(ptrs[4] == (ptrs[3] + 20));
  assert(*PPTR(ptrs[4] - 4) == PTR(4));
  assert(*(unsigned long*)(ptrs[4] + 0) == 0x12345678);
  assert(*(unsigned long*)(ptrs[4] + 4) == 0x0);
  assert(*(unsigned long*)(ptrs[4] + 8) == 0x0);
  ptrs[5] = GC_realloc(PTR(5), ptrs[0], 32);
  assert(ptrs[5] == (ptrs[4] + 12));
  assert(*PPTR(ptrs[5] - 4) == PTR(5));
  assert(*(unsigned long*)(ptrs[5] + 0) == 0x12345678);
  assert(*(unsigned long*)(ptrs[5] + 4) == 0x0);
  assert(*(unsigned long*)(ptrs[5] + 8) == 0x87654321);
  assert(*(unsigned long*)(ptrs[5] + 12) == 0x13579ace);
  assert(ptrs[4] == find_object_start(nursery_start, nursery_info, ptrs[4]));
  assert(ptrs[4] == find_object_start(nursery_start, nursery_info, ptrs[4]+4));
  assert(ptrs[4] + 8 == find_object_end(nursery_start, nursery_info, ptrs[4]));
  assert(ptrs[5] == find_object_start(nursery_start, nursery_info, ptrs[5]));
  assert(ptrs[5] == find_object_start(nursery_start, nursery_info, ptrs[5]+16));
  assert(ptrs[5] + 32 == find_object_end(nursery_start, nursery_info, ptrs[5]));

  printf("  Test #3\n");
  ptrs[6] = GC_malloc(PTR(6), 4096 - (20 + 20 + 20 + 20 + 12 + 36) - 16);
  assert(*(unsigned long*)(ptrs[6] - 4) == 6);
  assert(ptrs[6] == find_object_start(nursery_start, nursery_info, ptrs[6]));
  assert(ptrs[6] == find_object_start(nursery_start, nursery_info, ptrs[6]+12));
  ptrs[6] = GC_realloc(PTR(7), ptrs[0], 32);
  assert(!OBJ_IN_NURSERY(ptrs[6]));
  assert(pages[HASH_OBJ(7)]);
  assert(find_page(ptrs[6]));
  assert(find_page(ptrs[6])->page == ptrs[6]);
  assert(find_page(ptrs[6])->tag == PTR(7));
  assert(ptrs[6] == find_object_start(find_page(ptrs[6])->page,
				      find_page(ptrs[6])->info, ptrs[6]));
  assert(ptrs[6] == find_object_start(find_page(ptrs[6])->page,
				      find_page(ptrs[6])->info, ptrs[6]+16));
  assert(ptrs[6] + 32 == find_object_end(find_page(ptrs[6])->page,
					 find_page(ptrs[6])->info, ptrs[6]));
  assert(*(unsigned long*)(ptrs[6] + 0) == 0x12345678);
  assert(*(unsigned long*)(ptrs[6] + 4) == 0x0);
  assert(*(unsigned long*)(ptrs[6] + 8) == 0x87654321);
  assert(*(unsigned long*)(ptrs[6] + 12) == 0x13579ace);

  free_pages(find_page(ptrs[6])->page, MPAGE_SIZE);
  gcint_free(find_page(ptrs[6])->info, INFO_SIZE);
  gcint_free(find_page(ptrs[6]), sizeof(struct gcpage));
  pages[HASH_OBJ(7)] = NULL;
  test_cleanup_nursery();

  printf("  Test #4\n");
  ptrs[0] = find_new_place_for_object(PTR(2), 32);
  ptrs[1] = find_new_place_for_object(PTR(2), 32);
  ptrs[2] = find_new_place_for_object(PTR(3), 32);
  ptrs[3] = find_new_place_for_object(PTR(2), 32);
  ptrs[4] = find_new_place_for_object(PTR(3), 32);
  ptrs[5] = find_new_place_for_object(PTR(2), 32);
  ptrs[6] = find_new_place_for_object(PTR(2), 32);

  assert(find_page(ptrs[4]) != find_page(ptrs[5]));
  assert(find_page(ptrs[2]) != find_page(ptrs[1]));
  assert(find_page(ptrs[2]) == find_page(ptrs[4]));
  assert(find_page(ptrs[0]) == find_page(ptrs[1]));
  assert(find_page(ptrs[0]) == find_page(ptrs[3]));
  assert(find_page(ptrs[0]) == find_page(ptrs[5]));
  assert(find_page(ptrs[0]) == find_page(ptrs[6]));
  assert(find_page(ptrs[0])->size = 32 * 5);
  assert(find_page(ptrs[2])->size = 32 * 2);

  assert(ptrs[1] == find_object_start(find_page(ptrs[1])->page,
				      find_page(ptrs[1])->info, ptrs[1]));
  assert(ptrs[1] == find_object_start(find_page(ptrs[1])->page,
				      find_page(ptrs[1])->info, ptrs[1]+16));
  assert(ptrs[3] == find_object_end(find_page(ptrs[1])->page,
				    find_page(ptrs[1])->info, ptrs[1]+16));

  free_pages(find_page(ptrs[0])->page, MPAGE_SIZE);
  gcint_free(find_page(ptrs[0])->info, INFO_SIZE);
  gcint_free(find_page(ptrs[0]), sizeof(struct gcpage));
  free_pages(find_page(ptrs[2])->page, MPAGE_SIZE);
  gcint_free(find_page(ptrs[2])->info, INFO_SIZE);
  gcint_free(find_page(ptrs[2]), sizeof(struct gcpage));
  bzero(pages, sizeof(pages));
  bzero(page_map, sizeof(page_map));
}

void test_clear_out_autotag_entries(ptrmapper *map)
{
  if(!map) return;
  if(map->subtrees) {
    int i;
    
    for(i = 0; i < 16; i++)
      test_clear_out_autotag_entries(map->subtrees[i]);
  }
  if(map->subtrees)
    gcint_free(map->subtrees, 16 * sizeof(ptrmapper*));
  gcint_free(map, sizeof(ptrmapper));
}

void test_cleanup_heap(void)
{
  FOR_EACH_PAGE(page, i) {
    unsigned long size = page->big_page ? page->size : MPAGE_SIZE;
    free_pages(page->page, size);
    if(!page->big_page) gcint_free(page->info, INFO_SIZE);
    gcint_free(page, sizeof(struct gcpage));
  }
  for(page = nursery_bigs; page; page = page->next) {
    free_pages(page->page, page->size);
    gcint_free(page, sizeof(struct gcpage));
  }

  free_pages(nursery_start, NUM(nursery_end) - NUM(nursery_start));
  gcint_free(nursery_info, nursery_info_size);
  nursery_max = nursery_info_size = 0;
  nursery_start = nursery_current = nursery_end = NULL;
  nursery_info = NULL;
  nursery_bigs = NULL;
  for(i = 0; i < HASH_SIZE; i++) pages[i] = NULL;
  test_clear_out_autotag_entries(autotag_entries);
  autotag_entries = NULL;
  while(pop_ptr((void**)&page)) {}
}

void test_mark_code(void)
{
  struct gcpage *page;
  void *ptrs[6], *repptrbase, *repptr;

  printf("  Test #1\n");
  reset_nursery();
  ptrs[0] = GC_malloc(PTR(3), MPAGE_SIZE * 3);
  ptrs[1] = GC_malloc(PTR(3), 128);
  ptrs[2] = GC_malloc(PTR(3), 256);
  ptrs[3] = GC_malloc(PTR(3), 32);
  ptrs[4] = find_new_place_for_object(PTR(3), 64);
  ptrs[5] = find_new_place_for_object(PTR(3), 76);

  assert(!OBJ_IN_NURSERY(ptrs[0]));
  assert(OBJ_IN_NURSERY(ptrs[1]));
  assert(OBJ_IN_NURSERY(ptrs[2]));
  assert(OBJ_IN_NURSERY(ptrs[3]));
  assert(!OBJ_IN_NURSERY(ptrs[4]));
  assert(!OBJ_IN_NURSERY(ptrs[5]));
  assert(find_page(ptrs[0])->big_page);
  assert(pages[HASH_OBJ(3)]->size == 64 + 76);
  assert(find_page(ptrs[4]) == find_page(ptrs[5]));

  set_object_autotagged(nursery_start, nursery_info, ptrs[1] + 12);
  set_object_autotagged(nursery_start, nursery_info, ptrs[2] + 64);
  set_object_autotagged(nursery_start, nursery_info, ptrs[3]);

  page = find_page(ptrs[4]);
  set_object_autotagged(page->page, page->info, ptrs[4] + 16);
  assert(ptrs[4] == find_object_start(page->page, page->info, ptrs[4]));
  assert(ptrs[4] == find_object_start(page->page, page->info, ptrs[4] + 8));
  assert(ptrs[4] == find_object_start(page->page, page->info, ptrs[4] + 16));
  assert(ptrs[4] == find_object_start(page->page, page->info, ptrs[4] + 60));

  GC_mark(ptrs[0]);
  GC_mark(ptrs[1] + 32);
  GC_mark(ptrs[2] + 4);
  GC_mark(ptrs[3]);
  GC_mark(ptrs[4]);
  GC_mark(ptrs[5]);

  for(page = pages[HASH_OBJ(3)]; page; page = page->next)
    if(page->big_page)
      assert(page->size == MPAGE_SIZE * 3);
    else
      assert(page->size == 128 + 256 + 32 + 64 + 76);

  assert(find_page(ptrs[0])->marked_on == PAGE_MARKED);
  page = find_page(ptrs[4]);
  assert(object_marked(nursery_start, nursery_info, ptrs[1]));
  assert(object_marked(nursery_start, nursery_info, ptrs[2]));
  assert(object_marked(nursery_start, nursery_info, ptrs[3]));
  assert(object_marked(page->page, page->info, ptrs[4]));
  assert(object_marked(page->page, page->info, ptrs[5]));
  assert(!nursery_bigs);

  assert(NUM(*(void**)ptrs[1]) < NUM(page->page) + page->size);
  assert(NUM(*(void**)ptrs[2]) < NUM(page->page) + page->size);
  assert(NUM(*(void**)ptrs[3]) < NUM(page->page) + page->size);
  assert(128 == object_size(page->page, page->info, *(void**)ptrs[1]));
  assert(256 == object_size(page->page, page->info, *(void**)ptrs[2]));
  assert(32 == object_size(page->page, page->info, *(void**)ptrs[3]));
  assert(object_autotagged(page->page, page->info, (*(void**)ptrs[1]) + 12));
  assert(object_autotagged(page->page, page->info, (*(void**)ptrs[2]) + 64));
  assert(object_autotagged(page->page, page->info, (*(void**)ptrs[3])));

  repptrbase = repptr = ptrs[0]; GC_repair(&repptr);
  assert(repptrbase == repptr);
  repptrbase = repptr = ptrs[1]; GC_repair(&repptr);
  assert(repptrbase != repptr);
  repptrbase = repptr = ptrs[2]; GC_repair(&repptr);
  assert(repptrbase != repptr);
  repptrbase = repptr = ptrs[3]; GC_repair(&repptr);
  assert(repptrbase != repptr);
  repptrbase = repptr = ptrs[4]; GC_repair(&repptr);
  assert(repptrbase == repptr);
  repptrbase = repptr = ptrs[5]; GC_repair(&repptr);
  assert(repptrbase == repptr);
  repptrbase = repptr = ptrs[2];
  repptr = repptr + 43; GC_repair(&repptr);
  assert(NUM(repptr) - NUM(*(void**)repptrbase) == 43);
  repptr = repptrbase = NULL;
  GC_repair(&repptr);
  assert(repptr == NULL && repptrbase == NULL);
  repptrbase = repptr = PTR(0x12345678);
  GC_repair(&repptr);
  assert(repptrbase == repptr);
  
  test_cleanup_heap();
}

void test_autotag_code(void)
{
  struct gcpage *page;
  void *ptrs[6];

  printf("  Test #1\n");
  reset_nursery();
  assert(!autotag_entries);
  ptrs[0] = GC_malloc(PTR(3), MPAGE_SIZE * 3);
  ptrs[1] = GC_malloc(PTR(3), 128);
  ptrs[2] = GC_malloc(PTR(3), 256);
  ptrs[3] = GC_malloc(PTR(3), 32);
  ptrs[4] = find_new_place_for_object(PTR(3), 64);
  ptrs[5] = find_new_place_for_object(PTR(3), 76);
  find_page(ptrs[4])->previous_size = 64 + 76;

  assert(!autotag_entries);
  GC_autotag_union((void**)&page, 0x11);
  GC_autotag_union(ptrs[0] + 78, 0x22);
  GC_autotag_union(ptrs[1] + 32, 0x33);
  GC_autotag_union(ptrs[2] + 12, 0x44);
  GC_autotag_union(ptrs[3], 0x55);
  GC_autotag_union(ptrs[4] + 36, 0x66);
  GC_autotag_union(ptrs[5] + 20, 0x77);

  assert(0x11 == GC_get_autotagged_case((void**)&page));
  assert(0x22 == GC_get_autotagged_case(ptrs[0] + 78));
  assert(0x33 == GC_get_autotagged_case(ptrs[1] + 32));
  assert(0x44 == GC_get_autotagged_case(ptrs[2] + 12));
  assert(0x55 == GC_get_autotagged_case(ptrs[3]));
  assert(0x66 == GC_get_autotagged_case(ptrs[4] + 36));
  assert(0x77 == GC_get_autotagged_case(ptrs[5] + 20));

  GC_mark(ptrs[0]);
  GC_mark(ptrs[1] + 32);
  GC_mark(ptrs[3]);
  GC_mark(ptrs[5]);
  repair_autotag_entries();

  assert(0x11 == GC_get_autotagged_case((void**)&page));
  assert(0x22 == GC_get_autotagged_case(ptrs[0] + 78));
  //  assert(0x33 == GC_get_autotagged_case((*(void**)ptrs[1]) + 32));
  assert(NOT_FOUND == PTR(GC_get_autotagged_case(ptrs[2] + 12)));
  //assert(0x55 == GC_get_autotagged_case((*(void**)ptrs[3])));
  //assert(NOT_FOUND == PTR(GC_get_autotagged_case(ptrs[4] + 36)));
  //assert(0x77 == GC_get_autotagged_case(ptrs[5] + 20));
  autotag_entries = remove_ptrmapped_val(autotag_entries, (void**)&page);
  autotag_entries = remove_ptrmapped_val(autotag_entries, ptrs[0] + 78);
  autotag_entries = remove_ptrmapped_val(autotag_entries,(*(void**)ptrs[1])+32);
  autotag_entries = remove_ptrmapped_val(autotag_entries, (*(void**)ptrs[3]));
  autotag_entries = remove_ptrmapped_val(autotag_entries, ptrs[5] + 20);
  //assert(!autotag_entries);
  
  test_cleanup_heap();
}

struct single_list {
  int num;
  struct single_list *next;
};

gc_tag single_list_tag = NULL;

void single_list_mark(void *_x)
{
  struct single_list *x;
  x = (struct single_list *)_x;
  gcMARK(x->next);
}

void single_list_repair(void *_x)
{
  struct single_list *x;
  x = (struct single_list *)_x;
  gcREPAIR(x->next);
}

void single_list_complex_trav(void (*mucker)(void*), void *ptr, void *info)
{
  struct single_list *x = ptr;
  mucker(x->next);
}

void test_stack_trav()
{
  void *obj;
  void *array[2];
  struct single_list tagged;
  struct single_list complex;

  void *simple_frame[3] = { 
    (void*)GC_variable_stack, 
    (void*)((3 << 2) + FRAME_TYPE_SIMPLE), 
    (void*)&obj
  };

  void *array_frame[4] = {
    (void*)simple_frame,
    (void*)((1 << 2) + FRAME_TYPE_ARRAY),
    (void*)&array,
    (void*)2
  };

  void *tagged_frame[4] = {
    (void*)array_frame,
    (void*)((1 << 2) + FRAME_TYPE_TAGGED),
    (void*)&tagged,
    (void*)single_list_tag
  };

  void *complex_frame[4] = {
    (void*)&tagged_frame,
    (void*)((0 << 2) + FRAME_TYPE_COMPLEX),
    (void*)&complex,
    (void*)&single_list_complex_trav
  };

  GC_variable_stack = complex_frame;
  printf("  Test #1\n");
  reset_nursery();
  assert(single_list_tag);
  obj = GC_malloc(PTR(1), 16);
  array[0] = GC_malloc(PTR(1), 16);
  array[1] = GC_malloc(PTR(1), 16);
  tagged.next = GC_malloc(single_list_tag, sizeof(struct single_list));
  complex.next = GC_malloc(single_list_tag, sizeof(struct single_list));
  assert(OBJ_IN_NURSERY(obj));
  assert(OBJ_IN_NURSERY(array[0]));
  assert(OBJ_IN_NURSERY(array[1]));
  assert(OBJ_IN_NURSERY(tagged.next));
  assert(OBJ_IN_NURSERY(complex.next));
  gcint_mark_stack(GC_variable_stack);
  assert(object_marked(nursery_start, nursery_info, obj));
  assert(object_marked(nursery_start, nursery_info, array[0]));
  assert(object_marked(nursery_start, nursery_info, array[1]));
  assert(object_marked(nursery_start, nursery_info, tagged.next));
  assert(object_marked(nursery_start, nursery_info, complex.next));
  while(pop_ptr(&obj)) { }
  GC_variable_stack = NULL;
  test_cleanup_heap();
}

void initialize_tags()
{
}

unsigned long current_memory_use()
{
  struct gcpage *work;
  unsigned long retval = NUM(nursery_start) - NUM(nursery_current);

  FOR_EACH_PAGE(page, i)
    retval += page->size;
  for(work = immobile_pages; work; work = work->next)
    retval += work->size;

  return retval;
}

void gc_test1()
{
  struct single_list *base = NULL, *temp;
  void *simple_frame[3] = { 
    (void*)GC_variable_stack,
    (void*)((3 << 2) + FRAME_TYPE_SIMPLE), 
    (void*)&base 
  };
  int i;
  
  printf("  Test #1\n");
  GC_variable_stack = simple_frame;
  for(i = 1000; i > 0; i--) {
    struct single_list *tmp;

    tmp = GC_malloc(single_list_tag, sizeof(struct single_list));
    assert(tmp);
    tmp->num = i;
    tmp->next = base;
    base = tmp;
  }
  /* Quick check that something isn't REALLY WEIRD */
  i = 0; 
  for(temp = base; temp; temp = temp->next)
    i++;
  assert(i == 1000);
  assert(!pages[HASH_OBJ(single_list_mark)]);
  assert(!pop_ptr((void**)&temp));

  garbage_collect(1);
  for(i = 1; i <= 1000; i++) {
    assert(base->num == i);
    base = base->next;
  }
  GC_variable_stack = simple_frame[0];
  garbage_collect(1);
  assert(!current_memory_use());
}

#define OBJS_TO_ALLOC (((10 * 1024 * 1024) / sizeof(struct single_list)) + 10)

void gc_test2()
{
  struct single_list *base = NULL, *temp;
  void *simple_frame[3] = { 
    (void*)GC_variable_stack, 
    (void*)((3 << 2) + FRAME_TYPE_SIMPLE), 
    (void*)&base 
  };
  int i;
  
  printf("  Test #2\n");
  GC_variable_stack = simple_frame;
  for(i = OBJS_TO_ALLOC; i > 0; i--) {
    temp = (struct single_list*)GC_malloc(single_list_tag, 
					  sizeof(struct single_list));
    assert(temp);
    temp->num = i;
    temp->next = base;
    base = temp;
  }
  /* Quick check that something isn't REALLY WEIRD */
  i = 0; 
  for(temp = base; temp; temp = temp->next)
    i++;
  assert(i == OBJS_TO_ALLOC);
  garbage_collect(1);
  i = 0; 
  for(temp = base; temp; temp = temp->next)
    i++;
  assert(i == OBJS_TO_ALLOC);
  temp = base;
  for(i = 1; i <= OBJS_TO_ALLOC; i++) {
    assert(temp->num == i);
    temp = temp->next;
  }
  GC_variable_stack = simple_frame[0];
  garbage_collect(1);
  assert(!current_memory_use());
}

void gc_test3()
{
  struct single_list *base = NULL, *temp;
  void *simple_frame[3] = { 
    (void*)GC_variable_stack, 
    (void*)((3 << 2) + FRAME_TYPE_SIMPLE), 
    (void*)&base 
  };
  int i;
  
  printf("  Test #3\n");
  GC_variable_stack = simple_frame;
  for(i = OBJS_TO_ALLOC; i > 0; i--) {
    struct single_list *temp;

    temp = GC_malloc(single_list_tag, sizeof(struct single_list));
    assert(temp);
    if(!(i & 0x1)) {
      temp->num = i;
      temp->next = base;
      base = temp;
    }
  }
  /* Quick check that something isn't REALLY WEIRD */
  i = 0; 
  for(temp = base; temp; temp = temp->next)
    i++;
  assert(i == (OBJS_TO_ALLOC >> 1));
  garbage_collect(1);
  for(i = 1; i <= OBJS_TO_ALLOC; i++) {
    if(!(i & 0x1)) {
      assert(base->num == i);
      base = base->next;
    }
  }
  GC_variable_stack = simple_frame[0];
  garbage_collect(1);
  assert(!current_memory_use());
}

struct atomic_data {
  int i;
  int i_times_2;
};

void gc_test4()
{
  struct atomic_data **array = GC_malloc(__gcstandard_array_tag,
					 100 * sizeof(struct atomic_data*));
  void *simple_frame[3] = { 
    (void*)GC_variable_stack,
    (void*)((3 << 2) + FRAME_TYPE_SIMPLE), 
    (void*)&array 
  };
  int i = 0;

  printf("  Test #4\n");
  GC_variable_stack = simple_frame;
  /* Allocated the item */
  for(i = 0; i < 100; i++) {
    array[i] = GC_malloc(__gcstandard_atomic_tag, sizeof(struct atomic_data));
    array[i]->i = i;
    array[i]->i_times_2 = i * 2;
  }
  /* Allocate a whole mess of junk */
  for(i = 0; i < OBJS_TO_ALLOC; i++)
    GC_malloc(__gcstandard_atomic_tag, sizeof(struct atomic_data));
  /* Check that everything's right */
  for(i = 0; i < 100; i++) {
    assert((array[i]->i == i) && (array[i]->i_times_2 == (i * 2)));
  }

  GC_variable_stack = simple_frame[0];
  garbage_collect(1);
  assert(!current_memory_use());
}

void gc_test5()
{
  struct atomic_data **array = GC_malloc(__gcstandard_array_tag,
					 100 * sizeof(struct atomic_data*));
  void *simple_frame[3] = { 
    (void*)GC_variable_stack, 
    (void*)((3 << 2) + FRAME_TYPE_SIMPLE), 
    (void*)&array 
  };
  void *old_array;
  int i = 0;

  printf("  Test #5\n");
  GC_variable_stack = simple_frame;
  GC_immobilize(1,array);
  old_array = array;
  /* Allocated the item */
  for(i = 0; i < 100; i++) {
    array[i] = GC_malloc(__gcstandard_atomic_tag, sizeof(struct atomic_data));
    array[i]->i = i;
    array[i]->i_times_2 = i * 2;
    assert(old_array == array);
  }
  /* Allocate a whole mess of junk */
  for(i = 0; i < OBJS_TO_ALLOC; i++) {
    GC_malloc(__gcstandard_atomic_tag, sizeof(struct atomic_data));
    assert(old_array == array);
  }
  /* Check that everything's right */
  for(i = 0; i < 100; i++) {
    assert(old_array == array);
    assert((array[i]->i == i) && (array[i]->i_times_2 == (i * 2)));
  }

  GC_variable_stack = simple_frame[0];
  garbage_collect(1);
  assert(current_memory_use() == (100 * (sizeof(struct atomic_data*) +
					 sizeof(struct atomic_data))));
}

void test_gc()
{
  GC_initialize();
  gc_test1();
  gc_test2();
  gc_test3();
  gc_test4();
  gc_test5();
}


int main(int argc, char **argv)
{
  single_list_tag = GC_init_tag(single_list_mark, single_list_repair);
  gc_top_generation = 1;

  printf("Testing bitmap structure\n");
  test_bitmap();
  printf("Testing allocation routines\n");
  test_allocation();
  printf("Testing internal pointer stack structure\n");
  test_internal_stack();
  printf("Testing marking code\n");
  test_mark_code();
  printf("Testing stack traversal routines\n");
  test_stack_trav();
  printf("Testing pointer mapping structure\n");
  test_ptrmapper();
  printf("Testing autotagging code\n");
  test_autotag_code();
  gc_top_generation = 0;
  printf("Testing collector\n");
  test_gc();

  gcint_free(single_list_tag, sizeof(struct gc_tag_struct));
  printf("Memory use after test (minus nursery): %li\n", 
	 gcint_memory_use - nursery_info_size);
  return 0;
}
#endif
