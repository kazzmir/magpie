#ifndef _gc_____
#define _gc_____
/*
 Copyright (C) 2006 Adam C. Wick
 See LICENSE for licensing information.
*/
/* The interface to the collector */

// #include <strings.h>

/* The types for a mark/repair procedure. */
typedef void (*mark_proc)(void *obj);
typedef void (*repair_proc)(void *obj);
typedef void (*debug_mark_proc)(char *name, void *obj);

/* The structure of a type information struction */
struct gc_tag_struct {
  mark_proc mark;
  repair_proc repair;
#ifdef HEAP_DEBUGGING
  debug_mark_proc debug_mark;
  int reserved; /* This structure must divide into 4096 */
#endif
};

void bzero( void * ptr, unsigned int size );

/* The structure of the type tags we use */
typedef struct gc_tag_struct *gc_tag;

extern gc_tag __gcstandard_atomic_tag;
extern gc_tag __gcstandard_array_tag;

/* The top of the stack-within-the-C-stack */
extern void **GC_variable_stack;

/* The interface published by the garbage collection system */
void GC_initialize(void);
void GC_add_root(void *pptr);
void GC_mark(const void *ptr);
void GC_repair(void **ptr);
void *GC_malloc(gc_tag tag, unsigned long size);
// #define GC_calloc(tag,x,y) GC_malloc(tag,(x)*(y))
inline void * GC_calloc( gc_tag tag, unsigned long x, unsigned long y ){
	return GC_malloc( tag, x * y );
}
void *GC_realloc(gc_tag tag, void *ptr, unsigned long size);
void *GC_kmalloc(gc_tag tag, unsigned long size, int priority);
void *GC_find_end_of_object(void *obj);
#ifdef HEAP_DEBUGGING
void GC_debug_mark(char *name, void *ptr);
gc_tag GC_init_tag(mark_proc mark, repair_proc repair, debug_mark_proc debug);
#else
gc_tag GC_init_tag(mark_proc mark, repair_proc repair);
#endif
void GC_assert(int test, char* file, unsigned long line, char *errstr);
int GC_test_object_type(void *obj, gc_tag type);
void GC_immobilize(int num, ...);
void garbage_collect(int force_full);

void GC_autotag_union(void **ptr, int tag);
int GC_get_autotagged_case(void **ptr);

/* The defines that make this all a bit easier to use */
#define GC_ASSERT(test, val) GC_assert((int)(test), __FILE__, __LINE__, val)
#define gcMARK(x) GC_mark((void*)x)
#define gcREPAIR(x) GC_repair((void*)&(x))
#define gcDEBUG_MARK(x,y) GC_debug_mark(x, (void*)y)
#define GC_END_OF_OBJECT(x) GC_find_end_of_object(x)
#define GC_OBJTYPE_IS(x, y) GC_test_object_type(x, y)
#define GC_AUTOTAG(x,y) (GC_autotag_union((void**)&(x),y),x)
#define GC_AUTOTAGGED_CASE(x) GC_get_autotagged_case((void**)x)
#define gcMARK_FOR_TYPE(x,y) y->mark((void*)(&x))
#define gcREPAIR_FOR_TYPE(x,y) y->repair((void*)&(x))
#ifdef HEAP_DEBUGGING
# define __gcINIT_TAG(x,y,z) GC_init_tag((mark_proc)x, (repair_proc)y, (debug_mark_proc)z)
#else
# define __gcINIT_TAG(x, y) GC_init_tag((mark_proc)x, (repair_proc)y)
#endif

#endif
