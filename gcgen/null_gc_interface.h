/* The interface to the collector */

#define GC_ASSERT(test, val) GC_assert(test, __FILE__, __LINE__, val)
#define gcMARK(x) GC_mark((void*)x)
#define gcREPAIR(x) GC_repair((void*)&(x))
#define gcMARK_FOR_TYPE(x,y) x
#define gcREPAIR_FOR_TYPE(x,y) y
#define gcDEBUG_MARK(x, y) gcMARK(y)

#define GC_END_OF_OBJECT(x) GC_find_end_of_object(x)
#define GC_OBJTYPE_IS(x, y) GC_test_object_type(x, y)
#define __gcINIT_TAG(x, y) GC_init_tag((mark_proc)x, (repair_proc)y)
#define GC_AUTOTAG(x,y) x
#define GC_AUTOTAGGED_CASE(x) 1

typedef int gc_tag;
typedef void (*mark_proc)(void *obj);
typedef void (*repair_proc)(void *obj);

extern int __gcstandard_atomic_tag;
extern int __gcstandard_array_tag;

/* The top of the stack-within-the-C-stack */
extern void **GC_variable_stack;

void GC_initialize();
void GC_mark(const void *ptr);
void GC_repair(void **ptr);
void *GC_malloc(gc_tag tag, unsigned int size);
#define GC_calloc(tag,x,y) GC_malloc(tag, (x)*(y))
void *GC_realloc(gc_tag tag, void *ptr, unsigned int size);
void *GC_kmalloc(gc_tag tag, unsigned int size, int priority);
void *GC_find_end_of_object(void *obj);
gc_tag GC_init_tag(mark_proc mark, repair_proc repair);
void GC_assert(int test, char* file, unsigned long line, char *errstr);
int GC_test_object_type(void *obj, gc_tag type);
void GC_add_root(void *pptr);
void GC_autotag_union(void **ptr, int tag);
int GC_get_autotagged_case(void **ptr);
