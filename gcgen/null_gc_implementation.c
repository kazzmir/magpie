/* 
   Copyright (C) 2006 Adam C. Wick
   See LICENSE for licensing information.
*/

/* The implementation of the collector */
#include "gc_interface.h"
#include "gc_tuning.h"
#include <stdlib.h>
#include <stdio.h>

void **GC_variable_stack;
gc_tag __gcstandard_atomic_tag;
gc_tag __gcstandard_array_tag;

void GC_assert(int test, char* file, unsigned long line, char *errstr)
{
  if(!test) {
    fprintf(stderr, "ASSERTION FAILURE(%s,%ul): %s\n", file, line, errstr);
  }
}

void *GC_malloc(gc_tag tag, unsigned int size)
{
  void *retval = malloc(size);
  bzero(retval, size);
  return retval;
}

void *GC_realloc(gc_tag tag, void *ptr, unsigned int size)
{
  return realloc(ptr, size);
}

void *GC_kmalloc(gc_tag tag, unsigned int size, int priority)
{
  return GC_malloc(tag, size);
}

void GC_mark(const void *ptr)
{
}

void GC_repair(void **ptr)
{
}

void *GC_find_end_of_object(void *obj)
{
  return NULL;
}

gc_tag GC_init_tag(void (mark)(void *ptr), void (repair)(void *ptr))
{
  return NULL;
}

int GC_test_object_type(void *obj, gc_tag type)
{
  return 0;
}

void GC_initialize()
{
}

void GC_immobilize(int num, ...)
{
}

void GC_add_root(void *pptr)
{
}

void GC_autotag_union(void **ptr, int tag)
{
}

int GC_get_autotagged_case(void **ptr)
{
}

