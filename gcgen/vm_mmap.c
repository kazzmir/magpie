/* This file is a submodule, included by several other modules. As such, we
   don't need to check any multiple definition or anything. It does, however
   implement all the standard exports, prefixed with mmap_ */

#include <unistd.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/mman.h>
#include <errno.h>

static int page_size; /* OS page size */

#if defined(MAP_ANONYMOUS) && !defined(MAP_ANON)
# define MAP_ANON MAP_ANONYMOUS
#endif

#ifndef MAP_ANON
int fd, fd_created;
#endif

static void *mmap_malloc_pages(unsigned long len, unsigned long alignment)
{
  void *r;
  size_t extra = 0;

  if(!page_size)
    page_size = getpagesize();

#ifndef MAP_ANON
  if(!fd_created) {
    fd_created = 1;
    fd = open("/dev/zero", O_RDWR);
  }
#endif

  /* Round up to nearest page: */
  if(len & (page_size - 1))
    len += page_size - (len & (page_size - 1));

  extra = alignment;
  
#ifdef MAP_ANON
  r = mmap(NULL, len + extra, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON,
	   -1, 0);
#else
  r = mmap(NULL, len + extra, PROT_READ | PROT_WRITE, MAP_PRIVATE, fd, 0);
#endif

  GC_ASSERT(r != (void*)-1, "Couldn't allocate data");

  if(extra) {
    /* We allocate too large so we can choose the alignment */
    void *real_r;
    long pre_extra;

    real_r = (void*)(((unsigned long)r + (alignment - 1)) & (~(alignment-1)));
    
    pre_extra = real_r - r;
    if(pre_extra)
      GC_ASSERT(!munmap(r, pre_extra), "Couldn't unmap pre-extra");
    if(pre_extra < extra)
      GC_ASSERT(!munmap(real_r + len, extra - pre_extra),
		"Couldn't unmap post-extra");

    r = real_r;
  }

  return r;
}

static void mmap_free_pages(void *p, unsigned long len)
{
  GC_ASSERT(!munmap(p, len), "Couldn't free page(s)!");
}

static void mmap_flush_freed_pages(void)
{
}

static void mmap_protect_pages(void *p, unsigned long len, int writeable)
{
  if(len & (page_size - 1)) {
    len += page_size - (len & (page_size - 1));
  }

  GC_ASSERT(!mprotect(p, len, (writeable ? (PROT_READ|PROT_WRITE) : PROT_READ)),
	    "Couldn't (un)protect page(s)!");
}
