#if defined(__FreeBSD__)

/* Check that we haven't duplicated the handlers */
#ifdef VM_SYSTEM_DEFINED
# error "Multiple VM subsystems defined. HUH?!"
#else
# define VM_SYSTEM_DEFINED
#endif

static void dirty_page(void *p);

#include <signal.h>

void fault_handler(int sn, int code, struct sigcontext *sc, char *addr)
{
  dirty_page(addr);
}

#include "vm_mmap.c"

#define malloc_pages(len, align) mmap_malloc_pages(len, align)
#define free_pages(p, len) mmap_free_pages(p, len)
#define flush_freed_pages() mmap_flush_freed_pages()
#define protect_pages(p,len,write) mmap_protect_pages(p, len, write)

static void init_vm_subsystem()
{
  signal(SIGBUS, (void (*)(int))fault_handler);
}

#endif /* #if defined(__FreeBSD__) */
