#if defined(sun)

/* Check that we haven't duplicated the handlers */
#ifdef VM_SYSTEM_DEFINED
# error "Multiple VM subsystems defined. HUH?!"
#else
# define VM_SYSTEM_DEFINED
#endif

static void dirty_page(void *p);

#include <signal.h>

void fault_handler(int sn, struct siginfo *si, void *ctx)
{
  dirty_page(si->si_addr);
}

#include "vm_mmap.c"

#define malloc_pages(len, align) mmap_malloc_pages(len, align)
#define free_pages(p, len) mmap_free_pages(p, len)
#define flush_freed_pages() mmap_flush_freed_pages()
#define protect_pages(p,len,write) mmap_protect_pages(p, len, write)

static void init_vm_subsystem()
{
  struct sigaction act, oact;
  memset(&act, sizeof(sigaction), 0);
  act.sa_sigaction = fault_handler;
  sigemptyset(&act.sa_mask);
  act.sa_flags = SA_SIGINFO;
  sigaction(SIGSEGV, &act, &oact);
}

#endif /* #if defined(sun) */
