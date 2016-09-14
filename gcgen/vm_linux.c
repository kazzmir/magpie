/* The VM subsystem for OS/X */
#if defined(linux)

/* Check that we haven't duplicated the handlers */
#ifdef VM_SYSTEM_DEFINED
# error "Multiple VM subsystems defined. HUH?!"
#else
# define VM_SYSTEM_DEFINED
#endif

#include "gc_interface.h"

extern void dirty_page(void *p);

#include <signal.h>
#include <linux/version.h>

#if LINUX_VERSION_CODE >= KERNEL_VERSION(2,4,0)
static void fault_handler(int sn, struct siginfo *si, void *ctx)
{
  dirty_page(si->si_addr);
}
#else
static void fault_handler(int sn, struct sigcontext sc)
{
#if defined(powerpc) || defined(__powerpc__)
  dirty_page((void*)sc.regs->dar);
#else
  dirty_page((void*)sc.cr2);
#endif
  signal(SIGSEGV, (void (*)(int))fault_handler);
}
#endif

#include "vm_mmap.c"

#define malloc_pages(len, align) mmap_malloc_pages(len, align)
#define free_pages(p, len) mmap_free_pages(p, len)
#define flush_freed_pages() mmap_flush_freed_pages()
#define protect_pages(p,len,write) mmap_protect_pages(p, len, write)

static void init_vm_subsystem()
{
#if LINUX_VERSION_CODE >= KERNEL_VERSION(2,4,0)
  struct sigaction act, oact;
  memset(&act, sizeof(sigaction), 0);
  act.sa_sigaction = fault_handler;
  sigemptyset(&act.sa_mask);
  act.sa_flags = SA_SIGINFO;
  sigaction(SIGSEGV, &act, &oact);
#else
  signal(SIGSEGV, (void (*)(int))fault_handler);
#endif
}

static void ** GC_stack = 0;
void ** GC_get_variable_stack(){
	return GC_stack;
}

void GC_set_variable_stack( void ** stack ){
	GC_stack = stack;
}

#endif /* #ifdef defined(linux) */
