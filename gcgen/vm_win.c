#if defined(_WIN32)

/* Check that we haven't duplicated the handlers */
#ifdef VM_SYSTEM_DEFINED
# error "Multiple VM subsystems defined. HUH?!"
#else
# define VM_SYSTEM_DEFINED
#endif

static void dirty_page(void *p);

LONG WINAPI fault_handler(LPEXCEPTION_POINTERS e)
{
  if ((e->ExceptionRecord->ExceptionCode == EXCEPTION_ACCESS_VIOLATION)
      && (e->ExceptionRecord->ExceptionInformation[0] == 1)) {
    designate_modified((void *)e->ExceptionRecord->ExceptionInformation[1]);

    return EXCEPTION_CONTINUE_EXECUTION;
  } else
    return EXCEPTION_CONTINUE_SEARCH;
}

typedef LONG (WINAPI*gcPVECTORED_EXCEPTION_HANDLER)(LPEXCEPTION_POINTERS e);

static void *malloc_pages(unsigned long len, unsigned long alignment)
{
  return (void*)VirtualAlloc(NULL, len, MEM_COMMIT|MEM_RESERVE, PAGE_READWRITE);
}
 
static void free_pages(void *p, unsigned long len)
{
  VirtualFree(p, 0, MEM_RELEASE);
}

static void flush_freed_pages()
{
}

static void protect_pages(void *p, unsigned long len, int writeable)
{
  DWORD old;

  VirtualProtect(p, len, (writeable ? PAGE_READWRITE : PAGE_READONLY), &old);
}

static void init_vm_subsystem()
{
  HMODULE hm;
  PVOID (WINAPI*aveh)(ULONG, gcPVECTORED_EXCEPTION_HANDLER);
  
  hm = LoadLibrary("kernel32.dll");
  if(hm) 
    aveh = (PVOID (WINAPI*)(ULONG, gcPVECTORED_EXCEPTION_HANDLER))
      GetProcAddress(hm, "AddVectoredExceptionHandler");
  else
    aveh = NULL;
  
  GC_ASSERT(aveh, "Generations not available in this rev of Windows");
  aveh(TRUE, fault_handler);
}

#endif /* defined(_WIN32) */
