/* The VM subsystem for OS/X */
#if defined(__APPLE__) && defined(__ppc__) && defined(__MACH__)

#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>
#include <mach/mach.h>
#include <mach/mach_error.h>
#include <architecture/ppc/cframe.h>

/* Check that we haven't duplicated the handlers */
#ifdef VM_SYSTEM_DEFINED
# error "Multiple VM subsystems defined. HUH?!"
#else
# define VM_SYSTEM_DEFINED
#endif

static void dirty_page(void *p);

/* the structure of an exception msg and its reply */
typedef struct rep_msg {
  mach_msg_header_t head;
  NDR_record_t NDR;
  kern_return_t ret_code;
} mach_reply_msg_t;

typedef struct exc_msg {
  mach_msg_header_t head;
  /* start of the kernel processed data */
  mach_msg_body_t msgh_body;
  mach_msg_port_descriptor_t thread;
  mach_msg_port_descriptor_t task;
  /* end of the kernel processed data */
  NDR_record_t NDR;
  exception_type_t exception;
  mach_msg_type_number_t code_cnt;
  exception_data_t code;
  /* some padding */
  char pad[512];
} mach_exc_msg_t;

/* this is a neat little mach callback */
extern boolean_t exc_server(mach_msg_header_t *in, mach_msg_header_t *out);

/* these are the globals everyone needs */
#define page_size vm_page_size
static mach_port_t task_self = 0;
static mach_port_t exc_port = 0;

kern_return_t catch_exception_raise_state(mach_port_t port,
					  exception_type_t exception_type,
					  exception_data_t exception_data,
					  mach_msg_type_number_t data_cnt,
					  thread_state_flavor_t *flavor,
					  thread_state_t in_state,
					  mach_msg_type_number_t is_cnt,
					  thread_state_t out_state,
					  mach_msg_type_number_t os_cnt)
{
  return KERN_FAILURE;
}

kern_return_t catch_exception_raise_state_identitity
  (mach_port_t port,  mach_port_t thread_port, mach_port_t task_port,
   exception_type_t exception_type, exception_data_t exception_data,
   mach_msg_type_number_t data_count, thread_state_flavor_t *state_flavor,
   thread_state_t in_state, mach_msg_type_number_t in_state_count,
   thread_state_t out_state, mach_msg_type_number_t out_state_count)
{
  return KERN_FAILURE;
}

kern_return_t catch_exception_raise(mach_port_t port,
				    mach_port_t thread_port,
				    mach_port_t task_port,
				    exception_type_t exception_type,
				    exception_data_t exception_data,
				    mach_msg_type_number_t data_count)
{
  /* kernel return value is in exception_data[0], faulting address in
     exception_data[1] */
  if(exception_data[0] == KERN_PROTECTION_FAILURE) {
    dirty_page((void*)exception_data[1]);
    return KERN_SUCCESS;
  } else return KERN_FAILURE;
}

/* this is the thread which forwards off exceptions read from the exception
   server off to our exception catchers and then back out to the other
   thread */
void exception_thread(void)
{
  mach_msg_header_t *message;
  mach_msg_header_t *reply;
  kern_return_t retval;
  
  /* allocate the space for the message and reply */
  message = (mach_msg_header_t*)malloc(sizeof(mach_exc_msg_t));
  reply = (mach_msg_header_t*)malloc(sizeof(mach_reply_msg_t));
  /* do this loop forever */
  while(1) {
    /* block until we get an exception message */
    retval = mach_msg(message, MACH_RCV_MSG, 0, sizeof(mach_exc_msg_t), 
		      exc_port, MACH_MSG_TIMEOUT_NONE, MACH_PORT_NULL);
    /* forward off the handling of this message */
    GC_ASSERT(exc_server(message, reply), "exc_server() didn't like something");
    /* send the message back out to the thread */
    retval = mach_msg(reply, MACH_SEND_MSG, sizeof(mach_reply_msg_t), 0, 
		      MACH_PORT_NULL, MACH_MSG_TIMEOUT_NONE, MACH_PORT_NULL);
  }
}

/* this initializes the subsystem (sets the exception port, starts the
   exception handling thread, etc) */
static void macosx_init_exception_handler() 
{
  mach_port_t thread_self, exc_port_s, exc_thread;
  ppc_thread_state_t *exc_thread_state;
  mach_msg_type_name_t type;
  void *subthread_stack;
  kern_return_t retval;

  /* get ids for ourself */
  if(!task_self) task_self = mach_task_self();
  thread_self = mach_thread_self();

  /* allocate the port we're going to get exceptions on */
  retval = mach_port_allocate(task_self, MACH_PORT_RIGHT_RECEIVE, &exc_port);
  GC_ASSERT(retval == KERN_SUCCESS, "Couldn't allocate exception port");

  /* extract out the send rights for that port, which the OS needs */
  retval = mach_port_extract_right(task_self, exc_port, MACH_MSG_TYPE_MAKE_SEND,
				   &exc_port_s, &type);
  GC_ASSERT(retval == KERN_SUCCESS, "Couldn't extract send rights");

  /* set the exception ports for this thread to the above */
  retval = thread_set_exception_ports(thread_self, EXC_MASK_BAD_ACCESS, 
				      exc_port_s, EXCEPTION_DEFAULT, 
				      PPC_THREAD_STATE);
  GC_ASSERT(retval == KERN_SUCCESS, "Couldn't set exception ports");

  /* set up the subthread */
  retval = thread_create(task_self, &exc_thread);
  GC_ASSERT(retval == KERN_SUCCESS, "Couldn't create exception thread");

  subthread_stack = (void*)malloc(page_size);
  subthread_stack += (page_size - C_ARGSAVE_LEN - C_RED_ZONE);
  exc_thread_state = (ppc_thread_state_t*)malloc(sizeof(ppc_thread_state_t));
  exc_thread_state->srr0 = (unsigned int)exception_thread;
  exc_thread_state->r1 = (unsigned int)subthread_stack;
  retval = thread_set_state(exc_thread, PPC_THREAD_STATE,
			    (thread_state_t)exc_thread_state,
			    PPC_THREAD_STATE_COUNT);
  GC_ASSERT(retval == KERN_SUCCESS, "Couldn't set subthread state");
  retval = thread_resume(exc_thread);
  GC_ASSERT(retval == KERN_SUCCESS, "Couldn't resume subthread");
}

/* the VM subsystem as defined by the GC files */
static void *malloc_pages(unsigned long len, unsigned long alignment)
{
  kern_return_t retval;
  unsigned long extra = 0;
  void *r;

  if(!task_self) task_self = mach_task_self();

  /* round up to the nearest page: */
  if(len & (page_size - 1))
    len += page_size - (len & (page_size - 1));

  extra = alignment;
  retval = vm_allocate(task_self, (vm_address_t*)&r, len + extra, TRUE);
  GC_ASSERT(retval == KERN_SUCCESS, "Couldn't allocate memory");

  if(extra) {
    /* we allocated too large so we can choose the alignment */
    void *real_r;
    long pre_extra;

    real_r = (void*)(((unsigned long)r + (alignment-1)) & (~(alignment-1)));
    pre_extra = real_r - r;
    if(pre_extra) {
      retval = vm_deallocate(task_self, (vm_address_t)r, pre_extra);
      GC_ASSERT(retval == KERN_SUCCESS, "Couldn't dealloc pre-extra");
    }
    if(pre_extra < extra) {
      retval = vm_deallocate(task_self, (vm_address_t)real_r + len, 
			     extra - pre_extra);
      GC_ASSERT(retval == KERN_SUCCESS, "Couldn't dealloc post-extra");
    }
    r = real_r;
  }

  return r;
}

static void free_pages(void *p, unsigned long len)
{
  kern_return_t retval;

  retval = vm_deallocate(task_self, (vm_address_t)p, len);
  GC_ASSERT(retval == KERN_SUCCESS, "Couldn't deallocate page(s)");
}

static void flush_freed_pages()
{
}

static void protect_pages(void *p, unsigned long len, int writeable)
{
  kern_return_t retval;

  if(len & (page_size - 1)) {
    len += page_size - (len & (page_size - 1));
  }

  retval = vm_protect(task_self, (vm_address_t)p, len, FALSE,
		      writeable ? VM_PROT_ALL : (VM_PROT_READ|VM_PROT_EXECUTE));
  GC_ASSERT(retval == KERN_SUCCESS, "Couldn't (un)protect page(s)");
}

static void init_vm_subsystem()
{
  macosx_init_exception_handler();
}

#endif /* #ifdef OS_X */
