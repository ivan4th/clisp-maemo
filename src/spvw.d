/*
 * (SPVW = Speicherverwaltung): Memory Management for CLISP
 * Bruno Haible 1990-2008
 * Sam Steingold 1998-2008
 * German comments translated into English: Stefan Kain 2002-03-24

 Content:
 module management
 debug utilities
 memory size
 object size determination
 Page Fault and Protection handling
 Garbage Collection
 memory provision functions
 cycle test
 memory walk
 elementary string functions
 other global auxiliary functions
 initialization
 loading and storing MEM-files
 dynamic loading of modules
 version */
#include "lispbibl.c"

#include <string.h> /* declares strchr() and possibly memset() */
#ifdef MULTITHREAD
  #define bzero(ptr,len)  memset(ptr,0,len)
  #define bcopy(source,dest,len)  memcpy(dest,source,len)
#endif

/* in this file, the table macros have a different utilization: */
  #undef LISPSPECFORM
  #undef LISPFUN
  #undef LISPSYM
  #undef LISPOBJ

/* table of all SUBRs: out-sourced to SPVWTABF
 size of this table: */
#define subr_count  ((sizeof(subr_tab)-varobjects_misaligned)/sizeof(subr_t))

/* table of all FSUBRs: moved to CONTROL
 size of this table: */
#define fsubr_count  (sizeof(fsubr_tab)/sizeof(fsubr_t))

/* tables of all relocatable pointers: moved to STREAM
 size of these tables: */
#define pseudocode_count  (sizeof(pseudocode_tab)/sizeof(Pseudofun))
#if defined(MICROSOFT) && !defined(UNICODE)
  #define pseudodata_count 0
#else
  #define pseudodata_count  (sizeof(pseudodata_tab)/sizeof(Pseudofun))
#endif
/* total table: */
#define pseudofun_count  (pseudocode_count+pseudodata_count)
local struct pseudofun_tab_ { object pointer[pseudofun_count]; } pseudofun_tab;

/* table of all fixed symbols: moved to SPVWTABS
 size of these tables: */
#define symbol_count  ((sizeof(symbol_tab)-varobjects_misaligned)/sizeof(symbol_))

/* table of all other fixed objects: moved to SPVWTABO
 size of these tables: */
#define object_count  (sizeof(object_tab)/sizeof(gcv_object_t))

/* looping over subr_tab:
 (NB: subr_tab_ptr_as_object(ptr) turns a traversing pointer
 into a genuine lisp-object.) */
#ifdef MAP_MEMORY_TABLES
  local uintC total_subr_count;
  #define for_all_subrs(statement)                                   \
    do {                                                             \
      var subr_t* ptr = (subr_t*)((char*)&subr_tab+varobjects_misaligned); /* traverse subr_tab */  \
      var uintC count;                                               \
      dotimesC(count,total_subr_count, { statement; ptr++; } );      \
    } while(0)
#else
  #define for_all_subrs(statement)                   \
    do {                                             \
      var module_t* module; /* traverse modules */   \
      for_modules(all_modules,{                      \
        if (module->initialized)                     \
          if (*module->stab_size > 0) {              \
            var subr_t* ptr = module->stab;          \
            var uintC count;                         \
            dotimespC(count,*module->stab_size,      \
                      { statement; ptr++; } );       \
          }                                          \
      });                                            \
    } while(0)
#endif

/* On traversal of symbol_tab:
 turns a traversing pointer into a genuine lisp-object. */
#ifdef MAP_MEMORY_TABLES
  #define symbol_tab_ptr_as_object(ptr)  as_object((oint)(ptr))
#else
  #ifdef TYPECODES
    #define symbol_tab_ptr_as_object(ptr) type_pointer_object(symbol_type,ptr)
  #else
    #ifdef WIDE_AUXI
      #define symbol_tab_ptr_as_object(ptr) as_object_with_auxi((aint)(ptr)+varobject_bias)
    #else
      #define symbol_tab_ptr_as_object(ptr) as_object((oint)(ptr)+varobject_bias)
    #endif
  #endif
#endif
/* traversal of symbol_tab: */
#define for_all_constsyms(statement)                                    \
  do { var symbol_* ptr = (symbol_*)((char*)&symbol_tab+varobjects_misaligned); /* pass through symbol_tab */ \
    var uintC count;                                                    \
    dotimesC(count,symbol_count, { statement; ptr++; } );               \
  } while(0)

/* Traverse object_tab: */
#define for_all_constobjs(statement)                                    \
  do { module_t* module;                   /* loop over modules */      \
       for_modules(all_modules,{                                        \
         if (module->initialized)                                       \
           if (*module->otab_size > 0) {                                \
             gcv_object_t* objptr = module->otab; /* loop over object_tab */ \
             uintC count;                                               \
             dotimespC(count,*module->otab_size,                        \
                       { statement; objptr++; } );                      \
       }});                                                             \
  } while(0)

/* Semaphores: decide, if a break is effectless (/=0) or
 effectual (all = 0) .
 Are set with set_break_sem_x and deleted with clr_break_sem_x again. */
#if !defined(MULTITHREAD)
/* in MT these semaphores are per thread */
global break_sems_ break_sems;
#endif
/* break_sem_0 == break_sems.einzeln[0]
     set, as long as a page-fault-handling is in progress
   break_sem_1 == break_sems.einzeln[1]
     set, as long as the memory management forbids a break
     (so that empty memory cannot be traversed by the GC)
   break_sem_2 == break_sems.einzeln[2]
     for package-management on lower level and hashtable-management
   break_sem_3 == break_sems.einzeln[3]
     for package-management on higher level
   break_sem_4 == break_sems.einzeln[4]
     set, as long as external functions are being called.
   break_sem_5 == break_sems.einzeln[5]
     set, as long as (UNIX) a signal-handler is being called. */

/* --------------------------------------------------------------------------
                          module management */

#include "spvw_module.c"

/* --------------------------------------------------------------------------
                            debug-helper */

#include "spvw_debug.c"

/* --------------------------------------------------------------------------
                          our own alloca() */

#include "spvw_alloca.c"

/* --------------------------------------------------------------------------
                         fast program-exit */

/* jmp_buf for return to the original-value of SP on program start: */
local jmp_buf original_context;

/* leave LISP immediately:
 quit_instantly(exitcode);
 > exitcode: 0 for normal, 1 for abnormal end of program, -signum for signal
   we must set the SP to the original value.
   (On some operating systems, the memory occupied by the program is
   returned with free() , before control is withdrawn from it.
   For this short span the SP has to be set reasonably.) */
local int exitcode;
#define quit_instantly(xcode)  exitcode = xcode; longjmp(original_context,1)

/* --------------------------------------------------------------------------
                         memory management, common part */

/* method of the memory management: */
#if defined(SPVW_BLOCKS) && defined(SPVW_MIXED) /* e.g. ATARI */
  #define SPVW_MIXED_BLOCKS
  #if !defined(TRIVIALMAP_MEMORY)
    /* Blocks grow like this:         |******-->     <--****| */
    #define SPVW_MIXED_BLOCKS_OPPOSITE
  #else  /* defined(TRIVIALMAP_MEMORY) */
    #if (!defined(WIDE_SOFT) || defined(CONS_HEAP_GROWS_DOWN)) && !defined(CONS_HEAP_GROWS_UP)
      /* Blocks grow like this:       |******-->     <--****| */
      #define SPVW_MIXED_BLOCKS_OPPOSITE
    #else
      /* Blocks grow like this:       |******-->      |***--> */
      #define SPVW_MIXED_BLOCKS_STAGGERED
    #endif
  #endif
#endif
#if defined(SPVW_BLOCKS) && defined(SPVW_PURE) /* e.g. UNIX_LINUX, Linux 0.99.7 */
  #define SPVW_PURE_BLOCKS
#endif
#if defined(SPVW_PAGES) && defined(SPVW_MIXED) /* e.g. HP9000_800 */
  #define SPVW_MIXED_PAGES
#endif
#if defined(SPVW_PAGES) && defined(SPVW_PURE) /* e.g. SUN4 */
  #define SPVW_PURE_PAGES
#endif

/* --------------------------------------------------------------------------
                          Page-Allocation */

#if defined(SINGLEMAP_MEMORY) || defined(TRIVIALMAP_MEMORY) || defined(MULTITHREAD)

#include "spvw_mmap.c"

#endif  /* SINGLEMAP_MEMORY || TRIVIALMAP_MEMORY || MULTITHREAD */

#if defined(SINGLEMAP_MEMORY) || defined(TRIVIALMAP_MEMORY)

#include "spvw_singlemap.c"

#if defined(SINGLEMAP_MEMORY) && defined(HAVE_WIN32_VM)
  /* Despite SINGLEMAP_MEMORY, a relocation may be necessary
   at loadmem() time. */
  #define SINGLEMAP_MEMORY_RELOCATE
#endif

#endif  /* SINGLEMAP_MEMORY || TRIVIALMAP_MEMORY */

/* Global variables. */

#ifndef MULTITHREAD

/* the STACK: */
#if !defined(STACK_register)
global gcv_object_t* STACK; 
#endif
#ifdef HAVE_SAVED_STACK
global gcv_object_t* saved_STACK;
#endif

/* MULTIPLE-VALUE-SPACE: */
#if !defined(mv_count_register)
global uintC mv_count;
#endif
#ifdef NEED_temp_mv_count
global uintC temp_mv_count;
#endif
#ifdef HAVE_SAVED_mv_count
global uintC saved_mv_count;
#endif
global object mv_space [mv_limit-1];
#ifdef NEED_temp_value1
global object temp_value1;
#endif
#ifdef HAVE_SAVED_value1
global object saved_value1;
#endif

/* During the execution of a SUBR, FSUBR: the current SUBR resp. FSUBR */
#if !defined(back_trace_register)
global p_backtrace_t back_trace = NULL;
#endif
#ifdef HAVE_SAVED_back_trace
global p_backtrace_t saved_back_trace;
#endif

/* during callbacks, the saved registers: */
#if defined(HAVE_SAVED_REGISTERS)
global struct registers * callback_saved_registers = NULL;
#endif

/* stack-limits: */
#ifndef NO_SP_CHECK
global void* SP_bound;          /* SP-growth-limit */
#endif
global void* STACK_bound;       /* STACK-growth-limit */
global void* STACK_start;       /* STACK initial value */

/* the lexical environment: */
global gcv_environment_t aktenv;

global unwind_protect_caller_t unwind_protect_to_save;

/* variables for passing of information to the top of the handler: */
global handler_args_t handler_args;

/* As only whole regions of handlers are deactivated and activated again,
 we treat the handlers on deactivation separately, but we maintain
 a list of the STACK-regions, in which the handlers are deactivated.
 A handler counts as inactive if and only if:
 low_limit <= handler < high_limit
 is true for one of the regions listed in inactive_handlers */
global stack_range_t* inactive_handlers = NULL;

/* --------------------------------------------------------------------------
                           Multithreading */

#define for_all_threadobjs(statement)                                   \
  do { var gcv_object_t* objptr = (gcv_object_t*)&aktenv;               \
    var uintC count;                                                    \
    dotimespC(count,sizeof(gcv_environment_t)/sizeof(gcv_object_t),     \
              { statement; objptr++; });                                \
  } while(0)

#define for_all_STACKs(statement)             \
  do { var gcv_object_t* objptr = &STACK_0;   \
    { statement; }                            \
  } while(0)

#define for_all_back_traces(statement)      \
  do { var p_backtrace_t bt = back_trace;   \
    { statement;  }                         \
  } while(0)

/* #if MULTITHREAD*/
#else

/* Mutex protecting the set of threads. */
local xmutex_t allthreads_lock;

/* Set of threads. */
#define THREAD_SYMVALUES_ALLOCATION_SIZE 4096
#define SYMVALUES_PER_PAGE (THREAD_SYMVALUES_ALLOCATION_SIZE/sizeof(gcv_object_t))
#define MAXNTHREADS  128
local uintC nthreads = 0;
local clisp_thread_t* allthreads[MAXNTHREADS];

/* POSIX threads with no recursive mutex support */
#if (defined(POSIX_THREADS) || defined(POSIXOLD_THREADS)) && !defined(PTHREAD_MUTEX_RECURSIVE_NP)
/* cache the global mutex attribute for recursive mutex creation */
global pthread_mutexattr_t recursive_mutexattr;
#endif

/* Number of symbol values currently in use in every thread. */
/* The first symvalue in thread is dummy - for faster Symbol_value*/
local uintL num_symvalues = 1;
/* Maximum number of symbol values in every thread before new thread-local
 storage must be added.
 = THREAD_SYMVALUES_ALLOCATION_SIZE/sizeof(gcv_object_t) */
global uintL maxnum_symvalues; 

#ifdef DEBUG_GCSAFETY
/* used during static initialization (before main() is called)
   at that time the multithreading has not been initialized and 
   there is no current thread. */
local uintL dummy_alloccount=0;
global uintL* current_thread_alloccount() 
{ 
  /* if MT is initialized - return the real alloccount. 
     otherwise (during subr_tab static initialization) the dummy one.
     anyway after this the tabs will be re-initialized*/
  return nthreads ? &current_thread()->_alloccount : &dummy_alloccount;
}
#endif

#ifdef per_thread
 global per_thread clisp_thread_t *_current_thread;
#else
 #if USE_CUSTOM_TLS == 1
  global xthread_key_t current_thread_tls_key;
 #elif USE_CUSTOM_TLS == 2

  global tsd threads_tls;

  /* A thread-specific data entry which will never    */
  /* appear valid to a reader.  Used to fill in empty */
  /* cache entries to avoid a check for 0.	    */
  local tse invalid_tse = {INVALID_QTID, 0, 0, 0};

  local void tsd_initialize()
  {
    var int i;
    xmutex_init(&(threads_tls.lock));
    for (i = 0; i < TS_CACHE_SIZE; ++i) {
      threads_tls.cache[i] = &invalid_tse;
    }
    memset(threads_tls.hash,0,sizeof(threads_tls.hash));
  }

  /* entry should be allocated by the caller (or reside on
     the stack at a location that will survive the thread
     lifespan) */
  global void tsd_setspecific(tse *entry, void *value) 
  {
    var xthread_t self = xthread_self();
    var int hash_val = TSD_HASH(self);
    xmutex_lock(&(threads_tls.lock));
    /* Could easily check for an existing entry here.	*/
    entry -> next = threads_tls.hash[hash_val];
    entry -> thread = self;
    entry -> value = value;
    entry -> qtid = INVALID_QTID; 
    /* There can only be one writer at a time, but this needs to be	*/
    /* atomic with respect to concurrent readers.			*/ 
    /****** TODO TODO TODO TODO: WAS ATOMIC *******/
    /* since we call it only during thread creation - we even may go without
      atomic operation - but I am not sure - should check it carefully */
    /*AO_store_release((volatile AO_t *)(threads_tls.hash + hash_val), (AO_t)entry);*/
    *(threads_tls.hash + hash_val)=entry;
    xmutex_unlock(&(threads_tls.lock));
  }

  /* Remove thread-specific data for this thread.  Should be called on	*/
  /* thread exit.						    */
  global void tsd_remove_specific() 
  {
    xthread_t self = xthread_self();
    unsigned hash_val = TSD_HASH(self);
    tse *entry;
    tse **link = threads_tls.hash + hash_val;
    xmutex_lock(&(threads_tls.lock));
    entry = *link;
    while (entry != NULL && entry->thread != self) {
      link = &(entry->next);
      entry = *link;
    }
    /* Invalidate qtid field, since qtids may be reused, and a later 	*/
    /* cache lookup could otherwise find this entry.			*/
    entry -> qtid = INVALID_QTID;
    if (entry != NULL) {
      *link = entry->next;
      /* Atomic! concurrent accesses still work.	*/
      /* They must, since readers don't lock.		*/
      /* We shouldn't need a volatile access here,	*/
      /* since both this and the preceding write 	*/
      /* should become visible no later than		*/
      /* the pthread_mutex_unlock() call.		*/
    }
    xmutex_unlock(&(threads_tls.lock));
  }

  /* Note that even the slow path doesn't lock.	*/
  global void* tsd_slow_getspecific(unsigned long qtid,
				  tse * volatile *cache_ptr) 
  {
    xthread_t self = xthread_self();
    unsigned hash_val = TSD_HASH(self);
    tse *entry = threads_tls.hash[hash_val];
    ASSERT(qtid != INVALID_QTID);
    while (entry != NULL && entry->thread != self) {
      entry = entry->next;
    } 
    if (entry == NULL) return NULL;
    /* Set cache_entry.		*/
    entry->qtid = qtid;
    /* It's safe to do this asynchronously.  Either value 	*/
    /* is safe, though may produce spurious misses.		*/
    /* We're replacing one qtid with another one for the	*/
    /* same thread.						*/
    *cache_ptr = entry;
    /* Again this is safe since pointer assignments are 	*/
    /* presumed atomic, and either pointer is valid.	*/
    return entry->value;
  }
 #elif USE_CUSTOM_TLS == 3
  /* Currently only POSIX_THREADS and Win32 are supported. 
     For other platforms we have to find a way to locate the 
     current thread's stack base and size. These two functions
     are useful not only for threading but for general stack
     checking (but currently defined only in this case).
  */
  /* libsigsegv can be used to obtain the stack region (stack-vma). 
   I do not use it since: 
     1. No exported interface to use stackvma-xxx functions.
     2. It may not be available - for some reason no generational GC is needed.
     3. There is a problem on linux. /proc may not exist if we are running 
        as a chroot program, so reading /proc/self/maps could fail.
  */

  #if defined(POSIX_THREADS) || defined(POSIXOLD_THREADS)
  /* there is difference between the main thread stack base/size and 
   the ones created via pthread_create(). For the latter we will use
   pthread_getattr_np(), however it returns bogus values for the main thread
   (seems only with LinuxThreads).
   So we have to find out whether the current thread is the main one and 
   get values in other way.*/

  /* helper function for threads created by pthread_create() */
  local bool get_stack_region(aint *base, size_t *size)
  {
    #ifdef UNIX_DARWIN
     var pthread_t self_id;
     self_id = pthread_self();
     *base = (aint)pthread_get_stackaddr_np(self_id);	
     *size = pthread_get_stacksize_np(self_id); 
     return true;
    #else /* assume fairly recent pthreads implementation */
     var pthread_attr_t attr;
     var void *start;
     pthread_getattr_np(pthread_self(), &attr);
     pthread_attr_getstack(&attr, &start, size);
     /* the start is the top of the stack (at least on x86) */
     *base=(aint)start + *size;
     return true;
    #endif
    return false;
  }

  local aint current_stack_base() 
  {
    if (!nthreads) { /* main thread ? */
      /* for practical reasons - not to have too much code that anyway will
	 not make big difference - just use the current SP. This is basically
	 good guess. It may fail if the threads globals are accessed by
	 the caller of this function and the SP is exactly/near page border. 
	 The caller here may be only main() - so it should be safe.
	 In any case there is STACK_PAGE_THRESHOLD (1 page is just a guess -
	 works fine. even if later on another thread stack should intefere
	 with this page - during the creation of the thread it will 
	 fix the mapping - this threshold is used only for the main thread) */
     #define STACK_PAGE_THRESHOLD 4096
     #ifdef SP_UP
      return roughly_SP() - STACK_PAGE_THRESHOLD;
     #else /* SP_DOWN */
      return roughly_SP() + STACK_PAGE_THRESHOLD;
     #endif
     #undef STACK_PAGE_THRESHOLD
    } else {
      /* created by pthread_create. */
      var aint base;
      var size_t size;
      if (get_stack_region(&base,&size))
	return base;
    }
    fprintf(stderr,"FATAL: current_stack_base(): cannot find stack base address.");
    return 0; /* certinaly will cause problems */
  }
  /* should return maximum possible thread stack size */
  local size_t current_stack_size() 
  {
    var size_t stack_size=0;
    if (!nthreads) {
      /* This is the main thread - the only one that is initialized
       before being registered (and thus nthreads=0). Use getrlimit().
      What to do if we do not have getrlimit()? Currently we will crash.*/
      var struct rlimit rl;
      if (getrlimit(RLIMIT_STACK, &rl) == 0)
	stack_size = (rl.rlim_max == RLIM_INFINITY) ? rl.rlim_cur : rl.rlim_max;
        /*NB: there is a chance this value to be larger that needed and to 
	  fill more items in threads_map. However since we are the first thread
	  there is no problem - other threads will overwrite these mapping later.*/
    } else {
      /* we are in a thread created by pthread_create() */
      var aint base;
      var size_t size;
      if (get_stack_region(&base,&size))
	return stack_size=size;
    }

    /* after all "computation"/guessing about the stack size let's check*/
    if (stack_size <= TLS_PAGE_SIZE) {
      fprintf(stderr,"FATAL: current_stack_size(): cannot find stack size.");
      abort();
    }

    return stack_size - TLS_PAGE_SIZE; 
  }
  #endif /* POSIX_THREADS */
  #ifdef WIN32_THREADS
  /* taken from Sun's Hotspot JVM */
  local aint current_stack_base() 
  {
    MEMORY_BASIC_INFORMATION minfo;
    aint stack_bottom;
    size_t stack_size;
    VirtualQuery(&minfo, &minfo, sizeof(minfo));
    stack_bottom =  (aint)minfo.AllocationBase;
    stack_size = minfo.RegionSize;
    /* Add up the sizes of all the regions with the same */
    /* AllocationBase. */
    while( 1 ) {
      VirtualQuery(stack_bottom+stack_size, &minfo, sizeof(minfo));
      if ( stack_bottom == (aint)minfo.AllocationBase )
        stack_size += minfo.RegionSize;
      else
        break;
    }
    return stack_bottom + stack_size;
  }
  local size_t current_stack_size() 
  {
    size_t sz;
    MEMORY_BASIC_INFORMATION minfo;
    VirtualQuery(&minfo, &minfo, sizeof(minfo));
    sz = (size_t)current_stack_base() - (size_t)minfo.AllocationBase;
    return sz;
  }
  #endif /* WIN32_THREADS */

  global clisp_thread_t *threads_map[1UL << (32 - TLS_SP_SHIFT)]={0};
  global void set_current_thread(clisp_thread_t *thr)
  {
    /* we should initialize the threads_map items in the 
     stack range of the current thread to point to thr. */
    var aint stack_top = current_stack_base(),p;
    var size_t stack_size = current_stack_size(), mapped=0;
    var int page_size=TLS_PAGE_SIZE ,signed_ps; 
    signed_ps=page_size;
    #ifdef SP_DOWN
     signed_ps*=-1; 
    #endif
    for (p=stack_top, mapped=0;
         mapped < stack_size;
         p+=signed_ps, mapped+=page_size) {
      threads_map[(unsigned long)p >> TLS_SP_SHIFT] = thr;
    }
  }
 #else /* bad value for USE_CUSTOM_TLS */
  #error "USE_CUSTOM_TLS should be defined as 1,2 or 3."
 #endif
#endif /* !per_thread */

/* Initialization. Called at the beginning of main(). */
local void init_multithread (void) {
  xthread_init();
  xmutex_init(&allthreads_lock);
  maxnum_symvalues = SYMVALUES_PER_PAGE;
  #if !defined(per_thread)
   #if USE_CUSTOM_TLS == 1
    xthread_key_create(&current_thread_tls_key);
   #elif USE_CUSTOM_TLS == 2
    tsd_initialize();
   #elif USE_CUSTOM_TLS == 3
   #endif
  #endif
}

/* Last stage of MT initialization. Called after the LISP heap and  symbols 
   are initialized. Initialize per thread special symbols */
local void init_multithread_special_symbols()
{
  /* currently there is just a single thread. get it.*/
  var clisp_thread_t *thr=current_thread();
  for_all_constsyms({
    gcv_object_t p=symbol_tab_ptr_as_object(ptr);
    if (special_var_p(TheSymbol(p))) {
      /* Also we do not care about possibility to exceed the already allocated
	 space for _symvalues - we have enough space for the standard symbols.
      */
      thr->_ptr_symvalues[num_symvalues]=SYMVALUE_EMPTY;
      TheSymbol(p)->tls_index=num_symvalues++;
    }
  });
}

/* VTZ: allocates a LISP stack for new thread (except for the main one) 
 The stack_size parameters is in bytes. 
 It is always called with main thread lock - so we are not going to call
 begin/end_system_call.*/
local void* allocate_lisp_thread_stack(clisp_thread_t* thread, uintM stack_size)
{ 
  var uintM low,high;
  begin_system_call();
  low=(uintM)malloc(stack_size);
  end_system_call();
  if (!low) return NULL;
  high=low+stack_size/sizeof(uintM);
  #ifdef STACK_DOWN
   thread->_STACK_bound=(gcv_object_t *)low + 0x40;
   thread->_STACK=(gcv_object_t *)high;
  #endif
  #ifdef STACK_UP
   thread->_STACK_bound=(gcv_object_t *)high - 0x40;
   thread->_STACK=(gcv_object_t *)low;
  #endif
  thread->_STACK_start=thread->_STACK;
  return thread->_STACK;
}

/* locks the global thread array */
global void lock_threads() 
{
  begin_system_call(); /* ! blocking */
  xmutex_lock(&allthreads_lock);
  end_system_call();
}
/* unlocks global thread array */
global void unlock_threads() 
{
  begin_system_call();
  xmutex_unlock(&allthreads_lock);
  end_system_call();
}

/* register a clisp-thread_t in global thread array 
 thread - the newly allocated thread.
 The called party shoul hold the global thread lock */
global int register_thread(clisp_thread_t *thread)
{
  /* register lisp_thread to global thread list. */
  if (nthreads >= MAXNTHREADS) return -1;
  thread->_index=nthreads;
  allthreads[nthreads] = thread;
  nthreads++;
  return thread->_index;
}

/* creates new cisp_thread_t structure and allocates LISP stack.
 It is always called with the main thread mutex locked. 
 when the lisp_stack_size is 0 - it means this is the very first thread,
 so we may(should not) perform some initializations */
global clisp_thread_t* create_thread(uintM lisp_stack_size)
{
  var clisp_thread_t* thread;
  begin_system_call();
  thread=(clisp_thread_t *)malloc(sizeof(clisp_thread_t));
  end_system_call();
  if (!thread) return NULL;
  begin_system_call();
  memset(thread,0,sizeof(clisp_thread_t)); /* zero-up everything */
  /* init _symvalues "proxy" */
  thread->_ptr_symvalues = (gcv_object_t *)malloc(sizeof(gcv_object_t)*
						  maxnum_symvalues);
  if (!thread->_ptr_symvalues) {
    free(thread);
    end_system_call();
    return NULL;
  }
  end_system_call();
  {
    var gcv_object_t* objptr = thread->_ptr_symvalues;
    var uintC count;
    dotimespC(count,num_symvalues,{ *objptr++ = SYMVALUE_EMPTY; });
  }
  if (lisp_stack_size) {
    /* allocate the LISP stack */
    if (!allocate_lisp_thread_stack(thread,lisp_stack_size)) { 
      begin_system_call();
      free(thread->_ptr_symvalues);
      free(thread);
      end_system_call();
      return NULL;
    }
  }
  spinlock_init(&thread->_gc_suspend_request); spinlock_acquire(&thread->_gc_suspend_request);
  spinlock_init(&thread->_gc_suspend_ack); spinlock_acquire(&thread->_gc_suspend_ack);
  xmutex_init(&thread->_gc_suspend_lock);
  /* initialize the environment*/
  thread->_aktenv.var_env   = NIL;
  thread->_aktenv.fun_env   = NIL;
  thread->_aktenv.block_env = NIL;
  thread->_aktenv.go_env    = NIL;
  thread->_aktenv.decl_env  = O(top_decl_env);
  /* VTZ:TODO. get the right SP_bound (pthreads and win32 can provide it ??).
   in USE_CUSTOM_TLS we have the functions. */
#ifndef NO_SP_CHECK
  thread->_SP_bound=0;
#endif
  return thread;
}

  /* VTZ: Releases current_thread resources */
global void delete_thread (clisp_thread_t *thread, bool full) {
  /* first give up any locks that the thread holds. 
   if GC is suspending threads - we do not want to block it
   anyway we are going away.*/
  begin_system_call();
  xmutex_destroy(&thread->_gc_suspend_lock);
  end_system_call();
  spinlock_release(&thread->_gc_suspend_ack);
  lock_threads(); /* lock all threads */
  ASSERT(thread->_index < nthreads);
  ASSERT(allthreads[thread->_index] == thread); 
  allthreads[nthreads-1]->_index = thread->_index;;
  allthreads[thread->_index] = allthreads[nthreads-1];
  nthreads--;
  xmutex_destroy(&thread->_gc_suspend_lock);
  thread->_index=MAXNTHREADS+1; /* mark as exitted */
  /* VTZ: The LISP stack should be unwound so no
     interesting stuff on it. Let's deallocate it.*/
  begin_system_call();
  free(THREAD_LISP_STACK_START(thread));
  thread->_STACK=NULL; 
  /* VTZ: the clisp_thread_t itself will be deallocated during 
     finalization phase of GC - when the thread record is discarded.
     why? (somebody may want to inspect the mv_space for "thread return 
     value")*/
  if (full) {
    free(thread->_ptr_symvalues);
    free(thread);
  }
  end_system_call();
  unlock_threads();
}

  #define for_all_threads(statement)                             \
    do { var clisp_thread_t** _pthread = &allthreads[nthreads];  \
      while (_pthread != &allthreads[0])                         \
        { var clisp_thread_t* thread = *--_pthread; statement; } \
    } while(0)

/* reallocate _ptr_symvalues in such a way that there is a place for 
   nsyms per thread symbol values.*/
local bool realloc_thread_symvalues(clisp_thread_t *thr, uintL nsyms)
{
  if (nsyms <= maxnum_symvalues) /* we already have enough place */
    return true;
  gcv_object_t *p=(gcv_object_t *)realloc(thr->_ptr_symvalues,
					  nsyms*sizeof(gcv_object_t));
  if (p)
    thr->_ptr_symvalues=p;
  return p!=NULL;
}

/* Clears any per thread value for symbol. Also set tls_index
   of the symbol to invalid. */
global void clear_per_thread_symvalues(object symbol)
{
  var uintL idx=TheSymbol(symbol)->tls_index;
  if (idx != SYMBOL_TLS_INDEX_NONE) {
    TheSymbol(symbol)->tls_index = SYMBOL_TLS_INDEX_NONE;
    /* also remove all per thread symbols for the index - we do not want 
       any memory leaks. No locking duringthis operation the caller 
       is responsible for any race conditions. */
    for_all_threads({ thread->_ptr_symvalues[idx] = SYMVALUE_EMPTY; });
  }
}

  #define for_all_threadobjs(statement)  \
    for_all_threads({                                     \
      var gcv_object_t* objptr = (gcv_object_t*)(&thread->_aktenv); \
      var uintC count;                                     \
      dotimespC(count,sizeof(thread->_aktenv)/sizeof(gcv_object_t),     \
        { statement; objptr++; });                         \
      objptr=thread->_ptr_symvalues; \
      dotimespC(count,num_symvalues,     \
        { statement; objptr++; });                         \
    })

  #define for_all_STACKs(statement)  \
    for_all_threads({                                            \
      var gcv_object_t* objptr = STACKpointable(thread->_STACK); \
      { statement; }                                             \
    })

  #define for_all_back_traces(statement)   \
    for_all_threads({ var p_backtrace_t bt = thread->_back_trace; \
      { statement; }                                              \
    })

#endif

/* --------------------------------------------------------------------------
                           Page-Management */

#include "spvw_page.c"
#include "spvw_heap.c"
#include "spvw_global.c"

#ifdef SPVW_PAGES

/* A dummy-page for lastused: */
  local NODE dummy_NODE;
  #define dummy_lastused  (&dummy_NODE)

#endif

/* ------------------------------------------------------------------------ */

#if defined(NOCOST_SP_CHECK) && !defined(WIN32_NATIVE)
/* Check for near stack overflow. */
global bool near_SP_overflow (void) {
  /* Force a stack overflow if there is not a minimum of room available. */
  var uintB dummy[0x1001];
  dummy[0] = 0; dummy[0x800] = 0; dummy[0x1000] = 0;
 #ifdef GNU
  alloca(1);                    /* Makes this function non-inlinable. */
 #endif
  return false;
}
#endif

/* At overflow of one of the stacks: */
nonreturning_function(global, SP_ueber, (void)) {
  var bool interactive_p = interactive_stream_p(Symbol_value(S(debug_io)));
  begin_system_call();
  fputs("\n",stderr);
  fputs(GETTEXTL("*** - " "Program stack overflow. RESET"),stderr);
  fputs("\n",stderr);
  fflush(stderr);
  end_system_call();
  if (interactive_p)
    reset(1);
  else {
    /* non-interactive session: quit */
    final_exitcode = 1; quit();
  }
}
nonreturning_function(global, STACK_ueber, (void)) {
  var bool interactive_p = interactive_stream_p(Symbol_value(S(debug_io)));
  begin_system_call();
  fputs("\n",stderr);
  fputs(GETTEXTL("*** - " "Lisp stack overflow. RESET"),stderr);
  fputs("\n",stderr);
  fflush(stderr);
  end_system_call();
  if (interactive_p)
    reset(1);
  else {
    /* non-interactive session: quit */
    final_exitcode = 1; quit();
  }
}

/* -------------------------------------------------------------------------
                       GC-Statistics */

#include "spvw_gcstat.c"

/* --------------------------------------------------------------------------
                       Memory-Size */

#include "spvw_space.c"

/* --------------------------------------------------------------------------
                       Marks */

#include "spvw_mark.c"

/* --------------------------------------------------------------------------
                   object size determination */

#include "spvw_objsize.c"

/* --------------------------------------------------------------------------
                    Memory Update */

#include "spvw_update.c"

/* --------------------------------------------------------------------------
                      Page Fault and Protection Handling */

#if defined(GENERATIONAL_GC)

#include "spvw_fault.c"

#endif  /* GENERATIONAL_GC */

/* --------------------------------------------------------------------------
                      Signal handlers */

#include "spvw_sigsegv.c"
#include "spvw_sigcld.c"
#include "spvw_sigpipe.c"
#include "spvw_sigint.c"
#include "spvw_sigwinch.c"
#include "spvw_sigterm.c"

/* --------------------------------------------------------------------------
                       Garbage-Collector */

#include "spvw_garcol.c"

/* --------------------------------------------------------------------------
                 Memory Allocation Functions */

#include "spvw_allocate.c"
#include "spvw_typealloc.c"

/* --------------------------------------------------------------------------
                   Circularity Test */

#include "spvw_circ.c"

/* --------------------------------------------------------------------------
                     Memory Walk */

#include "spvw_walk.c"

/* --------------------------------------------------------------------------
                  Elementary String Functions */

#ifndef asciz_length
/* UP: Returns the length of an ASCIZ-string.
 asciz_length(asciz)
 > char* asciz: ASCIZ-string
       (address of a character sequence terminated by a nullbyte)
 < result: length of the character sequence (without nullbyte) */
global uintL asciz_length (const char * asciz) {
  var const char* ptr = asciz;
  var uintL len = 0;
  /* search nullbyte and increment length: */
  while (*ptr++ != 0) { len++; }
  return len;
}
#endif

/* UP: compares two ASCIZ-strings.
 asciz_equal(asciz1,asciz2)
 > char* asciz1: first ASCIZ-string
 > char* asciz2: second ASCIZ-string
 < result: true if both sequences are equal */
global bool asciz_equal (const char * asciz1, const char * asciz2) {
  /* compare bytes until the first nullbyte: */
  while (1) {
    var char ch1 = *asciz1++;
    if (ch1 != *asciz2++) goto no;
    if (ch1 == '\0') goto yes;
  }
 yes: return true;
 no: return false;
}

/* --------------------------------------------------------------------------
                  Other Global Helper Functions */

/* malloc() with error check. */
global void* clisp_malloc (size_t size)
{
  begin_system_call();
  var void* ptr = malloc(size);
  end_system_call();
  if (ptr)
    return ptr;
  pushSTACK(TheSubr(subr_self)->name);
  error(storage_condition,GETTEXT("~S: malloc() failed"));
}
/* realloc() with error check. */
global void* clisp_realloc (void* ptr, size_t size)
{
  begin_system_call();
  ptr = realloc(ptr,size);
  end_system_call();
  if (ptr)
    return ptr;
  pushSTACK(TheSubr(subr_self)->name);
  error(storage_condition,GETTEXT("~S: realloc() failed"));
}

#if (int_bitsize < long_bitsize)
/* passing value from longjmpl() to setjmpl()  : */
global long jmpl_value;
#endif

#ifdef NEED_OWN_GETSP
/* determine (an approximation) of the SP-stackpointer. */
global void* getSP (void) {
  var long dummy;
  return &dummy;
}
#endif

/* VTZ: moved SP_anchor to clisp_thread_t. in MT it is part of the thread 
 Seems it is used only for debugging/checking purposes. */
#if !defined(MULTITHREAD)
/* The initial value of SP() during main(). */
global void* SP_anchor; 
#endif

/* error-message when a location of the program is reached that is (should be)
 unreachable. Does not return.
 error_notreached(file,line);
 > file: filename (with quotation marks) as constant ASCIZ-string
 > line: line number */
nonreturning_function(global, error_notreached,
                      (const char* file, uintL line)) {
  end_system_call();            /* just in case */
  pushSTACK(fixnum(line));
  pushSTACK(ascii_to_string(file));
  error(serious_condition,
        GETTEXT("Internal error: statement in file ~S, line ~S has been reached!!\n"
                "Please see <http://clisp.cons.org/impnotes/faq.html#faq-bugs> for bug reporting instructions."));
}

#include "spvw_ctype.c"

#include "spvw_language.c"

/* --------------------------------------------------------------------------
                        Initialization */

/* name of the program (for error reporting) */
local const char* program_name;

/* flag, if SYS::READ-FORM should behave ILISP-compatible: */
global bool ilisp_mode = false;

local fsubr_argtype_t fsubr_argtype (uintW req_count, uintW opt_count,
                                     fsubr_body_t body_flag)
{ /* conversion of the argument types of a FSUBR into a code: */
  switch (body_flag) {
    case fsubr_nobody:
      switch (opt_count) {
        case 0:
          switch (req_count) {
            case 1: return(fsubr_argtype_1_0_nobody);
            case 2: return(fsubr_argtype_2_0_nobody);
            default: goto illegal;
          }
        case 1:
          switch (req_count) {
            case 1: return(fsubr_argtype_1_1_nobody);
            case 2: return(fsubr_argtype_2_1_nobody);
            default: goto illegal;
          }
        default: goto illegal;
      }
    case fsubr_body:
      switch (opt_count) {
        case 0:
          switch (req_count) {
            case 0: return(fsubr_argtype_0_body);
            case 1: return(fsubr_argtype_1_body);
            case 2: return(fsubr_argtype_2_body);
            default: goto illegal;
          }
        default: goto illegal;
      }
    default: goto illegal;
  }
 illegal:
  fprintf(stderr,GETTEXTL("Unknown FSUBR signature: %d %d %d\n"),
          req_count,opt_count,body_flag);
  quit_instantly(1);
}

local subr_argtype_t subr_argtype (uintW req_count, uintW opt_count,
                                   subr_rest_t rest_flag, subr_key_t key_flag,
                                   const subr_initdata_t *sid)
{ /* conversion of the argument types of a FSUBR into a code: */
  switch (key_flag) {
    case subr_nokey:
      switch (rest_flag) {
        case subr_norest:
          switch (opt_count) {
            case 0:
              switch (req_count) {
                case 0: return(subr_argtype_0_0);
                case 1: return(subr_argtype_1_0);
                case 2: return(subr_argtype_2_0);
                case 3: return(subr_argtype_3_0);
                case 4: return(subr_argtype_4_0);
                case 5: return(subr_argtype_5_0);
                case 6: return(subr_argtype_6_0);
                default: goto illegal;
              }
            case 1:
              switch (req_count) {
                case 0: return(subr_argtype_0_1);
                case 1: return(subr_argtype_1_1);
                case 2: return(subr_argtype_2_1);
                case 3: return(subr_argtype_3_1);
                case 4: return(subr_argtype_4_1);
                default: goto illegal;
              }
            case 2:
              switch (req_count) {
                case 0: return(subr_argtype_0_2);
                case 1: return(subr_argtype_1_2);
                case 2: return(subr_argtype_2_2);
                case 3: return(subr_argtype_3_2);
                default: goto illegal;
              }
            case 3:
              switch (req_count) {
                case 0: return(subr_argtype_0_3);
                case 1: return(subr_argtype_1_3);
                case 2: return(subr_argtype_2_3);
                default: goto illegal;
              }
            case 4:
              switch (req_count) {
                case 0: return(subr_argtype_0_4);
                default: goto illegal;
              }
            case 5:
              switch (req_count) {
                case 0: return(subr_argtype_0_5);
                default: goto illegal;
              }
            default: goto illegal;
          }
        case subr_rest:
          switch (opt_count) {
            case 0:
              switch (req_count) {
                case 0: return(subr_argtype_0_0_rest);
                case 1: return(subr_argtype_1_0_rest);
                case 2: return(subr_argtype_2_0_rest);
                case 3: return(subr_argtype_3_0_rest);
                default: goto illegal;
              }
            default: goto illegal;
          }
        default: goto illegal;
      }
    case subr_key:
      switch (rest_flag) {
        case subr_norest:
          switch (opt_count) {
            case 0:
              switch (req_count) {
                case 0: return(subr_argtype_0_0_key);
                case 1: return(subr_argtype_1_0_key);
                case 2: return(subr_argtype_2_0_key);
                case 3: return(subr_argtype_3_0_key);
                case 4: return(subr_argtype_4_0_key);
                default: goto illegal;
              }
            case 1:
              switch (req_count) {
                case 0: return(subr_argtype_0_1_key);
                case 1: return(subr_argtype_1_1_key);
                default: goto illegal;
              }
            case 2:
              switch (req_count) {
                case 1: return(subr_argtype_1_2_key);
                default: goto illegal;
              }
            default: goto illegal;
          }
        case subr_rest:
        default: goto illegal;
      }
    case subr_key_allow: goto illegal;
    default: goto illegal;
  }
 illegal:
  fprintf(stderr,GETTEXTL("Unknown SUBR signature: %d %d %d %d"),
          req_count,opt_count,rest_flag,key_flag);
  if (sid)
    fprintf(stderr," (%s::%s)\n",sid->packname,sid->symname);
  else fputs("\n",stderr);
  quit_instantly(1);
}
/* set the argtype of a subr_t *ptr */
#define SUBR_SET_ARGTYPE(ptr,sid)                                       \
  ptr->argtype = (uintW)subr_argtype(ptr->req_count,ptr->opt_count,     \
                                     (subr_rest_t)(ptr->rest_flag),     \
                                     (subr_key_t)(ptr->key_flag),sid)

local inline void module_set_argtypes (module_t *module)
{ /* set artype for all SUBRs in the module */
  var subr_t* stab_ptr = module->stab; /* traverse subr_tab */
  var const subr_initdata_t *stab_init_ptr = module->stab_initdata;
  var uintC count = *module->stab_size;
  do { SUBR_SET_ARGTYPE(stab_ptr,stab_init_ptr);
    stab_ptr++; stab_init_ptr++;
  } while (--count);
}

/* Verify that a code address has the C_CODE_ALIGNMENT.
 This is important for calling make_machine_code, but it's easiest verified
 on Fsubrs and Subrs. */
#ifdef TYPECODES
  #define verify_code_alignment(ptr,symbol) /* not needed */
#else
  #define verify_code_alignment(ptr,symbol)  \
    if ((uintP)(void*)(ptr) & (C_CODE_ALIGNMENT-1))     \
      error_code_alignment((uintP)(void*)(ptr),symbol)
nonreturning_function(local, error_code_alignment,
                      (uintP address, object symbol)) {
  fprintf(stderr,"C_CODE_ALIGNMENT is wrong. &%s = 0x%lx.\n",
          TheAsciz(string_to_asciz(Symbol_name(symbol),O(terminal_encoding))),
          address);
 #if (__GNUC__ >= 3)
  fprintf(stderr,"Add -falign-functions=%d to CFLAGS in the Makefile.\n",
          C_CODE_ALIGNMENT);
 #endif
  abort();
}
#endif

/* Initialization-routines for the tables
 during the first part of the initialization phase:
 initialize subr_tab: */
local void init_subr_tab_1 (void) {
 #if defined(HEAPCODES)
  /* lispbibl.d normally takes care of this, using a gcc __attribute__.
   But __attribute__((aligned(4))) is ignored for some GCC targets,
   so we check it here for safety. */
  if (alignof(subr_t) < 4) {
    fprintf(stderr,"Alignment of SUBRs is %d. HEAPCODES requires it to be at least 4.\nRecompile CLISP with -DHEAPCODES.\n",alignof(subr_t));
    abort();
  }
 #endif
 #if defined(INIT_SUBR_TAB)
  #ifdef MAP_MEMORY_TABLES
  /* copy table into the designated region: */
  subr_tab = subr_tab_data;
  #endif
  #if !NIL_IS_CONSTANT
  {                             /* initialize the name-slot first: */
    var subr_t* ptr = (subr_t*)((char*)&subr_tab+varobjects_misaligned); /* traverse subr_tab */
     #define LISPFUN  LISPFUN_E
       #include "subr.c"
     #undef LISPFUN
  }
  {       /* and initialize the GCself and keywords-slot temporarily: */
    var subr_t* ptr = (subr_t*)((char*)&subr_tab+varobjects_misaligned); /* traverse subr_tab */
    var uintC count = subr_count;
    while (count--) {
      ptr->GCself = subr_tab_ptr_as_object(ptr);
      ptr->keywords = NIL;
      ptr++;
    }
  }
  #endif
  /* Because of SPVWTABF all slots except keywords and argtype
   are already initialized. */
  {                          /* now initialize the argtype-slot: */
    var subr_t* ptr = (subr_t*)((char*)&subr_tab+varobjects_misaligned); /* traverse subr_tab */
    var uintC count = subr_count;
    while (count--) { SUBR_SET_ARGTYPE(ptr,NULL); ptr++; }
  }
 #else
  {                          /* initialize all slots except keywords: */
    var subr_t* ptr = (subr_t*)((char*)&subr_tab+varobjects_misaligned); /* traverse subr_tab */
    #define LISPFUN  LISPFUN_D
      #include "subr.c"
    #undef LISPFUN
  }
 #endif
  {
    var module_t* module;
    for_modules(all_other_modules,{
      if (*module->stab_size > 0) module_set_argtypes(module);
    });
  }
 #ifdef MAP_MEMORY_TABLES
  {               /* ditto, copy other tables tino the mapped region: */
    var subr_t* newptr = (subr_t*)((char*)&subr_tab+varobjects_misaligned);
    var module_t* module;
    main_module.stab = newptr; newptr += subr_count;
    for_modules(all_other_modules,{
      if (*module->stab_size > 0) {
        var subr_t* oldptr = module->stab;
        var uintC count = *module->stab_size;
        module->stab = newptr;
        do { *newptr++ = *oldptr++; } while (--count);
      }
    });
    ASSERT(newptr == (subr_t*)((char*)&subr_tab+varobjects_misaligned) + total_subr_count);
  }
 #endif
}
/* initialize symbol_tab: */
local void init_symbol_tab_1 (void) {
 #if defined(INIT_SYMBOL_TAB) && NIL_IS_CONSTANT
  #ifdef MAP_MEMORY_TABLES
  /* copy table into the designated region: */
  symbol_tab = symbol_tab_data;
  #endif
 #else
  {                             /* traverse symbol_tab */
    var symbol_* ptr = (symbol_*)((char*)&symbol_tab+varobjects_misaligned);
    var uintC count;
    for (count = symbol_count; count > 0; count--) {
      ptr->GCself = symbol_tab_ptr_as_object(ptr);
     #ifndef TYPECODES
      ptr->tfl = xrecord_tfl(Rectype_Symbol,0,5,0);
     #endif
      ptr->symvalue = unbound;
      ptr->symfunction = unbound;
      ptr->hashcode = unbound;
      ptr->proplist = NIL;
      ptr->pname = NIL;
      ptr->homepackage = NIL;
      ptr++;
    }
  }
 #endif
}
/* initialize object_tab: */
local void init_object_tab_1 (void) {
  var module_t* module;
 #if defined(INIT_OBJECT_TAB) && NIL_IS_CONSTANT /* object_tab already pre-initialized? */
  for_modules(all_other_modules,{
    if (*module->otab_size > 0) {
      var gcv_object_t* ptr = module->otab; /* traverse object_tab */
      var uintC count;
      dotimespC(count,*module->otab_size, { *ptr++ = NIL; });
    }
  });
 #else
  for_modules(all_modules,{
    if (*module->otab_size > 0) {
      var gcv_object_t* ptr = module->otab; /* traverse object_tab */
      var uintC count;
      dotimespC(count,*module->otab_size, { *ptr++ = NIL; });
    }
  });
 #endif
  O(all_weakpointers) = Fixnum_0;
  O(all_finalizers) = Fixnum_0; O(pending_finalizers) = Fixnum_0;
}
/* initialize other modules coarsely: */
local void init_other_modules_1 (void) {
  var module_t* module;
  for_modules(all_other_modules, {
    /* fill pointer in the subr-table with NIL, for GC to become possible: */
    if (*module->stab_size > 0) {
      var subr_t* ptr = module->stab;
      var uintC count;
      dotimespC(count,*module->stab_size, {
        ptr->GCself = subr_tab_ptr_as_object(ptr);
        ptr->name = NIL; ptr->keywords = NIL;
        ptr++;
      });
    }
    /* the pointers in the object-table have already been inizialized
     by init_object_tab_1(). */
  });
}

/* Initialization-routines for the tables
 during the second part of the initialization phase:
 finish initialization of subr_tab: enter keyword-vectors. */
local void init_subr_tab_2 (void) {
#if 0
  /* I would love to have a simple solution here, but
   TURBO-C doesn't get enough memory for compilation!
   traverse subr_tab */
  var object vec;
  var gcv_object_t* vecptr;
 #define LISPFUN  LISPFUN_H
  #define kw(name)  *vecptr++ = S(K##name)
  #include "subr.c"
  #undef LISPFUN
 #undef kw
#else
  /* create keyword-vectors individually: */
  var object vec;
  var gcv_object_t* vecptr;
  /* fills another single keyword into the vector: */
  #define kw(name)  *vecptr++ = S(K##name)
  /* creates vector with given keywords: */
  #define v(key_count,keywords)                 \
     vec = allocate_vector(key_count);          \
     vecptr = &TheSvector(vec)->data[0];        \
     keywords;
  /* sets the vector as keyword-vector for SUBR name: */
  #define s(name)  subr_tab.D_##name.keywords = vec;
  #include "subrkw.c"
  #undef s
  #undef v
  #undef kw
#endif
}
/* finish initialization of symbol_tab: enter printnames and home-package. */
local void init_symbol_tab_2 (void) {
  /* table of printnames: */
  local const char * const pname_table[symbol_count] = {
    #define LISPSYM  LISPSYM_C
    #include "constsym.c"
    #undef LISPSYM
  };
  /* table of packages: */
  enum {                     /* the values in this enum are 0,1,2,... */
    enum_lisp_index,
    enum_user_index,
    enum_system_index,
    enum_keyword_index,
    enum_charset_index,
    enum_cs_lisp_index,
    enum_cs_user_index,
    #define LISPPACK  LISPPACK_A
    #include "constpack.c"
    #undef LISPPACK
    enum_dummy_index
  };
  #define package_count  ((uintL)enum_dummy_index)
  local const uintB package_index_table[symbol_count] = {
    #define LISPSYM  LISPSYM_D
    #include "constsym.c"
    #undef LISPSYM
  };
  {
    var object list = O(all_packages); /* list of packages */
    /* shortly after the initialization:
     (#<PACKAGE LISP> #<PACKAGE SYSTEM> #<PACKAGE KEYWORD> #<PACKAGE CHARSET> ...) */
    var uintC count = package_count;
    do { pushSTACK(Car(list)); list = Cdr(list); } while (--count);
  }
  {                             /* traverse symbol_tab */
    var symbol_* ptr = (symbol_*)((char*)&symbol_tab+varobjects_misaligned);
    var const char * const * pname_ptr = &pname_table[0]; /* traverse pname_table */
    var const uintB* index_ptr = &package_index_table[0]; /* traverse package_index_table */
    var uintC count = symbol_count;
    do {
      ptr->pname =
        coerce_imm_ss(' ' == **pname_ptr              /* non-ASCII */
                      ? asciz_to_string(*pname_ptr+1, /* skip ' ' */
                                        Symbol_value(S(utf_8)))
                      : ascii_to_string(*pname_ptr));
      pname_ptr++;
      var uintB this_index = *index_ptr++;
      var gcv_object_t* package_ = /* pointer to the package */
        &STACK_(package_count-1) STACKop -(uintP)this_index;
      pushSTACK(symbol_tab_ptr_as_object(ptr)); /* Symbol */
      import(&STACK_0,package_);                /* import normally */
      switch (this_index) {
        case enum_lisp_index:    /* in #<PACKAGE COMMON-LISP>? */
        case enum_charset_index: /* in #<PACKAGE CHARSET>? */
        case enum_cs_lisp_index: /* in #<PACKAGE CS-COMMON-LISP>? */
        case enum_socket_index:
        case enum_custom_index:
          export(&STACK_0,package_); /* also export */
      }
      Symbol_package(popSTACK()) = *package_; /* set the home-package */
      ptr++;
    } while (--count != 0);
    skipSTACK(package_count);
  }
}
/* enter FSUBRs/SUBRs into their symbols: */
local void init_symbol_functions (void) {
  {                             /* enter FSUBRs: */
    typedef struct {
      #if defined(INIT_SUBR_TAB) && NIL_IS_CONSTANT
        #define LISPSPECFORM LISPSPECFORM_F
        gcv_object_t name;
        #define fsubr_name(p)  (p)->name
      #else
        #define LISPSPECFORM LISPSPECFORM_E
        uintL name_offset;
        #define fsubr_name(p)  symbol_tab_ptr_as_object((char*)&symbol_tab+(p)->name_offset)
      #endif
      uintW req_count;
      uintW opt_count;
      uintW body_flag;
    } fsubr_data_t;
    local const fsubr_data_t fsubr_data_tab[] = {
      #include "fsubr.c"
    };
    #undef LISPSPECFORM
    var const fsubr_t* ptr1 = (const fsubr_t *)&fsubr_tab; /* traverse fsubr_tab */
    var const fsubr_data_t * ptr2 = &fsubr_data_tab[0]; /* traverse fsubr_data_tab */
    var uintC count = fsubr_count;
    while (count--) {
      var object sym = fsubr_name(ptr2);
      var object obj = allocate_fsubr();
      TheFsubr(obj)->name = sym;
      TheFsubr(obj)->argtype =
        fixnum((uintW)fsubr_argtype(ptr2->req_count,ptr2->opt_count,
                                    (fsubr_body_t)(ptr2->body_flag)));
      TheFsubr(obj)->function = (void*)(*ptr1);
      Symbol_function(sym) = obj;
      verify_code_alignment(*ptr1,sym);
      ptr1++; ptr2++;
    }
  }
  {                             /* enter SUBRs: */
    var subr_t* ptr = (subr_t*)((char*)&subr_tab+varobjects_misaligned); /* traverse subr_tab */
    var uintC count = subr_count;
    while (count--) {
      Symbol_function(ptr->name) = subr_tab_ptr_as_object(ptr);
      verify_code_alignment(ptr->function,ptr->name);
      ptr++;
    }
  }
}
/* assign values to constants/variables: */
local void init_symbol_values (void) {
  /* helper macro: constant := value+1 */
  #define define_constant_UL1(symbol,value)                    \
    do { var object x =            /* value+1 as integer */    \
           (((uintV)(value) < (uintV)(vbitm(oint_data_len)-1)) \
            ? fixnum(value+1)                                  \
            : I_1_plus_I(UV_to_I(value))                       \
           );                                                  \
          define_constant(symbol,x);                           \
    } while(0)
  /* common: */
  define_constant(S(nil),S(nil)); /* NIL := NIL */
  define_constant(S(t),S(t));     /* T := T */
  define_variable(S(gc_statistics_star),Fixnum_minus1); /* SYS::*GC-STATISTICS* := -1 */
  /* for EVAL/CONTROL: */
  define_constant_UL1(S(lambda_parameters_limit),lp_limit_1); /* LAMBDA-PARAMETERS-LIMIT := lp_limit_1 + 1 */
  define_constant_UL1(S(call_arguments_limit),ca_limit_1); /* CALL-ARGUMENTS-LIMIT := ca_limit_1 + 1 */
  define_constant(S(multiple_values_limit),fixnum(mv_limit)); /* MULTIPLE-VALUES-LIMIT := mv_limit */
  define_constant(S(jmpbuf_size),fixnum(jmpbufsize)); /* SYS::*JMPBUF-SIZE* := size of a jmp_buf */
  define_constant(S(big_endian),(BIG_ENDIAN_P ? T : NIL)); /* SYS::*BIG-ENDIAN* := NIL resp. T */
  define_variable(S(macroexpand_hook),L(funcall)); /* *MACROEXPAND-HOOK* := #'FUNCALL */
  define_variable(S(evalhookstar),NIL);            /* *EVALHOOK* */
  define_variable(S(applyhookstar),NIL);           /* *APPLYHOOK* */
  /* for HASHTABL: */
  define_variable(S(eq_hashfunction),S(fasthash_eq)); /* EXT:*EQ-HASHFUNCTION* := 'EXT:FASTHASH-EQ */
  define_variable(S(eql_hashfunction),S(fasthash_eql)); /* EXT:*EQL-HASHFUNCTION* := 'EXT:FASTHASH-EQL */
  define_variable(S(equal_hashfunction),S(fasthash_equal)); /* EXT:*EQUAL-HASHFUNCTION* := 'EXT:FASTHASH-EQUAL */
  define_variable(S(warn_on_hashtable_needing_rehash_after_gc),NIL); /* CUSTOM:*WARN-ON-HASHTABLE-NEEDING-REHASH-AFTER-GC* := NIL */
  /* for PACKAGE: */
  define_variable(S(packagestar),Car(O(all_packages))); /* *PACKAGE* := '#<PACKAGE LISP> */
  /* for SYMBOL: */
  define_variable(S(gensym_counter),Fixnum_1); /* *GENSYM-COUNTER* := 1 */
  /* for PATHNAME: */
  define_variable(S(merge_pathnames_ansi),NIL); /* *MERGE-PATHNAMES-ANSI* */
  /* for LISPARIT: */
  init_arith();     /* defines the following: */
  /* define_variable(S(pi),);                      - PI
   define_constant(S(most_positive_fixnum),);    - MOST-POSITIVE-FIXNUM
   define_constant(S(most_negative_fixnum),);    - MOST-NEGATIVE-FIXNUM
   define_constant(S(most_positive_short_float),); - MOST-POSITIVE-SHORT-FLOAT
   define_constant(S(least_positive_short_float),); - LEAST-POSITIVE-SHORT-FLOAT
   define_constant(S(least_negative_short_float),); - LEAST-NEGATIVE-SHORT-FLOAT
   define_constant(S(most_negative_short_float),); - MOST-NEGATIVE-SHORT-FLOAT
   define_constant(S(most_positive_single_float),); - MOST-POSITIVE-SINGLE-FLOAT
   define_constant(S(least_positive_single_float),); - LEAST-POSITIVE-SINGLE-FLOAT
   define_constant(S(least_negative_single_float),); - LEAST-NEGATIVE-SINGLE-FLOAT
   define_constant(S(most_negative_single_float),); - MOST-NEGATIVE-SINGLE-FLOAT
   define_constant(S(most_positive_double_float),); - MOST-POSITIVE-DOUBLE-FLOAT
   define_constant(S(least_positive_double_float),); - LEAST-POSITIVE-DOUBLE-FLOAT
   define_constant(S(least_negative_double_float),); - LEAST-NEGATIVE-DOUBLE-FLOAT
   define_constant(S(most_negative_double_float),); - MOST-NEGATIVE-DOUBLE-FLOAT
   define_variable(S(most_positive_long_float),); - MOST-POSITIVE-LONG-FLOAT
   define_variable(S(least_positive_long_float),); - LEAST-POSITIVE-LONG-FLOAT
   define_variable(S(least_negative_long_float),); - LEAST-NEGATIVE-LONG-FLOAT
   define_variable(S(most_negative_long_float),); - MOST-NEGATIVE-LONG-FLOAT
   define_variable(S(least_positive_normalized_long_float),); - LEAST-POSITIVE-NORMALIZED-LONG-FLOAT
   define_variable(S(least_negative_normalized_long_float),); - LEAST-NEGATIVE-NORMALIZED-LONG-FLOAT
   define_constant(S(short_float_epsilon),);     - SHORT-FLOAT-EPSILON
   define_constant(S(single_float_epsilon),);    - SINGLE-FLOAT-EPSILON
   define_constant(S(double_float_epsilon),);    - DOUBLE-FLOAT-EPSILON
   define_variable(S(long_float_epsilon),);      - LONG-FLOAT-EPSILON
   define_constant(S(short_float_negative_epsilon),); - SHORT-FLOAT-NEGATIVE-EPSILON
   define_constant(S(single_float_negative_epsilon),); - SINGLE-FLOAT-NEGATIVE-EPSILON
   define_constant(S(double_float_negative_epsilon),); - DOUBLE-FLOAT-NEGATIVE-EPSILON
   define_variable(S(long_float_negative_epsilon),); - LONG-FLOAT-NEGATIVE-EPSILON
   define_variable(S(read_default_float_format),); - *READ-DEFAULT-FLOAT-FORMAT*
   define_variable(S(random_state),);            - *RANDOM-STATE*
   for ARRAY: */
  define_constant(S(array_total_size_limit),fixnum(arraysize_limit_1+1)); /* ARRAY-TOTAL-SIZE-LIMIT := arraysize_limit_1 + 1 */
  define_constant(S(array_dimension_limit),fixnum(arraysize_limit_1+1)); /* ARRAY-DIMENSION-LIMIT := arraysize_limit_1 + 1 */
  define_constant_UL1(S(string_dimension_limit),stringsize_limit_1); /* SYSTEM::STRING-DIMENSION-LIMIT := stringsize_limit_1 + 1 */
  define_constant(S(array_rank_limit),fixnum(arrayrank_limit_1+1)); /* ARRAY-RANK-LIMIT := arrayrank_limit_1 + 1 */
  /* for CHARSTRG: */
  define_constant(S(char_cod_limit),fixnum(char_code_limit)); /* CHAR-CODE-LIMIT */
  define_constant(S(base_char_cod_limit),fixnum(base_char_code_limit)); /* BASE-CHAR-CODE-LIMIT */
  define_variable(S(coerce_fixnum_char_ansi),NIL); /* LISP:*COERCE-FIXNUM-CHAR-ANSI* */
  /* for SEQUENCE: */
  define_variable(S(sequence_count_ansi),NIL); /* LISP:*SEQUENCE-COUNT-ANSI* */
  /* for DEBUG: */
  define_variable(S(plus),NIL);             /* + */
  define_variable(S(plus2),NIL);            /* ++ */
  define_variable(S(plus3),NIL);            /* +++ */
  define_variable(S(minus),NIL);            /* - */
  define_variable(S(star),NIL);             /* * */
  define_variable(S(star2),NIL);            /* ** */
  define_variable(S(star3),NIL);            /* *** */
  define_variable(S(slash),NIL);            /* / */
  define_variable(S(slash2),NIL);           /* // */
  define_variable(S(slash3),NIL);           /* /// */
  define_variable(S(driverstar),NIL);       /* *DRIVER* := NIL */
  define_variable(S(break_driver),NIL);     /* *BREAK-DRIVER* := NIL */
  define_variable(S(break_count),Fixnum_0); /* SYS::*BREAK-COUNT* := 0 */
  define_variable(S(recurse_count_standard_output),Fixnum_0); /* SYS::*RECURSE-COUNT-STANDARD-OUTPUT* := 0 */
  define_variable(S(recurse_count_debug_io),Fixnum_0); /* SYS::*RECURSE-COUNT-DEBUG-IO* := 0 */
  /* for STREAM:
   later: init_streamvars(); - defines the following:
   define_variable(S(standard_input),);          - *STANDARD-INPUT*
   define_variable(S(standard_output),);         - *STANDARD-OUTPUT*
   define_variable(S(error_output),);            - *ERROR-OUTPUT*
   define_variable(S(query_io),);                - *QUERY-IO*
   define_variable(S(debug_io),);                - *DEBUG-IO*
   define_variable(S(terminal_io),);             - *TERMINAL-IO*
   define_variable(S(trace_output),);            - *TRACE-OUTPUT*
   define_variable(S(keyboard_input),);          - *KEYBOARD-INPUT* */
  define_variable(S(default_pathname_defaults),unbound); /* *DEFAULT-PATHNAME-DEFAULTS* */
  /* for IO: */
  init_reader();                /* defines the following:
   define_variable(S(read_base),);               - *READ-BASE* := 10
   define_variable(S(read_suppress),);           - *READ-SUPPRESS* := NIL
   define_variable(S(read_eval),);               - *READ-EVAL* := T
   define_variable(S(readtablestar),);           - *READTABLE* */
  define_variable(S(read_preserve_whitespace),unbound); /* SYS::*READ-PRESERVE-WHITESPACE* */
  define_variable(S(read_recursive_p),unbound); /* SYS::*READ-RECURSIVE-P* */
  define_variable(S(read_reference_table),unbound); /* SYS::*READ-REFERENCE-TABLE* */
  define_variable(S(backquote_level),unbound); /* SYS::*BACKQUOTE-LEVEL* */
  define_variable(S(compiling),NIL); /* SYS::*COMPILING* ;= NIL */
  define_variable(S(print_case),S(Kupcase)); /* *PRINT-CASE* := :UPCASE */
  define_variable(S(print_level),NIL);       /* *PRINT-LEVEL* := NIL */
  define_variable(S(print_length),NIL);      /* *PRINT-LENGTH* := NIL */
  define_variable(S(print_gensym),T);        /* *PRINT-GENSYM* := T */
  define_variable(S(print_escape),T);        /* *PRINT-ESCAPE* := T */
  define_variable(S(print_radix),NIL);       /* *PRINT-RADIX* := NIL */
  define_variable(S(print_base),fixnum(10)); /* *PRINT-BASE* := 10 */
  define_variable(S(print_array),T);         /* *PRINT-ARRAY* := T */
  define_variable(S(print_circle),NIL);      /* *PRINT-CIRCLE* := NIL */
  define_variable(S(print_pretty),NIL);      /* *PRINT-PRETTY* := NIL */
  define_variable(S(print_closure),NIL);  /* *PRINT-CLOSURE* := NIL */
  define_variable(S(print_readably),NIL); /* *PRINT-READABLY* := NIL */
  define_variable(S(print_lines),NIL);    /* *PRINT-LINES* := NIL */
  define_variable(S(print_miser_width),NIL); /* *PRINT-MISER-WIDTH* := NIL */
  define_variable(S(prin_line_prefix),unbound); /* *PRIN-LINE-PREFIX* */
  define_variable(S(prin_miserp),unbound);      /* *PRIN-MISERP* */
  define_variable(S(prin_pprinter),unbound);    /* *PRIN-PPRINTER* */
  define_variable(S(prin_indentation),unbound); /* *PRIN-INDENTATION* */
  define_variable(S(print_pprint_dispatch),NIL); /* *PRINT-PPRINT-DISPATCH* := NIL */
  define_variable(S(print_right_margin),NIL); /* *PRINT-RIGHT-MARGIN* := NIL */
  define_variable(S(print_rpars),NIL);        /* *PRINT-RPARS* := NIL */
  define_variable(S(print_indent_lists),fixnum(1)); /* *PRINT-INDENT-LISTS* := 1 */
  define_variable(S(print_pretty_fill),NIL); /* *PRINT-PRETTY-FILL* := NIL */
  define_variable(S(print_circle_table),unbound); /* SYS::*PRINT-CIRCLE-TABLE* */
  define_variable(S(print_symbol_package_prefix_shortest),NIL); /* CUSTOM:*PRINT-SYMBOL-PACKAGE-PREFIX-SHORTEST* */
  define_variable(S(prin_level),unbound);  /* SYS::*PRIN-LEVEL* */
  define_variable(S(prin_lines),unbound);  /* SYS::*PRIN-LINES* */
  define_variable(S(prin_stream),unbound); /* SYS::*PRIN-STREAM* */
  define_variable(S(prin_linelength),fixnum(79)); /* SYS::*PRIN-LINELENGTH* := 79 (preliminarily) */
  define_variable(S(prin_l1),unbound);            /* SYS::*PRIN-L1* */
  define_variable(S(prin_lm),unbound);            /* SYS::*PRIN-LM* */
  define_variable(S(prin_rpar),unbound);          /* SYS::*PRIN-RPAR* */
  define_variable(S(prin_traillength),unbound); /* SYS::*PRIN-TRAILLENGTH* */
  define_variable(S(prin_prev_traillength),unbound); /* SYS::*PRIN-PREV-TRAILLENGTH* */
  define_variable(S(prin_jblocks),unbound);   /* SYS::*PRIN-JBLOCKS* */
  define_variable(S(prin_jbstrings),unbound); /* SYS::*PRIN-JBSTRINGS* */
  define_variable(S(prin_jbmodus),unbound);   /* SYS::*PRIN-JBMODUS* */
  define_variable(S(prin_jblpos),unbound);    /* SYS::*PRIN-JBLPOS* */
  define_variable(S(load_forms),NIL); /* SYS::*LOAD-FORMS* */
  define_variable(S(terminal_read_open_object),unbound); /* SYS::*TERMINAL-READ-OPEN-OBJECT* */
  define_variable(S(terminal_read_stream),unbound); /* SYS::*TERMINAL-READ-STREAM* */
  define_variable(S(pprint_first_newline),T); /* CUSTOM:*PPRINT-FIRST-NEWLINE* */
  define_variable(S(print_pathnames_ansi),NIL); /* CUSTOM:*PRINT-PATHNAMES-ANSI* */
  define_variable(S(print_space_char_ansi),NIL); /* CUSTOM:*PRINT-SPACE-CHAR-ANSI* */
  define_variable(S(print_empty_arrays_ansi),NIL); /* CUSTOM:*PRINT-EMPTY-ARRAYS-ANSI* */
  define_variable(S(print_unreadable_ansi),NIL); /* CUSTOM:*PRINT-UNREADABLE-ANSI* */
  define_variable(S(parse_namestring_ansi),NIL); /* CUSTOM:*PARSE-NAMESTRING-ANSI* */
  define_variable(S(reopen_open_file),S(error)); /* CUSTOM:*REOPEN-OPEN-FILE* */
 #ifdef PATHNAME_NOEXT
  define_variable(S(parse_namestring_dot_file),S(Ktype)); /* CUSTOM:*PARSE-NAMESTRING-DOT-FILE* */
 #endif
  define_variable(S(deftype_depth_limit),NIL); /* CUSTOM:*DEFTYPE-DEPTH-LIMIT* */
 #if defined(WIN32_NATIVE) || defined(UNIX_CYGWIN32)
  define_variable(S(device_prefix),NIL); /* CUSTOM:*DEVICE-PREFIX* */
 #endif
  /* for EVAL: */
  define_variable(S(evalhookstar),NIL);  /* *EVALHOOK* := NIL */
  define_variable(S(applyhookstar),NIL); /* *APPLYHOOK* := NIL */
  /* for MISC: */
  define_constant(S(internal_time_units_per_second), /* INTERNAL-TIME-UNITS-PER-SECOND */
                  fixnum(ticks_per_second) ); /* := 200 resp. 1000000 */
  /* for PREDTYPE: */
  define_variable(S(recurse_count_gc_statistics),Fixnum_0); /* SYS::*RECURSE-COUNT-GC-STATISTICS* := 0 */
  /* for ERROR: */
  define_variable(S(use_clcs),NIL); /* SYS::*USE-CLCS* := NIL */
  define_variable(S(recursive_error_count),Fixnum_0); /* SYS::*RECURSIVE-ERROR-COUNT* := 0 */
  define_variable(S(error_handler),NIL);  /* *ERROR-HANDLER* := NIL */
  /* for SPVW: */
  define_variable(S(init_hooks),NIL); /* CUSTOM::*INIT-HOOKS* := NIL */
  define_variable(S(fini_hooks),NIL); /* CUSTOM::*FINI-HOOKS* := NIL */
  define_variable(S(quiet),NIL);      /* SYS::*QUIET* := NIL */
  define_variable(S(norc),NIL);       /* SYS::*NORC* := NIL */
  define_variable(S(script),T);       /* SYS::*SCRIPT* := T */
  define_variable(S(image_doc),NIL);  /* SYS::*IMAGE-DOC* := NIL */
  define_variable(S(args),NIL);       /* EXT:*ARGS* := NIL */
  define_variable(S(load_compiling),NIL); /* *LOAD-COMPILING* := NIL */
  define_variable(S(load_verbose),T); /* *LOAD-VERBOSE* := T */
  define_variable(S(load_print),NIL); /* *LOAD-PRINT* := NIL */
  define_variable(S(load_echo),NIL); /* *LOAD-ECHO* := NIL */
  define_variable(S(load_paths),NIL); /* *LOAD-PATHS* := NIL */
  define_variable(S(compile_print),NIL); /* *COMPILE-PRINT* := NIL */
  define_variable(S(compile_verbose),T); /* *COMPILE-VERBOSE* := T */
  define_variable(S(saveinitmem_verbose),T); /* *SAVEINITMEM-VERBOSE* := T */
  define_variable(S(report_error_print_backtrace),NIL); /* *REPORT-ERROR-PRINT-BACKTRACE* := NIL */
  define_variable(S(loop_ansi),NIL); /* CUSTOM:*LOOP-ANSI* := NIL */
  define_variable(S(defun_accept_specialized_lambda_list),NIL); /* CUSTOM:*DEFUN-ACCEPT-SPECIALIZED-LAMBDA-LIST* := NIL */
  /* for FOREIGN: */
 #ifdef DYNAMIC_FFI
  define_constant(S(fv_flag_readonly),fixnum(fv_readonly)); /* FFI::FV-FLAG-READONLY */
  define_constant(S(fv_flag_malloc_free),fixnum(fv_malloc)); /* FFI::FV-FLAG-MALLOC-FREE */
  define_constant(S(ff_flag_alloca),fixnum(ff_alloca)); /* FFI::FF-FLAG-ALLOCA */
  define_constant(S(ff_flag_malloc_free),fixnum(ff_malloc)); /* FFI::FF-FLAG-MALLOC-FREE */
  define_constant(S(ff_flag_out),fixnum(ff_out)); /* FFI::FF-FLAG-OUT */
  define_constant(S(ff_flag_in_out),fixnum(ff_inout)); /* FFI::FF-FLAG-IN-OUT */
  define_constant(S(ff_language_asm),fixnum(ff_lang_asm)); /* FFI::FF-LANGUAGE-ASM */
  define_constant(S(ff_language_c),fixnum(ff_lang_c)); /* FFI::FF-LANGUAGE-C */
  define_constant(S(ff_language_ansi_c),fixnum(ff_lang_ansi_c)); /* FFI::FF-LANGUAGE-ANSI-C */
  define_constant(S(ff_language_stdcall),fixnum(ff_lang_stdcall)); /* FFI::FF-LANGUAGE-STDCALL */
 #endif
  /* for DISASSEM.LISP: */
 #ifdef UNIX
  /* SYS::*DISASSEMBLE-USE-LIVE-PROCESS* is system dependent:
   We use it where possible, because it allows peeking into dynamically
   loaded shared libraries.
   On FreeBSD 4.0, if set to T, gdb stops the clisp process.
   On Linux ppc64 (sf cf openpower-linux1), if set to T, clisp hangs until C-c.
   On Woe32, the debugging APIs are flawed, the Cygwin developers say. */
  #if defined(UNIX_FREEBSD) || defined(UNIX_CYGWIN32) || (defined(UNIX_LINUX) && defined(POWERPC))
  define_variable(S(disassemble_use_live_process),NIL);
  #else
  define_variable(S(disassemble_use_live_process),T);
  #endif
 #endif
  /* for PATHNAME: */
 #ifdef LOGICAL_PATHNAMES
  { /* SYS::*LOGICAL-PATHNAME-TRANSLATIONS* :=
      (MAKE-HASH-TABLE :KEY-TYPE 'STRING :VALUE-TYPE 'LIST :TEST #'EQUALP) */
    pushSTACK(S(Ktest)); pushSTACK(L(equalp)); funcall(L(make_hash_table),2);
    define_variable(S(logpathname_translations),value1);
  }
  O(empty_logical_pathname) = allocate_logpathname();
 #endif
  /* initialize *DEFAULT-PATHNAME-DEFAULTS* preliminarily: */
  define_variable(S(default_pathname_defaults),allocate_pathname());
 #undef define_constant_UL1
}
/* create other objects and fill object table: */
local void init_object_tab (void) {
  /* table with initialization strings: */
  local var const char * const object_initstring_tab [] = {
    #define LISPOBJ LISPOBJ_C
    #include "constobj.c"
    #undef LISPOBJ
  };
  {                             /* initialize *FEATURES* : */
    var const char * features_initstring =
      "(:CLISP :ANSI-CL :COMMON-LISP :LISP=CL :INTERPRETER"
     #ifdef DEBUG_COMPILER
      " :CLISP-DEBUG"
     #endif
     #ifdef MULTITHREAD
      " :MT"
     #endif
     #ifdef SOCKET_STREAMS
      " :SOCKETS"
     #endif
     #ifdef GENERIC_STREAMS
      " :GENERIC-STREAMS"
     #endif
     #ifdef LOGICAL_PATHNAMES
      " :LOGICAL-PATHNAMES"
     #endif
     #ifdef SCREEN
      " :SCREEN"
     #endif
     #ifdef DYNAMIC_FFI
      " :FFI"
     #endif
     #ifdef GNU_GETTEXT
      " :GETTEXT"
     #endif
     #ifdef UNICODE
      " :UNICODE"
     #endif
     #if (base_char_code_limit == char_code_limit)
      " :BASE-CHAR=CHARACTER"
     #endif
     #ifdef WIDE_HARD
      " :WORD-SIZE=64"
     #endif
     #ifdef PC386
      " :PC386"
     #endif
     #ifdef UNIX
      " :UNIX"
     #endif
     #ifdef UNIX_MACOSX
      " :MACOS"
     #endif
     #ifdef UNIX_CYGWIN32
      " :CYGWIN"
     #endif
     #ifdef UNIX_BEOS
      " :BEOS"
     #endif
     #ifdef WIN32
      " :WIN32"
     #endif
      ")";
    pushSTACK(ascii_to_string(features_initstring));
    var object list = (funcall(L(read_from_string),1), value1);
    define_variable(S(features),list); /* *FEATURES* */
  }
  {                             /* read objects from the strings: */
    var gcv_object_t* objptr = (gcv_object_t*)&object_tab; /* traverse object_tab */
    var const char * const * stringptr = &object_initstring_tab[0]; /* traverse string table */
    var uintC count = object_count;
    while (count--) {
      var const char * string = *stringptr++;
      if (*string == '@') {
        /* no READ-FROM-STRING for LISPOBJ_L && GNU_GETTEXT */
        *objptr = asciz_to_string(&string[1],O(internal_encoding));
      } else if (!(string[0] == '.' && string[1] == 0)) {
        pushSTACK(asciz_to_string(string,O(internal_encoding))); /* string */
        funcall(L(make_string_input_stream),1); /* pack into stream */
        pushSTACK(value1);
        var object obj = stream_read(&STACK_0,NIL,NIL); /* read object */
        skipSTACK(1);
        *objptr = obj; /* store (except ".") */
      }
      objptr++;
    }
  }
  /* initialize software_type */
  O(software_type) = built_flags();
  /* build toplevel-declaration-environment */
  Car(O(top_decl_env)) = O(declaration_types);
  /* Initialize compiled closures. */
  init_cclosures();
}
/* manual initialization of all LISP-data: */
local void initmem (void) {
  init_symbol_tab_1();          /* initialize symbol_tab */
  init_object_tab_1();          /* initialize object_tab */
  init_other_modules_1();       /* initialize other modules coarsely */
  {
    aktenv.var_env = NIL; aktenv.fun_env = NIL; aktenv.block_env = NIL;
    aktenv.go_env = NIL; aktenv.decl_env = NIL;
  }
  /* Now the tables are coarsely initialized,
   nothing can happen at GC.
   finish initialization of subr_tab: */
  init_subr_tab_2();
  /* initialize packages: */
  init_packages();
  init_encodings_1(); /* init some encodings (utf_8 for init_symbol_tab_2) */
  /* finish initialization of symbol_tab: */
  init_symbol_tab_2();
  init_encodings_2();           /* init the rest of encodings */
  /* enter SUBRs/FSUBRs into their symbols: */
  init_symbol_functions();
  /* constants/variables: enter value into the symbols: */
  init_symbol_values();
#if defined(MULTITHREAD)
  /* initialize standard per thread special symbols */
  init_multithread_special_symbols();
#endif
  /* create other objects: */
  init_object_tab();
}
/* loading of MEM-file: */
local void loadmem (const char* filename); /* see below */
local int loadmem_from_executable (void);
/* initialization of the other, not yet initialized modules: */
local void init_other_modules_2 (void);
local void init_module_2 (module_t* module) {
  /* pre-initialize subr_tab, object_tab, so that GC becomes possible: */
  if (*module->stab_size > 0) {
    var subr_t* ptr = module->stab; /* traverse subr_tab */
    var uintC count = *module->stab_size;
    do {
      ptr->GCself = subr_tab_ptr_as_object(ptr);
      ptr->name = NIL; ptr->keywords = NIL;
      ptr++;
    } while (--count);
  }
  if (*module->otab_size > 0) {
    var gcv_object_t* ptr = module->otab; /* traverse object_tab */
    var uintC count = *module->otab_size;
    do { *ptr++ = NIL; } while(--count);
  }
  module->initialized = true; /* GC can see this subr_tab, object_tab */
  /* enter Subr-symbols: */
  if (*module->stab_size > 0) {
    var subr_t* subr_ptr = module->stab;
    var const subr_initdata_t* init_ptr = module->stab_initdata;
    var uintC count = *module->stab_size;
    do {
      var const char* packname = init_ptr->packname;
      var object symname = asciz_to_string(init_ptr->symname,O(internal_encoding));
      var object symbol;
      if (packname==NULL) {
        symbol = make_symbol(symname);
      } else {
        pushSTACK(symname);
        var object pack =
          find_package(asciz_to_string(packname,O(internal_encoding)));
        if (nullp(pack)) {      /* package not found? */
          fprintf(stderr,GETTEXTL("module '%s' requires package %s.\n"),
                  module->name, packname);
          quit_instantly(1);
        }
        symname = popSTACK();
        intern(symname,false,pack,&symbol);
      }
      subr_ptr->name = symbol;  /* complete Subr */
      if (pack_locked_p(Symbol_package(symbol))
          && !nullp(Symbol_function(symbol))) { /* package lock error */
        fprintf(stderr,GETTEXTL("module '%s' redefines symbol "),module->name);
        nobject_out(stderr,symbol);
        fprintf(stderr,GETTEXTL(" in the locked package "));
        nobject_out(stderr,Symbol_package(symbol));
        fprintf(stderr,GETTEXTL("\nold definition: "));
        nobject_out(stderr,Symbol_function(symbol));
        fprintf(stderr,"\n");
        quit_instantly(1);
      }
      Symbol_function(symbol) = subr_tab_ptr_as_object(subr_ptr); /* define function */
      init_ptr++; subr_ptr++;
    } while (--count);
  }
  /* enter objects: */
  if (*module->otab_size > 0) {
    var gcv_object_t* object_ptr = module->otab;
    var const object_initdata_t* init_ptr = module->otab_initdata;
    var uintC count = *module->otab_size;
    do {
      pushSTACK(asciz_to_string(init_ptr->initstring,O(internal_encoding))); /* string */
      funcall(L(make_string_input_stream),1); /* pack into stream */
      pushSTACK(value1);
      *object_ptr = stream_read(&STACK_0,NIL,NIL); /* read object */
      skipSTACK(1);
      object_ptr++; init_ptr++;
    } while (--count);
  }
  /* call initialization function: */
  (*module->initfunction1)(module);
}
local void init_other_modules_2 (void) {
  var module_t* module;         /* traverse modules */
  for_modules(all_other_modules,{
    if (!module->initialized)
      init_module_2(module);
  });
}

/* print usage */
local void usage (void) {
  printf(PACKAGE_NAME " (" PACKAGE_BUGREPORT ") ");
  printf(GETTEXTL("is an ANSI Common Lisp implementation."));
  printf("\n");
  printf(GETTEXTL("Usage:  "));
  printf(program_name);
  printf(GETTEXTL(" [options] [lispfile [argument ...]]\n"
                  " When 'lispfile' is given, it is loaded and '*ARGS*' is set\n"
                  " to the list of argument strings. Otherwise, an interactive\n"
                  " read-eval-print loop is entered.\n"));
  printf(GETTEXTL("Informative output:\n"));
  printf(GETTEXTL(" -h, --help    - print this help and exit\n"));
  printf(GETTEXTL(" --version     - print the version information\n"));
  printf(GETTEXTL(" --license     - print the licensing information\n"));
  printf(GETTEXTL(" -help-image   - print image-specific help and exit\n"));
  printf(GETTEXTL("Memory image selection:\n"));
  printf(GETTEXTL(" -B lisplibdir - set the installation directory\n"));
 #if defined(UNIX) || defined(WIN32_NATIVE)
  printf(GETTEXTL(" -K linkingset - use this executable and memory image\n"));
 #endif
  printf(GETTEXTL(" -M memfile    - use this memory image\n"));
  printf(GETTEXTL(" -m size       - memory size (size = nB or nKB or nMB)\n"));
  printf(GETTEXTL("Internationalization:\n"));
  printf(GETTEXTL(" -L language   - set user language\n"));
  printf(GETTEXTL(" -N nlsdir     - NLS catalog directory\n"));
  printf(GETTEXTL(" -Edomain encoding - set encoding\n"));
  printf(GETTEXTL("Interoperability:\n"));
  printf(GETTEXTL(" -q, --quiet, --silent, -v, --verbose - verbosity level:\n"
                  "     affects banner, *LOAD-VERBOSE*/*COMPILE-VERBOSE*,\n"
                  "     and *LOAD-PRINT*/*COMPILE-PRINT*\n"));
  printf(GETTEXTL(" -w            - wait for a keypress after program termination\n"));
  printf(GETTEXTL(" -I            - be ILISP-friendly\n"));
  printf(GETTEXTL("Startup actions:\n"));
  printf(GETTEXTL(" -ansi         - more ANSI CL compliance\n"));
  printf(GETTEXTL(" -traditional  - traditional (undoes -ansi)\n"));
  printf(GETTEXTL(" -modern       - start in a case-sensitive lowercase-preferring package\n"));
  printf(GETTEXTL(" -p package    - start in the package\n"));
  printf(GETTEXTL(" -C            - set *LOAD-COMPILING* to T\n"));
  printf(GETTEXTL(" -norc         - do not load the user ~/.clisprc file\n"));
  printf(GETTEXTL(" -lp dir       - add dir to *LOAD-PATHS* (can be repeated)\n"));
  printf(GETTEXTL(" -i file       - load initfile (can be repeated)\n"));
  printf(GETTEXTL("Actions:\n"));
  printf(GETTEXTL(" -c [-l] lispfile [-o outputfile] - compile lispfile\n"));
  printf(GETTEXTL(" -x expressions - execute the expressions, then exit\n"));
  printf(GETTEXTL(" Depending on the image, positional arguments can mean:\n"));
  printf(GETTEXTL("   lispscript [argument ...] - load script, then exit\n"));
  printf(GETTEXTL("   [argument ...]            - run the init-function\n"));
  printf(GETTEXTL("  arguments are placed in EXT:*ARGS* as strings.\n"));
  printf(GETTEXTL("These actions put CLISP into a batch mode, which is overridden by\n"));
  printf(GETTEXTL(" -on-error action - action can be one of debug, exit, abort, appease\n"));
  printf(GETTEXTL(" -repl            - enter the interactive read-eval-print loop when done\n"));
  printf(GETTEXTL("Default action is an interactive read-eval-print loop.\n"));
}

/* argument diagnostics */
local void arg_error (const char *error_message, const char *arg) {
  if (arg)
    fprintf(stderr,"%s: %s: '%s'\n",PACKAGE_NAME,error_message,arg);
  else
    fprintf(stderr,"%s: %s\n",PACKAGE_NAME,error_message);
  fprintf(stderr,GETTEXTL("%s: use '-h' for help"),PACKAGE_NAME);
  fputs("\n",stderr);
}
#define INVALID_ARG(a)  arg_error(GETTEXTL("invalid argument"),a)

/* print license */
nonreturning_function (local, print_license, (void)) {
  local const char * const license [] = {
    PACKAGE_NAME " is free software; you can redistribute and/or modify it\n",
    "under the terms of the GNU General Public License as published by\n",
    "the Free Software Foundation; either version 2, or (at your option)\n",
    "any later version.\n",
    "\n",
    PACKAGE_NAME " is distributed in the hope that it will be useful,\n",
    "but WITHOUT ANY WARRANTY; without even the implied warranty of\n",
    "MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.\n",
    "See the GNU General Public License for more details.\n",
    "\n",
    "You should have received a copy of the GNU General Public License\n",
    "along with " PACKAGE_NAME ", see file GNU-GPL.\n",
    "If not, write to the Free Software Foundation, Inc.,\n",
    "51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA.\n",
    "\n",
    "Distribution of Lisp programs meant to run in " PACKAGE_NAME "\n",
    "without sources is possible under certain conditions.\n",
    "See file COPYRIGHT that came with " PACKAGE_NAME " for details.\n",
    "\n",
  };
  var const char * const * ptr = license;
  var uintC count = sizeof(license)/sizeof(license[0]);
  pushSTACK(var_stream(S(standard_output),strmflags_wr_ch_B));
  fresh_line(&STACK_0); /* The *INIT-HOOKS* might have done output. */
  while (count--)
    write_sstring(&STACK_0,asciz_to_string(*ptr++,O(internal_encoding)));
  skipSTACK(1);
  quit_instantly(0);
}

#include "spvw_calendar.c"

/* print the banner */
local void print_banner (void)
{ const char * const banner0[] = { /* some lines above 66 characters */
  /*|Column 0           |Column 20                                    |Col 66
   "012345678901234567890123456789012345678901234567890123456789012345678901"*/
    "  i i i i i i i       ooooo    o        ooooooo   ooooo   ooooo\n",
    "  I I I I I I I      8     8   8           8     8     o  8    8\n",
   "  I  \\ `+' /  I      8         8           8     8        8    8\n",
   "   \\  `-+-'  /       8         8           8      ooooo   8oooo\n",
    "    `-__|__-'        8         8           8           8  8\n",
    "        |            8     o   8           8     o     8  8\n",
    "  ------+------       ooooo    8oooooo  ooo8ooo   ooooo   8\n",
   };
  const char * banner0_hanukka[] = { /* some lines above 66 characters */
 /*|Column 0           |Column 20                                    |Col 66
  "012345678901234567890123456789012345678901234567890123456789012345678901" */
   "        .\n",
   ". . . . I . . . .     ooooo    o        ooooooo   ooooo   ooooo\n",
   "I I I I I I I I I    8     8   8           8     8     o  8    8\n",
  "I I  \\ `+' /  I I    8         8           8     8        8    8\n",
  "I  \\  `-+-'  /  I    8         8           8      ooooo   8oooo\n",
  " \\  `-__|__-'  /     8         8           8           8  8\n",
   "  `--___|___--'      8     o   8           8     o     8  8\n",
   "        |             ooooo    8oooooo  ooo8ooo   ooooo   8\n",
   "--------+--------\n",
  };
  char banner0_line0[100];
  char banner0_line1[100];
  const char * const banner1[] = {
   "Copyright (c) Bruno Haible, Michael Stoll 1992, 1993\n",
   "Copyright (c) Bruno Haible, Marcus Daniels 1994-1997\n",
   "Copyright (c) Bruno Haible, Pierpaolo Bernardi, Sam Steingold 1998\n",
   "Copyright (c) Bruno Haible, Sam Steingold 1999-2000\n",
   "Copyright (c) Sam Steingold, Bruno Haible 2001-2008\n",
  };
  var int candles = 0;
  var uintL offset = (posfixnum_to_V(Symbol_value(S(prin_linelength))) >= 65 ? 0 : 20);
  if (offset == 0) {
    begin_system_call();
    strcpy(banner0_line0,banner0_hanukka[0]);
    strcpy(banner0_line1,banner0_hanukka[1]);
    var time_t now = time(NULL);
    var struct tm now_local;
    var struct tm now_gm;
    now_local = *(localtime(&now));
    now_gm = *(gmtime(&now));
    end_system_call();
    var sintL dayswest = /* Tage-Differenz, kann als 0,1,-1 angenommen werden */
      (now_gm.tm_year < now_local.tm_year ? -1 :
       now_gm.tm_year > now_local.tm_year ? 1 :
       (now_gm.tm_mon < now_local.tm_mon ? -1 :
        now_gm.tm_mon > now_local.tm_mon ? 1 :
        (now_gm.tm_mday < now_local.tm_mday ? -1 :
         now_gm.tm_mday > now_local.tm_mday ? 1 :
         0)));
    var sintL hourswest = 24*dayswest
      + (sintL)(now_gm.tm_hour - now_local.tm_hour);
    var uintL hours_since_1900 = ((unsigned long)now / 3600) - hourswest + 613608;
    /* Add 6 because Hebrew days begin in the evening. */
    var uintL days_since_1900 = (hours_since_1900 + 6) / 24;
    candles = hebrew_calendar_hanukka_candles(days_since_1900);
    if (candles > 0) {
      banner0_line0[8] = 'i';
      if (candles >= 1) {
        banner0_line1[16] = 'i';
        if (candles >= 2) {
          banner0_line1[14] = 'i';
          if (candles >= 3) {
            banner0_line1[12] = 'i';
            if (candles >= 4) {
              banner0_line1[10] = 'i';
              if (candles >= 5) {
                banner0_line1[6] = 'i';
                if (candles >= 6) {
                  banner0_line1[4] = 'i';
                  if (candles >= 7) {
                    banner0_line1[2] = 'i';
                    if (candles >= 8) {
                      banner0_line1[0] = 'i';
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    banner0_hanukka[0] = banner0_line0;
    banner0_hanukka[1] = banner0_line1;
  }
  var const char * const * ptr;
  var uintC count;
  pushSTACK(var_stream(S(standard_output),strmflags_wr_ch_B)); /* to *STANDARD-OUTPUT* */
  fresh_line(&STACK_0); /* The *INIT-HOOKS* might have done output. */
  if (candles > 0) {
    ptr = banner0_hanukka; count = sizeof(banner0_hanukka)/sizeof(banner0_hanukka[0]);
  } else {
    ptr = banner0; count = sizeof(banner0)/sizeof(banner0[0]);
  }
  while (count--)
    write_sstring(&STACK_0,asciz_to_string((*ptr++)+offset,O(internal_encoding)));
  terpri(&STACK_0);
  write_sstring(&STACK_0,asciz_to_string(GETTEXT("Welcome to"),O(internal_encoding)));
  write_sstring(&STACK_0,asciz_to_string(" " PACKAGE_STRING " <" PACKAGE_BUGREPORT ">\n\n",O(internal_encoding)));
  ptr = banner1; count = sizeof(banner1)/sizeof(banner1[0]);
  while (count--)
    write_sstring(&STACK_0,asciz_to_string(*ptr++,O(internal_encoding)));
  terpri(&STACK_0);
  write_sstring(&STACK_0,asciz_to_string(GETTEXT("Type :h and hit Enter for context help."),O(internal_encoding)));
  terpri(&STACK_0); terpri(&STACK_0);
  skipSTACK(1);
}

typedef enum {
  ON_ERROR_DEFAULT,
  ON_ERROR_DEBUG,
  ON_ERROR_ABORT,
  ON_ERROR_APPEASE,
  ON_ERROR_EXIT
} on_error_t;

/* install the appropriate global handglers
 can trigger GC */
local maygc void install_global_handlers (on_error_t on_error)
{
  /* do nothing if there is no memory image */
  if (!boundp(Symbol_function(S(set_global_handler)))) return;
  switch (on_error) {
    case ON_ERROR_EXIT: {
      pushSTACK(S(interrupt_condition));
      pushSTACK(Symbol_function(S(exitunconditionally)));
      funcall(S(set_global_handler),2);
      pushSTACK(S(serious_condition));
      pushSTACK(Symbol_function(S(exitonerror)));
      funcall(S(set_global_handler),2);
    } goto appease;
    case ON_ERROR_ABORT: {
      pushSTACK(S(serious_condition));
      pushSTACK(Symbol_function(S(abortonerror)));
      funcall(S(set_global_handler),2);
    } /*FALLTHROUGH*/
    case ON_ERROR_APPEASE: appease: {
      pushSTACK(S(error)); pushSTACK(Symbol_function(S(appease_cerror)));
      funcall(S(set_global_handler),2); return;
    }
    case ON_ERROR_DEBUG: return;
    default: NOTREACHED;
  }
}

/* Very early initializations. */
local inline void init_lowest_level (char* argv[]) {
 #ifdef WIN32_NATIVE
  init_win32();
 #endif
  begin_system_call();
  find_executable(argv[0]);
  end_system_call();
}

/* Very late de-initializations, */
local inline void fini_lowest_level (void) {
 #ifdef WIN32_NATIVE
  done_win32();
 #endif
 #if defined(UNIX)
  terminal_sane();            /* switch terminal again in normal mode */
 #endif
}

/* There are three type of command-line options:
 - Those which set global variables,
 - Those which set parameters needed to initialize C I/O.
 - Those which set parameters needed to initialize Lisp memory,
 - Those which set parameters that determine the actions to be executed. */

/* Global variables. */
global const char* locale_encoding = NULL; /* GNU canonical name of locale encoding */
global const char* argv_encoding_misc = NULL; /* override for *misc-encoding* */
global const char* argv_encoding_file = NULL; /* ... for *default-file-encoding* */
global const char* argv_encoding_pathname = NULL; /* ... for *pathname-encoding* */
global const char* argv_encoding_terminal = NULL; /* ... for *terminal-encoding* */
global const char* argv_encoding_foreign = NULL; /* ... for *foreign-encoding* */

/* Parameters needed to initialize C I/O. */
struct argv_init_c {
  const char* argv_language;
  const char* argv_localedir;
};

/* Parameters needed to initialize Lisp memory. */
struct argv_initparams {
  uintM argv_memneed;
  const char* argv_memfile;
};

/* Parameters that determine the actions to be executed. */
typedef struct { const char* input_file; const char* output_file; } argv_compile_file_t;
struct argv_actions {
  const char* argv_memfile;
  int argv_verbose; /* verbosity level */
  const char* argv_lisplibdir;
  bool argv_developer;
  bool argv_load_compiling;
  uintL argv_load_paths_count;
  argv_compile_file_t* argv_load_paths; /* share space with -c args */
  uintL argv_init_filecount;
  const char **argv_init_files;
  bool argv_compile;
  bool argv_compile_listing;
  bool argv_norc;
  on_error_t argv_on_error;
  uintL argv_compile_filecount;
  argv_compile_file_t* argv_compile_files;
  const char* argv_package;
  int argv_ansi;               /* 0: default; 1: ANSI; 2: traditional */
  bool argv_modern;
  bool argv_repl;
  uintL argv_expr_count;
  const char **argv_exprs;      /* stored backwards! */
  const char* argv_execute_file;
  const char* const* argv_execute_args;
  uintL argv_execute_arg_count;
  bool argv_batchmode_p;
  bool argv_license;
  bool argv_wait_keypress;
  bool argv_help_image;
};

/* parses the rest of an option, that specifies a byte-size.
   also checks, if certain boundaries are obeyed. */
local inline int size_arg (const char *arg, const char *docstring, uintM *ret,
                           uintM limit_low, uintM limit_high) {
  /* arg should consist of a few decimal places, then
     maybe K/M/G/T/P, then maybe B or W: [0-9]+[KMGTP]?[BW]? */
  uintM val = 0;
  while ((*arg >= '0') && (*arg <= '9'))
    val = 10*val + (uintM)(*arg++ - '0');
  switch (*arg) {
    case 'k': case 'K':         /* in kilobytes */
      val <<= 10; arg++; break; /* *= 1024 */
    case 'm': case 'M':         /* in megabytes */
      val <<= 20; arg++; break; /* *= 1024*1024 */
    case 'g': case 'G':         /* in gigabytes */
      val <<= 30; arg++; break; /* *= 1024*1024*1024 */
   #if intMsize > 32            /* 64-bit platforms only */
    case 't': case 'T':         /* in terabytes */
      val <<= 40; arg++; break; /* *= 1024*1024*1024*1024 */
    case 'p': case 'P':         /* in petabytes */
      val <<= 50; arg++; break; /* *= 1024*1024*1024*1024*1024 */
   #endif
  }
  switch (*arg) {
    case 'w': case 'W':            /* in words */
      val *= sizeof(gcv_object_t); /*FALLTHROUGH*/
    case 'b': case 'B':            /* in bytes */
      arg++; break;
  }
  if (*arg != '\0') {           /* argument finished? */
    fprintf(stderr,GETTEXTL("Syntax for %s: nnnnnnn or nnnnKB or nMB"),
            docstring);
    fputs("\n",stderr);
    return 1;
  }
  if (val < limit_low) {
    fprintf(stderr,GETTEXTL("warning: %s %lu too small, using %lu instead"),
            docstring, val, limit_low);
    fputs("\n",stderr);
    val = limit_low;
  }
  if (val > limit_high) {
    fprintf(stderr,GETTEXTL("warning: %s %lu too large, using %lu instead"),
            docstring, val, limit_high);
    fputs("\n",stderr);
    val = limit_high;
  }
  /* For multiple -m arguments, only the last counts. */
  *ret = val;
  return 0;
}

/* Parse the command-line options.
 Returns -1 on normal termination, or an exit code >= 0 for immediate exit. */
local inline int parse_options (int argc, const char* const* argv,
                                struct argv_init_c* p0,
                                struct argv_initparams* p1,
                                struct argv_actions* p2) {
  p0->argv_language = NULL;
  p0->argv_localedir = NULL;
  p1->argv_memneed = 0;
  p1->argv_memfile = NULL;
  p2->argv_memfile = NULL;
  p2->argv_verbose = 2;
  p2->argv_lisplibdir = NULL;
  p2->argv_developer = false;
  p2->argv_load_compiling = false;
  p2->argv_init_filecount = 0;
  p2->argv_init_files = (const char**) malloc((uintL)argc*sizeof(const char*)); /* max argc -x/-i options */
  p2->argv_compile = false;
  p2->argv_compile_listing = false;
  p2->argv_norc = false;
  p2->argv_on_error = ON_ERROR_DEFAULT;
  p2->argv_compile_filecount = 0;
  p2->argv_compile_files = (argv_compile_file_t*) malloc((uintL)argc*sizeof(argv_compile_file_t)); /* max argc file-arguments + -lp arguments */
  p2->argv_load_paths_count = 0;
  p2->argv_load_paths = p2->argv_compile_files + argc; /* share space with -c */
  p2->argv_package = NULL;
  p2->argv_ansi = 0;
  p2->argv_modern = false;
  p2->argv_repl = false;
  p2->argv_expr_count = 0;
  p2->argv_exprs = p2->argv_init_files + argc; /* put -x and -i arguments into the same array */
  p2->argv_execute_file = NULL;
  p2->argv_execute_args = NULL;
  p2->argv_execute_arg_count = 0;
  p2->argv_batchmode_p = false;
  p2->argv_license = false;
  p2->argv_wait_keypress = false;
  p2->argv_help_image = false;

  /* process arguments argv[0..argc-1] :
     -h              Help
     -m size         Memory size (size = nB or nKB or nMB)
     -t directory    temporary directory
     -B directory    set lisplibdir
     -K linkingset   specify executable and mem file
     -M file         load MEM-file
     -L language     set the user language
     -N directory    NLS catalog directory
     -Edomain encoding  set encoding
     -q/-v           verbosity level:
        3:   banner, VERBOSE=T, PRINT=T
      * 2:   banner, VERBOSE=T, PRINT=NIL  ======= default
        1:   no banner, VERBOSE=T, PRINT=NIL
        0:   no banner, VERBOSE=NIL, PRINT=NIL
     -norc           do not load the user ~/.clisprc file
     -I              ILISP-friendly
     -C              set *LOAD-COMPILING* to T
     -i file ...     load LISP-file for initialization
     -c file ...     compile LISP-files, then leave LISP
     -l              At compilation: create listings
     -p package      set *PACKAGE*
     -ansi           more ANSI CL Compliance
     -traditional    traditional (undoes -ansi)
     -modern         modern (set *PACKAGE* and *PRINT-CASE*)
     -x expr         execute LISP-expressions, then leave LISP
     -on-error debug override batch-mode for -c, -x and file
     -repl           enter REPL after -c, -x and file
     -w              wait for keypress after termination
     --help          print usage and exit (should be the only option)
     --version       print version and exit (should be the only option)
     file [arg ...]  load LISP-file in batch-mode and execute, then leave LISP
                     or put all positional arguments into *ARGS* and run DRIVER
     -help-image     print what this image does
   -d -- developer mode -- undocumented, unsupported &c
      - unlock all packages.

   Newly added options have to be listed:
   - in the above table,
   - in the usage-message here,
   - in the options parser,
   - in the options parser in _clisp.c,
   - in the manual page doc/clisp.xml.in. */

  program_name = argv[0];       /* argv[0] is the program name */
  {
    var const char* const* argptr = &argv[1];
    var const char* const* argptr_limit = &argv[argc];
    var enum { for_exec, for_init, for_compile, for_expr, for_load_path }
    argv_for = for_exec;
    /* loop and process options, replace processed options with NULL: */
    while (argptr < argptr_limit) {
      var const char* arg = *argptr++; /* next argument */
      if ((arg[0] == '-') && !(arg[1] == '\0')) {
        switch (arg[1]) {
          case 'h':             /* help */
            if (asciz_equal(arg,"-help-image")) {
              p2->argv_help_image = true;
              break;
            } else if (arg[2] != 0) {
              INVALID_ARG(arg);
              return 1;
            } else {
              usage();
              return 0;
            }
            /* returns after a one-character token the rest of the
             option in arg. poss. space is skipped. */
            #define OPTION_ARG                  \
              if (arg[2] == '\0') {             \
                if (argptr < argptr_limit)      \
                  arg = *argptr++;              \
                else {                          \
                  INVALID_ARG(arg);             \
                  return 1;                     \
                }                               \
              } else arg += 2
          case 'm':             /* memory size  */
           #ifdef WIN32_NATIVE
            if (arg[2]=='m' && arg[3]=='\0') /* "-mm" -> print a memory map */
              { DumpProcessMemoryMap(); return 1; }
           #endif
            if (asciz_equal(arg,"-modern"))
              p2->argv_modern = true;
            else {
              OPTION_ARG;
              if (size_arg(arg,GETTEXTL("memory size"),&(p1->argv_memneed),
                           (MINIMUM_SPACE + RESERVE) * 8 /*teile/teile_STACK*/,
                           (oint_addr_len+addr_shift < intLsize-1
                            /* address space in oint_addr_len+addr_shift bits */
                            ? vbitm(oint_addr_len+addr_shift)
                            /* (resp. big dummy-limit) */
                            : vbitm(oint_addr_len+addr_shift)-1)))
                return 1;
            } break;
          case 't':             /* traditional, temporary directory */
            if (asciz_equal(arg,"-traditional"))
              p2->argv_ansi = 2; /* traditional */
            else {
              INVALID_ARG(arg);
              return 1;
            }
            break;
          case 'd': /* developer mode */
            p2->argv_developer = true;
            if (arg[2] != '\0') {
              INVALID_ARG(arg);
              return 1;
            }
            break;
          case 'B':             /* lisplibdir */
            OPTION_ARG;
            if (!(p2->argv_lisplibdir == NULL)) {
              arg_error(GETTEXTL("multiple -B"),arg);
              return 1;
            }
            p2->argv_lisplibdir = arg;
            break;
          case 'n':
            if (asciz_equal(arg,"-norc"))
              p2->argv_norc = true;
            else {
              INVALID_ARG(arg);
              return 1;
            }
            break;
         #if defined(UNIX) || defined(WIN32_NATIVE)
          case 'K':             /* linKing set */
            OPTION_ARG;
            /* This option has already been digested by clisp.c.
             We can ignore it. */
            break;
         #endif
          case 'M': /* MEM-file: when repeated, only the last one counts. */
            OPTION_ARG;
            p1->argv_memfile = arg;
            p2->argv_memfile = arg;
            break;
          case 'L': /* Language: when repeated, only the last one counts. */
            OPTION_ARG;
            p0->argv_language = arg;
            break;
          case 'N': /* NLS-directory: when repeated, only the last one counts. */
            OPTION_ARG;
            p0->argv_localedir = arg;
            break;
          case 'E':             /* encoding */
            if (!(argptr < argptr_limit)) {
              arg_error(GETTEXTL("-E requires an argument"),arg);
              return 1;
            }
            if (asciz_equal(&arg[2],"file"))
              argv_encoding_file = *argptr++;
            else if (asciz_equal(&arg[2],"pathname"))
              argv_encoding_pathname = *argptr++;
            else if (asciz_equal(&arg[2],"terminal"))
              argv_encoding_terminal = *argptr++;
            else if (asciz_equal(&arg[2],"foreign"))
              argv_encoding_foreign = *argptr++;
            else if (asciz_equal(&arg[2],"misc"))
              argv_encoding_misc = *argptr++;
            else if (arg[2] == '\0') /* unspecified => all */
              argv_encoding_file = argv_encoding_pathname =
                argv_encoding_terminal = argv_encoding_foreign =
                argv_encoding_misc = *argptr++;
            else {
              INVALID_ARG(arg);
              return 1;
            }
            break;
          case 'q':             /* verbosity level */
            p2->argv_verbose--;
            if (arg[2] != '\0') {
              INVALID_ARG(arg);
              return 1;
            }
            break;
          case 'v':             /* verbosity level */
            p2->argv_verbose++;
            if (arg[2] != '\0') {
              INVALID_ARG(arg);
              return 1;
            }
            break;
          case 'I':             /* ILISP-friendly */
            ilisp_mode = true;
            if (arg[2] != '\0') {
              INVALID_ARG(arg);
              return 1;
            }
            break;
          case 'C':             /* set *LOAD-COMPILING* */
            p2->argv_load_compiling = true;
            if (arg[2] != '\0') {
              INVALID_ARG(arg);
              return 1;
            }
            break;
          case 'r': /* -repl */
            if (asciz_equal(&arg[1],"repl"))
              p2->argv_repl = true;
            else {
              INVALID_ARG(arg);
              return 1;
            }
            break;
          case 'i':             /* initialization files */
            if (arg[2] == '\0')
              argv_for = for_init;
            else {
              INVALID_ARG(arg);
              return 1;
            }
            break;
          case 'c':             /* files to be compiled */
            p2->argv_compile = true;
            argv_for = for_compile;
            if (arg[2] == 'l') {
              p2->argv_compile_listing = true;
              if (arg[3] != '\0') {
                INVALID_ARG(arg);
                return 1;
              }
            } else {
              if (arg[2] != '\0') {
                INVALID_ARG(arg);
                return 1;
              }
            }
            break;
          case 'l':             /* compilation listings */
            if (arg[2] == 0)
              p2->argv_compile_listing = true;
            else if (arg[2] == 'p' && arg[3] == 0) {
              argv_for = for_load_path;
            } else {
              INVALID_ARG(arg);
              return 1;
            }
            break;
          case 'o':
            if (asciz_equal(&arg[1],"on-error")) {
              if (argptr < argptr_limit)
                arg = *argptr++;
              else {
                INVALID_ARG(arg);
                return 1;
              }
              if (asciz_equal(arg,"default"))
                p2->argv_on_error = ON_ERROR_DEFAULT;
              else if (asciz_equal(arg,"debug"))
                p2->argv_on_error = ON_ERROR_DEBUG;
              else if (asciz_equal(arg,"abort"))
                p2->argv_on_error = ON_ERROR_ABORT;
              else if (asciz_equal(arg,"appease"))
                p2->argv_on_error = ON_ERROR_APPEASE;
              else if (asciz_equal(arg,"exit"))
                p2->argv_on_error = ON_ERROR_EXIT;
              else {
                arg_error("invalid `on-error' action",arg);
                return 1;
              }
            } else if (arg[2] == '\0') { /* target for files to be compiled */
              OPTION_ARG;
              if (!((p2->argv_compile_filecount > 0)
                    && (p2->argv_compile_files[p2->argv_compile_filecount-1].output_file==NULL))) {
                INVALID_ARG(arg);
                return 1;
              }
              p2->argv_compile_files[p2->argv_compile_filecount-1].output_file = arg;
            } else {
              INVALID_ARG(arg);
              return 1;
            }
            break;
          case 'p': /* package: when repeated, only the last one counts. */
            OPTION_ARG;
            p2->argv_package = arg;
            break;
          case 'a':             /* ANSI CL Compliance */
            if (asciz_equal(arg,"-ansi"))
              p2->argv_ansi = 1; /* ANSI */
            else {
              INVALID_ARG(arg);
              return 1;
            }
            break;
          case 'x':             /* execute LISP-expression */
            if (arg[2] != '\0') {
              INVALID_ARG(arg);
              return 1;
            }
            argv_for = for_expr;
            break;
          case 'w':            /* wait for keypress after termination */
            p2->argv_wait_keypress = true;
            if (arg[2] != '\0') {
              INVALID_ARG(arg);
              return 1;
            }
            break;
          case '-':             /* -- GNU-style long options */
            if (arg[2] == 0) /* "--" ==> end of options */
              goto done_with_argv;
            else if (asciz_equal(&arg[2],"help")) {
              usage();
              return 0;
            } else if (asciz_equal(&arg[2],"version")) {
              p2->argv_expr_count = 0;  /* discard previous -x */
              p2->argv_verbose = 1;
              p2->argv_norc = true;
              p2->argv_repl = false;
              p2->argv_exprs[-1-(sintP)(p2->argv_expr_count++)] =
                /* FIXME: i18n */
                "(PROGN (PRINC \"" PACKAGE_NAME " \")"
                "(PRINC (LISP-IMPLEMENTATION-VERSION)) (TERPRI)"
                "(PRINC \"Software: \") (PRINC (SOFTWARE-VERSION))"
                "(PRINC \" \") (PRINC (SOFTWARE-TYPE)) (TERPRI)"
                "(PRINC \"Features: \") (PRINC *FEATURES*) (TERPRI)"
                /* Each module should augment *FEATURES*, so this should
                   not be necessary.
                   Unfortunately, we have no control over the user code,
                   thus we cannot enforce this requirement.
                   Since the "--version" output is used for bug reporting,
                   we must make it as complete and accurate as possible,
                   so we prefer to err on the side of verbosity. */
                "(PRINC \"C Modules: \") (PRINC (EXT::MODULE-INFO)) (TERPRI)"
                "(PRINC \"Installation directory: \")"
                "(PRINC (SYS::LIB-DIRECTORY)) (TERPRI)"
                "(PRINC \"User language: \")"
                "(PRINC (SYS::CURRENT-LANGUAGE)) (TERPRI)"
                "(PRINC \"Machine: \") (PRINC (MACHINE-TYPE))"
                "(PRINC \" (\") (PRINC (MACHINE-VERSION))"
                "(PRINC \") \") (PRINC (MACHINE-INSTANCE)) (TERPRI)"
                /*"(PRINC \"Arguments: \") (PRIN1 (EXT::ARGV)) (TERPRI)"*/
                "(SYS::%EXIT))";
              break;
            } else if (asciz_equal(&arg[2],"quiet")
                       || asciz_equal(&arg[2],"silent")) {
              p2->argv_verbose--;
              break;
            } else if (asciz_equal(&arg[2],"verbose")) {
              p2->argv_verbose++;
              break;
            } else if (asciz_equal(&arg[2],"license")) {
              p2->argv_license = true;
              break;
            } else {            /* unknown option */
              INVALID_ARG(arg);
              return 1;
            }
            break;
          default:              /* unknown option */
            INVALID_ARG(arg);
            return 1;
        }
      } else if (arg[0] == 0) {  /* done with the arguments */
       done_with_argv:
        p2->argv_execute_args = argptr;
        p2->argv_execute_arg_count = argptr_limit - argptr;
        argptr = argptr_limit; /* abort loop */
      } else {
        /* no option -> is interpreted as file to be loaded / compiled / executed */
        switch (argv_for) {
          case for_init:
            p2->argv_init_files[p2->argv_init_filecount++] = arg;
            break;
          case for_compile:
            p2->argv_compile_files[p2->argv_compile_filecount].input_file = arg;
            p2->argv_compile_files[p2->argv_compile_filecount].output_file = NULL;
            p2->argv_compile_filecount++;
            break;
          case for_exec:
            p2->argv_execute_file = arg;
            /* All further arguments are arguments for argv_execute_file. */
            p2->argv_execute_args = argptr;
            p2->argv_execute_arg_count = argptr_limit - argptr;
            /* Simulate -norc. Batch scripts should be executed in an
             environment which does not depend on files in $HOME, for
             maximum portability. */
            p2->argv_norc = true;
            argptr = argptr_limit; /* abort loop */
            break;
          case for_expr:
            p2->argv_exprs[-1-(sintP)(p2->argv_expr_count++)] = arg;
            break;
          case for_load_path:
            p2->argv_load_paths[-1-(sintP)(p2->argv_load_paths_count)].input_file = arg;
            p2->argv_load_paths[-1-(sintP)(p2->argv_load_paths_count++)].output_file = NULL;
            break;
          default: NOTREACHED;
        }
        argv_for = for_exec;
      }
    }
    p2->argv_batchmode_p = /* '-c' or '-x' or file => batch-mode: */
      ((p2->argv_compile || p2->argv_expr_count || p2->argv_execute_file != NULL)
       && p2->argv_on_error != ON_ERROR_DEBUG
       && p2->argv_on_error != ON_ERROR_APPEASE
       && !p2->argv_repl);
    /* check options semantically and store defaults: */
    if (p1->argv_memneed == 0) {
     #if defined(SPVW_MIXED_BLOCKS_OPPOSITE) && defined(GENERATIONAL_GC)
      /* Because of GENERATIONAL_GC the memory region is hardly exhausted. */
      p1->argv_memneed = 3584*1024*sizeof(gcv_object_t); /* 3584 KW = 14 MB Default */
     #else
      /* normal */
      p1->argv_memneed = 768*1024*sizeof(gcv_object_t); /* 768 KW = 3 MB Default */
     #endif
    }
    if (!p2->argv_compile) {
      /* Some options are useful only together with '-c' : */
      if (p2->argv_compile_listing) {
        arg_error(GETTEXTL("-l without -c is invalid"),NULL);
        return 1;
      }
    } else {
      /* Other options are useful only without '-c' : */
      if (p2->argv_expr_count) {
        arg_error(GETTEXTL("-x with -c is invalid"),NULL);
        return 1;
      }
    }
    if (p2->argv_expr_count && p2->argv_execute_file) {
      arg_error(GETTEXTL("-x with lisp-file is invalid"),p2->argv_execute_file);
      return 1;
    }
  }
  return -1;
}

/* Delete command-line options. */
local inline void free_argv_initparams (struct argv_initparams *p) {
}
local inline void free_argv_actions (struct argv_actions *p) {
  free(p->argv_init_files);
  free(p->argv_compile_files);
}

/* Initialize memory and load the specified memory image.
 Returns 0 if successful, -1 upon error (after printing an error message
 to stderr). */
#if 0
#define VAROUT(v)  printf("[%s:%d] %s=%ld\n",__FILE__,__LINE__,STRING(v),v)
#else
#define VAROUT(v)
#endif
extern char *get_executable_name (void);
local inline int init_memory (struct argv_initparams *p) {
  {                  /* Initialize the table of relocatable pointers: */
    var object* ptr2 = &pseudofun_tab.pointer[0];
    { var const Pseudofun* ptr1 = (const Pseudofun*)&pseudocode_tab;
      var uintC count = pseudocode_count;
      while (count--) { *ptr2++ = make_machine_code(*ptr1); ptr1++; }
    }
    { var const Pseudofun* ptr1 = (const Pseudofun*)&pseudodata_tab;
      var uintC count = pseudodata_count;
      while(count--) { *ptr2++ = make_machine(*ptr1); ptr1++; }
    }
  }
  /* fetch memory: */
  begin_system_call();
 #if (defined(SINGLEMAP_MEMORY) || defined(TRIVIALMAP_MEMORY) || defined(MULTITHREAD)) && (defined(HAVE_MMAP_ANON) || defined(HAVE_MMAP_DEVZERO) || defined(HAVE_MACH_VM) || defined(HAVE_WIN32_VM))
  mmap_init_pagesize();
 #endif
 #if defined(SINGLEMAP_MEMORY) || defined(TRIVIALMAP_MEMORY)
  init_map_pagesize();
 #endif
 #if defined(LINUX_NOEXEC_HEAPCODES) && defined(HAVE_MMAP_ANON)
  /* On machines on which the address space extends up to 0xFFFFFFFF,
     disable the address range 0xC0000000..0xDFFFFFFF,
     so that we can use it for immediate objects. */
  mmap((void*)0xC0000000,0x20000000,PROT_NONE,MAP_ANON|MAP_PRIVATE|MAP_FIXED,-1,0);
 #endif
 #ifdef SPVW_PURE
  init_mem_heaptypes();
  init_objsize_table();
 #endif
 #if defined(HAVE_HEAPNR_FROM_TYPE)
  init_mem_heapnr_from_type();
 #endif
  init_modules_0();             /* assemble the list of modules */
  end_system_call();

  back_trace = NULL;
 #ifdef MAP_MEMORY_TABLES
  {                             /* calculate total_subr_count: */
    var uintC total = 0;
    var module_t* module;
    for_modules(all_modules, { total += *module->stab_size; } );
    total_subr_count = total;
  }
 #endif
  {                              /* partitioning of the total memory: */
    #define teile             16 /* 16/16 */
    #define teile_STACK        2 /* 2/16 */
    #ifdef SPVW_MIXED_BLOCKS
      #define teile_objects    (teile - teile_STACK) /* rest */
    #else
      #define teile_objects    0
    #endif
    var uintL pagesize =        /* size of a page */
     #if defined(GENERATIONAL_GC)
      mmap_pagesize
     #else  /* if the system-pagesize does not play a role */
      teile*varobject_alignment
     #endif
      ;
    VAROUT(pagesize);
    var uintM memneed = p->argv_memneed; /* needed memory */
    VAROUT(memneed);
    var aint memblock;  /* lower address of the provided memory block */
   #if !(defined(SPVW_MIXED_BLOCKS_OPPOSITE) && !defined(TRIVIALMAP_MEMORY))
    memneed = teile_STACK*floor(memneed,teile); /* do not yet calculate memory for objects */
    VAROUT(memneed);
    #undef teile
    #define teile  teile_STACK
   #endif
   #if defined(TRIVIALMAP_MEMORY) && defined(WIN32_NATIVE)
    /* Somehow the RESERVE_FOR_MALLOC limit for mallocs after prepare_zeromap()
     seems also to encompass the mallocs before prepare_zeromap().
     Do not know why. */
    if (memneed > RESERVE_FOR_MALLOC*3/4) { memneed = RESERVE_FOR_MALLOC*3/4; }
    VAROUT(memneed);
   #endif
    while (1) {
      memblock = (aint)mymalloc(memneed); /* try to allocate memory */
      VAROUT(memneed); VAROUT(memblock);
      if (!((void*)memblock == NULL)) break; /* successful -> OK */
      memneed = floor(memneed,8)*7; /* else try again with 7/8 thereof */
      if (memneed == 0) break;
    }
    if (memneed == 0) {
      begin_system_call();
      memblock = (aint)malloc(1);
      end_system_call();
      fprintf(stderr,GETTEXTL("Return value of malloc() = %lx is not compatible with type code distribution."),
              memblock);
      fputs("\n",stderr);
      return -1;
    }
    if (memneed < MINIMUM_SPACE+RESERVE) { /* but with less than MINIMUM_SPACE */
      /* we will not be satisfied: */
      fprintf(stderr,GETTEXTL("Only %ld bytes available."),memneed);
      fputs("\n",stderr);
      return -1;
    }
    {                       /* round to the next lower page boundary: */
      var uintL unaligned = (uintL)(-memblock) % pagesize;
      memblock += unaligned; memneed -= unaligned;
      VAROUT(unaligned); VAROUT(memneed);
    }
    {                         /* round off to the last page boundary: */
      var uintL unaligned = memneed % pagesize;
      memneed -= unaligned;
      VAROUT(unaligned); VAROUT(memneed);
    }
    /* the memory region [memblock,memblock+memneed-1] is now free,
     and its boundaries are located on page boundaries. */
   #if defined(SINGLEMAP_MEMORY) || defined(TRIVIALMAP_MEMORY) /* <==> SPVW_PURE_BLOCKS || TRIVIALMAP_MEMORY */
    if ( initmap() <0) return -1;
    #ifdef SINGLEMAP_MEMORY
    {                           /* pre-initialize all heaps: */
      var uintL heapnr;
      for (heapnr=0; heapnr<heapcount; heapnr++) {
        var Heap* heapptr = &mem.heaps[heapnr];
        heapptr->heap_limit = (aint)type_zero_oint(heapnr);
        heapptr->heap_hardlimit = (aint)type_zero_oint(heapnr+1);
        if ((mem.heaptype[heapnr] >= -1)
            && prepare_zeromap(&heapptr->heap_limit,
                               &heapptr->heap_hardlimit,true) <0)
          return -1;
      }
    }
    /* set symbol_tab, subr_tab to address 0:
     (for this purpose case_symbolflagged must be equivalent to case_symbol!) */
    #define map_tab(tab,size)                                                \
      do { var uintM map_len = round_up(size,map_pagesize);                  \
           if ( zeromap(&tab,map_len) <0) return -1;                         \
           mem.heaps[typecode(as_object((oint)&tab))].heap_limit += map_len; \
      } while(0)
    map_tab(symbol_tab,sizeof(symbol_tab));
    map_tab(subr_tab,varobjects_misaligned+total_subr_count*sizeof(subr_t));
    #endif
    #ifdef TRIVIALMAP_MEMORY
    /* initialize all heaps as empty.
     Partition the whole available space with a ratio
     1:1 , if it is scarce. Otherwise, appoint the two heaps at
     1/5 resp. 2/5 of the address range. (An "awry" denominator,
     in order to avoid diverse Shared-Library-regions.) */
    {
      var void* malloc_addr = malloc(1);
      var aint start = round_up((aint)malloc_addr+RESERVE_FOR_MALLOC,map_pagesize); /* reserve for malloc() */
     #ifdef SPVW_MIXED_BLOCKS_OPPOSITE
      #if defined(SUN4_29)
      var aint end = bitm(oint_addr_len+addr_shift < 29 ? oint_addr_len+addr_shift : 29);
      mem.heaps[0].heap_limit = start + round_down(floor(end-start,5),map_pagesize);
      mem.heaps[1].heap_limit = round_down(end,map_pagesize);
      #elif defined(UNIX_LINUX) && defined(WIDE_SOFT) && !defined(SPARC)
      mem.heaps[0].heap_limit = 0x2E000000; /* room until at least 0x40000000 */
      mem.heaps[1].heap_limit = 0x7F000000; /* room until at least 0x64000000 */
      #else
       #ifdef TYPECODES
      var aint end = bitm(oint_addr_len+addr_shift);
       #else
      var aint end = bitm(oint_addr_len-1); /* keep garcol_bit zero */
       #endif
      var aint part = floor(end - (start & (end-1)),5);
      #if defined(AMD64) && defined(UNIX_LINUX)
      /* Don't use more than 36 address bits, otherwise mmap() fails. */
      part &= 0x0000000FFFFFFFFFUL;
      #endif
      mem.heaps[0].heap_limit = start + round_down(1*part,map_pagesize);
      mem.heaps[1].heap_limit = start + round_down(4*part,map_pagesize);
      #endif
      if ( prepare_zeromap(&mem.heaps[0].heap_limit,&mem.heaps[1].heap_limit,true) <0) return -1;
     #else  /* SPVW_MIXED_BLOCKS_STAGGERED */
      #if defined(SUN4_29)
      var aint end = bitm(oint_addr_len+addr_shift < 29 ? oint_addr_len+addr_shift : 29);
      mem.heaps[0].heap_limit = start + round_down(floor(end-start,5),map_pagesize);
      mem.heaps[0].heap_hardlimit =
        mem.heaps[1].heap_limit = start + round_down(floor((end-start)*3,5),map_pagesize);
      mem.heaps[1].heap_hardlimit = end;
      #elif defined(UNIX_LINUX) && defined(WIDE_SOFT) && !defined(SPARC)
      mem.heaps[0].heap_limit = 0x2E000000; /* room until at least 0x40000000 */
      mem.heaps[0].heap_hardlimit = 0x40000000;
      mem.heaps[1].heap_limit = 0x64000000; /* room until at least 0x7F000000 */
      mem.heaps[1].heap_hardlimit = 0x7F000000;
      #elif defined(TYPECODES) && (oint_addr_len+addr_shift > pointer_bitsize)
       #ifdef UNIX_DARWIN
      /* 'vmmap' shows that there is room between the malloc area at 0x01...... or 0x02......
       and the dyld at 0x8f...... */
      mem.heaps[0].heap_limit = 0x10000000; /* lower bound of large usable range */
      mem.heaps[1].heap_hardlimit = 0x8F000000; /* upper bound of large usable range */
      mem.heaps[0].heap_hardlimit = mem.heaps[1].heap_limit = 0x60000000; /* arbitrary separator address */
       #else
        #error Where is room in the memory map to put the heaps?
       #endif
      #else
       #ifdef TYPECODES
      var aint end = bitm(oint_addr_len+addr_shift);
       #else
        #ifdef STANDARD_HEAPCODES
      var aint end = (start | (bit(garcol_bit_o)-1)) + 1; /* keep garcol_bit zero */
        #endif
        #ifdef LINUX_NOEXEC_HEAPCODES
      var aint end = 0xBF000000; /* virtual addresses end at 0xC0000000. */
        #endif
       #endif
      var aint part = floor(end - (start & (end-1)),5);
      #if defined(AMD64) && defined(UNIX_LINUX)
      /* Don't use more than 36 address bits, otherwise mmap() fails. */
      part &= 0x0000000FFFFFFFFFUL;
      #endif
      mem.heaps[0].heap_limit = start + round_down(1*part,map_pagesize);
      mem.heaps[0].heap_hardlimit =
        mem.heaps[1].heap_limit = start + round_down(2*part,map_pagesize);
      mem.heaps[1].heap_hardlimit = start + round_down(3*part,map_pagesize);
      #endif
      if ( prepare_zeromap(&mem.heaps[0].heap_limit,&mem.heaps[1].heap_hardlimit,true) <0) return -1;
     #endif
      free(malloc_addr);
    }
   #endif  /* TRIVIALMAP_MEMORY */
    {      /* initialize all heaps as empty: */
      var uintL heapnr;
      for (heapnr=0; heapnr<heapcount; heapnr++) {
        var Heap* heapptr = &mem.heaps[heapnr];
        heapptr->heap_start = heapptr->heap_limit;
       #if varobjects_misaligned
        if (is_varobject_heap(heapnr)) {
          heapptr->heap_start += varobjects_misaligned;
          heapptr->heap_limit = heapptr->heap_start;
        }
       #endif
        heapptr->heap_end = heapptr->heap_start;
       #ifdef GENERATIONAL_GC
        heapptr->heap_gen0_start = heapptr->heap_gen0_end =
          heapptr->heap_gen1_start = heapptr->heap_start;
        heapptr->physpages = NULL;
       #endif
      }
    }
   #ifdef SINGLEMAP_MEMORY_STACK
    {                           /* initialize STACK: */
      var uintM map_len = round_up(memneed * teile_STACK/teile, map_pagesize);
      /* The stack occupies the interval between 0 and map_len
       for typecode = system_type: */
      var aint low = (aint)type_zero_oint(system_type);
      var aint high = low + map_len;
      if ( prepare_zeromap(&low,&high,true) <0) return -1;
      if ( zeromap((void*)low,map_len) <0) return -1;
     #ifdef STACK_DOWN
      STACK_bound = (gcv_object_t*)low + 0x40; /* 64 pointers additionally safety margin */
      setSTACK(STACK = (gcv_object_t*)high);   /* initialize STACK */
     #endif
     #ifdef STACK_UP
      setSTACK(STACK = (gcv_object_t*)low); /* initialize STACK */
      STACK_bound = (gcv_object_t*)high - 0x40; /* 64 pointers additionally safety margin */
      #endif
      STACK_start = STACK;
    }
    #undef teile_STACK
    #define teile_STACK 0       /* need no more room for the STACK */
    #if (teile==0)
     #undef teile
     #define teile 1            /* avoid division by 0 */
    #endif
   #endif  /* SINGLEMAP_MEMORY_STACK */
   #endif  /* SINGLEMAP_MEMORY || TRIVIALMAP_MEMORY */
   #if defined(GENERATIONAL_GC)
    init_physpagesize();
   #endif
    {                           /* divide memory block: */
      var uintM free_reserved;  /* number of reserved bytes */
      var uintM for_STACK;      /* number of bytes for Lisp-stack */
      var uintM for_objects;    /* number of bytes for Lisp-objects */
      /* the STACK needs alignment, because for frame-pointers
       the last Bit must be =0: */
      #define STACK_alignment  bit(addr_shift+1)
      #define alignment  (varobject_alignment>STACK_alignment ? varobject_alignment : STACK_alignment)
      free_reserved = memneed;
      /* make divisible by teile*alignment, so that each 1/16 is aligned: */
      free_reserved = round_down(free_reserved,teile*alignment);
      free_reserved = free_reserved - RESERVE;
      {
        var uintM teil = free_reserved/teile; /* a sub block, a 1/16 of the room */
        var aint ptr = memblock;
        mem.MEMBOT = ptr;
          #if defined(WIN32_NATIVE) && !defined(NO_SP_CHECK)
            /* Even if the NOCOST_SP_CHECK stack overflow detection (using a
             guard page) works, we set SP_bound.
             Normally, the stack's `AllocationBase' is = 0x30000, the guard
             page is 0x32000-0x32FFF, hence we can set SP_bound = 0x34000. */
            { var MEMORY_BASIC_INFORMATION info;
              if (!(VirtualQuery((void*)SP(),&info,sizeof(info)) == sizeof(info))) {
                fprintf(stderr,GETTEXTL("Could not determine the end of the SP stack!"));
                fputs("\n",stderr);
                SP_bound = 0;
              } else { /* 0x4000 might be enough, but 0x8000 will be better. */
                SP_bound = (void*)((aint)info.AllocationBase + 0x8000);
              }
            }
          #endif
        /* allocate STACK: */
        #ifdef SINGLEMAP_MEMORY_STACK
        for_STACK = 0;       /* STACK is already allocated elsewhere. */
        #else
        #ifdef STACK_DOWN
          STACK_bound = (gcv_object_t*)ptr + 0x40; /* 64 pointer safety margin */
          ptr += for_STACK = teile_STACK*teil; /* 2/16 for Lisp-stack */
          setSTACK(STACK = (gcv_object_t*)ptr); /* initialize STACK */
        #endif
        #ifdef STACK_UP
          setSTACK(STACK = (gcv_object_t*)ptr); /* initialize STACK */
          ptr += for_STACK = teile_STACK*teil; /* 2/16 for Lisp-stack */
          STACK_bound = (gcv_object_t*)ptr - 0x40; /* 64 pointer safety margin */
        #endif
          STACK_start = STACK;
        #endif
        #if defined(SPVW_MIXED_BLOCKS_OPPOSITE) && !defined(TRIVIALMAP_MEMORY)
        /* now, the lisp-objects start: */
        #ifdef GENERATIONAL_GC
        mem.varobjects.heap_gen0_start = mem.varobjects.heap_gen0_end =
          mem.varobjects.heap_gen1_start = mem.varobjects.heap_start =
          ((ptr + (physpagesize-1)) & -physpagesize) + varobjects_misaligned;
        #else
        mem.varobjects.heap_start = ptr + varobjects_misaligned;
        #endif
        mem.varobjects.heap_end = mem.varobjects.heap_start; /* there are no objects of variable length, yet */
        /* rest (14/16 or a little less) for lisp-objects: */
        for_objects = memblock+free_reserved - ptr; /* about = teile_objects*teil */
        ptr += for_objects;
        #ifdef GENERATIONAL_GC
        mem.conses.heap_gen0_start = mem.conses.heap_gen0_end =
          mem.conses.heap_gen1_end = mem.conses.heap_end =
          ptr & -physpagesize;
        #else
        mem.conses.heap_end = ptr;
        #endif
        mem.conses.heap_start = mem.conses.heap_end; /* there are no conses yet */
        /* ptr = memblock+free_reserved, because 2/16 + 14/16 = 1
         allocate memory reserve: */
        ptr += RESERVE;
        /* upper memory limit reached. */
        mem.MEMTOP = ptr;
        /* above (far away) the machine stack. */
        #endif
        #if defined(SPVW_PURE_BLOCKS) || defined(TRIVIALMAP_MEMORY) || defined(GENERATIONAL_GC)
        mem.total_room = 0;
        #ifdef GENERATIONAL_GC
        mem.last_gcend_space0 = 0;
        mem.last_gcend_space1 = 0;
        #endif
        #endif
        #ifdef SPVW_PAGES
        for_each_heap(heap, { heap->inuse = EMPTY; } );
        for_each_cons_heap(heap, { heap->lastused = dummy_lastused; } );
        dummy_lastused->page_room = 0;
        for_each_varobject_heap(heap, { heap->misaligned = varobjects_misaligned; } );
        for_each_cons_heap(heap, { heap->misaligned = conses_misaligned; } );
        mem.free_pages = NULL;
        mem.total_space = 0;
        mem.used_space = 0;
        mem.last_gcend_space = 0;
        mem.gctrigger_space = 0;
        #endif
        /* initialize stack: */
        pushSTACK(nullobj); pushSTACK(nullobj); /* two nullpointer as STACK end marker */
      }
    }
  }
 #ifdef DEBUG_SPVW
  { /* STACK & SP are settled - check that we have enough STACK */
    var uintM stack_depth =
      STACK_item_count((gcv_object_t*)STACK_bound,STACK);
    fprintf(stderr,"STACK depth: %lu [0x%lx 0x%lx]\n",stack_depth,
            (aint)STACK_bound,(aint)STACK);
   #ifndef NO_SP_CHECK
    if (SP_bound != 0) {
      fprintf(stderr,"SP depth: %lu\n",(uintM)
             #ifdef SP_UP
              ((SPint*)SP_bound - (SPint*)SP())
             #else
              ((SPint*)SP() - (SPint*)SP_bound)
             #endif
             );
    }
   #endif
    if (stack_depth < ca_limit_1) {
      fprintf(stderr,"STACK depth is less than CALL-ARGUMENTS-LIMIT (%d)\n",
              ca_limit_1);
      abort();
    }
  }
 #endif
  init_subr_tab_1();            /* initialize subr_tab */
  markwatchset = NULL; markwatchset_allocated = markwatchset_size = 0;
  if (p->argv_memfile)
    loadmem(p->argv_memfile);   /* load memory file */
  else if (!loadmem_from_executable())
    p->argv_memfile = get_executable_name();
  else initmem();               /* manual initialization */
#if defined(MULTITHREAD)
  /* "FIX"
     VTZ:TODO. list threads records currently are saved into the lisp image 
     but are not re-created when the image is restored.
     the records themeselves are tottally invalid - since they point to
     nowhere - no clisp_threat_t for them.
     We should be able to re-create the saved threads - save the all
     relevant data from clisp_thread_t and re-create new threads from it.
  */
  O(all_threads) = NIL;
#endif
  /* init O(current_language) */
  O(current_language) = current_language_o(language);
  /* set current evaluator-environments to the toplevel-value: */
  aktenv.var_env   = NIL;
  aktenv.fun_env   = NIL;
  aktenv.block_env = NIL;
  aktenv.go_env    = NIL;
  aktenv.decl_env  = O(top_decl_env);
  /* That's it. */
  return 0;
}

/* run all functions in the list
 can trigger GC */
local void maygc run_hooks (object hooks) {
  var gcv_object_t* top_of_frame = STACK; /* pointer over frame */
  var sp_jmp_buf returner; /* return point */
  finish_entry_frame(DRIVER,returner,,goto done_driver_run_hooks;);
  pushSTACK(hooks);
  while (mconsp(STACK_0)) {     /* process */
    var object obj = STACK_0;
    STACK_0 = Cdr(obj); funcall(Car(obj),0);
  }
 done_driver_run_hooks:
  setSTACK(STACK = top_of_frame); /* drop hooks & skip driver-frame */
}

/* Perform the main actions as specified by the command-line arguments. */
local inline void main_actions (struct argv_actions *p) {
  /* print greeting: */
  if (!nullpSv(quiet)                    /* SYS::*QUIET* /= NIL ? */
      || p->argv_execute_file != NULL) { /* batch-mode ? */
    /* prevents the greeting */
    if (p->argv_verbose > 1)
      p->argv_verbose = 1;
  }
  if (p->argv_verbose>=2 || p->argv_license)
    print_banner();
  if (p->argv_license)
    print_license();
  if (p->argv_execute_arg_count > 0) {
    var const char* const* execute_arg_ptr = p->argv_execute_args;
    var uintL count = p->argv_execute_arg_count;
    do { pushSTACK(asciz_to_string(*execute_arg_ptr++,O(misc_encoding))); }
    while (--count);
    Symbol_value(S(args)) = listof(p->argv_execute_arg_count);
  }
  if ((p->argv_memfile == NULL) && (p->argv_expr_count == 0)) {
    /* warning for beginners */
    pushSTACK(var_stream(S(standard_output),strmflags_wr_ch_B)); /* auf *STANDARD-OUTPUT* */
    terpri(&STACK_0);
    write_sstring(&STACK_0,CLSTEXT("WARNING: No initialization file specified."));
    terpri(&STACK_0);
    write_sstring(&STACK_0,CLSTEXT("Please try: "));
    write_string(&STACK_0,asciz_to_string(program_name,O(pathname_encoding)));
    write_string(&STACK_0,ascii_to_string(" -M lispinit.mem\n"));
    skipSTACK(1);
  }
  if (p->argv_lisplibdir == NULL) {
    if (nullp(O(lib_dir))) {
      /* warning for beginners and careless developers */
      pushSTACK(var_stream(S(standard_output),strmflags_wr_ch_B)); /* on *STANDARD-OUTPUT* */
      terpri(&STACK_0);
      write_sstring(&STACK_0,CLSTEXT("WARNING: No installation directory specified."));
      terpri(&STACK_0);
      write_sstring(&STACK_0,CLSTEXT("Please try: "));
      write_string(&STACK_0,asciz_to_string(program_name,O(pathname_encoding)));
      write_string(&STACK_0,ascii_to_string(" -B /usr/local/lib/clisp\n"));
      skipSTACK(1);
    }
  } else {                      /* set it */
    pushSTACK(asciz_to_string(p->argv_lisplibdir,O(pathname_encoding)));
    funcall(L(set_lib_directory),1);
  }
  if (p->argv_batchmode_p) {
    /* (setq *debug-io*
         (make-two-way-stream (make-string-input-stream "") *query-io*)) */
    funcall(L(make_concatenated_stream),0); /* (MAKE-CONCATENATED-STREAM) */
    pushSTACK(value1);                      /* empty input-stream */
    var object stream = var_stream(S(query_io),strmflags_wr_ch_B);
    Symbol_value(S(debug_io)) = make_twoway_stream(popSTACK(),stream);
  }
  if (p->argv_on_error == ON_ERROR_DEFAULT)
    p->argv_on_error =
      (!p->argv_repl
       && (p->argv_compile || p->argv_execute_file || p->argv_expr_count))
      ? ON_ERROR_EXIT : ON_ERROR_DEBUG;
  install_global_handlers(p->argv_on_error);
  switch (p->argv_ansi) {
    case 1:                     /* Maximum ANSI CL compliance */
      { pushSTACK(T); funcall(L(set_ansi),1); break; }
    case 2:                     /* The traditional CLISP behavior */
      { pushSTACK(NIL); funcall(L(set_ansi),1); break; }
    default:                /* use the settings from the memory image */
      break;
  }
  if (p->argv_modern) {
    /* (IN-PACKAGE "CS-COMMON-LISP-USER") */
    Symbol_value(S(packagestar)) = O(modern_user_package);
    /* (SETQ *PRINT-CASE* :DOWNCASE) */
    Symbol_value(S(print_case)) = S(Kdowncase);
  }
  if (p->argv_load_compiling)   /* (SETQ *LOAD-COMPILING* T) : */
    { Symbol_value(S(load_compiling)) = T; }
  if (p->argv_verbose < 1) /* (setq *load-verbose* nil *compile-verbose* nil
                                    *saveinitmem-verbose* nil) */
    Symbol_value(S(load_verbose)) = Symbol_value(S(compile_verbose)) =
      Symbol_value(S(saveinitmem_verbose)) = NIL;
  if (p->argv_verbose > 2) /* (setq *load-print* t *compile-print* t
                                    *report-error-print-backtrace* t) */
    Symbol_value(S(report_error_print_backtrace)) =
      Symbol_value(S(load_print)) = Symbol_value(S(compile_print)) = T;
  if (p->argv_verbose > 3)      /* (setq *load-echo* t) */
    Symbol_value(S(load_echo)) = T;
  if (p->argv_developer) { /* developer mode */
    /* unlock all packages */
    var object packlist = O(all_packages);
    while (consp(packlist)) {
      mark_pack_unlocked(Car(packlist));
      packlist = Cdr(packlist);
    }
  }
  if (p->argv_help_image) { /* -help-image */
    if (p->argv_memfile == NULL) return;
    pushSTACK(var_stream(S(standard_output),strmflags_wr_ch_B));
    if (nullpSv(script))
      write_sstring(&STACK_0,CLSTEXT("All positional arguments are put into "));
    else
      write_sstring(&STACK_0,CLSTEXT("The first positional argument is the script name,\nthe rest are put into "));
    prin1(&STACK_0,S(args));
    terpri(&STACK_0);
    var object image_doc = Symbol_value(S(image_doc));
    if (stringp(image_doc))
      write_string(&STACK_0,image_doc);
    fresh_line(&STACK_0);
    skipSTACK(1);
    return;
  }
  /* load RC file ~/.clisprc */
  if (nullpSv(norc) && !p->argv_norc && p->argv_memfile) {
    var gcv_object_t* top_of_frame = STACK; /* pointer over frame */
    var sp_jmp_buf returner; /* return point */
    finish_entry_frame(DRIVER,returner,,goto done_driver_rc;);
    { /* If no memfile is given, LOAD cannot be called with 3 arguments.
       (LOAD (MAKE-PATHNAME :NAME ".clisprc"
                            :DEFAULTS (USER-HOMEDIR-PATHNAME))
             :IF-DOES-NOT-EXIST NIL) */
      pushSTACK(S(Kname));
      pushSTACK(ascii_to_string(".clisprc"));
      pushSTACK(S(Kdefaults));
      funcall(S(user_homedir_pathname),0);
      pushSTACK(value1);
      funcall(L(make_pathname),4);
      pushSTACK(value1);
      pushSTACK(S(Kif_does_not_exist));
      pushSTACK(S(nil));
      funcall(S(load),3);
    }
   done_driver_rc:
    setSTACK(STACK = top_of_frame); /* skip driver-frame */
  }
  /* augment *LOAD-PATHS* from -lp - after loading RC so that setting
   *LOAD-PATHS* in ~/.clisprc does not override the command line */
  if (p->argv_load_paths_count > 0) {
    var const argv_compile_file_t* fileptr = &p->argv_load_paths[-1];
    var uintL count = p->argv_load_paths_count;
    do { pushSTACK(asciz_to_string((fileptr--)->input_file,O(misc_encoding))); }
    while (--count);
    pushSTACK(Symbol_value(S(load_paths)));
    funcall(L(liststar),p->argv_load_paths_count+1);
    Symbol_value(S(load_paths)) = value1;
  }
  /* execute (LOAD initfile) for each initfile: */
  if (p->argv_init_filecount > 0) {
    var gcv_object_t* top_of_frame = STACK; /* pointer over frame */
    var sp_jmp_buf returner; /* return point */
    var const char* const* fileptr = &p->argv_init_files[0];
    var uintL count = p->argv_init_filecount;
    finish_entry_frame(DRIVER,returner,,goto done_driver_init_files;);
    do {
      pushSTACK(asciz_to_string(*fileptr++,O(misc_encoding)));
      funcall(S(load),1);
    } while (--count);
   done_driver_init_files:
    setSTACK(STACK = top_of_frame); /* skip driver-frame */
  }
  if (p->argv_compile) {
    /* execute
     (COMPILE-FILE (setq file (MERGE-PATHNAMES file (MERGE-PATHNAMES #".lisp" (CD))))
                   [:OUTPUT-FILE (setq output-file (MERGE-PATHNAMES (MERGE-PATHNAMES output-file (MERGE-PATHNAMES #".fas" (CD))) file))]
                   [:LISTING (MERGE-PATHNAMES #".lis" (or output-file file))])
     for each file: */
    if (p->argv_compile_filecount > 0) {
      var gcv_object_t* top_of_frame = STACK; /* pointer over frame */
      var sp_jmp_buf returner; /* return point */
      var const argv_compile_file_t* fileptr = &p->argv_compile_files[0];
      var uintL count = p->argv_compile_filecount;
      finish_entry_frame(DRIVER,returner,,goto done_driver_compile_files;);
      do {
        var uintC argcount = 1;
        var object filename = asciz_to_string(fileptr->input_file,O(misc_encoding));
        pushSTACK(filename);
        pushSTACK(O(source_file_type));      /* #".lisp" */
        funcall(L(cd),0); pushSTACK(value1); /* (CD) */
        funcall(L(merge_pathnames),2); /* (MERGE-PATHNAMES '#".lisp" (CD)) */
        pushSTACK(value1);
        funcall(L(merge_pathnames),2); /* (MERGE-PATHNAMES file ...) */
        pushSTACK(value1);
        if (fileptr->output_file) {
          filename = asciz_to_string(fileptr->output_file,O(misc_encoding));
          pushSTACK(S(Koutput_file));
          pushSTACK(filename);
          pushSTACK(O(compiled_file_type));    /* #".fas" */
          funcall(L(cd),0); pushSTACK(value1); /* (CD) */
          funcall(L(merge_pathnames),2); /* (MERGE-PATHNAMES '#".fas" (CD)) */
          pushSTACK(value1);
          funcall(L(merge_pathnames),2); /* (MERGE-PATHNAMES output-file ...) */
          pushSTACK(value1);
          pushSTACK(STACK_2);            /* file */
          funcall(L(merge_pathnames),2); /* (MERGE-PATHNAMES ... file) */
          pushSTACK(value1);
          argcount += 2;
        }
        if (p->argv_compile_listing) {
          pushSTACK(S(Klisting));
          pushSTACK(O(listing_file_type)); /* #".lis" */
          pushSTACK(STACK_2);              /* (or output-file file) */
          funcall(L(merge_pathnames),2); /* (MERGE-PATHNAMES '#".lis" ...) */
          pushSTACK(value1);
          argcount += 2;
        }
        funcall(S(compile_file),argcount);
        fileptr++;
      } while (--count);
     done_driver_compile_files:
      setSTACK(STACK = top_of_frame); /* skip driver-frame */
    }
    if (!p->argv_repl)
      return;
  }
  if (p->argv_package != NULL) { /* (IN-PACKAGE packagename) */
    var object packname = asciz_to_string(p->argv_package,O(misc_encoding));
    pushSTACK(packname);
    var object package = find_package(packname);
    if (!nullp(package)) {
      Symbol_value(S(packagestar)) = package;
    } else {
      pushSTACK(var_stream(S(standard_output),strmflags_wr_ch_B));
      terpri(&STACK_0);
      write_sstring(&STACK_0,CLSTEXT("WARNING: no such package: "));
      write_sstring(&STACK_0,STACK_1);
      terpri(&STACK_0);
      skipSTACK(1);
    }
    skipSTACK(1);
  }
  if (p->argv_execute_file != NULL && !nullpSv(script)) {
    var gcv_object_t* top_of_frame = STACK; /* pointer over frame */
    var sp_jmp_buf returner; /* return point */
    finish_entry_frame(DRIVER,returner,,goto done_driver_execute_file;);
    { /*  execute:
       (PROGN
         #+UNIX (SET-DISPATCH-MACRO-CHARACTER #\##\!
                 (FUNCTION SYS::UNIX-EXECUTABLE-READER))
         (SETQ *LOAD-VERBOSE* NIL)
         (LOAD argv_execute_file :EXTRA-FILE-TYPES ...)
         (UNLESS argv_repl (EXIT))) */
     #if defined(UNIX) || defined(WIN32_NATIVE)
      /* Make clisp ignore the leading #! line. */
      pushSTACK(ascii_char('#')); pushSTACK(ascii_char('!'));
      pushSTACK(L(unix_executable_reader));
      funcall(L(set_dispatch_macro_character),3);
     #endif
      Symbol_value(S(load_verbose)) = NIL;
      if (asciz_equal(p->argv_execute_file,"-")) {
        pushSTACK(Symbol_value(S(standard_input))); /* *STANDARD-INPUT* */
      } else {
        pushSTACK(asciz_to_string(p->argv_execute_file,O(misc_encoding)));
      }
     #ifdef WIN32_NATIVE
      pushSTACK(S(Kextra_file_types));
      pushSTACK(O(load_extra_file_types));
      funcall(S(load),3);
     #else
      funcall(S(load),1);
     #endif
    }
   done_driver_execute_file:
    setSTACK(STACK = top_of_frame); /* skip driver-frame */
    if (!p->argv_repl)
      return;
  } else if (p->argv_execute_file) { /* !scripting => (push exec-file *args*) */
    pushSTACK(asciz_to_string(p->argv_execute_file,O(misc_encoding)));
    var object new_cons = allocate_cons();
    Car(new_cons) = popSTACK();
    Cdr(new_cons) = Symbol_value(S(args));
    Symbol_value(S(args)) = new_cons;
  }
  if (p->argv_expr_count) {
    /* set *STANDARD-INPUT* to a stream, that produces argv_exprs: */
    var const char* const* exprs = &p->argv_exprs[-1];
    if (p->argv_expr_count > 1) {
      var uintL count = p->argv_expr_count;
      do { pushSTACK(asciz_to_string(*exprs--,O(misc_encoding))); }
      while (--count);
      var object total = string_concat(p->argv_expr_count);
      pushSTACK(total);
    } else
      pushSTACK(asciz_to_string(*exprs--,O(misc_encoding)));
    funcall(L(make_string_input_stream),1);
    /* During bootstrapping, *DRIVER* has no value and SYS::BATCHMODE-ERRORS
     is undefined. Do not set an error handler in that case.
     we use SYS::MAIN-LOOP instead of the image-specific user-defined
     SYS::*DRIVER* so that the users can always get to the repl using
     -x '(saveinitmem ...)'
    SYS::MAIN-LOOP calls DRIVER, so we do not need to do
      finish_entry_frame(DRIVER,returner,,;);
    here */
    var object main_loop_function = Symbol_function(S(main_loop));
    if (closurep(main_loop_function)) { /* see reploop.lisp:main-loop ! */
      dynamic_bind(S(standard_input),value1);
      /* (MAIN-LOOP !p->argv_repl) */
      pushSTACK(p->argv_repl ? NIL : T);
      funcall(main_loop_function,1);
      dynamic_unbind(S(standard_input));
    } else /* no *DRIVER* => bootstrap, no -repl */
      Symbol_value(S(standard_input)) = value1;
  }
  /* call read-eval-print-loop: */
  driver();
}

static struct argv_initparams argv1;
static struct argv_actions argv2;

/* main program stores the name 'main'. */
#ifndef argc_t
  #define argc_t int            /* Type of argc is mostly 'int'. */
#endif
global int main (argc_t argc, char* argv[]) {
  /* initialization of memory management.
   overall procedure:
   process command-line-options.
   determine memory partitioning.
   look at command string and either load LISP-data from .MEM-file
   or create manually and initialize static LISP-data.
   build up interrupt-handler.
   print banner.
   jump into the driver.
  This is also described in <doc/impext.xml#cradle-grave>! */
#if defined(MULTITHREAD)
/* if on 32 bit machine, no per_thread and asked by the user*/
  #if USE_CUSTOM_TLS == 2
  tse __tse_entry;
  tse *__thread_tse_entry=&__tse_entry;
  #endif
  /* initialize main thread */
  {
    init_multithread();
    init_heap_locks();
    set_current_thread(create_thread(0));
    register_thread(current_thread());
    #ifdef DEBUG_GCSAFETY
      current_thread()->_alloccount=1;
    #endif
  }
#endif
  init_lowest_level(argv);
  var struct argv_init_c argv0;
  {
    var int parse_result =
      parse_options(argc,(const char**)argv,&argv0,&argv1,&argv2);
    if (parse_result >= 0) {
      exitcode = parse_result;
      goto end_of_main;
    }
  }
  /* The argv_* variables now have their final values.
   Analyze the environment variables determining the locale.
   Deal with LC_CTYPE. */
  init_ctype();
  /* Deal with LC_MESSAGE.
   (This must come last, because it may unset environment variable LC_ALL) */
 #ifndef LANGUAGE_STATIC
  init_language(argv0.argv_language,argv0.argv_localedir);
 #endif

  if (!(setjmp(original_context) == 0)) goto end_of_main;
  /* Initialize memory and load a memory image (if specified). */
  if (init_memory(&argv1) < 0) goto no_mem;
  SP_anchor = (void*)SP(); /* VTZ: in MT current_thread() should be initialized */
#if defined(MULTITHREAD)
  /* after heap is initialized - allocate thread record for main thread.
     no locking is needed here*/
  {
    /* VTZ:TODO when we are loaded from mem file - we should restore the 
     threads from there. 
     Currently we just register our main thread and do not care what we have in
     mem file!!! Threads do not survive mem file save/restore - just create 
     garbage in it :( */
    /* TODO: give better name :)*/
    var object thr_name = coerce_imm_ss(asciz_to_string("main thread"
 #ifdef UNICODE
							,Symbol_value(S(utf_8))
#endif
							));
    pushSTACK(thr_name);
    pushSTACK(allocate_thread(&STACK_0));
    var object new_cons=allocate_cons();
    var object lthr;
    /* add to all_threads global */
    Car(new_cons) = lthr = popSTACK();
    Cdr(new_cons) = O(all_threads);
    O(all_threads) = new_cons;
    /* initialize the thread references */
    current_thread()->_lthread=lthr;
    TheThread(lthr)->xth_globals=current_thread();
    TheThread(lthr)->xth_system=xthread_self();
    popSTACK();
  }
#endif
  /* if the image was read from the executable, argv1.argv_memfile was
     set to exec name and now it has to be propagated to argv2.argv_memfile
     to avoid the beginner warning */
  argv2.argv_memfile = argv1.argv_memfile; /* propagate exec name */
  /* Prepare for catching SP overflow. */
  install_stackoverflow_handler(0x4000); /* 16 KB reserve should be enough */
  /* everything completely initialized. */
 {var struct backtrace_t bt;
  bt.bt_next = NULL;
  bt.bt_function = L(driver);
  bt.bt_stack = STACK STACKop -1;
  bt.bt_num_arg = -1;
  back_trace = &bt;
  clear_break_sems(); set_break_sem_1();
  begin_system_call();

 #if defined(WIN32_NATIVE)
  /* cannot do it in init_win32 - too early */
  if (isatty(stdout_handle)) {
    var HANDLE handle = GetStdHandle(STD_OUTPUT_HANDLE);
    if (handle!=INVALID_HANDLE_VALUE) {
      var CONSOLE_SCREEN_BUFFER_INFO info;
      if (GetConsoleScreenBufferInfo(handle,&info))
        Symbol_value(S(prin_linelength)) = fixnum(info.dwSize.X - 1);
    }
  }
 #endif
  /* handling of async interrupts with single thread */
#if !defined(MULTITHREAD)
  /* establish interrupt-handler: */
 #if defined(HAVE_SIGNALS) && defined(SIGWINCH) && !defined(NO_ASYNC_INTERRUPTS)
  install_sigwinch_handler();
 #endif
  /* query the size of the terminal-window also now on program start: */
 #if defined(HAVE_SIGNALS)
  update_linelength();
 #endif
 #if (defined(HAVE_SIGNALS) && defined(UNIX)) || defined(WIN32_NATIVE)
  /* install Ctrl-C-Handler: */
  install_sigint_handler();
 #endif
 #ifdef HAVE_SIGNALS
  install_sigcld_handler();
  install_sigterm_handler();    /* install SIGTERM &c handlers */
 #endif
#else
 #ifdef HAVE_SIGNALS
  install_sigcld_handler();
  install_async_signal_handlers();
 #endif
 #ifdef WIN32_NATIVE
  #warning "thread-interrupt and \"signal\" handlers for Win32 are still not implemented."
 #endif
#endif 
 #if defined(GENERATIONAL_GC)
  /* insatll Page-Fault-Handler: */
  install_segv_handler();
 #endif
 #if defined(HAVE_SIGNALS) && defined(SIGPIPE)
  install_sigpipe_handler();
 #endif
  /* initialize time variables: */
  init_time();
  /* Initialize locale dependent encodings: */
  init_dependent_encodings();
  /* initialize stream-variables: */
  init_streamvars(argv2.argv_batchmode_p);
  /* make break possible: */
  end_system_call();
  clr_break_sem_1();
  /* initialize pathnames: */
  init_pathnames();
 #ifdef DYNAMIC_FFI
  /* initialize FFI: */
  init_ffi();
 #endif
  init_other_modules_2();     /* initialize modules yet uninitialized */
  { /* final module initializations: */
    var module_t* module;     /* loop over modules */
    for_modules(all_other_modules,{
      if (module->initfunction2)
        /* call initialization function: */
        (*module->initfunction2)(module);
    });
  }
  run_hooks(Symbol_value(S(init_hooks)));
  { /* Init O(argv). */
    O(argv) = allocate_vector(argc);
    var argc_t count;
    for (count = 0; count < argc; count++) {
      var object arg = asciz_to_string(argv[count],O(misc_encoding));
      TheSvector(O(argv))->data[count] = arg;
    }
  }
  /* Perform the desired actions (compilations, read-eval-print loop etc.): */
  main_actions(&argv2);
  quit();
  /*NOTREACHED*/
 } /* end var bt */
  /* if the memory does not suffice: */
  no_mem:
  fprintf(stderr,GETTEXTL("%s: Not enough memory for Lisp."),program_name);
  fputs("\n",stderr);
  quit_instantly(1);
  /*NOTREACHED*/
  /* termination of program via quit_instantly(): */
  end_of_main:
  free_argv_initparams(&argv1);
  free_argv_actions(&argv2);
  fini_lowest_level();
  if (exitcode < 0) {
    var int sig = -exitcode;
    #ifdef HAVE_SIGNALS
     /* Reset the signal handler. */
     SIGNAL(sig,SIG_DFL);
     /* Unblock the signal. */
     #if defined(SIGNALBLOCK_POSIX)
     {
       var sigset_t sigblock_mask;
       sigemptyset(&sigblock_mask); sigaddset(&sigblock_mask,sig);
       sigprocmask(SIG_UNBLOCK,&sigblock_mask,NULL);
     }
     #endif
    #endif
    /* Raise the signal. */
    raise(sig);
    /* If that did not help: use a fake exit code that encodes the signal. */
    exitcode = 128 + sig;
  }
 #ifdef UNIX
  exit(exitcode); /* Calling exit(), not _exit(), allows profiling to work. */
 #endif
 #ifdef WIN32_NATIVE
  _exit(exitcode);
 #endif
  /* if that did not help: */
  return exitcode;
}

/* leave LISP-interpreter
 quit();
 > final_exitcode: 0 on normal exit, 1 on abort */
global int final_exitcode = 0;
local int quit_retry = 0;
nonreturning_function(global, quit, (void)) {
  /* first "unwind" the STACK downto STACK-end: */
  VALUES0; /* do not save values for UNWIND-PROTECT-frames */
  unwind_protect_to_save.fun = (restartf_t)&quit;
  while (!(eq(STACK_0,nullobj) && eq(STACK_1,nullobj)))
    if (framecode(STACK_0) & bit(frame_bit_t))
      /* At STACK_0 a frame starts */
      { unwind(); }             /* unwind frame */
    else
      /* STACK_0 contains a normal LISP-object */
      { skipSTACK(1); }
  run_hooks(Symbol_value(S(fini_hooks)));
  /* Then, a farewell message: */
  if (quit_retry==0) {
    quit_retry++;  /* If this fails, do not retry it. For robustness. */
    /* when running as a script, i.e. "clisp lisp-file",
        *standard-input*  is /dev/fd/0
        *standard-output* is /dev/fd/1
        *error-output*    is /dev/fd/2
       and *terminal-io* is an #<IO TERMINAL-STREAM>,
       so they all need to be terminated individually */
    funcall(L(fresh_line),0);   /* (FRESH-LINE [*standard-output*]) */
    pushSTACK(var_stream(S(error_output),strmflags_wr_ch_B));
    funcall(L(fresh_line),1);   /* (FRESH-LINE *error-output*) */
    pushSTACK(Symbol_value(S(terminal_io)));
    funcall(L(fresh_line),1);   /* (FRESH-LINE *terminal-io*) */
    if (argv2.argv_verbose >= 2) {
      pushSTACK(CLSTEXT("Bye.")); funcall(L(write_line),1);
    }
  }
  /* Then wait for a keypress: */
  if (argv2.argv_wait_keypress) {
    argv2.argv_wait_keypress = false; /* If this fails, do not retry it (robustness) */
    pushSTACK(CLSTEXT("Press a key to terminate..."));
    funcall(L(write_line),1);
    funcall(S(wait_keypress),0); /* (SYS::WAIT-KEYPRESS) */
  }
  close_all_files();            /* close all files */
  { /* module finalization: */
    var module_t* module;       /* loop over modules */
    for_modules(all_other_modules,{
      if (module->finifunction) /* call exit function: */
        (*module->finifunction)(module);
    });
  }
 #ifdef DYNAMIC_FFI
  exit_ffi();                   /* close FFI */
 #endif
  quit_instantly(final_exitcode);  /* leave program */
}

/* --------------------------------------------------------------------------
                  Saving and Loading of MEM-Files */

#include "spvw_memfile.c"

/* ------------------------ dll loading ----------------------------------- */
#if defined(DYNAMIC_MODULES) || (defined(DYNAMIC_FFI) && (defined(WIN32_NATIVE) || defined(HAVE_DLOPEN)))

#if defined(HAVE_DLFCN_H)
#include <dlfcn.h>
#endif

/* open the dynamic library
 libname is the name of the library
 returns a handle suitable for find_name()
 calls dlopen() or LoadLibrary() */
global void * libopen (const char* libname)
{
 #if defined(WIN32_NATIVE)
  return (void*)LoadLibrary(libname);
 #else
  /* FIXME: On UNIX_DARWIN, need to search for the library in /usr/lib */
  return dlopen(libname,RTLD_NOW|RTLD_GLOBAL);
 #endif
}

#if defined(WIN32_NATIVE)
/* #include <psapi.h> */
/* support older woe32 incarnations:
   fEnumProcessModules is 1 until the first call,
   it is NULL if this woe32 does not have EnumProcessModules(),
   and it points to EnumProcessModules() when it is present */
typedef BOOL (WINAPI * EnumProcessModules_t)
  (HANDLE hProcess,HMODULE* lphModule,DWORD cb,LPDWORD lpcbNeeded);
static EnumProcessModules_t fEnumProcessModules = (EnumProcessModules_t)1;
#endif

/* find the name in the dynamic library handle
 calls dlsym() or GetProcAddress()
 handle is an object returned by libopen()
        or NULL, which means emulate RTLD_DEFAULT on older FreeBSD and AIX
        and WIN32_NATIVE by searching through all libraries
 name is the name of the function (or variable) in the library */
global void* find_name (void *handle, const char *name)
{
  var void *ret = NULL;
 #if defined(WIN32_NATIVE)
  if (handle == NULL) { /* RTLD_DEFAULT -- search all modules */
    HANDLE cur_proc;
    HMODULE *modules;
    DWORD needed, i;
    if ((EnumProcessModules_t)1 == fEnumProcessModules) {
      /* first call: try to load EnumProcessModules */
      HMODULE psapi = LoadLibrary("psapi.dll");
      if (psapi == NULL) fEnumProcessModules = NULL;
      else fEnumProcessModules =
        (EnumProcessModules_t)GetProcAddress(psapi,"EnumProcessModules");
    }
    if (NULL != fEnumProcessModules) {
      cur_proc = GetCurrentProcess();
      if (!fEnumProcessModules(cur_proc,NULL,0,&needed)) OS_error();
      modules = (HMODULE*)alloca(needed);
      if (!fEnumProcessModules(cur_proc,modules,needed,&needed)) OS_error();
      for (i=0; i < needed/sizeof(HMODULE); i++)
        if ((ret = (void*)GetProcAddress(modules[i],name)))
          break;
    } else ret = NULL;
  } else ret = (void*)GetProcAddress((HMODULE)handle,name);
 #elif !defined(RTLD_DEFAULT)
  /* FreeBSD 4.0 and AIX 5.1 do not support RTLD_DEFAULT, so we emulate it by
     searching the executable and the libc. */
  if (handle == NULL) {
    /* Search the executable. */
    ret = dlsym(NULL,name);
    if (ret == NULL) {
      /* Search the libc. */
      static void* libc_handle;
      if (libc_handle == NULL)
        libc_handle = dlopen("libc.so",RTLD_LAZY);
      if (libc_handle != NULL)
        ret = dlsym(libc_handle,name);
    }
  } else
    ret = dlsym(handle,name);
 #else
  ret = dlsym(handle,name);
 #endif
  return ret;
}

#endif

/* --------------------------------------------------------------------------
                       Dynamic Loading of Modules */

#ifdef DYNAMIC_MODULES

/* Attaches a shared library to this process' memory, and attempts to load
 a number of clisp modules from it. */
nonreturning_function(local, error_dlerror,
                      (const char* func, const char* symbol,
                       const char* errstring)) {
  end_system_call();
  pushSTACK(asciz_to_string(errstring==NULL ? "Unknown error" : errstring,
                            O(misc_encoding)));
  if (symbol != NULL)
    pushSTACK(asciz_to_string(symbol,O(internal_encoding)));
  pushSTACK(asciz_to_string(func,O(internal_encoding)));
  pushSTACK(TheSubr(subr_self)->name);
  error(error_condition, (symbol == NULL ? "~S: ~S -> ~S" : "~S: ~S(~S) -> ~S"));
}

#if !defined(HAVE_DLERROR)
#define dlerror()  NULL
#endif

/* find the symbol, signal an error if not found
 format: a format string with a single %s, substituted with ...
 modname: the name of the module
 libhandle: the dll handle, returned by libopen()
 returns: non-NULL pointer to the symbol in the library */
local void* get_module_symbol (const char* format, const char* modname,
                               void* libhandle) {
  var char * symbolbuf = alloca(strlen(format)+strlen(modname));
  sprintf(symbolbuf,format,modname);
  var void * ret = find_name(libhandle,symbolbuf);
  if (ret == NULL) error_dlerror("dlsym",symbolbuf,dlerror());
  return ret;
}

global void dynload_modules (const char * library, uintC modcount,
                             const char * const * modnames) {
  var void* libhandle;
  begin_system_call();
  /* Open the library. */
  libhandle = libopen(library);
  if (libhandle == NULL) error_dlerror("dlopen",NULL,dlerror());
  end_system_call();
  if (modcount > 0) {
    /* What's the longest module name? What's their total size? */
    var uintL total_modname_length = 0;
    begin_system_call();
    {
      var const char * const * modnameptr = modnames;
      var uintC count = modcount;
      do {
        var uintL len = asciz_length(*modnameptr);
        total_modname_length += len+1;
        modnameptr++;
      } while (--count);
    }
    {                        /* Make room for the module descriptors. */
      var module_t* modules = (module_t*)clisp_malloc(modcount*sizeof(module_t)+total_modname_length);
      {
        var char* modnamebuf = (char*)(&modules[modcount]);
        var const char * const * modnameptr = modnames;
        var module_t* module = modules;
        var uintC count = modcount;
        do {
          var const char * modname = *modnameptr;
          var uintL len = asciz_length(modname);
          var const char * err;
          /* Copy modname into modnamebuf: */
          module->name = modnamebuf;
          {
            var const char * ptr = modname;
            while ((*modnamebuf++ = *ptr++) != '\0') {}
          }
          /* Find the addresses of some C data in the shared library: */
          module->stab = (subr_t*) ((char*) get_module_symbol("module__%s__subr_tab",modname,libhandle) + varobjects_misaligned);
          module->stab_size = (const uintC*) get_module_symbol("module__%s__subr_tab_size",modname,libhandle);
          module->otab = (gcv_object_t*) get_module_symbol("module__%s__object_tab",modname,libhandle);
          module->otab_size = (const uintC*) get_module_symbol("module__%s__object_tab_size",modname,libhandle);
          module->initialized = false;
          module->stab_initdata = (const subr_initdata_t*) get_module_symbol("module__%s__subr_tab_initdata",modname,libhandle);
          module->otab_initdata = (const object_initdata_t*) get_module_symbol("module__%s__object_tab_initdata",modname,libhandle);
          /* Find the addresses of some C functions in the shared library: */
          module->initfunction1 = (void (*) (module_t*)) get_module_symbol("module__%s__init_function_1",modname,libhandle);
          module->initfunction2 = (void (*) (module_t*)) get_module_symbol("module__%s__init_function_2",modname,libhandle);
          module->finifunction = (void (*) (module_t*)) get_module_symbol("module__%s__fini_function",modname,libhandle);
          module->next = NULL;
          modnameptr++; module++;
        } while (--count);
        FREE_DYNAMIC_ARRAY(symbolbuf);
      }
      end_system_call();
      { /* We found all the necessary symbols. Now register the modules. */
        var module_t* module = modules;
        var uintC mcount = modcount;
        while (mcount-- > 0) {
          add_module(module);
          /* pre-initialization, cf. init_subr_tab_1. */
          if (*module->stab_size > 0) module_set_argtypes(module);
         #if defined(SINGLEMAP_MEMORY) && defined(MAP_MEMORY_TABLES)
          {
            var subr_t* newptr = (subr_t*)((char*)&subr_tab+varobjects_misaligned) + total_subr_count;
            var uintC count = *module->stab_size;
            if (count > 0) {
              {
                var uintM old_map_len = round_up(varobjects_misaligned+total_subr_count*sizeof(subr_t),map_pagesize);
                var uintM new_map_len = round_up(varobjects_misaligned+(total_subr_count+count)*sizeof(subr_t),map_pagesize);
                if (old_map_len < new_map_len) {
                  if (zeromap((void*)((aint)&subr_tab+old_map_len),new_map_len-old_map_len) <0)
                    error_dlerror("zeromap",NULL,"out of memory for subr_tab");
                }
              }
              {
                var subr_t* oldptr = module->stab;
                module->stab = newptr;
                do {
                  *newptr = *oldptr++;
                  newptr->GCself = subr_tab_ptr_as_object(newptr);
                  newptr->name = NIL; newptr->keywords = NIL; /* GC stays possible with it */
                  newptr++;
                } while (--count);
              }
              total_subr_count += *module->stab_size;
            }
          }
         #endif
          /* main initialization. */
          init_module_2(module);
          module++;
        }
      }
      {                         /* Now start the modules' life. */
        var module_t* module = modules;
        var uintC count = modcount;
        do {
          if (module->initfunction2) /* call initialization function: */
            (*module->initfunction2)(module);
          module++;
        } while (--count);
      }
    }
  }
}

#endif


/* --------------------------------------------------------------------------
                      Multithreading signal handling  */
#if defined(MULTITHREAD) 
#ifdef HAVE_SIGNALS

/* creates mask of of signals that we do not want to be delivered
   directly to threads. The same signals are handled by special non
   lisp thread */
local sigset_t async_signal_mask()
{
  var sigset_t sigblock_mask;
  sigemptyset(&sigblock_mask);
  sigaddset(&sigblock_mask,SIGINT);
  /* may be we can use SIGALRM for with-timeout ??? */
  sigaddset(&sigblock_mask,SIGALRM);
  #ifdef SIGHUP
   sigaddset(&sigblock_mask,SIGHUP);
  #endif
  #ifdef SIGQUIT
   sigaddset(&sigblock_mask,SIGQUIT);
  #endif
  #ifdef SIGILL
   sigaddset(&sigblock_mask,SIGILL);
  #endif
  #ifdef SIGABRT
   sigaddset(&sigblock_mask,SIGABRT);
  #endif
  #ifdef SIGKILL
   sigaddset(&sigblock_mask,SIGKILL);
  #endif
  #ifdef SIGTERM
   sigaddset(&sigblock_mask,SIGTERM);
  #endif
  #if defined(SIGWINCH) 
    sigaddset(&sigblock_mask,SIGWINCH);
  #endif
  return sigblock_mask;
}

/* SIG_THREAD_INTERRUPT handler */
local void interrupt_thread_signal_handler (int sig) {
  signal_acknowledge(SIG_THREAD_INTERRUPT,&interrupt_thread_signal_handler);
  /* wait for the world to resume */
  clisp_thread_t *thr=current_thread();
  GC_SAFE_REGION_END(); /* end the safe region at which we are*/
  var object fun=popSTACK();
  var uintC args=posfixnum_to_V(popSTACK());
  /* have to unblock SIG_THREAD_INTERRUPT since 
     our funcall may exit non-locally with longjmp() 
     (do not want to rely on SA_NODEFER).
     there is signalblock_on() but it sets process wide mask - hmm not that
     bad - probably should use it ??? */
  var sigset_t mask;
  sigemptyset(&mask);
  sigaddset(&mask,SIG_THREAD_INTERRUPT);
  xthread_sigmask(SIG_UNBLOCK,&mask,NULL);
  /* NB: IT IS REALLY, REALLY NOT SAFE DO THIS ACCORDING POSIX - BUT SEEMS
     TO WORK QUITE WELL (OF COURSE ANY USER LOCKS MAY INTEFERE VERY BADLY).
     (PROBABLY IT IS RELATED WITH THE FACT THAT WE CANNOT BE INTERRUPTED AT 
     ARBITRARY PLACE IN THE PROGRAM - WHEN WE ARE IN LISP LAND - I DO NO SEE
     PROBLEMS, WHEN WE ARE IN BLOCKED SYSTEM CALL - IT'S OS SPECIFIC) 

     The initial plan was to handle the interrupt in the normal thread 
     execution. Since the thread can be safely stopped at only two places - 
     allocate_xxxx and in blocking system call - i had the intention to 
     execute the handler after we are unblocked. And here came the problem:
     All I/O (unixaux.d) is done by retrying on EINTR - so with the above 
     scheme we cannot interrupt the system calls - our GC_SAFE_REGIONs are 
     plced above the low level stuff in unixaux.d.

     It's tested on osx and debian 32 bit.
  */
  funcall(fun,args);
  /* if we come here - we have to set again the safe region 
   we will resume in a system call or in allocate_xxxx. */
  GC_SAFE_REGION_BEGIN();
}

local void *signal_handler_thread(void *arg)
{
  int sig;
  var sigset_t sig_mask=async_signal_mask();
  while (1) {
    if (sigwait(&sig_mask, &sig)) {
      /* strange - no way to have bad mask but it happens sometimes 
	(observed on 32 bit debian during (disaseemble 'car) and 
	CTRL-Z and "fg" later) */
      continue;
    }
    switch (sig) {
    case SIGINT:
      /* stop all threads - it seems enough to stop
	 only the one that is going to handle the signal. however - since
	 it is possible the other threads to cause GC (and again try to
	 top the world) - we play safe here and stop everything. */
      {
	var clisp_thread_t *thr=NULL;
	var xthread_t systhr;
	/* let's first acquire the HEAP lock. The ACQUIRE_HEAP_LOCK - called 
	   within WITH_STOPPED_WORLD is great - however We are not in the lisp 
	   world so GC_SAFE_POINT_ELSE() is not safe (no current_thread()).*/
	while (!spinlock_tryacquire(&mem.alloc_lock)) 
	  { xthread_yield(); }
	WITH_STOPPED_WORLD({
	  /* TODO: find thread to handle it 
	     currently we just pick the first one */
	  thr=allthreads[0];
	  systhr=TheThread(thr->_lthread)->xth_system;
	  if (thr == NULL) {
	    /* really strange - no thread can handle the interrupt.*/
	    fprintf(stderr,GETTEXT("*** SIGINT signal will be missed.\n"));
	  } else {
	    NC_pushSTACK(thr->_STACK,O(thread_break_description));
	    NC_pushSTACK(thr->_STACK,S(interrupt_condition)); /* condition */
	    NC_pushSTACK(thr->_STACK,fixnum(2)); /* two arguments */
	    NC_pushSTACK(thr->_STACK,S(cerror)); /* function to be called */
	    xthread_signal(systhr,SIG_THREAD_INTERRUPT);
	  }
	},
	  false,true); /* we own the heap lock now*/
	spinlock_release(&mem.alloc_lock);
      }
      break;
    case SIGALRM:
      /* currently not used */
      break;

  #if defined(SIGWINCH) 
    case SIGWINCH:
      /* update all threads SYS::*PRIN-LINELENGTH* bindings 
	 and the global symbol value as well */
      WITH_STOPPED_WORLD({
	var Symbol prl = TheSymbol(S(prin_linelength));
	for_all_threads({
	  /* TODO: implement */
	});},
	true,true);
      break;
  #endif
#ifdef SIGTTOU
    case SIGTTOU:
      break; /* just ignore it */
#endif
    default:
      /* some of the termination signals */
      /* TODO: terminate */
      /* quit_on_signal (int sig) - but not exactly - we should 
	 unwind all threads stacks at least */
      break;
    }
  }
  return NULL;
}

global void install_async_signal_handlers()
{
  /* SIGCLD needs special handling ???
     1. disable all async signals 
     2. install SIG_THREAD_INTERRUPT handler
     3. create thread waiting for signals (sigwait).
  */
  var sigset_t sigblock_mask=async_signal_mask();
  /* since we are called from the main thread - all threads
   in the process will inherit this mask !!*/
  sigprocmask(SIG_BLOCK,&sigblock_mask,NULL);

  /* install SIG_THREAD_INTERRUPT */
  SIGNAL(SIG_THREAD_INTERRUPT,&interrupt_thread_signal_handler);
  /* start the signal handling thread */
  xthread_t sthr;
  xthread_create(&sthr,signal_handler_thread,0);
}

#endif /* HAVE_SIGNALS */

#endif
