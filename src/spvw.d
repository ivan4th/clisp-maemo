# (SPVW = Speicherverwaltung): Memory Management for CLISP
# Bruno Haible 1990-2003
# Sam Steingold 1998-2003
# German comments translated into English: Stefan Kain 2002-03-24

# Content:
# module management
# debug utilities
# memory size
# object size determination
# Page Fault and Protection handling
# Garbage Collection
# memory provision functions
# cycle test
# memory walk
# elementary string functions
# other global auxiliary functions
# initialization
# loading and storing MEM-files
# dynamic loading of modules
# version
#include "lispbibl.c"

#include "version.h"

#include <string.h> # declares strchr() and possibly memset()
#ifdef MULTITHREAD
  #ifndef memset
    extern_C RETMEMSETTYPE memset (void* ptr, int c, size_t len); # see MEMORY(3)
  #endif
  #define bzero(ptr,len)  memset(ptr,0,len)
  #define bcopy(source,dest,len)  memcpy(dest,source,len)
#endif

# in this file, the table macros have a different utilization:
  #undef LISPSPECFORM
  #undef LISPFUN
  #undef LISPSYM
  #undef LISPOBJ

# table of all SUBRs: out-sourced to SPVWTABF
# size of this table:
#define subr_anz  (sizeof(subr_tab)/sizeof(subr_t))

# table of all FSUBRs: moved to CONTROL
# size of this table:
#define fsubr_anz  (sizeof(fsubr_tab)/sizeof(fsubr_t))

# tables of all relocatable pointers: moved to STREAM
# size of these tables:
#define pseudocode_anz  (sizeof(pseudocode_tab)/sizeof(Pseudofun))
#if defined(MICROSOFT) && !defined(UNICODE)
  #define pseudodata_anz 0
#else
  #define pseudodata_anz  (sizeof(pseudodata_tab)/sizeof(Pseudofun))
#endif
# total table:
#define pseudofun_anz  (pseudocode_anz+pseudodata_anz)
local struct pseudofun_tab_ { object pointer[pseudofun_anz]; } pseudofun_tab;

# table of all fixed symbols: moved to SPVWTABS
# size of these tables:
#define symbol_anz  (sizeof(symbol_tab)/sizeof(symbol_))

# table of all other fixed objects: moved to SPVWTABO
# size of these tables:
#define object_anz  (sizeof(object_tab)/sizeof(gcv_object_t))

# looping over subr_tab:
# (NB: subr_tab_ptr_as_object(ptr) turns a traversing pointer
# into a genuine lisp-object.)
#ifdef MAP_MEMORY_TABLES
  local uintC total_subr_anz;
  #define for_all_subrs(statement)                                      \
    do { var subr_t* ptr = (subr_t*)&subr_tab; /* traverse subr_tab */  \
         var uintC count;                                               \
         dotimesC(count,total_subr_anz, { statement; ptr++; } );        \
    } while(0)
#else
  #define for_all_subrs(statement)                      \
    do { var module_t* module; /* traverse modules */   \
         for_modules(all_modules,{                      \
           if (module->initialized)                     \
             if (*module->stab_size > 0) {              \
               var subr_t* ptr = module->stab;          \
               var uintC count;                         \
               dotimespC(count,*module->stab_size,      \
                         { statement; ptr++; } );       \
         }});                                           \
    } while(0)
#endif

# On traversal of symbol_tab:
# turns a traversing pointer into a genuine lisp-object.
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
# traversal of symbol_tab:
#define for_all_constsyms(statement)                                       \
  do { var symbol_* ptr = (symbol_*)&symbol_tab; # pass through symbol_tab \
       var uintC count;                                                    \
       dotimesC(count,symbol_anz, { statement; ptr++; } );                 \
  } while(0)

# Traverse object_tab:
#define for_all_constobjs(statement)                                         \
  do { var module_t* module; # loop over modules                             \
       for_modules(all_modules,{                                             \
         if (module->initialized)                                            \
           if (*module->otab_size > 0) {                                     \
             var gcv_object_t* objptr = module->otab; # loop over object_tab \
             var uintC count;                                                \
             dotimespC(count,*module->otab_size,                             \
                       { statement; objptr++; } );                           \
       }});                                                                  \
  } while(0)

# Semaphores: decide, if a break is effectless (/=0) or
# effectual (all = 0) .
# Are set with set_break_sem_x and deleted with clr_break_sem_x again.
global break_sems_ break_sems;
  # break_sem_0 == break_sems.einzeln[0]
  #   set, as long as a page-fault-handling is in progress
  # break_sem_1 == break_sems.einzeln[1]
  #   set, as long as the memory management forbids a break
  #   (so that empty memory cannot be traversed by the GC)
  # break_sem_2 == break_sems.einzeln[2]
  #   for package-management on lower level and hashtable-management
  # break_sem_3 == break_sems.einzeln[3]
  #   for package-management on higher level
  # break_sem_4 == break_sems.einzeln[4]
  #   set, as long as (AMIGAOS) DOS or external functions are being called.
  # break_sem_5 == break_sems.einzeln[5]
  #   set, as long as (UNIX) a signal-handler is being called.

# -----------------------------------------------------------------------------
#                          module management

#include "spvw_module.c"

# -----------------------------------------------------------------------------
#                            debug-helper

#include "spvw_debug.c"

# -----------------------------------------------------------------------------
#                          our own alloca()

#include "spvw_alloca.c"

# -----------------------------------------------------------------------------
#                         fast program-exit

# jmp_buf for return to the original-value of SP on program start:
local jmp_buf original_context;

# leave LISP immediately:
# quit_sofort(exitcode);
# > exitcode: 0 for normal, 1 for abnormal end of program
  # we must set the SP to the original value.
  # (On some operating systems, the memory occupied by the program is
  # returned with free() , before control is withdrawn from it.
  # For this short span the SP has to be set reasonably.)
local int exitcode;
#define quit_sofort(xcode)  exitcode = xcode; longjmp(&!original_context,1)

# -----------------------------------------------------------------------------
#                         memory management, common part

# method of the memory management:
#if defined(SPVW_BLOCKS) && defined(SPVW_MIXED) # e.g. ATARI
  #define SPVW_MIXED_BLOCKS
  #if !defined(TRIVIALMAP_MEMORY)
    # Blocks grow like this:         |******-->     <--****|
    #define SPVW_MIXED_BLOCKS_OPPOSITE
  #else # defined(TRIVIALMAP_MEMORY)
    #if !defined(WIDE_SOFT) && !defined(SELFMADE_MMAP)
      # Blocks grow like this:       |******-->     <--****|
      #define SPVW_MIXED_BLOCKS_OPPOSITE
    #else
      # Blocks grow like this:       |******-->      |***-->
      #define SPVW_MIXED_BLOCKS_STAGGERED
    #endif
  #endif
#endif
#if defined(SPVW_BLOCKS) && defined(SPVW_PURE) # e.g. UNIX_LINUX, Linux 0.99.7
  #define SPVW_PURE_BLOCKS
#endif
#if defined(SPVW_PAGES) && defined(SPVW_MIXED) # e.g. SUN3, AMIGA, HP9000_800
  #define SPVW_MIXED_PAGES
#endif
#if defined(SPVW_PAGES) && defined(SPVW_PURE) # e.g. SUN4, SUN386
  #define SPVW_PURE_PAGES
#endif

# canonical addresses:
# With MULTIMAP_MEMORY, the same spot in memory can be accessed with different
# pointers-types. The management of the heaps needs a "canonical"
# pointer. Via this pointer access takes place, and comparisons occur
# via >=, <=. heap_start and heap_end are canonical addresses.
#ifdef MULTIMAP_MEMORY
  #define canonaddr(obj)  upointer(obj)
  #define canon(address)  ((address) & oint_addr_mask)
#else
  #define canonaddr(obj)  (aint)ThePointer(obj)
  #define canon(address)  (address)
#endif
# canonaddr(obj) == canon((aint)ThePointer(obj)).

# -----------------------------------------------------------------------------
#                          Page-Allocation

#if defined(SINGLEMAP_MEMORY) || defined(TRIVIALMAP_MEMORY) || defined(MULTITHREAD)

#include "spvw_mmap.c"

#endif # SINGLEMAP_MEMORY || TRIVIALMAP_MEMORY || MULTITHREAD

#ifdef MULTIMAP_MEMORY

#include "spvw_multimap.c"

#if defined(MAP_MEMORY_TABLES)
  # symbol_tab is multi-mapped, always at the same address.
  # This speeds up loadmem() a little.
  #define MULTIMAP_MEMORY_SYMBOL_TAB
#endif

#endif # MULTIMAP_MEMORY

#if defined(SINGLEMAP_MEMORY) || defined(TRIVIALMAP_MEMORY)

#include "spvw_singlemap.c"

#if defined(SINGLEMAP_MEMORY) && defined(HAVE_WIN32_VM)
  # Despite of SINGLEMAP_MEMORY, a relocation may be necessary
  # at loadmem() time.
  #define SINGLEMAP_MEMORY_RELOCATE
#endif

#endif # SINGLEMAP_MEMORY || TRIVIALMAP_MEMORY

# -----------------------------------------------------------------------------
#                           Multithreading

#ifndef MULTITHREAD

  # Global variables.

  # the STACK:
  #if !defined(STACK_register)
    global gcv_object_t* STACK;
  #endif
  #ifdef HAVE_SAVED_STACK
    global gcv_object_t* saved_STACK;
  #endif

  # MULTIPLE-VALUE-SPACE:
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

  # During the execution of a SUBR, FSUBR: the current SUBR resp. FSUBR
  #if !defined(back_trace_register)
    global p_backtrace_t back_trace = NULL;
  #endif
  #ifdef HAVE_SAVED_back_trace
    global p_backtrace_t saved_back_trace;
  #endif

  # during callbacks, the saved registers:
  #if defined(HAVE_SAVED_REGISTERS)
    global struct registers * callback_saved_registers = NULL;
  #endif

  # stack-limits:
  #ifndef NO_SP_CHECK
    global void* SP_bound;  # SP-growth-limit
  #endif
  global void* STACK_bound; # STACK-growth-limit

  # the lexical environment:
  global gcv_environment_t aktenv;

  global unwind_protect_caller_t unwind_protect_to_save;

  # variables for passing of information to the top of the handler:
  global handler_args_t handler_args;

  # As only whole regions of handlers are deactivated and activated again,
  # we treat the handlers on deactivation apartly, but we maintain
  # a list of the STACK-regions, in which the handlers are deactivated.
  global stack_range_t* inactive_handlers = NULL;
  # A handler counts as inactiv if and only if:
  # low_limit <= handler < high_limit
  # is true for one of the regions listed in inactive_handlers:

  #define for_all_threadobjs(statement)                                  \
    do { var gcv_object_t* objptr = (gcv_object_t*)&aktenv;              \
         var uintC count;                                                \
         dotimespC(count,sizeof(gcv_environment_t)/sizeof(gcv_object_t), \
           { statement; objptr++; });                                    \
    } while(0)

  #define for_all_STACKs(statement)           \
    do { var gcv_object_t* objptr = &STACK_0; \
         { statement; }                       \
    } while(0)

  #define for_all_back_traces(statement)    \
    do { var p_backtrace_t bt = back_trace; \
      { statement;  }                       \
    } while(0)

#else

  # Mutex protecting the set of threads.
  local xmutex_t allthreads_lock;

  # Set of threads.
  #define MAXNTHREADS  128
  local uintC nthreads = 0;
  local thread_t* allthreads[MAXNTHREADS];

  # Number of symbol values currently in use in every thread.
  local uintL num_symvalues = 0;
  # Maximum number of symbol values in every thread before new thread-local
  # storage must be added.
  # = floor(round_up(thread_size(num_symvalues),mmap_pagesize)
  #         -offsetofa(thread_t,_symvalues),sizeof(gcv_object_t))
  local uintL maxnum_symvalues;

  # Initialization.
local void init_multithread (void) {
  xthread_init();
  xmutex_init(&allthreads_lock);
  maxnum_symvalues = floor(((thread_size(0)+mmap_pagesize-1)&-mmap_pagesize)
                           -offsetofa(thread_t,_symvalues),sizeof(gcv_object_t));
}

  # Create a new thread.
local thread_t* create_thread (void* sp) {
  var thread_t* thread;
  xmutex_lock(&allthreads_lock);
  if (nthreads >= MAXNTHREADS) { thread = NULL; goto done; }
  thread = sp_to_thread(sp);
  if (mmap_zeromap(thread,(thread_size(num_symvalues)+mmap_pagesize-1)&-mmap_pagesize) < 0)
    { thread = NULL; goto done; }
  thread->_index = nthreads;
  {
    var gcv_object_t* objptr =
      (gcv_object_t*)((uintP)thread+thread_objects_offset(num_symvalues));
    var uintC count;
    dotimespC(count,thread_objects_anz(num_symvalues),
      { *objptr++ = NIL; objptr++; });
  }
  allthreads[nthreads] = thread;
  nthreads++;
 done:
  xmutex_unlock(&allthreads_lock);
  return thread;
}

  # Delete a thread.
local void delete_thread (thread_t* thread) {
  xmutex_lock(&allthreads_lock);
  ASSERT(thread->_index < nthreads);
  ASSERT(allthreads[thread->_index] == thread);
  allthreads[thread->_index] = allthreads[nthreads-1];
  nthreads--;
  xmutex_unlock(&allthreads_lock);
}

  #define for_all_threads(statement)                            \
    do { var thread_t** _pthread = &allthreads[nthreads];        \
         while (_pthread != &allthreads[0])                     \
           { var thread_t* thread = *--_pthread; statement; }    \
    } while(0)

  # Add a new symbol value.
  # > value: the default value in all threads
  # < returns: the index in the every thread's _symvalues[] array
local uintL make_symvalue_perthread (object value) {
  var uintL index;
  xmutex_lock(&allthreads_lock);
  if (num_symvalues == maxnum_symvalues) {
    for_all_threads({
      if (mmap_zeromap((void*)((uintP)thread+((thread_size(num_symvalues)+mmap_pagesize-1)&-mmap_pagesize)),mmap_pagesize) < 0)
        goto failed;
    });
    maxnum_symvalues += mmap_pagesize/sizeof(gcv_object_t);
  }
  index = num_symvalues++;
  for_all_threads({ thread->_symvalues[index] = value; });
  xmutex_unlock(&allthreads_lock);
  return index;
 failed:
  xmutex_unlock(&allthreads_lock);
  fehler(error,GETTEXT("could not make symbol value per-thread"));
}

  #define for_all_threadobjs(statement)  \
    for_all_threads({                                    \
      var gcv_object_t* objptr = (gcv_object_t*)((uintP)thread+thread_objects_offset(num_symvalues)); \
      var uintC count;                                   \
      dotimespC(count,thread_objects_anz(num_symvalues), \
        { statement; objptr++; });                       \
    })

  #define for_all_STACKs(statement)  \
    for_all_threads({                                            \
      var gcv_object_t* objptr = STACKpointable(thread->_STACK); \
      { statement; }                                             \
    })

  #define for_all_back_traces(statement)   \
    for_all_back_traces({ var p_backtrace_t bt = thread->_back_trace; \
      { statement; }                                                  \
    })

#endif

# -----------------------------------------------------------------------------
#                           Page-Management

#include "spvw_page.c"
#include "spvw_heap.c"
#include "spvw_global.c"

#ifdef SPVW_PAGES

# A dummy-page for lastused:
  local NODE dummy_NODE;
  #define dummy_lastused  (&dummy_NODE)

#endif

#ifdef SPVW_BLOCKS

#ifdef SELFMADE_MMAP
# Pages from the memfile are read in when they are first used.
# We manage this ourselves by trapping page faults.
# Works only with SPVW_PURE_BLOCKS or SPVW_MIXED_BLOCKS_STAGGERED.
#endif

#endif

# -----------------------------------------------------------------------------

#if defined(NOCOST_SP_CHECK) && !defined(WIN32_NATIVE)
# Check for near stack overflow.
global bool near_SP_overflow (void) {
  # Force a stack overflow if there is not a minimum of room available.
  var uintB dummy[0x1001];
  dummy[0] = 0; dummy[0x800] = 0; dummy[0x1000] = 0;
 #ifdef GNU
  alloca(1); # Makes this function non-inlinable.
 #endif
  return false;
}
#endif

# At overflow of one of the stacks:
nonreturning_function(global, SP_ueber, (void)) {
  fputs(GETTEXTL(NLstring "*** - " "Program stack overflow. RESET"),stderr);
  if (interactive_stream_p(Symbol_value(S(debug_io))))
    reset();
  /* non-interactive session: quit */
  else { fputs(NLstring,stderr); final_exitcode=1; quit(); }
}
nonreturning_function(global, STACK_ueber, (void)) {
  fputs(GETTEXTL(NLstring "*** - " "Lisp stack overflow. RESET"),stderr);
  if (interactive_stream_p(Symbol_value(S(debug_io))))
    reset();
  /* non-interactive session: quit */
  else { fputs(NLstring,stderr); final_exitcode=1; quit(); }
}

# ----------------------------------------------------------------------------
#                       GC-Statistics

#include "spvw_gcstat.c"

# -----------------------------------------------------------------------------
#                       Memory-Size

#include "spvw_space.c"

# -----------------------------------------------------------------------------
#                       Marks

#include "spvw_mark.c"

# -----------------------------------------------------------------------------
#                   object size determination

#include "spvw_objsize.c"

# -----------------------------------------------------------------------------
#                    Memory Update

#include "spvw_update.c"

# -----------------------------------------------------------------------------
#                      Page Fault and Protection Handling

#if defined(SELFMADE_MMAP) || defined(GENERATIONAL_GC)

#include "spvw_fault.c"

#endif # SELFMADE_MMAP || GENERATIONAL_GC

# -----------------------------------------------------------------------------
#                      Signal handlers

#include "spvw_sigsegv.c"
#include "spvw_sigcld.c"
#include "spvw_sigpipe.c"
#include "spvw_sigint.c"
#include "spvw_sigwinch.c"

# -----------------------------------------------------------------------------
#                       Garbage-Collector

#include "spvw_garcol.c"

# -----------------------------------------------------------------------------
#                 Memory Allocation Functions

#include "spvw_allocate.c"
#include "spvw_typealloc.c"

# -----------------------------------------------------------------------------
#                   Circularity Test

#include "spvw_circ.c"

# -----------------------------------------------------------------------------
#                     Memory Walk

#include "spvw_walk.c"

# -----------------------------------------------------------------------------
#                  Elementary String Functions

#ifndef asciz_length
# UP: Returns the length of an ASCIZ-string.
# asciz_length(asciz)
# > char* asciz: ASCIZ-string
#       (address of a character sequence terminated by a nullbyte)
# < result: length of the character sequence (without nullbyte)
global uintL asciz_length (const char * asciz) {
  var const char* ptr = asciz;
  var uintL len = 0;
  # search nullbyte and increment length:
  while (*ptr++ != 0) { len++; }
  return len;
}
#endif

# UP: compares two ASCIZ-strings.
# asciz_equal(asciz1,asciz2)
# > char* asciz1: first ASCIZ-string
# > char* asciz2: second ASCIZ-string
# < result: true if both sequences are equal
global bool asciz_equal (const char * asciz1, const char * asciz2) {
  # compare bytes until the first nullbyte:
  loop {
    var char ch1 = *asciz1++;
    if (ch1 != *asciz2++) goto no;
    if (ch1 == '\0') goto yes;
  }
 yes: return true;
 no: return false;
}

# -----------------------------------------------------------------------------
#                  Other Global Helper Functions

#if (int_bitsize < long_bitsize)
# passing value from longjmpl() to setjmpl()  :
  global long jmpl_value;
#endif

#ifndef SP
# determine (an approximation) of the SP-stackpointer.
global void* SP (void) {
  var long dummy;
  return &dummy;
}
#endif

# error-message when a location of the program is reached that is (should be)
# unreachable. Does not return.
# fehler_notreached(file,line);
# > file: filename (with quotation marks) as constant ASCIZ-string
# > line: line number
nonreturning_function(global, fehler_notreached,
                      (const char* file, uintL line)) {
  end_system_call(); # just in case
  pushSTACK(fixnum(line));
  pushSTACK(ascii_to_string(file));
  fehler(serious_condition,
         GETTEXT("internal error: statement in file ~, line ~ has been reached!!" NLstring
                 "Please send the authors of the program a description how you produced this error!"));
}

#include "spvw_ctype.c"

#include "spvw_language.c"

# -----------------------------------------------------------------------------
#                        Initialization

# name of the program (for error reporting)
local char* program_name;

# flag, if SYS::READ-FORM should behave ILISP-compatible:
global bool ilisp_mode = false;

#ifdef UNIX

# Real User ID of the running process.
  global uid_t user_uid;

#endif

# conversion of the argument types of a FSUBR into a code:
local fsubr_argtype_t fsubr_argtype (uintW req_anz, uintW opt_anz,
                                     fsubr_body_t body_flag) {
  switch (body_flag) {
    case fsubr_nobody:
      switch (opt_anz) {
        case 0:
          switch (req_anz) {
            case 1: return(fsubr_argtype_1_0_nobody);
            case 2: return(fsubr_argtype_2_0_nobody);
            default: goto illegal;
          }
        case 1:
          switch (req_anz) {
            case 1: return(fsubr_argtype_1_1_nobody);
            case 2: return(fsubr_argtype_2_1_nobody);
            default: goto illegal;
          }
        default: goto illegal;
      }
    case fsubr_body:
      switch (opt_anz) {
        case 0:
          switch (req_anz) {
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
  fputs(GETTEXTL("Unknown signature of an FSUBR" NLstring),stderr);
  quit_sofort(1);
}

# conversion of the argument types of a FSUBR into a code:
local subr_argtype_t subr_argtype (uintW req_anz, uintW opt_anz,
                                   subr_rest_t rest_flag,
                                   subr_key_t key_flag) {
  switch (key_flag) {
    case subr_nokey:
      switch (rest_flag) {
        case subr_norest:
          switch (opt_anz) {
            case 0:
              switch (req_anz) {
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
              switch (req_anz) {
                case 0: return(subr_argtype_0_1);
                case 1: return(subr_argtype_1_1);
                case 2: return(subr_argtype_2_1);
                case 3: return(subr_argtype_3_1);
                case 4: return(subr_argtype_4_1);
                default: goto illegal;
              }
            case 2:
              switch (req_anz) {
                case 0: return(subr_argtype_0_2);
                case 1: return(subr_argtype_1_2);
                case 2: return(subr_argtype_2_2);
                case 3: return(subr_argtype_3_2);
                default: goto illegal;
              }
            case 3:
              switch (req_anz) {
                case 0: return(subr_argtype_0_3);
                case 1: return(subr_argtype_1_3);
                case 2: return(subr_argtype_2_3);
                default: goto illegal;
              }
            case 4:
              switch (req_anz) {
                case 0: return(subr_argtype_0_4);
                default: goto illegal;
              }
            case 5:
              switch (req_anz) {
                case 0: return(subr_argtype_0_5);
                default: goto illegal;
              }
            default: goto illegal;
          }
        case subr_rest:
          switch (opt_anz) {
            case 0:
              switch (req_anz) {
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
          switch (opt_anz) {
            case 0:
              switch (req_anz) {
                case 0: return(subr_argtype_0_0_key);
                case 1: return(subr_argtype_1_0_key);
                case 2: return(subr_argtype_2_0_key);
                case 3: return(subr_argtype_3_0_key);
                case 4: return(subr_argtype_4_0_key);
                default: goto illegal;
              }
            case 1:
              switch (req_anz) {
                case 0: return(subr_argtype_0_1_key);
                case 1: return(subr_argtype_1_1_key);
                default: goto illegal;
              }
            case 2:
              switch (req_anz) {
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
  fputs(GETTEXTL("Unknown signature of a SUBR" NLstring),stderr);
  quit_sofort(1);
}
# set the argtype of a subr_t *ptr
#define SUBR_SET_ARGTYPE(ptr)                                           \
  ptr->argtype = (uintW)subr_argtype(ptr->req_anz,ptr->opt_anz,         \
                                     (subr_rest_t)(ptr->rest_flag),     \
                                     (subr_key_t)(ptr->key_flag))

# Verify that a code address has the C_CODE_ALIGNMENT.
# This is important for calling make_machine_code, but it's easiest verified
# on Fsubrs and Subrs.
#ifdef TYPECODES
  #define verify_code_alignment(ptr,symbol)  # not needed
#else
  #define verify_code_alignment(ptr,symbol)  \
    if ((uintP)(void*)(ptr) & (C_CODE_ALIGNMENT-1))     \
      fehler_code_alignment((uintP)(void*)(ptr),symbol)
nonreturning_function(local, fehler_code_alignment,
                      (uintP address, object symbol)) {
  fprintf(stderr,"C_CODE_ALIGNMENT is wrong. &%s = 0x%x.\n",
          TheAsciz(string_to_asciz(Symbol_name(symbol),O(terminal_encoding))),
          address);
 #if (__GNUC__ >= 3)
  fprintf(stderr,"Add -falign-functions=%d to CFLAGS in the Makefile.\n",
          C_CODE_ALIGNMENT);
 #endif
  abort();
}
#endif

# Initialization-routines for the tables
# during the first part of the initialization phase:
# initialize subr_tab:
local void init_subr_tab_1 (void) {
 #if defined(NO_TYPECODES)
  # lispbibl.d normally takes care of this, using a gcc __attribute__.
  # But __attribute__((aligned(4))) is ignored for some GCC targets,
  # so we check it here for safety.
  if (alignof(subr_t) < 4) {
    fprintf(stderr,"Alignment of SUBRs is %d. NO_TYPECODES requires it to be at least 4.\nRecompile CLISP with -DNO_TYPECODES.\n",alignof(subr_t));
    abort();
  }
 #endif
 #if defined(INIT_SUBR_TAB)
  #ifdef MAP_MEMORY_TABLES
  # copy table into the designated region:
  subr_tab = subr_tab_data;
  #endif
  #if !NIL_IS_CONSTANT
  { # initialize the name-slot first:
    var subr_t* ptr = (subr_t*)&subr_tab; # traverse subr_tab
     #define LISPFUN  LISPFUN_E
       #include "subr.c"
     #undef LISPFUN
  }
  { # and initialize the keywords-slot temporarily:
    var subr_t* ptr = (subr_t*)&subr_tab; # traverse subr_tab
    var uintC count = subr_anz;
    dotimesC(count,subr_anz, { ptr->keywords = NIL; ptr++; });
  }
  #endif
  # Because of SPVWTABF all slots except keywords and argtype
  # are already initialized.
  { # now initialize the argtype-slot:
    var subr_t* ptr = (subr_t*)&subr_tab; # traverse subr_tab
    var uintC count;
    dotimesC(count,subr_anz,{ SUBR_SET_ARGTYPE(ptr); ptr++; });
  }
 #else
  { # initialize all slots except keywords:
    var subr_t* ptr = (subr_t*)&subr_tab; # traverse subr_tab
    #define LISPFUN  LISPFUN_D
      #include "subr.c"
    #undef LISPFUN
  }
 #endif
  {
    var module_t* module;
    for_modules(all_other_modules,{
      if (*module->stab_size > 0) {
        var subr_t* ptr = module->stab; # traverse subr_tab
        var uintC count;
        dotimespC(count,*module->stab_size,{ SUBR_SET_ARGTYPE(ptr); ptr++; });
      }
    });
  }
 #ifdef MAP_MEMORY_TABLES
  { # ditto, copy other tables tino the mapped region:
    var subr_t* newptr = (subr_t*)&subr_tab;
    var module_t* module;
    main_module.stab = newptr; newptr += subr_anz;
    for_modules(all_other_modules,{
      if (*module->stab_size > 0) {
        var subr_t* oldptr = module->stab;
        var uintC count;
        module->stab = newptr;
        dotimespC(count,*module->stab_size, { *newptr++ = *oldptr++; } );
      }
    });
    ASSERT(newptr == (subr_t*)&subr_tab + total_subr_anz);
  }
 #endif
}
# initialize symbol_tab:
local void init_symbol_tab_1 (void) {
 #if defined(INIT_SYMBOL_TAB) && NIL_IS_CONSTANT
  #ifdef MAP_MEMORY_TABLES
  # copy table into the designated region:
  symbol_tab = symbol_tab_data;
  #endif
 #else
  {
    var symbol_* ptr = (symbol_*)&symbol_tab; # traverse symbol_tab
    var uintC count;
    for (count = symbol_anz; count > 0; count--) {
      ptr->GCself = symbol_tab_ptr_as_object(ptr);
     #ifndef TYPECODES
      ptr->tfl = xrecord_tfl(Rectype_Symbol,0,5,0);
     #endif
      ptr->symvalue = unbound;
      ptr->symfunction = unbound;
      ptr->proplist = NIL;
      ptr->pname = NIL;
      ptr->homepackage = NIL;
      ptr++;
    }
  }
 #endif
}
# initialize object_tab:
local void init_object_tab_1 (void) {
  var module_t* module;
 #if defined(INIT_OBJECT_TAB) && NIL_IS_CONSTANT # object_tab already pre-initialized?
  for_modules(all_other_modules,{
    if (*module->otab_size > 0) {
      var gcv_object_t* ptr = module->otab; # traverse object_tab
      var uintC count;
      dotimespC(count,*module->otab_size, { *ptr++ = NIL; });
    }
  });
 #else
  for_modules(all_modules,{
    if (*module->otab_size > 0) {
      var gcv_object_t* ptr = module->otab; # traverse object_tab
      var uintC count;
      dotimespC(count,*module->otab_size, { *ptr++ = NIL; });
    }
  });
 #endif
  O(all_weakpointers) = Fixnum_0;
  O(all_weakkvtables) = Fixnum_0;
  O(all_finalizers) = Fixnum_0; O(pending_finalizers) = Fixnum_0;
}
# initialize other modules coarsely:
local void init_other_modules_1 (void) {
  var module_t* module;
  for_modules(all_other_modules, {
    # fill pointer in the subr-table with NIL, for GC to become possible:
    if (*module->stab_size > 0) {
      var subr_t* ptr = module->stab;
      var uintC count;
      dotimespC(count,*module->stab_size,
      { ptr->name = NIL; ptr->keywords = NIL; ptr++; });
    }
    # the pointers in the object-table have already been inizialized
    # by init_object_tab_1().
  });
}

# Initialization-routines for the tables
# during the second part of the initialization phase:
# finish initialization of subr_tab: enter keyword-vectors.
local void init_subr_tab_2 (void) {
#if 0
  # I would love to have a simple solution here, but
  # TURBO-C doesn't get enough memory for compilation!
  # traverse subr_tab
  var object vec;
  var gcv_object_t* vecptr;
 #define LISPFUN  LISPFUN_H
  #define kw(name)  *vecptr++ = S(K##name)
  #include "subr.c"
  #undef LISPFUN
 #undef kw
#else
  # create keyword-vectors individually:
  var object vec;
  var gcv_object_t* vecptr;
  # fills another single keyword into the vector:
  #define kw(name)  *vecptr++ = S(K##name)
  # creates vector with given keywords:
  #define v(key_anz,keywords)                   \
     vec = allocate_vector(key_anz);            \
     vecptr = &TheSvector(vec)->data[0];        \
     keywords;
  # sets the vector as keyword-vector for SUBR name:
  #define s(name)  subr_tab.D_##name.keywords = vec;
  #include "subrkw.c"
  #undef s
  #undef v
  #undef kw
#endif
}
# finish initialization of symbol_tab: enter printnames and home-package.
local void init_symbol_tab_2 (void) {
  # table of printnames:
  local const char * const pname_table[symbol_anz] = {
    #define LISPSYM  LISPSYM_C
    #include "constsym.c"
    #undef LISPSYM
  };
  # table of packages:
  enum { # the values in this enum are 0,1,2,...
    enum_lisp_index,
    enum_user_index,
    enum_system_index,
    enum_keyword_index,
    enum_charset_index,
    #define LISPPACK  LISPPACK_A
    #include "constpack.c"
    #undef LISPPACK
    enum_dummy_index
  };
  #define package_anz  ((uintL)enum_dummy_index)
  local const uintB package_index_table[symbol_anz] = {
    #define LISPSYM  LISPSYM_D
    #include "constsym.c"
    #undef LISPSYM
  };
  {
    var object list = O(all_packages); # list of packages
    # shortly after the initialization:
    # (#<PACKAGE LISP> #<PACKAGE SYSTEM> #<PACKAGE KEYWORD> #<PACKAGE CHARSET> ...)
    var uintC count;
    dotimespC(count,package_anz, { pushSTACK(Car(list)); list = Cdr(list); });
  }
  {
    var symbol_* ptr = (symbol_*)&symbol_tab; # traverse symbol_tab
    var const char * const * pname_ptr = &pname_table[0]; # traverse pname_table
    var const uintB* index_ptr = &package_index_table[0]; # traverse package_index_table
    var uintC count = symbol_anz;
    do {
      ptr->pname =
        coerce_imm_ss(' ' == **pname_ptr # non-ASCII
                      ? asciz_to_string(*pname_ptr+1, # skip ' '
                                        Symbol_value(S(utf_8)))
                      : ascii_to_string(*pname_ptr));
      pname_ptr++;
      var uintB index = *index_ptr++;
      var gcv_object_t* package_ = &STACK_(package_anz-1) STACKop -(uintP)index; # Pointer auf Package
      pushSTACK(symbol_tab_ptr_as_object(ptr)); # Symbol
      import(&STACK_0,package_); # first, import normally
      if (index == (uintB)enum_lisp_index # in #<PACKAGE LISP>?
          || index == (uintB)enum_charset_index # in #<PACKAGE CHARSET>?
          || index == (uintB)enum_socket_index
          || index == (uintB)enum_custom_index)
        { export(&STACK_0,package_); } # yes -> also export
      Symbol_package(popSTACK()) = *package_; # and set the home-package
      ptr++;
    } while (--count != 0);
    skipSTACK(package_anz);
  }
}
# enter FSUBRs/SUBRs into their symbols:
local void init_symbol_functions (void) {
  { # enter FSUBRs:
    typedef struct {
      #if defined(INIT_SUBR_TAB) && NIL_IS_CONSTANT
        #define LISPSPECFORM LISPSPECFORM_F
        object name;
        #define fsubr_name(p)  (p)->name
      #else
        #define LISPSPECFORM LISPSPECFORM_E
        uintL name_offset;
        #define fsubr_name(p)  symbol_tab_ptr_as_object((char*)&symbol_tab+(p)->name_offset)
      #endif
      uintW req_anz;
      uintW opt_anz;
      uintW body_flag;
    } fsubr_data_t;
    local const fsubr_data_t fsubr_data_tab[] = {
      #include "fsubr.c"
    };
    #undef LISPSPECFORM
    var const fsubr_t* ptr1 = (const fsubr_t *)&fsubr_tab; # traverse fsubr_tab
    var const fsubr_data_t * ptr2 = &fsubr_data_tab[0]; # traverse fsubr_data_tab
    var uintC count;
    dotimesC(count,fsubr_anz,{
      var object sym = fsubr_name(ptr2);
      var object obj = allocate_fsubr();
      TheFsubr(obj)->name = sym;
      TheFsubr(obj)->argtype = fixnum((uintW)fsubr_argtype(ptr2->req_anz,ptr2->opt_anz,(fsubr_body_t)(ptr2->body_flag)));
      TheFsubr(obj)->function = (void*)(*ptr1);
      Symbol_function(sym) = obj;
      verify_code_alignment(*ptr1,sym);
      ptr1++; ptr2++;
    });
  }
  { # enter SUBRs:
    var subr_t* ptr = (subr_t*)&subr_tab; # traverse subr_tab
    var uintC count;
    dotimesC(count,subr_anz,{
      Symbol_function(ptr->name) = subr_tab_ptr_as_object(ptr);
      verify_code_alignment(ptr->function,ptr->name);
      ptr++;
    });
  }
}
# assign values to constants/variables:
local void init_symbol_values (void) {
  # helper macro: constant := value+1
  #define define_constant_UL1(symbol,value)                     \
    do { var object x = # value+1 as integer                    \
           ( ((uintL)(value) < (uintL)(bitm(oint_data_len)-1))  \
                ? fixnum(value+1)                               \
                : I_1_plus_I(UL_to_I(value))                    \
            );                                                  \
          define_constant(symbol,x);                            \
    } while(0)
  # common:
  define_constant(S(nil),S(nil));                 # NIL := NIL
  define_constant(S(t),S(t));                     # T := T
  define_variable(S(gc_statistics_stern),Fixnum_minus1); # SYS::*GC-STATISTICS* := -1
  # for EVAL/CONTROL:
  define_constant_UL1(S(lambda_parameters_limit),lp_limit_1); # LAMBDA-PARAMETERS-LIMIT := lp_limit_1 + 1
  define_constant_UL1(S(call_arguments_limit),ca_limit_1); # CALL-ARGUMENTS-LIMIT := ca_limit_1 + 1
  define_constant(S(multiple_values_limit),fixnum(mv_limit)); # MULTIPLE-VALUES-LIMIT := mv_limit
  define_constant(S(jmpbuf_size),fixnum(jmpbufsize)); # SYS::*JMPBUF-SIZE* := size of a jmp_buf
  define_constant(S(big_endian),(BIG_ENDIAN_P ? T : NIL)); # SYS::*BIG-ENDIAN* := NIL resp. T
  define_variable(S(macroexpand_hook),L(funcall)); # *MACROEXPAND-HOOK* := #'FUNCALL
  define_variable(S(evalhookstern),NIL);          # *EVALHOOK*
  define_variable(S(applyhookstern),NIL);         # *APPLYHOOK*
  # for PACKAGE:
  define_variable(S(packagestern),Car(O(all_packages))); # *PACKAGE* := '#<PACKAGE LISP>
  # for SYMBOL:
  define_variable(S(gensym_counter),Fixnum_1);    # *GENSYM-COUNTER* := 1
  # for PATHNAME:
  define_variable(S(merge_pathnames_ansi),NIL); # *MERGE-PATHNAMES-ANSI*
  # for LISPARIT:
  init_arith(); # defines the following:
  # define_variable(S(pi),);                      # PI
  # define_constant(S(most_positive_fixnum),);    # MOST-POSITIVE-FIXNUM
  # define_constant(S(most_negative_fixnum),);    # MOST-NEGATIVE-FIXNUM
  # define_constant(S(most_positive_short_float),); # MOST-POSITIVE-SHORT-FLOAT
  # define_constant(S(least_positive_short_float),); # LEAST-POSITIVE-SHORT-FLOAT
  # define_constant(S(least_negative_short_float),); # LEAST-NEGATIVE-SHORT-FLOAT
  # define_constant(S(most_negative_short_float),); # MOST-NEGATIVE-SHORT-FLOAT
  # define_constant(S(most_positive_single_float),); # MOST-POSITIVE-SINGLE-FLOAT
  # define_constant(S(least_positive_single_float),); # LEAST-POSITIVE-SINGLE-FLOAT
  # define_constant(S(least_negative_single_float),); # LEAST-NEGATIVE-SINGLE-FLOAT
  # define_constant(S(most_negative_single_float),); # MOST-NEGATIVE-SINGLE-FLOAT
  # define_constant(S(most_positive_double_float),); # MOST-POSITIVE-DOUBLE-FLOAT
  # define_constant(S(least_positive_double_float),); # LEAST-POSITIVE-DOUBLE-FLOAT
  # define_constant(S(least_negative_double_float),); # LEAST-NEGATIVE-DOUBLE-FLOAT
  # define_constant(S(most_negative_double_float),); # MOST-NEGATIVE-DOUBLE-FLOAT
  # define_variable(S(most_positive_long_float),); # MOST-POSITIVE-LONG-FLOAT
  # define_variable(S(least_positive_long_float),); # LEAST-POSITIVE-LONG-FLOAT
  # define_variable(S(least_negative_long_float),); # LEAST-NEGATIVE-LONG-FLOAT
  # define_variable(S(most_negative_long_float),); # MOST-NEGATIVE-LONG-FLOAT
  # define_variable(S(least_positive_normalized_long_float),); # LEAST-POSITIVE-NORMALIZED-LONG-FLOAT
  # define_variable(S(least_negative_normalized_long_float),); # LEAST-NEGATIVE-NORMALIZED-LONG-FLOAT
  # define_constant(S(short_float_epsilon),);     # SHORT-FLOAT-EPSILON
  # define_constant(S(single_float_epsilon),);    # SINGLE-FLOAT-EPSILON
  # define_constant(S(double_float_epsilon),);    # DOUBLE-FLOAT-EPSILON
  # define_variable(S(long_float_epsilon),);      # LONG-FLOAT-EPSILON
  # define_constant(S(short_float_negative_epsilon),); # SHORT-FLOAT-NEGATIVE-EPSILON
  # define_constant(S(single_float_negative_epsilon),); # SINGLE-FLOAT-NEGATIVE-EPSILON
  # define_constant(S(double_float_negative_epsilon),); # DOUBLE-FLOAT-NEGATIVE-EPSILON
  # define_variable(S(long_float_negative_epsilon),); # LONG-FLOAT-NEGATIVE-EPSILON
  # define_variable(S(read_default_float_format),); # *READ-DEFAULT-FLOAT-FORMAT*
  # define_variable(S(random_state),);            # *RANDOM-STATE*
  # for ARRAY:
  define_constant_UL1(S(array_total_size_limit),arraysize_limit_1); # ARRAY-TOTAL-SIZE-LIMIT := arraysize_limit_1 + 1
  define_constant_UL1(S(array_dimension_limit),arraysize_limit_1); # ARRAY-DIMENSION-LIMIT := arraysize_limit_1 + 1
  define_constant_UL1(S(array_rank_limit),arrayrank_limit_1); # ARRAY-RANK-LIMIT := arrayrank_limit_1 + 1
  # for CHARSTRG:
  define_constant(S(char_cod_limit),fixnum(char_code_limit)); # CHAR-CODE-LIMIT
  define_constant(S(base_char_cod_limit),fixnum(base_char_code_limit)); # BASE-CHAR-CODE-LIMIT
  define_variable(S(coerce_fixnum_char_ansi),NIL); # LISP:*COERCE-FIXNUM-CHAR-ANSI*
  # for SEQUENCE:
  define_variable(S(sequence_count_ansi),NIL); # LISP:*SEQUENCE-COUNT-ANSI*
  # for DEBUG:
  define_variable(S(plus),NIL);                   # +
  define_variable(S(plus2),NIL);                  # ++
  define_variable(S(plus3),NIL);                  # +++
  define_variable(S(minus),NIL);                  # -
  define_variable(S(mal),NIL);                    # *
  define_variable(S(mal2),NIL);                   # **
  define_variable(S(mal3),NIL);                   # ***
  define_variable(S(durch),NIL);                  # /
  define_variable(S(durch2),NIL);                 # //
  define_variable(S(durch3),NIL);                 # ///
  define_variable(S(driverstern),NIL);            # *DRIVER* := NIL
  define_variable(S(break_driver),NIL);           # *BREAK-DRIVER* := NIL
  define_variable(S(break_count),Fixnum_0);       # SYS::*BREAK-COUNT* := 0
  define_variable(S(recurse_count_standard_output),Fixnum_0); # SYS::*RECURSE-COUNT-STANDARD-OUTPUT* := 0
  define_variable(S(recurse_count_debug_io),Fixnum_0); # SYS::*RECURSE-COUNT-DEBUG-IO* := 0
  # for STREAM:
  # later: init_streamvars(); # defines the following:
  # define_variable(S(standard_input),);          # *STANDARD-INPUT*
  # define_variable(S(standard_output),);         # *STANDARD-OUTPUT*
  # define_variable(S(error_output),);            # *ERROR-OUTPUT*
  # define_variable(S(query_io),);                # *QUERY-IO*
  # define_variable(S(debug_io),);                # *DEBUG-IO*
  # define_variable(S(terminal_io),);             # *TERMINAL-IO*
  # define_variable(S(trace_output),);            # *TRACE-OUTPUT*
  # define_variable(S(keyboard_input),);          # *KEYBOARD-INPUT*
  define_variable(S(default_pathname_defaults),unbound); # *DEFAULT-PATHNAME-DEFAULTS*
  # for IO:
  init_reader(); # defines the following:
  # define_variable(S(read_base),);               # *READ-BASE* := 10
  # define_variable(S(read_suppress),);           # *READ-SUPPRESS* := NIL
  # define_variable(S(read_eval),);               # *READ-EVAL* := T
  # define_variable(S(readtablestern),);          # *READTABLE*
  define_variable(S(read_preserve_whitespace),unbound); # SYS::*READ-PRESERVE-WHITESPACE*
  define_variable(S(read_recursive_p),unbound);   # SYS::*READ-RECURSIVE-P*
  define_variable(S(read_reference_table),unbound); # SYS::*READ-REFERENCE-TABLE*
  define_variable(S(backquote_level),unbound);    # SYS::*BACKQUOTE-LEVEL*
  define_variable(S(compiling),NIL);              # SYS::*COMPILING* ;= NIL
  define_variable(S(print_case),S(Kupcase));      # *PRINT-CASE* := :UPCASE
  define_variable(S(print_level),NIL);            # *PRINT-LEVEL* := NIL
  define_variable(S(print_length),NIL);           # *PRINT-LENGTH* := NIL
  define_variable(S(print_gensym),T);             # *PRINT-GENSYM* := T
  define_variable(S(print_escape),T);             # *PRINT-ESCAPE* := T
  define_variable(S(print_radix),NIL);            # *PRINT-RADIX* := NIL
  define_variable(S(print_base),fixnum(10));      # *PRINT-BASE* := 10
  define_variable(S(print_array),T);              # *PRINT-ARRAY* := T
  define_variable(S(print_circle),NIL);           # *PRINT-CIRCLE* := NIL
  define_variable(S(print_pretty),NIL);           # *PRINT-PRETTY* := NIL
  define_variable(S(print_closure),NIL);          # *PRINT-CLOSURE* := NIL
  define_variable(S(print_readably),NIL);         # *PRINT-READABLY* := NIL
  define_variable(S(print_lines),NIL);            # *PRINT-LINES* := NIL
  define_variable(S(print_miser_width),NIL);      # *PRINT-MISER-WIDTH* := NIL
  define_variable(S(prin_line_prefix),unbound);   # *PRIN-LINE-PREFIX*
  define_variable(S(prin_miserp),unbound);        # *PRIN-MISERP*
  define_variable(S(prin_pprinter),unbound);      # *PRIN-PPRINTER*
  define_variable(S(prin_indentation),unbound);   # *PRIN-INDENTATION*
  define_variable(S(print_pprint_dispatch),NIL);  # *PRINT-PPRINT-DISPATCH* := NIL
  define_variable(S(print_right_margin),NIL);     # *PRINT-RIGHT-MARGIN* := NIL
  define_variable(S(print_rpars),NIL);            # *PRINT-RPARS* := NIL
  define_variable(S(print_indent_lists),fixnum(1)); # *PRINT-INDENT-LISTS* := 1
  define_variable(S(print_pretty_fill),NIL);      # *PRINT-PRETTY-FILL* := NIL
  define_variable(S(print_circle_table),unbound); # SYS::*PRINT-CIRCLE-TABLE*
  define_variable(S(prin_level),unbound);         # SYS::*PRIN-LEVEL*
  define_variable(S(prin_lines),unbound);         # SYS::*PRIN-LINES*
  define_variable(S(prin_stream),unbound);        # SYS::*PRIN-STREAM*
  define_variable(S(prin_linelength),fixnum(79)); # SYS::*PRIN-LINELENGTH* := 79 (preliminarily)
  define_variable(S(prin_l1),unbound);            # SYS::*PRIN-L1*
  define_variable(S(prin_lm),unbound);            # SYS::*PRIN-LM*
  define_variable(S(prin_rpar),unbound);          # SYS::*PRIN-RPAR*
  define_variable(S(prin_traillength),unbound);   # SYS::*PRIN-TRAILLENGTH*
  define_variable(S(prin_prev_traillength),unbound); # SYS::*PRIN-PREV-TRAILLENGTH*
  define_variable(S(prin_jblocks),unbound);       # SYS::*PRIN-JBLOCKS*
  define_variable(S(prin_jbstrings),unbound);     # SYS::*PRIN-JBSTRINGS*
  define_variable(S(prin_jbmodus),unbound);       # SYS::*PRIN-JBMODUS*
  define_variable(S(prin_jblpos),unbound);        # SYS::*PRIN-JBLPOS*
  define_variable(S(terminal_read_open_object),unbound); # SYS::*TERMINAL-READ-OPEN-OBJECT*
  define_variable(S(terminal_read_stream),unbound); # SYS::*TERMINAL-READ-STREAM*
  define_variable(S(pprint_first_newline),T);     # CUSTOM:*PPRINT-FIRST-NEWLINE*
  define_variable(S(print_symbols_long),NIL);     # CUSTOM:*PRINT-SYMBOLS-LONG*
  define_variable(S(print_pathnames_ansi),NIL);   # CUSTOM:*PRINT-PATHNAMES-ANSI*
  define_variable(S(parse_namestring_ansi),NIL);  # CUSTOM:*PARSE-NAMESTRING-ANSI*
 #ifdef PATHNAME_NOEXT
  define_variable(S(parse_namestring_dot_file),S(Ktype)); # CUSTOM:*PARSE-NAMESTRING-DOT-FILE*
 #endif
  define_variable(S(deftype_depth_limit),NIL);    # CUSTOM:*DEFTYPE-DEPTH-LIMIT*
 #if defined(WIN32_NATIVE) || defined(UNIX_CYGWIN32)
  define_variable(S(device_prefix),NIL); # CUSTOM:*DEVICE-PREFIX*
 #endif
  # for EVAL:
  define_variable(S(evalhookstern),NIL);          # *EVALHOOK* := NIL
  define_variable(S(applyhookstern),NIL);         # *APPLYHOOK* := NIL
  # for MISC:
  define_constant(S(internal_time_units_per_second),  # INTERNAL-TIME-UNITS-PER-SECOND
                  fixnum(ticks_per_second) ); # := 200 resp. 1000000
  # for PREDTYPE:
  define_variable(S(recurse_count_gc_statistics),Fixnum_0); # SYS::*RECURSE-COUNT-GC-STATISTICS* := 0
  # for ERROR:
  define_variable(S(use_clcs),NIL);               # SYS::*USE-CLCS* := NIL
  define_variable(S(recursive_error_count),Fixnum_0); # SYS::*RECURSIVE-ERROR-COUNT* := 0
  define_variable(S(error_handler),NIL);          # *ERROR-HANDLER* := NIL
  # for SPVW:
  define_variable(S(init_hooks),NIL);             # SYS::*INIT-HOOKS* := NIL
  define_variable(S(quiet),NIL);                  # SYS::*QUIET* := NIL
  define_variable(S(args),NIL);                   # EXT:*ARGS* := NIL
  define_variable(S(load_compiling),NIL); /* *LOAD-COMPILING* := NIL */
  define_variable(S(load_verbose),T); /* *LOAD-VERBOSE* := T */
  define_variable(S(load_print),NIL); /* *LOAD-PRINT* := NIL */
  define_variable(S(compile_print),NIL); /* *COMPILE-PRINT* := NIL */
  # for FOREIGN:
 #ifdef DYNAMIC_FFI
  define_constant(S(fv_flag_readonly),fixnum(fv_readonly));  # FFI::FV-FLAG-READONLY
  define_constant(S(fv_flag_malloc_free),fixnum(fv_malloc)); # FFI::FV-FLAG-MALLOC-FREE
  define_constant(S(ff_flag_alloca),fixnum(ff_alloca));      # FFI::FF-FLAG-ALLOCA
  define_constant(S(ff_flag_malloc_free),fixnum(ff_malloc)); # FFI::FF-FLAG-MALLOC-FREE
  define_constant(S(ff_flag_out),fixnum(ff_out));            # FFI::FF-FLAG-OUT
  define_constant(S(ff_flag_in_out),fixnum(ff_inout));       # FFI::FF-FLAG-IN-OUT
  define_constant(S(ff_language_asm),fixnum(ff_lang_asm));       # FFI::FF-LANGUAGE-ASM
  define_constant(S(ff_language_c),fixnum(ff_lang_c));           # FFI::FF-LANGUAGE-C
  define_constant(S(ff_language_ansi_c),fixnum(ff_lang_ansi_c)); # FFI::FF-LANGUAGE-ANSI-C
  define_constant(S(ff_language_stdcall),fixnum(ff_lang_stdcall)); # FFI::FF-LANGUAGE-STDCALL
 #endif
  # for PATHNAME:
 #ifdef LOGICAL_PATHNAMES
  { # SYS::*LOGICAL-PATHNAME-TRANSLATIONS* := (MAKE-HASH-TABLE :TEST #'EQUALP)
    pushSTACK(S(Ktest)); pushSTACK(L(equalp)); funcall(L(make_hash_table),2);
    define_variable(S(logpathname_translations),value1);
  }
  O(empty_logical_pathname) = allocate_logpathname();
 #endif
  # initialize *DEFAULT-PATHNAME-DEFAULTS* preliminarily:
  define_variable(S(default_pathname_defaults),allocate_pathname());
 #undef define_constant_UL1
}
# create other objects and fill object table:
local void init_object_tab (void) {
  # table with initialization strings:
  local var const char * const object_initstring_tab [] = {
    #define LISPOBJ LISPOBJ_C
    #include "constobj.c"
    #undef LISPOBJ
  };
  { # initialize *FEATURES* :
    var const char * features_initstring =
      "(:CLISP :ANSI-CL :COMMON-LISP :LISP=CL :INTERPRETER"
     #ifdef DEBUG_SPVW
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
     #ifdef EXPORT_SYSCALLS
      " :SYSCALLS"
     #endif
     #ifdef DIR_KEY
      " :DIR-KEY"
     #endif
     #ifdef AMIGA
      " :AMIGA"
     #endif
     #ifdef PC386
      " :PC386"
     #endif
     #ifdef MSDOS
      #ifdef OS2
      " :OS/2"
      #else
      " :DOS"
      #endif
     #endif
     #ifdef RISCOS
      " :ACORN-RISCOS"
     #endif
     #ifdef UNIX
      " :UNIX"
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
    define_variable(S(features),list);             # *FEATURES*
  }
  { # read objects from the strings:
    var gcv_object_t* objptr = (gcv_object_t*)&object_tab; # traverse object_tab
    var const char * const * stringptr = &object_initstring_tab[0]; # traverse string table
    var uintC count;
    dotimesC(count,object_anz,{
      var const char * string = *stringptr++;
      if (*string == '@') {
        # no READ-FROM-STRING for LISPOBJ_L && GNU_GETTEXT
        *objptr = asciz_to_string(&string[1],O(internal_encoding));
      } else {
        pushSTACK(asciz_to_string(string,O(internal_encoding))); # string
        funcall(L(make_string_input_stream),1); # pack into stream
        pushSTACK(value1);
        var object obj = stream_read(&STACK_0,NIL,NIL); # read object
        skipSTACK(1);
        if (!eq(obj,dot_value)) { *objptr = obj; } # and store (except ".")
      }
      objptr++;
    });
  }
  # build toplevel-declaration-environment
  Car(O(top_decl_env)) = O(declaration_types);
}
# manual initialization of all LISP-data:
local void initmem (void) {
  init_symbol_tab_1(); # initialize symbol_tab
  init_object_tab_1(); # initialize object_tab
  init_other_modules_1(); # initialize other modules coarsely
  {
    aktenv.var_env = NIL; aktenv.fun_env = NIL; aktenv.block_env = NIL;
    aktenv.go_env = NIL; aktenv.decl_env = NIL;
  }
  # Now the tables are coarsely initialized,
  # nothing can happen at GC.
  # finish initialization of subr_tab:
  init_subr_tab_2();
  # initialize packages:
  init_packages();
  init_encodings_1(); # init some encodings (utf_8 for init_symbol_tab_2)
  # finish initialization of symbol_tab:
  init_symbol_tab_2();
  init_encodings_2(); # init the rest of encodings
  # enter SUBRs/FSUBRs into their symbols:
  init_symbol_functions();
  # constants/variables: enter value into the symbols:
  init_symbol_values();
  # create other objects:
  init_object_tab();
}
# loading of MEM-file:
local void loadmem (const char* filename); # see below
# initialization of the other, not yet initialized modules:
local void init_other_modules_2 (void);
local void init_module_2 (module_t* module) {
  # pre-initialize subr_tab, object_tab, so that GC becomes possible:
  if (*module->stab_size > 0) {
    var subr_t* ptr = module->stab; # traverse subr_tab
    var uintC count;
    dotimespC(count,*module->stab_size,
    { ptr->name = NIL; ptr->keywords = NIL; ptr++; });
  }
  if (*module->otab_size > 0) {
    var gcv_object_t* ptr = module->otab; # traverse object_tab
    var uintC count;
    dotimespC(count,*module->otab_size, { *ptr++ = NIL; });
  }
  # now, GC my see this subr_tab, object_tab:
  module->initialized = true;
  # enter Subr-symbols:
  if (*module->stab_size > 0) {
    var subr_t* subr_ptr = module->stab;
    var const subr_initdata_t* init_ptr = module->stab_initdata;
    var uintC count;
    dotimespC(count,*module->stab_size,{
      var const char* packname = init_ptr->packname;
      var object symname = asciz_to_string(init_ptr->symname,O(internal_encoding));
      var object symbol;
      if (packname==NULL) {
        symbol = make_symbol(symname);
      } else {
        var object pack =
          find_package(asciz_to_string(packname,O(internal_encoding)));
        if (nullp(pack)) { # package not found?
          fprintf(stderr,GETTEXTL("module `%s' requires package %s." NLstring),
                  module->name, packname);
          quit_sofort(1);
        }
        intern(symname,pack,&symbol);
      }
      subr_ptr->name = symbol; # complete Subr
      Symbol_function(symbol) = subr_tab_ptr_as_object(subr_ptr); # define function
      init_ptr++; subr_ptr++;
    });
  }
  # enter objects:
  if (*module->otab_size > 0) {
    var gcv_object_t* object_ptr = module->otab;
    var const object_initdata_t* init_ptr = module->otab_initdata;
    var uintC count;
    dotimespC(count,*module->otab_size, {
      pushSTACK(asciz_to_string(init_ptr->initstring,O(internal_encoding))); # string
      funcall(L(make_string_input_stream),1); # pack into stream
      pushSTACK(value1);
      *object_ptr = stream_read(&STACK_0,NIL,NIL); # read object
      skipSTACK(1);
      object_ptr++; init_ptr++;
    });
  }
  # call initialization function:
  (*module->initfunction1)(module);
}
local void init_other_modules_2 (void) {
  var module_t* module; # traverse modules
  for_modules(all_other_modules,{
    if (!module->initialized)
      init_module_2(module);
  });
}

# print usage and exit
nonreturning_function (local, usage, (int exit_code)) {
  printf(GETTEXTL("GNU CLISP (http://clisp.cons.org/) is an ANSI Common Lisp."
                  NLstring "Usage:  "));
  printf(program_name);
  printf(GETTEXTL(" [options] [lispfile [argument ...]]" NLstring
                  " When `lispfile' is given, it is loaded and `*ARGS*' is set" NLstring
                  " to the list of argument strings. Otherwise, an interactive" NLstring
                  " read-eval-print loop is entered." NLstring));
  printf(GETTEXTL("Informative output:" NLstring));
  printf(GETTEXTL(" -h, --help    - print this help and exit" NLstring));
  printf(GETTEXTL(" --version     - print the version information" NLstring));
  printf(GETTEXTL(" --license     - print the licensing information" NLstring));
  printf(GETTEXTL("Memory image selection:" NLstring));
  printf(GETTEXTL(" -B lisplibdir - set the installation directory" NLstring));
  #ifdef UNIX
  printf(GETTEXTL(" -K linkingset - use this executable and memory image" NLstring));
  #endif
  printf(GETTEXTL(" -M memfile    - use this memory image" NLstring));
  printf(GETTEXTL(" -m size       - memory size (size = xxxxxxxB or xxxxKB or xMB)" NLstring));
  #ifndef NO_SP_MALLOC
  printf(GETTEXTL(" -s size       - stack size (size = xxxxxxxB or xxxxKB or xMB)" NLstring));
  #endif
  #ifdef MULTIMAP_MEMORY_VIA_FILE
  printf(GETTEXTL(" -t tmpdir     - temporary directory for memmap" NLstring));
  #endif
  printf(GETTEXTL("Internationalization:" NLstring));
  printf(GETTEXTL(" -L language   - set user language" NLstring));
  printf(GETTEXTL(" -N nlsdir     - NLS catalog directory" NLstring));
  printf(GETTEXTL(" -Edomain encoding - set encoding" NLstring));
  printf(GETTEXTL("Interoperability:" NLstring));
  printf(GETTEXTL(" -q, --quiet, --silent - do not print the banner" NLstring));
  printf(GETTEXTL(" -w            - wait for keypress after program termination" NLstring));
  printf(GETTEXTL(" -I            - be ILISP-friendly" NLstring));
  printf(GETTEXTL("Startup actions:" NLstring));
  printf(GETTEXTL(" -ansi         - more ANSI CL compliance" NLstring));
  printf(GETTEXTL(" -traditional  - traditional (undoes -ansi)" NLstring));
  printf(GETTEXTL(" -p package    - start in the package" NLstring));
  printf(GETTEXTL(" -C            - set *LOAD-COMPILING* to T" NLstring));
  printf(GETTEXTL(" -v, --verbose - set *LOAD-PRINT* and *COMPILE-PRINT* to T" NLstring));
  printf(GETTEXTL(" -norc         - do not load the user ~/.clisprc file" NLstring));
  printf(GETTEXTL(" -i file       - load initfile (can be repeated)" NLstring));
  printf(GETTEXTL("Actions:" NLstring));
  printf(GETTEXTL(" -c [-l] lispfile [-o outputfile] - compile LISPFILE" NLstring));
  printf(GETTEXTL(" -x expressions - execute the expressions, then exit" NLstring));
  printf(GETTEXTL(" lispfile [argument ...] - load lispfile, then exit" NLstring));
  printf(GETTEXTL("These actions put CLISP into a batch mode, which is overridden by" NLstring));
  printf(GETTEXTL(" -interactive-debug - allow interaction for failed ASSERT and friends" NLstring));
  printf(GETTEXTL(" -repl              - enter the interactive read-eval-print loop when done" NLstring));
  printf(GETTEXTL("Default action is an interactive read-eval-print loop." NLstring));
  quit_sofort (exit_code); # abnormal end of program
}

# print license and exit
nonreturning_function (local, print_license, (void)) {
  local const char * const license [] = {
    "This program is free software; you can redistribute it and/or modify" NLstring,
    "it under the terms of the GNU General Public License as published by" NLstring,
    "the Free Software Foundation; either version 2, or (at your option)"  NLstring,
    "any later version."                                                   NLstring,
                                                                           NLstring,
    "This program is distributed in the hope that it will be useful, but"  NLstring,
    "WITHOUT ANY WARRANTY; without even the implied warranty of"           NLstring,
    "MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU"    NLstring,
    "General Public License for more details."                             NLstring,
                                                                           NLstring,
    "You should have received a copy of the GNU General Public License"    NLstring,
    "along with this program; if not, write to the Free Software"          NLstring,
    "Foundation, 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA." NLstring,
                                                                           NLstring,
    "Distribution of Lisp programs meant to run in CLISP in compiled form" NLstring,
    "and without source is possible under certain conditions.  See"        NLstring,
    "http://clisp.sourceforge.net/copyright.html for details."             NLstring,
                                                                           NLstring,
  };
  var const char * const * ptr = license;
  var uintC count;
  pushSTACK(var_stream(S(standard_output),strmflags_wr_ch_B));
  dotimesC(count,sizeof(license)/sizeof(license[0]),
           { write_sstring(&STACK_0,asciz_to_string(*ptr++,O(internal_encoding)));});
  skipSTACK(1);
  quit_sofort (0);
}

# print the banner
local void print_banner ()
{ const char * const banner0[] = { # some lines above 66 characters
 #  |Column 0           |Column 20                                    |Col 66
 # "012345678901234567890123456789012345678901234567890123456789012345678901"
   "  i i i i i i i       ooooo    o        ooooooo   ooooo   ooooo" NLstring,
   "  I I I I I I I      8     8   8           8     8     o  8    8" NLstring,
  "  I  \\ `+' /  I      8         8           8     8        8    8" NLstring,
  "   \\  `-+-'  /       8         8           8      ooooo   8oooo" NLstring,
   "    `-__|__-'        8         8           8           8  8" NLstring,
   "        |            8     o   8           8     o     8  8" NLstring,
   "  ------+------       ooooo    8oooooo  ooo8ooo   ooooo   8" NLstring,
  };
  const char * const banner1[] = {
   NLstring,
   "Copyright (c) Bruno Haible, Michael Stoll 1992, 1993" NLstring,
   "Copyright (c) Bruno Haible, Marcus Daniels 1994-1997" NLstring,
   "Copyright (c) Bruno Haible, Pierpaolo Bernardi, Sam Steingold 1998" NLstring,
   "Copyright (c) Bruno Haible, Sam Steingold 1999-2003" NLstring,
  };
  #ifdef AMIGA
  var const char * banner2 =
    GETTEXT("                    Amiga version: Joerg Hoehle" NLstring);
  #endif
  #ifdef RISCOS
  var const char * banner2 =
    GETTEXT("                    RISCOS port: Peter Burwood, Bruno Haible" NLstring);
  #endif
  var const char * banner3 = NLstring ;
  var uintL offset = (posfixnum_to_L(Symbol_value(S(prin_linelength))) >= 65 ? 0 : 20);
  var const char * const * ptr = banner0;
  var uintC count;
  pushSTACK(var_stream(S(standard_output),strmflags_wr_ch_B)); # to *STANDARD-OUTPUT*
  dotimesC(count,sizeof(banner0)/sizeof(banner0[0]),
           { write_sstring(&STACK_0,asciz_to_string(&(*ptr++)[offset],O(internal_encoding))); });
  ptr = banner1;
  dotimesC(count,sizeof(banner1)/sizeof(banner1[0]),
           { write_sstring(&STACK_0,asciz_to_string(*ptr++,O(internal_encoding))); });
  #if defined(AMIGA) || defined(RISCOS)
  write_sstring(&STACK_0,asciz_to_string(&banner2[offset],O(internal_encoding)));
  #endif
  write_sstring(&STACK_0,asciz_to_string(&banner3[offset],O(internal_encoding)));
  skipSTACK(1);
}

# main program stores the name 'main'.
#ifdef NEXTAPP
  # main() already exists in Lisp_main.m
  #define main  clisp_main
#endif
#ifndef argc_t
  #define argc_t int  # Type of argc is mostly 'int'.
#endif
global const char* locale_encoding = NULL; # GNU canonical name of locale encoding
global const char* argv_encoding_misc = NULL; # override for *misc-encoding*
global const char* argv_encoding_file = NULL; # ... for *default-file-encoding*
global const char* argv_encoding_pathname = NULL; # ... for *pathname-encoding*
global const char* argv_encoding_terminal = NULL; # ... for *terminal-encoding*
global const char* argv_encoding_foreign = NULL; # ... for *foreign-encoding*
local bool argv_quiet = false; # if quiet-option is specified at start
local bool argv_wait_keypress = false;
local bool argv_license = false;
global int main (argc_t argc, char* argv[]) {
  # initialization of memory management.
  # overall procedure:
  # process command-line-options.
  # determine memory partitioning.
  # look at command string and either load LISP-data from .MEM-file
  # or create manually and initialize static LISP-data.
  # build up interrupt-handler.
  # print banner.
  # jump into the driver.
 #ifdef AMIGAOS
  init_amiga();
 #endif
 #ifdef EMUNIX
  # expand wildcards and response-files int the command line:
  _response(&argc,&argv);
  _wildcard(&argc,&argv);
 #endif
 #if defined(MSDOS) && 0 # usually unnecessary
  # access stdin and stdout in text-mode:
  begin_system_call();
  setmode(stdin_handle,O_TEXT);
  setmode(stdout_handle,O_TEXT);
  end_system_call();
 #endif
 #ifdef WIN32_NATIVE
  init_win32();
 #endif
 #ifdef RISCOS
  # disable unixlib's automatic name munging:
  __uname_control = 1;
  #if !defined(HAVE_FFI)
  # Disable save/restore of floating-point registers in setjmp(), longjmp().
  # This gives a substantial performance increase, especially in the
  # interpreter. However, it is extremely hairy: It relies on the fact
  # that we do not use floating-point operations (except possibly in ffloat.d
  # or dfloat.d - where we do not use longjmp() and do not call any C code
  # which could perform a longjmp()). This optimization is not possible
  # if we intend to call foreign functions (and maybe longjmp out of a
  # Lisp callback, thus unwinding the stack of a C function which uses
  # floating-point registers).
  { extern int __fpflag; __fpflag = 0; }
  #endif
  # Attach "delete" behaviour to the "backspace" key.
  if (!getenv("Clisp$Backspace_Backspaces")) { # this is user-configurable
    # Fix UnixLib's interpretation of the normal "delete" key being
    # delete (and "backspace" key being Ctrl-H ?? - the Emacs disease).
    struct termio tin;
    begin_system_call();
    if (!( ioctl(0,TCGETA,&tin) ==0))
      { if (!((errno==ENOTTY)||(errno==EINVAL))) { OS_error(); } }
    tin.c_cc[VERASE] = BS;
    if (!( ioctl(0,TCSETA,&tin) ==0))
      { if (!((errno==ENOTTY)||(errno==EINVAL))) { OS_error(); } }
    end_system_call();
  }
 #endif
 #ifdef UNIX
  begin_system_call();
  user_uid = getuid();
  find_executable(argv[0]);
  end_system_call();
 #endif
  var uintL argv_memneed = 0;
 #ifndef NO_SP_MALLOC
  var uintL argv_stackneed = 0;
 #endif
 #ifdef MULTIMAP_MEMORY_VIA_FILE
  var local char* argv_tmpdir = NULL;
 #endif
  var local char* argv_lisplibdir;
  var local bool argv_developer = false;
  var local char* argv_memfile = NULL;
  var local bool argv_load_compiling = false;
  var local bool argv_verbose = false;
  var local uintL argv_init_filecount = 0;
  var local bool argv_compile = false;
  var local bool argv_compile_listing = false;
  var local bool argv_norc = false;
  var local bool argv_interactive_debug = false;
  var local uintL argv_compile_filecount = 0;
  typedef struct { char* input_file; char* output_file; } argv_compile_file_t;
  var local argv_compile_file_t* argv_compile_files;
  var local char* argv_package = NULL;
  var local int argv_ansi = 0; # 0: default; 1: ANSI; 2: traditional
  var local bool argv_repl = false;
  var local uintL argv_expr_count = 0;
  var local char* argv_execute_file = NULL;
  var local char** argv_execute_args = NULL;
  var local uintL argv_execute_arg_count;
  var local char* argv_language = NULL;
  var local char* argv_localedir = NULL;
  {var DYNAMIC_ARRAY(argv_selection_array,char*,(uintL)argc); # max argc -x/-i
  var DYNAMIC_ARRAY(argv_compile_files_array,argv_compile_file_t,(uintL)argc); # maximal argc file-arguments
  argv_compile_files = argv_compile_files_array;
  if (!(setjmp(&!original_context) == 0)) goto end_of_main;
  # process arguments argv[0..argc-1] :
  #   -h              Help
  #   -m size         Memory size (size = xxxxxxxB oder xxxxKB oder xMB)
  #   -s size         Stack size (size = xxxxxxxB oder xxxxKB oder xMB)
  #   -t directory    temporary directory
  #   -B directory    set lisplibdir
  #   -K linkingset   specify executable and mem file
  #   -M file         load MEM-file
  #   -L language     set the user language
  #   -N directory    NLS catalog directory
  #   -Edomain encoding  set encoding
  #   -q              quiet: no splash-screen
  #   -norc           do not load the user ~/.clisprc file
  #   -I              ILISP-friendly
  #   -C              set *LOAD-COMPILING* to T
  #   -v --verbose    set *LOAD-PRINT* and *COMPILE-PRINT* to T
  #   -i file ...     load LISP-file for initialization
  #   -c file ...     compile LISP-files, then leave LISP
  #   -l              At compilation: create listings
  #   -p package      set *PACKAGE*
  #   -ansi           more ANSI CL Compliance
  #   -traditional    traditional (undoes -ansi)
  #   -x expr         execute LISP-expressions, then leave LISP
  #   -interactive-debug  override batch-mode for -c, -x and file
  #   -repl           enter REPL after -c, -x and file
  #   -w              wait for keypress after termination
  #   --help          print usage and exit (should be the only option)
  #   --version       print version and exit (should be the only option)
  #   file [arg ...]  load LISP-file in batch-mode and execute,
  #                   then leave LISP
  # -d -- developer mode -- undocumented, unsupported &c
  #    - unlock all packages.

  # Newly added options have to be lised:
  # - in the above table,
  # - in the usage-message here,
  # - in the options parser,
  # - in the options parser in _clisp.c,
  # - in the manual-pages _clisp.1 and _clisp.html.

  program_name = argv[0]; # argv[0] is the program name
  {
    var char** argptr = &argv[1];
    var char** argptr_limit = &argv[argc];
    var enum { for_exec, for_init, for_compile, for_expr } argv_for = for_exec;
    # loop and process options, replace processed options with NULL:
    while (argptr < argptr_limit) {
      var char* arg = *argptr++; # next argument
      if ((arg[0] == '-') && !(arg[1] == '\0')) {
        switch (arg[1]) {
          case 'h': # help
            usage ((arg[2] != 0));
            # returns after a one-character token the rest of the
            # option in arg. poss. space is skipped.
            #define OPTION_ARG                                             \
              if (arg[2] == '\0') {                                        \
                if (argptr < argptr_limit) arg = *argptr++; else usage (1);\
              } else { arg = &arg[2]; }
            # parses the rest of an option, that specifies a byte-size.
            # also checks, if certain boundaries are obeyed.
            #define SIZE_ARG(docstring,sizevar,limit_low,limit_high)       \
               # arg should consist of a few decimal places, then          \
               # maybe K or M, then maybe B or W.                          \
              do { # arg: [0-9]+[KM]?[BW]?                                 \
                var uintL val = 0;                                         \
                while ((*arg >= '0') && (*arg <= '9'))                     \
                  val = 10*val + (uintL)(*arg++ - '0');                    \
                switch (*arg) {                                            \
                  case 'k': case 'K': # in kilobytes                       \
                    val = val * 1024; arg++; break;                        \
                  case 'm': case 'M': # in megabytes                       \
                    val = val * 1024*1024; arg++; break;                   \
                }                                                          \
                switch (*arg) {                                            \
                  case 'w': case 'W': # in words                           \
                    val = val * sizeof(gcv_object_t);                      \
                  case 'b': case 'B': # in bytes                           \
                    arg++; break;                                          \
                }                                                          \
                if (*arg != '\0') { # argument finished?                   \
                  fprintf(stderr,GETTEXTL("Syntax for %s: nnnnnnn or nnnnKB or nMB" NLstring), docstring); \
                  usage (1);                                               \
                }                                                          \
                if (!((val >= limit_low) && (val <= limit_high))) {        \
                  fprintf(stderr,GETTEXTL("%s out of range" NLstring),  \
                          docstring);                                   \
                  usage (1);                                               \
                }                                                          \
                # For multiple -m resp. -s arguments, only the last counts.\
                sizevar = val;                                             \
              } while(0)
          case 'm': # memory size
           #ifdef WIN32_NATIVE
            if (arg[2]=='m' && arg[3]=='\0') # "-mm" -> print a memory map
              { DumpProcessMemoryMap(); quit_sofort(1); }
           #endif
            OPTION_ARG;
            SIZE_ARG(GETTEXTL("memory size"),argv_memneed,100000,
                     # memory size limited by:
                     (oint_addr_len+addr_shift < intLsize-1
                      # address space in oint_addr_len+addr_shift bits
                      ? bitm(oint_addr_len+addr_shift)
                      # (resp. big dummy-limit)
                      : (uintL)bit(intLsize-1)-1));
            break;
         #ifndef NO_SP_MALLOC
          case 's': # stack size
            OPTION_ARG;
            SIZE_ARG(GETTEXTL("stack size"),argv_stackneed,40000,8*1024*1024);
            break;
         #endif
         #ifdef MULTIMAP_MEMORY_VIA_FILE
          case 't': # temporary directory
            OPTION_ARG;
            if (!(argv_tmpdir == NULL)) usage (1);
            argv_tmpdir = arg;
            break;
         #endif
          case 'd': /* developer mode */
            argv_developer = true;
            if (arg[2] != '\0') usage (1);
            break;
          case 'B': # lisplibdir
            OPTION_ARG;
            if (!(argv_lisplibdir == NULL)) usage (1);
            argv_lisplibdir = arg;
            break;
          case 'n':
            if (asciz_equal(arg,"-norc"))
              argv_norc = true;
            else
              usage (1);
            break;
         #ifdef UNIX
          case 'K': # linKing set
            OPTION_ARG;
            # This option has already been digested by clisp.c.
            # We can ignore it.
            break;
         #endif
          case 'M': # MEM-file: when repeated, only the last one counts.
            OPTION_ARG;
            argv_memfile = arg;
            break;
          case 'L': # Language: when repeated, only the last one counts.
            OPTION_ARG;
            argv_language = arg;
            break;
          case 'N': # NLS-directory: when repeated, only the last one counts.
            OPTION_ARG;
            argv_localedir = arg;
            break;
          case 'E': # encoding
            if (!(argptr < argptr_limit)) usage(1);
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
            else if (arg[2] == '\0') # unspecified => all
              argv_encoding_file = argv_encoding_pathname =
                argv_encoding_terminal = argv_encoding_foreign =
                argv_encoding_misc = *argptr++;
            else
              usage(1);
            break;
          case 'q': # no copyright message
            argv_quiet = true;
            if (arg[2] != '\0') usage (1);
            break;
          case 'I': # ILISP-friendly
            ilisp_mode = true;
            if (arg[2] != '\0') usage (1);
            break;
          case 'C': # set *LOAD-COMPILING*
            argv_load_compiling = true;
            if (arg[2] != '\0') usage (1);
            break;
          case 'v': /* set *LOAD-PRINT* & *COMPILE-PRINT* */
            argv_verbose = true;
            if (!asciz_equal(&arg[1],"verbose") && arg[2] != '\0') usage (1);
            break;
          case 'r': /* -repl */
            if (asciz_equal(&arg[1],"repl"))
              argv_repl = true;
            break;
          case 'i': # initialization files
            if (arg[2] == '\0') argv_for = for_init;
            else if (asciz_equal(&arg[1],"interactive-debug"))
              argv_interactive_debug = true;
            else usage (1);
            break;
          case 'c': # files to be compiled
            argv_compile = true;
            argv_for = for_compile;
            if (arg[2] == 'l') {
              argv_compile_listing = true;
              if (arg[3] != '\0') usage (1);
            } else {
              if (arg[2] != '\0') usage (1);
            }
            break;
          case 'l': # compilation listings
            argv_compile_listing = true;
            if (arg[2] != '\0') usage (1);
            break;
          case 'o': # target for files to be compiled
            if (arg[2] != '\0') usage (1);
            OPTION_ARG;
            if (!((argv_compile_filecount > 0) &&
                  (argv_compile_files[argv_compile_filecount-1].output_file==NULL)))
              usage (1);
            argv_compile_files[argv_compile_filecount-1].output_file = arg;
            break;
          case 'p': # package: when repeated, only the last one counts.
            OPTION_ARG;
            argv_package = arg;
            break;
          case 'a': # ANSI CL Compliance
            if (asciz_equal(arg,"-ansi"))
              argv_ansi = 1; # ANSI
            else if (arg[2] != '\0') usage (1);
            else {
              fprintf(stderr,GETTEXTL("CLISP: -a is deprecated, use -ansi"
                                      NLstring));
              argv_ansi = 1; # ANSI
            }
            break;
          case 't': # traditional
            if (asciz_equal(arg,"-traditional"))
              argv_ansi = 2; # traditional
            else usage(1);
            break;
          case 'x': # execute LISP-expression
            if (arg[2] != '\0') usage (1);
            argv_for = for_expr;
            break;
          case 'w': # wait for keypress after termination
            argv_wait_keypress = true;
            if (arg[2] != '\0') usage (1);
            break;
          case '-': # -- GNU-style long options
            if (arg[2] == 0) /* "--" ==> end of options */
              goto done_with_argv;
            else if (asciz_equal(&arg[2],"help"))
              usage (0);
            else if (asciz_equal(&arg[2],"version")) {
              argv_expr_count = 0;  /* discard previous -x */
              argv_quiet = true;
              argv_norc = true;
              argv_repl = false;
              /* force processing this argument again,
                 but this time as if it came after an '-x' */
              argv_for = for_expr;
              *--argptr = "(PROGN (PRINC \"GNU CLISP \")"
                "(PRINC (LISP-IMPLEMENTATION-VERSION)) (TERPRI)"
                "(PRINC \"Features"
               #ifdef DEBUG_SPVW
                " [SAFETY=" STRINGIFY(SAFETY)
                #ifdef TYPECODES
                " TYPECODES"
                #endif
                #ifdef WIDE
                " WIDE"
                #endif
                #ifdef GENERATIONAL_GC
                " GENERATIONAL_GC"
                #endif
                "]"
               #endif
                ": \") (PRINC *FEATURES*) (TERPRI)"
                "(PRINC \"Installation directory: \")"
                "(PRINC (SYS::LIB-DIRECTORY)) (TERPRI)"
                "(PRINC \"User language: \")"
                "(PRINC (SYS::CURRENT-LANGUAGE)) (TERPRI)"
                "(SYS::%EXIT))";
              break;
            } else if (asciz_equal(&arg[2],"quiet")
                       || asciz_equal(&arg[2],"silent")) {
              argv_quiet = true; break;
            } else if (asciz_equal(&arg[2],"license")) {
              argv_license = true; break;
            } else if (asciz_equal(&arg[2],"verbose")) {
              argv_verbose = true; break;
            } else
              usage (1); # unknown option
            break;
          default: # unknown option
            usage (1);
        }
      } else if (arg[0] == 0) {  /* done with the arguments */
       done_with_argv:
        argv_execute_args = argptr;
        argv_execute_arg_count = argptr_limit - argptr;
        argptr = argptr_limit; /* abort loop */
      } else {
        # no option is interpreted as file to be loaded / compiled / executed
        switch (argv_for) {
          case for_init:
            argv_selection_array[argv_init_filecount++] = arg; break;
          case for_compile:
            argv_compile_files[argv_compile_filecount].input_file = arg;
            argv_compile_files[argv_compile_filecount].output_file = NULL;
            argv_compile_filecount++;
            break;
          case for_exec:
            argv_execute_file = arg;
            # All further arguments are arguments for argv_execute_file.
            argv_execute_args = argptr;
            argv_execute_arg_count = argptr_limit - argptr;
            # Simulate -norc. Batch scripts should be executed in an
            # environment which does not depend on files in $HOME, for
            # maximum portability.
            argv_norc = true;
            argptr = argptr_limit; # abort loop
            break;
          case for_expr:
            argv_selection_array[argc-1- argv_expr_count++] = arg; break;
          default: NOTREACHED;
        }
      }
    }
    # check options semantically and store defaults:
    if (argv_memneed == 0) {
     #if defined(SPVW_MIXED_BLOCKS_OPPOSITE) && defined(GENERATIONAL_GC)
      # Because of GENERATIONAL_GC the memory region is hardly exhausted.
      argv_memneed = 3584*1024*sizeof(gcv_object_t); # 3584 KW = 14 MB Default
     #else
      # normal
      argv_memneed = 512*1024*sizeof(gcv_object_t); # 512 KW = 2 MB Default
     #endif
    }
   #ifdef MULTIMAP_MEMORY_VIA_FILE
    if (argv_tmpdir == NULL) {
      argv_tmpdir = getenv("TMPDIR"); # try environment-variable
      if (argv_tmpdir == NULL) { argv_tmpdir = "/tmp"; }
    }
   #endif
    if (argv_memfile == NULL)
      # If no memfile is given, LOAD cannot be called with 3 arguments.
      # So disable the loading of ~/.clisprc.
      argv_norc = true;
    if (!argv_compile) {
      # Some options are useful only together with '-c' :
      if (argv_compile_listing) usage (1);
    } else {
      # Other options are useful only without '-c' :
      if (argv_expr_count) usage (1);
    }
    if (argv_expr_count && argv_execute_file) usage (1);
    # The argv_* variables now have their final values.
    # Analyze the environment variables determining the locale.
    # Deal with LC_CTYPE.
    init_ctype();
    # Deal with LC_MESSAGE.
    # (This must come last, because it may unset environment variable LC_ALL)
   #ifndef LANGUAGE_STATIC
    init_language(argv_language,argv_localedir);
   #endif
  } # option processing is over
  { # Initialize the table of relocatable pointers:
    var object* ptr2 = &pseudofun_tab.pointer[0];
    { var const Pseudofun* ptr1 = (const Pseudofun*)&pseudocode_tab;
      var uintC count;
      dotimesC(count,pseudocode_anz,
        { *ptr2++ = make_machine_code(*ptr1); ptr1++; });
    }
    { var const Pseudofun* ptr1 = (const Pseudofun*)&pseudodata_tab;
      var uintC count;
      dotimesC(count,pseudodata_anz,
        { *ptr2++ = make_machine(*ptr1); ptr1++; });
    }
  }
  # fetch memory:
  begin_system_call();
 #if (defined(SINGLEMAP_MEMORY) || defined(TRIVIALMAP_MEMORY) || defined(MULTITHREAD)) && (defined(HAVE_MMAP_ANON) || defined(HAVE_MMAP_DEVZERO) || defined(HAVE_MACH_VM) || defined(HAVE_WIN32_VM))
  mmap_init_pagesize();
 #endif
 #if defined(MULTIMAP_MEMORY) || defined(SINGLEMAP_MEMORY) || defined(TRIVIALMAP_MEMORY)
  init_map_pagesize();
 #endif
 #ifdef SPVW_PURE
  init_mem_heaptypes();
  init_objsize_table();
 #endif
 #if defined(SPVW_MIXED_BLOCKS) && defined(TYPECODES) && defined(GENERATIONAL_GC)
  init_mem_heapnr_from_type();
 #endif
  init_modules_0(); # assemble the list of modules
 #ifdef MULTITHREAD
  init_multithread();
  create_thread((void*)roughly_SP());
 #endif
  end_system_call();
 #ifdef MAP_MEMORY_TABLES
  { # calculate total_subr_anz:
    var uintC total = 0;
    var module_t* module;
    for_modules(all_modules, { total += *module->stab_size; } );
    total_subr_anz = total;
  }
 #endif
  { # partitioning of the total memory:
    #define teile             16  # 16/16
    #ifdef NO_SP_MALLOC # is SP provided by the OS?
      #define teile_SP         0
    #else
      #define teile_SP         2  # 2/16 (1/16 often is not enough)
    #endif
    #define teile_STACK      2  # 2/16
    #define teile_stacks     (teile_SP + teile_STACK)
    #ifdef SPVW_MIXED_BLOCKS
      #define teile_objects    (teile - teile_stacks)  # rest
    #else
      #define teile_objects    0
    #endif
    var uintL pagesize = # size of a page
     #if defined(MULTIMAP_MEMORY)
      map_pagesize
     #elif defined(SELFMADE_MMAP) || defined(GENERATIONAL_GC)
      mmap_pagesize
     #else # if the system-pagesize does not play a role
      teile*varobject_alignment
     #endif
      ;
    var uintL memneed = argv_memneed; # needed memory
    var aint memblock; # lower address of the provided memory block
   #if !(defined(SPVW_MIXED_BLOCKS_OPPOSITE) && !defined(TRIVIALMAP_MEMORY))
    memneed = teile_stacks*floor(memneed,teile); # do not yet calculate memory for objects
    #undef teile
    #define teile  teile_stacks
   #endif
   #ifndef NO_SP_MALLOC
    if (!(argv_stackneed==0)) {
      memneed = memneed*(teile-teile_SP)/teile;
      # the SP-size specified with option -s is not yet included in memneed.
      memneed = memneed + argv_stackneed;
    }
   #endif
   #if defined(TRIVIALMAP_MEMORY) && defined(WIN32_NATIVE)
    # Somehow the RESERVE_FOR_MALLOC limit for mallocs after prepare_zeromap()
    # seems also to encompass the mallocs before prepare_zeromap().
    # Do not know why.
    if (memneed > RESERVE_FOR_MALLOC*3/4) { memneed = RESERVE_FOR_MALLOC*3/4; }
   #endif
   #if defined(MULTIMAP_MEMORY_VIA_SHM) && (defined(UNIX_SUNOS4) || defined(UNIX_SUNOS5))
    # SunOS 4 refuses to shmat() into a previously malloc-ed region,
    # even if there is a munmap() inbetween:
    # errno = EINVAL. Also the reverse, first to shmat() and then to
    # merge the occupied region with sbrk() or brk()  into the
    # data segment, fails with errno = ENOMEM.
    # The only way out is to fetch the necessary memory from far,
    # if possible, out of reach of malloc() .
    {
      var uintL memhave = round_down(bit(oint_addr_len)-(aint)sbrk(0),SHMLBA);
      if (memhave < memneed) { memneed = memhave; }
      memblock = round_down(bit(oint_addr_len) - memneed,SHMLBA);
    }
   #else
    loop {
      memblock = (aint)mymalloc(memneed); # try to allocate memory
      if (!((void*)memblock == NULL)) break; # successful -> OK
      memneed = floor(memneed,8)*7; # else try again with 7/8 thereof
      if (memneed == 0) break;
    }
    if (memneed == 0) {
      begin_system_call();
      memblock = (aint)malloc(1);
      end_system_call();
      fprintf(stderr,GETTEXTL("Return value of malloc() = %x is not compatible with type code distribution." NLstring),
              memblock);
      goto no_mem;
    }
    if (memneed < MINIMUM_SPACE+RESERVE) { # but with less than MINIMUM_SPACE
      # we will not be satisfied:
      fprintf(stderr,GETTEXTL("Only %d bytes available." NLstring),memneed);
      goto no_mem;
    }
   #endif
   #ifdef MULTIMAP_MEMORY
    # Though we only need this address space and not its content, we must
    # not free it, as it must stay under our control.
   #endif
    { # round to the next lower page boundary:
      var uintL unaligned = (uintL)(-memblock) % pagesize;
      memblock += unaligned; memneed -= unaligned;
    }
    { # round off to the last page boundary:
      var uintL unaligned = memneed % pagesize;
      memneed -= unaligned;
    }
    # the memory region [memblock,memblock+memneed-1] is now free,
    # and its boundaries are located on page boundaries.
   #ifdef MULTIMAP_MEMORY
    #ifdef MULTIMAP_MEMORY_VIA_FILE
    if ( initmap(argv_tmpdir) <0) goto no_mem;
    #else
    if ( initmap() <0) goto no_mem;
    #endif
    multimap(case_machine: MM_TYPECASES, memblock, memneed, false);
    #ifdef MAP_MEMORY_TABLES
    { # set symbol_tab to address 0:
      var uintL memneed = round_up(sizeof(symbol_tab),pagesize); # round up length
      multimap(case_symbolflagged: , 0, memneed, false);
    }
    # set subr_tab to address 0:
    if (zeromap(&subr_tab,round_up(total_subr_anz*sizeof(subr_t),pagesize)) <0)
      goto no_mem;
    #else
    # multimap symbol_tab and subr_tab:
    # symbol_tab and subr_tab keep their address. The region, they
    # are located in (in the data segment of the program!!), becomes
    # Shared Memory resp. shared-mmap-attach . What a hack!
    # This is irreconcilable with the existence of external modules
    # (DYNAMIC_MODULES) ! ??
    {
      var aint symbol_tab_start = round_down((aint)&symbol_tab,pagesize);
      var aint symbol_tab_end = round_up((aint)&symbol_tab+sizeof(symbol_tab),pagesize);
      var aint subr_tab_start = round_down((aint)&subr_tab,pagesize);
      var aint subr_tab_end = round_up((aint)&subr_tab+sizeof(subr_tab),pagesize);
      if ((symbol_tab_end <= subr_tab_start)
          || (subr_tab_end <= symbol_tab_start)) {
        # two distinct intervals
        multimap(case_machine: case_symbolflagged: , symbol_tab_start, symbol_tab_end-symbol_tab_start, true);
        multimap(case_machine: case_subr: , subr_tab_start, subr_tab_end-subr_tab_start, true);
      } else { # the tables have overlap!
        var aint tab_start = (symbol_tab_start < subr_tab_start ? symbol_tab_start : subr_tab_start);
        var aint tab_end = (symbol_tab_end > subr_tab_end ? symbol_tab_end : subr_tab_end);
        multimap(case_machine: case_symbolflagged: case_subr: , tab_start, tab_end-tab_start, true);
      }
    }
    #endif # MAP_MEMORY_TABLES
   #endif # MULTIMAP_MEMORY
   #if defined(SINGLEMAP_MEMORY) || defined(TRIVIALMAP_MEMORY) # <==> SPVW_PURE_BLOCKS || TRIVIALMAP_MEMORY
    if ( initmap() <0) goto no_mem;
    #ifdef SINGLEMAP_MEMORY
    { # pre-initialize all heaps:
      var uintL heapnr;
      for (heapnr=0; heapnr<heapcount; heapnr++) {
        var Heap* heapptr = &mem.heaps[heapnr];
        heapptr->heap_limit = (aint)type_zero_oint(heapnr);
        heapptr->heap_hardlimit = (aint)type_zero_oint(heapnr+1);
        if ((mem.heaptype[heapnr] >= -1)
            && prepare_zeromap(&heapptr->heap_limit,
                               &heapptr->heap_hardlimit,true) <0)
          goto no_mem;
      }
    }
    # set symbol_tab, subr_tab to address 0:
    # (for this purpose case_symbolflagged must be equivalent to case_symbol!)
    #define map_tab(tab,size)                                                \
      do { var uintL map_len = round_up(size,map_pagesize);                  \
           if ( zeromap(&tab,map_len) <0) goto no_mem;                       \
           mem.heaps[typecode(as_object((oint)&tab))].heap_limit += map_len; \
      } while(0)
    map_tab(symbol_tab,sizeof(symbol_tab));
    map_tab(subr_tab,total_subr_anz*sizeof(subr_t));
    #endif
    #ifdef TRIVIALMAP_MEMORY
    # initialize all heaps as empty.
    # Partition the whole available space with a ratio
    # 1:1 , if it is scarce. Otherwise, appoint the two heaps at
    # 1/5 resp. 2/5 of the address range. (An "awry" denominator,
    # in order to avoid diverse Shared-Library-regions.)
    {
      var void* malloc_addr = malloc(1);
      var aint start = round_up((aint)malloc_addr+RESERVE_FOR_MALLOC,map_pagesize); # reserve for malloc()
     #ifdef SPVW_MIXED_BLOCKS_OPPOSITE
      #if defined(SUN4_29)
      var aint end = bitm(oint_addr_len+addr_shift < 29 ? oint_addr_len+addr_shift : 29);
      mem.heaps[0].heap_limit = start + round_down(floor(end-start,5),map_pagesize);
      mem.heaps[1].heap_limit = round_down(end,map_pagesize);
      #elif defined(UNIX_LINUX) && defined(WIDE_SOFT) && !defined(SPARC)
      mem.heaps[0].heap_limit = 0x2E000000; # room until at least 0x40000000
      mem.heaps[1].heap_limit = 0x7F000000; # room until at least 0x64000000
      #else
       #ifdef TYPECODES
      var aint end = bitm(oint_addr_len+addr_shift);
       #else
      var aint end = bitm(oint_addr_len-1); # keep garcol_bit zero
       #endif
      var aint part = floor(end - (start & (end-1)),5);
      mem.heaps[0].heap_limit = start + round_down(1*part,map_pagesize);
      mem.heaps[1].heap_limit = start + round_down(4*part,map_pagesize);
      #endif
      if ( prepare_zeromap(&mem.heaps[0].heap_limit,&mem.heaps[1].heap_limit,true) <0) goto no_mem;
     #else # SPVW_MIXED_BLOCKS_STAGGERED
      #if defined(SUN4_29)
      var aint end = bitm(oint_addr_len+addr_shift < 29 ? oint_addr_len+addr_shift : 29);
      mem.heaps[0].heap_limit = start + round_down(floor(end-start,5),map_pagesize);
      mem.heaps[0].heap_hardlimit =
        mem.heaps[1].heap_limit = start + round_down(floor((end-start)*3,5),map_pagesize);
      mem.heaps[1].heap_hardlimit = end;
      #elif defined(UNIX_LINUX) && defined(WIDE_SOFT) && !defined(SPARC)
      mem.heaps[0].heap_limit = 0x2E000000; # room until at least 0x40000000
      mem.heaps[0].heap_hardlimit = 0x40000000;
      mem.heaps[1].heap_limit = 0x64000000; # room until at least 0x7F000000
      mem.heaps[1].heap_hardlimit = 0x7F000000;
      #else
       #ifdef TYPECODES
      var aint end = bitm(oint_addr_len+addr_shift);
       #else
      var aint end = (start | (bitm(garcol_bit_o)-1)) + 1; # keep garcol_bit zero
       #endif
      var aint part = floor(end - (start & (end-1)),5);
      mem.heaps[0].heap_limit = start + round_down(1*part,map_pagesize);
      mem.heaps[0].heap_hardlimit =
        mem.heaps[1].heap_limit = start + round_down(2*part,map_pagesize);
      mem.heaps[1].heap_hardlimit = start + round_down(3*part,map_pagesize);
      #endif
      if ( prepare_zeromap(&mem.heaps[0].heap_limit,&mem.heaps[1].heap_hardlimit,true) <0) goto no_mem;
     #endif
      free(malloc_addr);
    }
   #endif # TRIVIALMAP_MEMORY
    { # initialize all heaps as empty:
      var uintL heapnr;
      for (heapnr=0; heapnr<heapcount; heapnr++) {
        var Heap* heapptr = &mem.heaps[heapnr];
        heapptr->heap_start = heapptr->heap_end = heapptr->heap_limit;
       #ifdef SELFMADE_MMAP
        heapptr->memfile_numpages = 0;
        # heapptr->memfile_pages = NULL; # irrelevant
        # heapptr->memfile_offset = 0; # irrelevant
       #endif
       #ifdef GENERATIONAL_GC
        heapptr->heap_gen0_start = heapptr->heap_gen0_end =
          heapptr->heap_gen1_start = heapptr->heap_limit;
        heapptr->physpages = NULL;
       #endif
      }
    }
   #ifdef SINGLEMAP_MEMORY_STACK
    { # initialize STACK:
      var uintL map_len = round_up(memneed * teile_STACK/teile, map_pagesize);
      # The stack occupies the interval between 0 and map_len
      # for typecode = system_type:
      var aint low = (aint)type_zero_oint(system_type);
      var aint high = low + map_len;
      if ( prepare_zeromap(&low,&high,true) <0) goto no_mem;
      if ( zeromap((void*)low,map_len) <0) goto no_mem;
     #ifdef STACK_DOWN
      STACK_bound = (gcv_object_t*)low + 0x40; # 64 pointers additionally safety margin
      setSTACK(STACK = (gcv_object_t*)high); # initialize STACK
     #endif
     #ifdef STACK_UP
      setSTACK(STACK = (gcv_object_t*)low); # initialize STACK
      STACK_bound = (gcv_object_t*)high - 0x40; # 64 pointers additionally safety margin
      #endif
    }
    #undef teile_STACK
    #define teile_STACK 0  # need no more room for the STACK
    #if (teile==0)
     #undef teile
     #define teile 1  # avoid division by 0
    #endif
   #endif # SINGLEMAP_MEMORY_STACK
   #endif # SINGLEMAP_MEMORY || TRIVIALMAP_MEMORY
   #if defined(SELFMADE_MMAP) || defined(GENERATIONAL_GC)
    init_physpagesize();
   #endif
    { # divide memory block:
      var uintL free_reserved; # number of reserved bytes
     #ifndef NO_SP_MALLOC
      var void* initial_SP; # initial value for SP-stackpointer
      var uintL for_SP = 0; # number of bytes for SP-stack
      #define min_for_SP  40000 # minimal SP-stack-size
     #endif
      var uintL for_STACK; # number of bytes for Lisp-stack
      var uintL for_objects; # number of bytes for Lisp-objects
      # the STACK needs alignment, because for frame-pointers
      # the last Bit must be =0:
      #define STACK_alignment  bit(addr_shift+1)
      #define alignment  (varobject_alignment>STACK_alignment ? varobject_alignment : STACK_alignment)
      free_reserved = memneed;
      #ifndef NO_SP_MALLOC
      if (argv_stackneed != 0 && 2*argv_stackneed <= free_reserved) {
        # do not reserve to much for the SP-stack
        for_SP = round_down(argv_stackneed,varobject_alignment);
        free_reserved -= argv_stackneed;
      }
      #endif
      # make divisible by teile*alignment, so that each 1/16 is aligned:
      free_reserved = round_down(free_reserved,teile*alignment);
      free_reserved = free_reserved - RESERVE;
      {
        var uintL teil = free_reserved/teile; # a sub block, a 1/16 of the room
        var aint ptr = memblock;
        mem.MEMBOT = ptr;
        #ifdef NO_SP_MALLOC
          #ifdef UNIX_NEXTSTEP
            # Set the stack size limit to 8 MB if possible to prevent
            # crashes from machine stack overflow.
            # (If the stack is large enough, the Lisp STACK will overflow
            # first, and the error will be handled in a reasonable way.)
            { var struct rlimit rl;
              var long need = 0x800000; # 8 Megabyte
              getrlimit(RLIMIT_STACK,&rl);
              if (rl.rlim_max < need) { need = rl.rlim_max; }
              if (rl.rlim_cur < need)
                { rl.rlim_cur = need; setrlimit(RLIMIT_STACK,&rl); }
            }
          #endif
          #ifdef AMIGAOS
          { var struct Process * myprocess = (struct Process *)FindTask(NULL);
            var aint original_SP = process->pr_ReturnAddr; # SP on program start
            # the shell moves the stack size before the start to the SP.
            var aint SP_bottom = original_SP - *(ULONG*)original_SP;
            SP_bound = SP_bottom + 0x1000; # 1024 pointer safety margin
          }
          #endif
          #if defined(WIN32_NATIVE) && !defined(NO_SP_CHECK)
            # Even if the NOCOST_SP_CHECK stack overflow detection (using a
            # guard page) works, we set SP_bound.
            # Normally, the stack's `AllocationBase' is = 0x30000, the guard
            # page is 0x32000-0x32FFF, hence we can set SP_bound = 0x34000.
            { var MEMORY_BASIC_INFORMATION info;
              if (!(VirtualQuery((void*)SP(),&info,sizeof(info)) == sizeof(info))) {
                fprintf(stderr,GETTEXTL("Could not determine the end of the SP stack!" NLstring));
                SP_bound = 0;
              } else { # 0x4000 might be enough, but 0x8000 will be better.
                SP_bound = (void*)((aint)info.AllocationBase + 0x8000);
              }
            }
          #endif
        #else
          # allocate SP:
          if (for_SP==0) { # 2/16 for program stack
            for_SP = teile_SP*teil;
          } else { # room for SP is already removed.
            # teile := teile-teile_SP; # is not possible anymore, instead:
            teil = round_down(free_reserved/(teile-teile_SP),alignment);
          }
          if (for_SP < min_for_SP) { for_SP = round_up(min_for_SP,alignment); } # but not too little
          #ifdef SP_DOWN
            SP_bound = (void*)(ptr + 0x800); # 512 pointer safety margin
            ptr += for_SP;
            initial_SP = (void*)ptr;
          #endif
          #ifdef SP_UP
            initial_SP = (void*)ptr;
            ptr += for_SP;
            SP_bound = (void*)(ptr - 0x800); # 512 pointer safety margin
          #endif
        #endif
        # allocate STACK:
        #ifdef SINGLEMAP_MEMORY_STACK
        for_STACK = 0; # STACK is already allocated elsewhere.
        #else
        #ifdef STACK_DOWN
          STACK_bound = (gcv_object_t*)ptr + 0x40; # 64 pointer safety margin
          ptr += for_STACK = teile_STACK*teil; # 2/16 for Lisp-stack
          setSTACK(STACK = (gcv_object_t*)ptr); # initialize STACK
        #endif
        #ifdef STACK_UP
          setSTACK(STACK = (gcv_object_t*)ptr); # initialize STACK
          ptr += for_STACK = teile_STACK*teil; # 2/16 for Lisp-stack
          STACK_bound = (gcv_object_t*)ptr - 0x40; # 64 pointer safety margin
        #endif
        #endif
        #if defined(SPVW_MIXED_BLOCKS_OPPOSITE) && !defined(TRIVIALMAP_MEMORY)
        # now, the lisp-objects start:
        #ifdef GENERATIONAL_GC
        mem.varobjects.heap_gen0_start = mem.varobjects.heap_gen0_end =
          mem.varobjects.heap_gen1_start = mem.varobjects.heap_start =
          (ptr + (physpagesize-1)) & -physpagesize;
        #else
        mem.varobjects.heap_start = ptr;
        #endif
        mem.varobjects.heap_end = mem.varobjects.heap_start; # there are no objects of variable length, yet
        # rest (14/16 or a little less) for lisp-objects:
        for_objects = memblock+free_reserved - ptr; # about = teile_objects*teil
        ptr += for_objects;
        #ifdef GENERATIONAL_GC
        mem.conses.heap_gen0_start = mem.conses.heap_gen0_end =
          mem.conses.heap_gen1_end = mem.conses.heap_end =
          ptr & -physpagesize;
        #else
        mem.conses.heap_end = ptr;
        #endif
        mem.conses.heap_start = mem.conses.heap_end; # there are no conses yet
        # ptr = memblock+free_reserved, because 2/16 + 14/16 = 1
        # allocate memory reserve:
        ptr += RESERVE;
        # upper memory limit reached.
        mem.MEMTOP = ptr;
        # above (far away) the machine stack.
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
        mem.free_pages = NULL;
        mem.total_space = 0;
        mem.used_space = 0;
        mem.last_gcend_space = 0;
        mem.gctrigger_space = 0;
        #endif
        # initialize stacks:
        #ifndef NO_SP_MALLOC
          #ifdef GNU
            # a little dummy-action, that prevents a delayed clean up of SP
            # at a later date:
            if (mem.MEMBOT) { printf(""); }
          #endif
          setSP(initial_SP); # set SP! All local variables get lost!
        #endif
        #ifdef NOCOST_SP_CHECK
          install_stackoverflow_handler(0x4000); # 16 KB reserve should be enough
        #endif
        pushSTACK(nullobj); pushSTACK(nullobj); # two nullpointer as STACK end marker
      }
    }
  }
 #ifdef DEBUG_SPVW
  { /* STACK & SP are settled - check that we have enough STACK */
    var uintL stack_depth =
      STACK_item_count((gcv_object_t*)STACK_bound,STACK)/sizeof(*STACK);
    fprintf(stderr,"STACK depth: %d\n",stack_depth);
   #ifndef NO_SP_CHECK
    fprintf(stderr,"SP depth: %d\n",
            STACK_item_count((SPint*)SP_bound,(SPint*)SP())/sizeof(SPint));
   #endif
    if (stack_depth < ca_limit_1) {
      fprintf(stderr,"STACK depth is less than CALL-ARGUMENTS-LIMIT (%d)\n",
              ca_limit_1);
      abort();
    }
  }
 #endif
  init_subr_tab_1(); # initialize subr_tab
  if (argv_memfile==NULL) # manual initialization:
    initmem();
  else # load memory file:
    loadmem(argv_memfile);
  # init O(current_language)
  O(current_language) = current_language_o(language);
  # set current evaluator-environments to the toplevel-value:
  aktenv.var_env   = NIL;
  aktenv.fun_env   = NIL;
  aktenv.block_env = NIL;
  aktenv.go_env    = NIL;
  aktenv.decl_env  = O(top_decl_env);
  # everything completely initialized.
 {var struct backtrace_t bt = { NULL, L(driver), STACK, -1 };
  back_trace = &bt;
  clear_break_sems(); set_break_sem_1();
  begin_system_call();
  # establish interrupt-handler:
 #if defined(HAVE_SIGNALS) && defined(SIGWINCH) && !defined(NO_ASYNC_INTERRUPTS)
  install_sigwinch_handler();
 #endif
  # query the size of the terminal-window also now on program start:
 #if defined(HAVE_SIGNALS)
  update_linelength();
 #endif
 #if defined(MSDOS)
  # the width of the screen in current screen-mode
  # query now on program start:
  if (isatty(stdout_handle)) { # standard-output a terminal?
    extern uintW v_cols(); # see STREAM.D
    var int scrsize[2];
    var uintL columns;
    columns = (_scrsize(&!scrsize), scrsize[0]);
    if (columns > 0) { # change value of SYS::*PRIN-LINELENGTH* :
      Symbol_value(S(prin_linelength)) = fixnum(columns-1);
    }
  }
 #elif defined(WIN32_NATIVE)
 # cannot do it in init_win32 - too early
 if (isatty(stdout_handle)) {
   var HANDLE handle = GetStdHandle(STD_OUTPUT_HANDLE);
   if (handle!=INVALID_HANDLE_VALUE) {
     var CONSOLE_SCREEN_BUFFER_INFO info;
     if (GetConsoleScreenBufferInfo(handle,&info))
       Symbol_value(S(prin_linelength)) = fixnum(info.dwSize.X - 1);
   }
 }
 #endif
 #if defined(AMIGAOS) && 0
  # ask the console.driver ??
  if (IsInteractive(stdin_handle) && IsInteractive(stdout_handle)) { # ??
    var uintL len;
    var uintB question[4] = { CSI, '0', ' ', 'q' };
    var uintB response[30+1];
    Write(stdout_handle,question,4);
    len = Read(stdin_handle,response,30);
    response[len] = `\0`; sscanf(&response[5],"%d;%d", &lines, &columns); # ??
  }
 #endif
 #if (defined(HAVE_SIGNALS) && (defined(UNIX) || defined(EMUNIX) || defined(RISCOS))) || defined(WIN32_NATIVE)
  # install Ctrl-C-Handler:
  install_sigint_handler();
 #endif
 #if defined(SELFMADE_MMAP) || defined(GENERATIONAL_GC)
  # insatll Page-Fault-Handler:
  install_segv_handler();
 #endif
 #ifdef HAVE_SIGNALS
  install_sigcld_handler();
 #endif
 #if defined(HAVE_SIGNALS) && defined(SIGPIPE)
  install_sigpipe_handler();
 #endif
  # initialize time variables:
  init_time();
  # Initialize locale dependent encodings:
  init_dependent_encodings();
  # initialize stream-variables:
  init_streamvars(argv_execute_file && !argv_repl);
 #ifdef NEXTAPP
  # make nxterminal-stream functional:
  if (nxterminal_init()) { final_exitcode = 17; quit(); }
 #endif
  # make break possible:
  end_system_call();
  clr_break_sem_1();
  # initialize pathnames:
  init_pathnames();
 #ifdef REXX
  # initialize Rexx-interface:
  init_rexx();
  # do without an error-message in case of failure.
  # we do not want to make CLISP unusable because of that!
 #endif
 #ifdef DYNAMIC_FFI
  # initialize FFI:
  init_ffi();
 #endif
  init_other_modules_2(); # initialize modules yet uninitialized
  { # final module initializations:
    var module_t* module; # loop over modules
    for_modules(all_other_modules,{
      if (module->initfunction2)
        # call initialization function:
        (*module->initfunction2)(module);
    });
  }
  { # other initializations:
    pushSTACK(Symbol_value(S(init_hooks))); # SYS::*INIT-HOOKS*
    while (mconsp(STACK_0)) { # process
      var object obj = STACK_0;
      STACK_0 = Cdr(obj); funcall(Car(obj),0);
    }
    skipSTACK(1);
  }
  # print greeting:
  if (!nullpSv(quiet)) /* SYS::*QUIET* /= NIL ? */
    { argv_quiet = true; } # prevents the greeting
  if (argv_execute_file != NULL) # batch-mode ?
    { argv_quiet = true; } # prevents the greeting
  if (!argv_quiet || argv_license) print_banner();
  if (argv_license) print_license();
  if (argv_execute_arg_count > 0) {
    var uintL count = argv_execute_arg_count;
    do { pushSTACK(asciz_to_string(*argv_execute_args++,O(misc_encoding))); }
    while (--count);
    Symbol_value(S(args)) = listof(argv_execute_arg_count);
  }
  if ((argv_memfile == NULL) && (argv_expr_count == 0)) {
    # warning for beginners
    pushSTACK(var_stream(S(standard_output),strmflags_wr_ch_B)); # auf *STANDARD-OUTPUT*
    write_sstring(&STACK_0,CLSTEXT(NLstring "WARNING: No initialization file specified." NLstring));
    write_sstring(&STACK_0,CLSTEXT("Please try: "));
    write_string(&STACK_0,asciz_to_string(program_name,O(pathname_encoding)));
   #ifdef RISCOS
    write_string(&STACK_0,ascii_to_string(" -M mem.lispinit" NLstring));
   #else
    write_string(&STACK_0,ascii_to_string(" -M lispinit.mem" NLstring));
   #endif
    skipSTACK(1);
  }
  if (argv_lisplibdir == NULL) {
    if (nullp(O(lib_dir))) {
      # warning for beginners and careless developers
      pushSTACK(var_stream(S(standard_output),strmflags_wr_ch_B)); # on *STANDARD-OUTPUT*
      write_sstring(&STACK_0,CLSTEXT(NLstring "WARNING: No installation directory specified." NLstring));
      write_sstring(&STACK_0,CLSTEXT("Please try: "));
      write_string(&STACK_0,asciz_to_string(program_name,O(pathname_encoding)));
      write_string(&STACK_0,ascii_to_string(" -B /usr/local/lib/clisp" NLstring));
      skipSTACK(1);
    }
  } else { # set it
    pushSTACK(asciz_to_string(argv_lisplibdir,O(pathname_encoding)));
    funcall(L(set_lib_directory),1);
  }
  if ((argv_compile || argv_expr_count || argv_execute_file != NULL)
      && !argv_interactive_debug && !argv_repl) {
    # '-c' or '-x' or file specified -> LISP runs in batch-mode:
    # (setq *debug-io*
    #   (make-two-way-stream (make-string-input-stream "") *query-io*)
    # )
    funcall(L(make_concatenated_stream),0); # (MAKE-CONCATENATED-STREAM)
    pushSTACK(value1); # empty input-stream
    var object stream = var_stream(S(query_io),strmflags_wr_ch_B);
    Symbol_value(S(debug_io)) = make_twoway_stream(popSTACK(),stream);
  }
  switch (argv_ansi) {
    case 1: # Maximum ANSI CL compliance
      pushSTACK(T); funcall(L(set_ansi),1); break;
    case 2: # The traditional CLISP behavior
      pushSTACK(NIL); funcall(L(set_ansi),1); break;
    default: # use the settings from the memory image
      break;
  }
  if (argv_load_compiling) # (SETQ *LOAD-COMPILING* T) :
    { Symbol_value(S(load_compiling)) = T; }
  if (argv_verbose) /* (setq *load-print* t *compile-print* t) */
    Symbol_value(S(load_print)) = Symbol_value(S(compile_print)) = T;
  if (argv_developer) { /* developer mode */
    /* unlock all packages */
    var object packlist = O(all_packages);
    while (consp(packlist)) {
      mark_pack_unlocked(Car(packlist));
      packlist = Cdr(packlist);
    }
  }
  # load RC file ~/.clisprc
  if (!argv_norc) {
    # (LOAD (MERGE-PATHNAMES (MAKE-PATHNAME :NAME ".clisprc")
    #                        (USER-HOMEDIR-PATHNAME))
    #       :IF-DOES-NOT-EXIST NIL
    # )
    pushSTACK(S(Kname));
   #if defined(PATHNAME_UNIX) || defined(PATHNAME_AMIGAOS)
    pushSTACK(ascii_to_string(".clisprc"));
   #endif
   #if defined(PATHNAME_OS2) || defined(PATHNAME_WIN32) || defined(PATHNAME_RISCOS)
    pushSTACK(ascii_to_string("_clisprc"));
   #endif
    funcall(L(make_pathname),2);
    pushSTACK(value1);
    funcall(S(user_homedir_pathname),0);
    pushSTACK(value1);
    funcall(L(merge_pathnames),2);
    pushSTACK(value1);
    pushSTACK(S(Kif_does_not_exist));
    pushSTACK(S(nil));
    funcall(S(load),3);
  }
  # execute (LOAD initfile) for each initfile:
  if (argv_init_filecount > 0) {
    var char** fileptr = &argv_selection_array[0];
    var uintL count;
    dotimespL(count,argv_init_filecount,{
      var object filename = asciz_to_string(*fileptr++,O(misc_encoding));
      pushSTACK(filename); funcall(S(load),1);
    });
  }
  if (argv_compile) {
    # execute
    #   (EXIT-ON-ERROR
    #     (APPEASE-CERRORS
    #       (COMPILE-FILE (setq file (MERGE-PATHNAMES file (MERGE-PATHNAMES '#".lisp" (CD))))
    #                     [:OUTPUT-FILE (setq output-file (MERGE-PATHNAMES (MERGE-PATHNAMES output-file (MERGE-PATHNAMES '#".fas" (CD))) file))]
    #                     [:LISTING (MERGE-PATHNAMES '#".lis" (or output-file file))]
    #   ) ) )
    # for each file:
    if (argv_compile_filecount > 0) {
      var argv_compile_file_t* fileptr = &argv_compile_files[0];
      var uintL count;
      dotimespL(count,argv_compile_filecount,{
        var uintC argcount = 1;
        var object filename = asciz_to_string(fileptr->input_file,O(misc_encoding));
        pushSTACK(S(compile_file));
        pushSTACK(filename);
        pushSTACK(O(source_file_type)); # #".lisp"
        funcall(L(cd),0); pushSTACK(value1); # (CD)
        funcall(L(merge_pathnames),2); # (MERGE-PATHNAMES '#".lisp" (CD))
        pushSTACK(value1);
        funcall(L(merge_pathnames),2); # (MERGE-PATHNAMES file ...)
        pushSTACK(value1);
        if (fileptr->output_file) {
          filename = asciz_to_string(fileptr->output_file,O(misc_encoding));
          pushSTACK(S(Koutput_file));
          pushSTACK(filename);
          pushSTACK(O(compiled_file_type)); # #".fas"
          funcall(L(cd),0); pushSTACK(value1); # (CD)
          funcall(L(merge_pathnames),2); # (MERGE-PATHNAMES '#".fas" (CD))
          pushSTACK(value1);
          funcall(L(merge_pathnames),2); # (MERGE-PATHNAMES output-file ...)
          pushSTACK(value1);
          pushSTACK(STACK_2); # file
          funcall(L(merge_pathnames),2); # (MERGE-PATHNAMES ... file)
          pushSTACK(value1);
          argcount += 2;
        }
        if (argv_compile_listing) {
          pushSTACK(S(Klisting));
          pushSTACK(O(listing_file_type)); # #".lis"
          pushSTACK(STACK_2); # (or output-file file)
          funcall(L(merge_pathnames),2); # (MERGE-PATHNAMES '#".lis" ...)
          pushSTACK(value1);
          argcount += 2;
        }
        # quote all arguments:
        if (argcount > 0) {
          var gcv_object_t* ptr = args_end_pointer;
          var uintC c;
          dotimespC(c,argcount,{
            pushSTACK(S(quote)); pushSTACK(Before(ptr));
            BEFORE(ptr) = listof(2);
          });
        }
        var object form = listof(1+argcount); # `(COMPILE-FILE ',...)
        if (!argv_repl) {
          if (argv_interactive_debug) pushSTACK(S(appease_cerrors));
          else pushSTACK(S(batchmode_errors));
          pushSTACK(form);
          form = listof(2); # `(SYS::BATCHMODE-ERRORS (COMPILE-FILE ',...))
        }
        eval_noenv(form); # execute
        fileptr++;
      });
    }
    if (!argv_repl) quit();
  }
  if (argv_package != NULL) { # (IN-PACKAGE packagename)
    var object packname = asciz_to_string(argv_package,O(misc_encoding));
    var object package = find_package(packname);
    if (!nullp(package)) {
      Symbol_value(S(packagestern)) = package;
    } else {
      pushSTACK(var_stream(S(standard_output),strmflags_wr_ch_B));
      write_sstring(&STACK_0,CLSTEXT(NLstring "WARNING: no such package: "));
      write_sstring(&STACK_0,packname);
      terpri(&STACK_0);
      skipSTACK(1);
    }
  }
  if (argv_execute_file != NULL) {
    #  execute:
    # (PROGN
    #   #+UNIX (SET-DISPATCH-MACRO-CHARACTER #\# #\!
    #           (FUNCTION SYS::UNIX-EXECUTABLE-READER))
    #   (SETQ *LOAD-VERBOSE* NIL)
    #   (EXIT-ON-ERROR
    #    (APPEASE-CERRORS
    #     (LOAD argv_execute_file :EXTRA-FILE-TYPES ...)))
    #   (UNLESS argv_repl (EXIT)))
   #if defined(UNIX) || defined(WIN32_NATIVE)
    # Make clisp ignore the leading #! line.
    pushSTACK(ascii_char('#')); pushSTACK(ascii_char('!'));
    pushSTACK(L(unix_executable_reader));
    funcall(L(set_dispatch_macro_character),3);
   #endif
    Symbol_value(S(load_verbose)) = NIL;
    var object form;
    pushSTACK(S(load));
    if (asciz_equal(argv_execute_file,"-")) {
      pushSTACK(S(standard_input)); # *STANDARD-INPUT*
    } else {
      pushSTACK(asciz_to_string(argv_execute_file,O(misc_encoding)));
    }
    pushSTACK(S(Kextra_file_types));
   #ifdef WIN32_NATIVE
    pushSTACK(S(quote));
    pushSTACK(O(load_extra_file_types));
    form = listof(2); # (QUOTE (".BAT"))
    pushSTACK(form);
   #else
    pushSTACK(NIL);
   #endif
    form = listof(4);
    if (!argv_repl) {
      if (argv_interactive_debug) pushSTACK(S(appease_cerrors));
      else pushSTACK(S(batchmode_errors));
      pushSTACK(form);
      form = listof(2); # `(SYS::BATCHMODE-ERRORS (LOAD "..."))
    }
    eval_noenv(form); # execute
    if (!argv_repl) quit();
  }
  if (argv_expr_count) {
    # set *STANDARD-INPUT* to a stream, that produces argv_exprs:
    var uintL count = argv_expr_count;
    var char** exprs = &argv_selection_array[argc-1];
    do { pushSTACK(asciz_to_string(*exprs--,O(misc_encoding))); }
    while (--count);
    pushSTACK(O(newline_string)); /* separate -x from REPL */
    var object total = string_concat(argv_expr_count+1);
    pushSTACK(total);
    funcall(L(make_string_input_stream),1);
    if (argv_repl) {
      pushSTACK(value1); pushSTACK(Symbol_value(S(standard_input)));
      funcall(L(make_concatenated_stream),2);
    }
    Symbol_value(S(standard_input)) = value1;
    # During bootstrapping, *DRIVER* has no value and SYS::BATCHMODE-ERRORS
    # is undefined. Do not set an error handler in that case.
    if (!nullpSv(driverstern) && !argv_repl) {
      # (PROGN
      #   (EXIT-ON-ERROR (APPEASE-CERRORS (FUNCALL *DRIVER*)))
      #   ; Normally this will exit by itself once the string has reached EOF,
      #   ; but to be sure:
      #   (UNLESS argv_repl (EXIT)))
      var object form;
      pushSTACK(S(funcall)); pushSTACK(S(driverstern)); form = listof(2);
      if (argv_interactive_debug) pushSTACK(S(appease_cerrors));
      else pushSTACK(S(batchmode_errors));
      pushSTACK(form); form = listof(2);
      eval_noenv(form);
      if (!argv_repl) quit();
    }
  }
  # call read-eval-print-loop:
  driver();
  quit();
  /*NOTREACHED*/
 } # end var bt
  # if the memory does not suffice:
  no_mem:
  fprintf(stderr,GETTEXTL("%s: Not enough memory for Lisp." NLstring),
          program_name);
  quit_sofort(1);
  /*NOTREACHED*/
  # termination of program via quit_sofort() (engl. quit_instantly() ):
  end_of_main:
 #ifdef MULTIMAP_MEMORY
  exitmap();
 #endif
  FREE_DYNAMIC_ARRAY(argv_compile_files_array);
  FREE_DYNAMIC_ARRAY(argv_selection_array); }
 #ifdef WIN32_NATIVE
  done_win32();
 #endif
 #if (defined(UNIX) && !defined(NEXTAPP)) || defined(AMIGAOS) || defined(RISCOS)
  terminal_sane(); # switch terminal again in normal mode
 #endif
 #if defined(UNIX) || defined(RISCOS)
  exit(exitcode); # Calling exit(), not _exit(), allows profiling to work.
 #endif
 #if defined(MSDOS) || defined(WIN32_NATIVE)
  _exit(exitcode);
 #endif
 #ifdef AMIGAOS
  exit_amiga(exitcode ? RETURN_ERROR : RETURN_OK);
 #endif
  # if that did not help:
  return exitcode;
}

# leave LISP-interpreter
# quit();
# > final_exitcode: 0 on normal exit, 1 on abort
global int final_exitcode = 0;
local int quit_retry = 0;
nonreturning_function(global, quit, (void)) {
  # first "unwind" the STACK downto STACK-end:
  VALUES0; /* do not save values for UNWIND-PROTECT-frames */
  unwind_protect_to_save.fun = (restartf_t)&quit;
  while (!(eq(STACK_0,nullobj) && eq(STACK_1,nullobj)))
    if (framecode(STACK_0) & bit(frame_bit_t))
      # At STACK_0 a frame starts
      { unwind(); } # unwind frame
    else
      # STACK_0 contains a normal LISP-object
      { skipSTACK(1); }
  # Then, a farewell message:
  if (quit_retry==0) {
    quit_retry++; # If this fails, do not retry it. For robustness.
    funcall(L(fresh_line),0); # (FRESH-LINE [*standard-output*])
    if (!argv_quiet) {
      pushSTACK(CLSTEXT("Bye.")); funcall(L(write_line),1);
    }
    pushSTACK(var_stream(S(error_output),strmflags_wr_ch_B)); # Stream *ERROR-OUTPUT*
    funcall(L(fresh_line),1); # (FRESH-LINE *error-output*)
  }
  # Then wait for a keypress:
  if (argv_wait_keypress) {
    argv_wait_keypress = false; # If this fails, do not retry it (robustness)
    pushSTACK(CLSTEXT("Press a key to terminate..."));
    funcall(L(write_line),1);
    funcall(S(wait_keypress),0); # (SYS::WAIT-KEYPRESS)
  }
  close_all_files(); # close all files
 #ifdef DYNAMIC_FFI
  exit_ffi(); # close FFI
 #endif
 #ifdef WIN32_NATIVE
  done_win32();
 #endif
 #ifdef REXX
  close_rexx(); # close Rexx-communication
 #endif
 #ifdef NEXTAPP
  nxterminal_exit(); # cloase terminal-stream-communication
 #endif
  quit_sofort(final_exitcode); # leave program
}

# -----------------------------------------------------------------------------
#                  Saving and Loading of MEM-Files

#include "spvw_memfile.c"

# -----------------------------------------------------------------------------
#                       Dynamic Loading of Modules

#ifdef DYNAMIC_MODULES

# Attaches a shared library to this process' memory, and attempts to load
# a number of clisp modules from it.
nonreturning_function(local, fehler_dlerror,
                      (const char* func, const char* symbol,
                       const char* errstring)) {
  end_system_call();
  if (errstring == NULL) { errstring = "Unknown error"; }
  pushSTACK(asciz_to_string(errstring,O(misc_encoding)));
  if (symbol != NULL)
    { pushSTACK(asciz_to_string(symbol,O(internal_encoding))); }
  pushSTACK(asciz_to_string(func,O(internal_encoding)));
  pushSTACK(TheSubr(subr_self)->name);
  fehler(error, (symbol == NULL ? "~: ~ -> ~" : "~: ~(~) -> ~"));
}
global void dynload_modules (const char * library, uintC modcount,
                             const char * const * modnames) {
  var void* libhandle;
  begin_system_call();
  # Open the library.
  libhandle = dlopen(library,RTLD_NOW);
  if (libhandle == NULL) fehler_dlerror("dlopen",NULL,dlerror());
  end_system_call();
  if (modcount > 0) {
    # What's the longest module name? What's their total size?
    var uintL max_modname_length = 0;
    var uintL total_modname_length = 0;
    begin_system_call();
    {
      var const char * const * modnameptr = modnames;
      var uintC count;
      dotimespC(count,modcount,{
        var uintL len = asciz_length(*modnameptr);
        if (len > max_modname_length) { max_modname_length = len; }
        total_modname_length += len+1;
        modnameptr++;
      });
    }
    { # Make room for the module descriptors.
      var module_t* modules = (module_t*) malloc(modcount*sizeof(module_t)+total_modname_length);
      if (modules==NULL) fehler_dlerror("malloc",NULL,"out of memory");
      {
        var char* modnamebuf = (char*)(&modules[modcount]);
        var DYNAMIC_ARRAY(symbolbuf,char,8+max_modname_length+21+1);
        var const char * const * modnameptr = modnames;
        var module_t* module = modules;
        var uintC count;
        dotimespC(count,modcount,{
          var const char * modname = *modnameptr;
          var uintL len = asciz_length(modname);
          var const char * err;
          # Copy modname into modnamebuf:
          module->name = modnamebuf;
          {
            var const char * ptr = modname;
            until ((*modnamebuf++ = *ptr++) == '\0') {}
          }
          { # Find the addresses of some C data in the shared library:
            sprintf(symbolbuf,"module__%s__subr_tab",modname);
            module->stab = (subr_t*) dlsym(libhandle,symbolbuf);
            err = dlerror();
            if (err) fehler_dlerror("dlsym",symbolbuf,err);
          }
          {
            sprintf(symbolbuf,"module__%s__subr_tab_size",modname);
            module->stab_size = (const uintC*) dlsym(libhandle,symbolbuf);
            err = dlerror();
            if (err) fehler_dlerror("dlsym",symbolbuf,err);
          }
          {
            sprintf(symbolbuf,"module__%s__object_tab",modname);
            module->otab = (gcv_object_t*) dlsym(libhandle,symbolbuf);
            err = dlerror();
            if (err) fehler_dlerror("dlsym",symbolbuf,err);
          }
          {
            sprintf(symbolbuf,"module__%s__object_tab_size",modname);
            module->otab_size = (const uintC*) dlsym(libhandle,symbolbuf);
            err = dlerror();
            if (err) fehler_dlerror("dlsym",symbolbuf,err);
          }
          module->initialized = false;
          {
            sprintf(symbolbuf,"module__%s__subr_tab_initdata",modname);
            module->stab_initdata = (const subr_initdata_t*)
              dlsym(libhandle,symbolbuf);
            err = dlerror();
            if (err) fehler_dlerror("dlsym",symbolbuf,err);
          }
          {
            sprintf(symbolbuf,"module__%s__object_tab_initdata",modname);
            module->otab_initdata = (const object_initdata_t*)
              dlsym(libhandle,symbolbuf);
            err = dlerror();
            if (err) fehler_dlerror("dlsym",symbolbuf,err);
          }
          { # Find the addresses of some C functions in the shared library:
            sprintf(symbolbuf,"module__%s__init_function_1",modname);
            module->initfunction1 = (void (*) (module_t*))
              dlsym(libhandle,symbolbuf);
            err = dlerror();
            if (err) fehler_dlerror("dlsym",symbolbuf,err);
          }
          {
            sprintf(symbolbuf,"module__%s__init_function_2",modname);
            module->initfunction2 = (void (*) (module_t*))
              dlsym(libhandle,symbolbuf);
            err = dlerror();
            if (err) fehler_dlerror("dlsym",symbolbuf,err);
          }
          module->next = NULL;
          modnameptr++; module++;
        });
        FREE_DYNAMIC_ARRAY(symbolbuf);
      }
      end_system_call();
      { # We found all the necessary symbols. Now register the modules.
        var module_t* module = modules;
        var uintC mcount = modcount;
        while (mcount-- > 0) {
          add_module(module);
          # pre-initialization, cf. init_subr_tab_1.
          if (*module->stab_size > 0) {
            var subr_t* ptr = module->stab; # peruse subr_tab
            var uintC count;
            dotimespC(count,*module->stab_size,
            { SUBR_SET_ARGTYPE(ptr); ptr++; });
          }
         #if (defined(MULTIMAP_MEMORY) || defined(SINGLEMAP_MEMORY)) && defined(MAP_MEMORY_TABLES)
          {
            var subr_t* newptr = (subr_t*)&subr_tab + total_subr_anz;
            var uintC count = *module->stab_size;
            if (count > 0) {
              {
                var uintL old_map_len = round_up(total_subr_anz*sizeof(subr_t),map_pagesize);
                var uintL new_map_len = round_up((total_subr_anz+count)*sizeof(subr_t),map_pagesize);
                if (old_map_len < new_map_len) {
                  if (zeromap((void*)((aint)&subr_tab+old_map_len),new_map_len-old_map_len) <0)
                    fehler_dlerror("zeromap",NULL,"out of memory for subr_tab");
                }
              }
              {
                var subr_t* oldptr = module->stab;
                module->stab = newptr;
                dotimespC(count,count, {
                  *newptr = *oldptr++;
                  newptr->name = NIL; newptr->keywords = NIL; # GC stays possible with it
                  newptr++;
                });
              }
              total_subr_anz += *module->stab_size;
            }
          }
         #elif defined(MULTIMAP_MEMORY)
          if (*module->stab_size > 0) {
            # multimap the subr_tab of the loaded module .
            # the pages to be mapped belong to the data segment of the
            # newly laoded Shared-Library, so are surely not yet
            # multi-mapped.
            var aint subr_tab_start = round_down((aint)module->stab,pagesize);
            var aint subr_tab_end = round_up((aint)module->stab+(*module->stab_size)*sizeof(subr_t),pagesize);
            multimap(case_machine: case_subr: , subr_tab_start, subr_tab_end-subr_tab_start, true);
            if (false)
              no_mem:
            fehler_dlerror("multimap",NULL,"out of memory for subr_tab");
          }
         #endif
          # main initialization.
          init_module_2(module);
          module++;
        }
      }
      { # Now start the modules' life.
        var module_t* module = modules;
        var uintC count;
        dotimespC(count,modcount,{
          if (module->initfunction2)
            # call initialization function:
            (*module->initfunction2)(module);
          module++;
        });
      }
    }
  }
}

#endif

# -----------------------------------------------------------------------------
#                                Version
#ifdef AMIGAOS
# There is a utility, that searches an executable for a version string.
# Format "name version.revision (date)\r\n"
  global const char version_string[] =
    "$VER: GNU CLISP"
    #if defined(WIDE)
      "-wide"
    #elif !defined(TYPECODES)
      "-typ2"
    #elif defined(AMIGA3000)
      "-high"
    #elif defined(MC68000)
      "-68000"
    #else
      "-low"
    #endif
    " " VERSION_NUMBER " (" VERSION_DATE ")\r\n";
#endif

# -----------------------------------------------------------------------------

