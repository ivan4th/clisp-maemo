# Memory management data structures, part 3: global data

# ------------------------------ Specification --------------------------------

#ifdef TYPECODES
# Number of possible typecodes.
  #define typecount  bit(oint_type_len<=8 ? oint_type_len : 8)
#endif

# Number of heaps.
# heapcount
  #ifdef SPVW_MIXED
    # Two heaps: One for varobjects, one for two-pointer objects.
    #define heapcount  2
  #endif
  #ifdef SPVW_PURE
    # A heap for each possible typecode.
    #define heapcount  typecount
  #endif

# Global memory management data structures.
  local struct {

        # Lower limit of big allocated memory block.
        aint MEMBOT;

        # now comes the Lisp STACK

        # now room for the heaps containing Lisp objects.
        Heap heaps[heapcount];
        #ifdef SPVW_PURE
          sintB heaptype[heapcount];
          # for every typecode:
          #   0 for conses
          #   1 for varobjects containing object pointers
          #   2 for varobjects containing no pointers (only immediate data)
          #  -1 for SUBRs (gcinvariant)
          #  -2 for unused or immediate typecodes
        #endif
        #ifdef SPVW_MIXED
          #define varobjects  heaps[0] # objects of various lengths
          #define conses      heaps[1] # conses and other two-pointer objects
        #endif
        #if defined(SPVW_MIXED_BLOCKS) && defined(TYPECODES) && defined(GENERATIONAL_GC)
          sintB heapnr_from_type[typecount]; # table type -> heapnr
        #endif

        #if defined(SPVW_MIXED_BLOCKS_OPPOSITE) && !defined(TRIVIALMAP_MEMORY)
          # now empty, free for Lisp objects.
          #define MEMRES  conses.heap_end
          # now the emergency reserve
          # Upper limit of big allocated memory block.
          aint MEMTOP;
        #endif

        # Statistical data, used for deciding when to start a GC.
        #if defined(SPVW_PURE_BLOCKS) || defined(TRIVIALMAP_MEMORY) || defined(GENERATIONAL_GC)
          uintL total_room; # the space that may be occupied without triggering GC
          #ifdef GENERATIONAL_GC
            bool last_gc_full; # if the last GC was a full one
            uintL last_gcend_space0; # how much space was occupied after the last GC
            uintL last_gcend_space1; # (from generation 0 resp. generation 1)
          #endif
        #endif
        #ifdef SPVW_PAGES
          Pages free_pages; # a list of free, normal-sized pages
          uintL total_space; # how much space do the occupied pages contain at all
          uintL used_space; # how much space is occupied just now
          uintL last_gcend_space; # how much space was occupied after the last GC
          bool last_gc_compacted; # if the last GC has already compacted
          uintL gctrigger_space; # how much space may be occupied, until the next GC becomes necessary
        #endif

        #ifdef SELFMADE_MMAP
          Handle memfile_handle;
          bool memfile_still_being_read;
        #endif

      }
      mem;

  #if defined(SPVW_MIXED_BLOCKS_OPPOSITE) && !defined(TRIVIALMAP_MEMORY) && !defined(GENERATIONAL_GC)
    #define RESERVE       0x00800L  # 2 KByte memory as reserve
  #else
    #define RESERVE             0   # need no preallocated reserve
  #endif
  #define MINIMUM_SPACE 0x10000L  # 64 KByte as minimal memory for LISP-data
  #ifdef TRIVIALMAP_MEMORY
    #define RESERVE_FOR_MALLOC 0x100000L  # leave 1 MByte address space free, for malloc
  #endif

# Iteration through all heaps.
# for_each_heap(heapvar,statement);

# Iteration through all heaps containing varobjects.
# for_each_varobject_heap(heapvar,statement);

# Iteration through all heaps containing conses.
# for_each_cons_heap(heapvar,statement);

# Iteration through all pages.
# for_each_page(page, statement using 'var Page* page');

# Iteration through all pages containing varobjects.
# for_each_varobject_page(page, statement using 'var Page* page');

# Iteration through all pages containing conses.
# for_each_cons_page(page, statement using 'var Page* page');
# for_each_cons_page_reversed(page, statement using 'var Page* page');

# While iterating through all heaps (0 <= heapnr < heapcount):
# Determine the type of a heap.
# is_heap_containing_objects(heapnr)
# is_varobject_heap(heapnr)
# is_cons_heap(heapnr)
# is_unused_heap(heapnr)

# Consistency checks.
# CHECK_AVL_CONSISTENCY();
# CHECK_GC_CONSISTENCY();
# CHECK_GC_CONSISTENCY_2();
# CHECK_PACK_CONSISTENCY();

# Initializations.
  #ifdef SPVW_PURE
    local inline void init_mem_heaptypes (void);
  #endif
  #if defined(SPVW_MIXED_BLOCKS) && defined(TYPECODES) && defined(GENERATIONAL_GC)
    local inline void init_mem_heapnr_from_type (void);
  #endif

# ------------------------------ Implementation -------------------------------

# partitioning of the whole memory (partly out-of-date):
# 1. C-program. Memory is allocated by the operating system.
#    un-movable after program start.
# 2. C-Stack.  Is fetched by the C-program.
#    un-movable.
# 3. C-Heap. Is unused here.
#ifdef SPVW_MIXED_BLOCKS
# 4. LISP-stack and LISP-data.
#    4a. LISP-stack. un-movable.
#    4b. Objects of variable length. (Un-movable).
#    4c. Conses and similar. Movable with move_conses.
#    Memory therefore is requested from the operating system (has the
#    advantage: On EXECUTE, the whole memory that LISP currently does not
#    need can be provided to the foreign program).
#    We dispense here with a partitioning into single pages.
#    || LISP-      |Objects of      |->  empty   <-|conses     | reserve |
#    || stack      |variable length !              !and similar|         |
#    |STACK_BOUND  |         objects.end     conses.start      |         |
#  MEMBOT   objects.start                                conses.end    MEMTOP
#endif
#ifdef SPVW_PURE_BLOCKS
# 4. LISP-stack. Un-movable.
# 5. LISP-data. For each type a large block of objects.
#endif
#ifdef SPVW_MIXED_PAGES
# 4. LISP-stack. Un-movable.
# 5. LISP-data.
#    subdivided into pages for objects of variable length and
#    pages for conses and similar.
#endif
#ifdef SPVW_PURE_PAGES
# 4. LISP-stack. Un-movable.
# 5. LISP-data. Subdivided into pages, that contain only objects
#    of the same type.
#endif

#ifdef SPVW_MIXED

# Iteration through heaps.
#define for_each_heap(heapvar,statement)  \
  do { var uintL heapnr;                                        \
       for (heapnr=0; heapnr<heapcount; heapnr++)               \
         { var Heap* heapvar = &mem.heaps[heapnr]; statement; } \
  } while(0)
#define for_each_varobject_heap(heapvar,statement)  \
  do { var Heap* heapvar = &mem.varobjects; statement; } while(0)
#define for_each_cons_heap(heapvar,statement)  \
  do { var Heap* heapvar = &mem.conses; statement; } while(0)

# Iteration through pages.
#define for_each_page(pagevar,statement)  \
  do { var uintL heapnr;                                \
       for (heapnr=0; heapnr<heapcount; heapnr++)       \
         map_heap(mem.heaps[heapnr],pagevar,statement); \
  } while(0)
#define for_each_varobject_page(pagevar,statement)  \
  map_heap(mem.varobjects,pagevar,statement)
#define for_each_cons_page(pagevar,statement)  \
  map_heap(mem.conses,pagevar,statement)
#define for_each_cons_page_reversed for_each_cons_page

# Heap classification.
  #define is_heap_containing_objects(heapnr)  (true)
  #define is_varobject_heap(heapnr)  ((heapnr)==0)
  #define is_cons_heap(heapnr)  ((heapnr)==1)
  #define is_unused_heap(heapnr)  (false)

#endif

#ifdef SPVW_PURE

# During iterations, `heapnr' is the number of the heap.

# Iteration through heaps.
#define for_each_heap(heapvar,statement)  \
  do { var uintL heapnr;                                          \
       for (heapnr=0; heapnr<heapcount; heapnr++)                 \
         if (mem.heaptype[heapnr] >= 0)                           \
           { var Heap* heapvar = &mem.heaps[heapnr]; statement; } \
  } while(0)
#define for_each_varobject_heap(heapvar,statement)  \
  do { var uintL heapnr;                                          \
       for (heapnr=0; heapnr<heapcount; heapnr++)                 \
         if (mem.heaptype[heapnr] > 0)                            \
           { var Heap* heapvar = &mem.heaps[heapnr]; statement; } \
  } while(0)
#define for_each_cons_heap(heapvar,statement)  \
  do { var uintL heapnr;                                          \
       for (heapnr=0; heapnr<heapcount; heapnr++)                 \
         if (mem.heaptype[heapnr] == 0)                           \
           { var Heap* heapvar = &mem.heaps[heapnr]; statement; } \
  } while(0)

# Iteration through pages.
#define for_each_page(pagevar,statement)  \
  do { var uintL heapnr;                                  \
       for (heapnr=0; heapnr<heapcount; heapnr++)         \
         if (mem.heaptype[heapnr] >= 0)                   \
           map_heap(mem.heaps[heapnr],pagevar,statement); \
  } while(0)
#define for_each_varobject_page(pagevar,statement)  \
  do { var uintL heapnr;                                  \
       for (heapnr=0; heapnr<heapcount; heapnr++)         \
         if (mem.heaptype[heapnr] > 0)                    \
           map_heap(mem.heaps[heapnr],pagevar,statement); \
  } while(0)
#define for_each_cons_page(pagevar,statement)  \
  do { var uintL heapnr;                                  \
       for (heapnr=0; heapnr<heapcount; heapnr++)         \
         if (mem.heaptype[heapnr] == 0)                   \
           map_heap(mem.heaps[heapnr],pagevar,statement); \
  } while(0)
#define for_each_cons_page_reversed(pagevar,statement)  \
  do { var uintL heapnr;                                  \
       for (heapnr=heapcount; heapnr-- > 0; )             \
         if (mem.heaptype[heapnr] == 0)                   \
           map_heap(mem.heaps[heapnr],pagevar,statement); \
  } while(0)

# Heap classification.
  #define is_heap_containing_objects(heapnr)  ((mem.heaptype[heapnr] >= 0) && (mem.heaptype[heapnr] < 2))
  #define is_cons_heap(heapnr)  (mem.heaptype[heapnr] == 0)
  #define is_varobject_heap(heapnr)  (mem.heaptype[heapnr] > 0)
  #define is_unused_heap(heapnr)  (mem.heaptype[heapnr] < 0)

#endif

# check of the memory content to be GC-proof:
  #if defined(SPVW_PAGES) && defined(DEBUG_SPVW)
    # check, if the administration of the pages is okay:
      #define CHECK_AVL_CONSISTENCY()  check_avl_consistency()
      local void check_avl_consistency (void);
      local void check_avl_consistency()
        {
          #ifdef DEBUG_AVL
          var uintL heapnr;
          for (heapnr=0; heapnr<heapcount; heapnr++) {
            AVL(AVLID,check) (mem.heaps[heapnr].inuse);
          }
          #endif
        }
    # check, if the boundaries of the pages are okay:
      #define CHECK_GC_CONSISTENCY()  check_gc_consistency()
      local void check_gc_consistency (void);
      local void check_gc_consistency()
        {
          for_each_page(page,
            if ((sintL)page->page_room < 0) {
              asciz_out_1("\nPage bei Adresse 0x%x uebergelaufen!!\n",page); abort();
            }
            if (!(page->page_start == page_start0(page))) {
              asciz_out_1("\nPage bei Adresse 0x%x inkonsistent!!\n",page); abort();
            }
            if (!(page->page_end + page->page_room
                  == round_down(page->m_start + page->m_length,varobject_alignment)
               ) ) {
              asciz_out_1("\nPage bei Adresse 0x%x inkonsistent!!\n",page); abort();
            }
          );
        }
    # check, if the boundaries of the pages are okay
    # during the compacting GC:
      #define CHECK_GC_CONSISTENCY_2()  check_gc_consistency_2()
      local void check_gc_consistency_2 (void);
      local void check_gc_consistency_2()
        {
          for_each_page(page,
            if ((sintL)page->page_room < 0) {
              asciz_out_1("\nPage bei Adresse 0x%x uebergelaufen!!\n",page); abort();
            }
            if (!(page->page_end + page->page_room - (page->page_start - page_start0(page))
                  == round_down(page->m_start + page->m_length,varobject_alignment)
               ) ) {
              asciz_out_1("\nPage bei Adresse 0x%x inkonsistent!!\n",page); abort();
            }
          );
        }
  #else
    #define CHECK_AVL_CONSISTENCY()
    #define CHECK_GC_CONSISTENCY()
    #define CHECK_GC_CONSISTENCY_2()
  #endif
  #ifdef DEBUG_SPVW
    # check, if the tables of the packages are to some extent okay:
      #define CHECK_PACK_CONSISTENCY()  check_pack_consistency()
      global void check_pack_consistency (void);
      global void check_pack_consistency()
        {
          var object plist = O(all_packages);
          while (consp(plist)) {
            var object pack = Car(plist);
            var object symtabs[2];
            var uintC i;
            symtabs[0] = ThePackage(pack)->pack_external_symbols;
            symtabs[1] = ThePackage(pack)->pack_internal_symbols;
            for (i = 0; i < 2; i++) {
              var object symtab = symtabs[i];
              var object table = TheSvector(symtab)->data[1];
              var uintL index = Svector_length(table);
              until (index==0) {
                var object entry = TheSvector(table)->data[--index];
                var uintC count = 0;
                while (consp(entry)) {
                  if (!symbolp(Car(entry))) abort();
                  entry = Cdr(entry);
                  count++; if (count>=10000) abort();
                }
              }
            }
            plist = Cdr(plist);
          }
        }
  #else
      #define CHECK_PACK_CONSISTENCY()
  #endif

# Initializations.
  #ifdef SPVW_PURE
    local inline void init_mem_heaptypes (void);
    local inline void init_mem_heaptypes()
      {
        var uintL heapnr;
        for (heapnr=0; heapnr<heapcount; heapnr++) {
          switch (heapnr) {
            case_sstring:
            case_sbvector:
            case_sb2vector:
            case_sb4vector:
            case_sb8vector:
            case_sb16vector:
            case_sb32vector:
            case_bignum:
            #ifndef WIDE
            case_ffloat:
            #endif
            case_dfloat:
            case_lfloat:
              mem.heaptype[heapnr] = 2; break;
            case_ostring:
            case_obvector:
            case_ob2vector:
            case_ob4vector:
            case_ob8vector:
            case_ob16vector:
            case_ob32vector:
            case_weakkvt:
            case_vector:
            case_mdarray:
            case_record:
            case_symbol:
              mem.heaptype[heapnr] = 1; break;
            case_pair:
              mem.heaptype[heapnr] = 0; break;
            case_subr:
              mem.heaptype[heapnr] = -1; break;
            default:
              mem.heaptype[heapnr] = -2; break;
          }
        }
      }
  #endif
  #if defined(SPVW_MIXED_BLOCKS) && defined(TYPECODES) && defined(GENERATIONAL_GC)
    local inline void init_mem_heapnr_from_type (void);
    local inline void init_mem_heapnr_from_type()
      {
        var uintL type;
        for (type = 0; type < typecount; type++) {
          #ifdef MULTIMAP_MEMORY
          switch (type) {
            MM_TYPECASES break;
            default: mem.heapnr_from_type[type] = -1; continue;
          }
          #endif
          switch (type) {
            case_pair: mem.heapnr_from_type[type] = 1; break;
            default:   mem.heapnr_from_type[type] = 0; break;
          }
        }
      }
  #endif
