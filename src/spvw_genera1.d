# Support for GENERATIONAL_GC, part 1.

# ------------------------------ Specification --------------------------------

#ifdef GENERATIONAL_GC

# Number of generation currently subject to collection.
# 0 means: everything (generation 0 and generation 1)
# 1 means: generation 1 only
local uintC generation;

#endif

# Test whether the object obj lies in the currently ignored generation.
# in_old_generation(obj,type,heapnr)
# > obj: object, satisfying !gcinvariant_type_p(type = typecode(obj))
# > heapnr: 0 for varobject, 1 for cons and other two-pointer objects
# < result: true if a partial GC is being run and obj belongs to the old
#           generation.
# Attention! The result is undefined for any of the constsyms.

#ifdef GENERATIONAL_GC

# Economic walking through all pointers of a physical page.
#   walk_physpage(heapnr,physpage,pageend,heapend,walkfun);
# Same thing, but start at an objptr which is actually the beginning of an
# object (or the page end).
#   walk_area(heapnr,physpage_start,physpage_end,walkfun);

# Same things as functions, calling a function, not a macro:
# walk_physpage_(heapnr,physpage,pageend,heapend,walkstep);
# walk_area_(heapnr,physpage_start,physpage_end,walkstep);
  typedef void (*walkstep_fun)(object* ptr);
  local void walk_physpage_ (uintL heapnr, const physpage_state* physpage, aint pageend, aint heapend, walkstep_fun walkstep);
  local void walk_area_ (uintL heapnr, aint physpage_start, aint physpage_end, walkstep_fun walkstep);

# Builds a cache of all pointers inside the old generation.
# This assumes that the new generation is empty, and therefore there are no
# such pointers!
  local void build_old_generation_cache (uintL heapnr);

# Builds a cache of all pointers inside the old generation, pointing into the
# new generation.
  local void rebuild_old_generation_cache (uintL heapnr);

#ifdef SPVW_PURE_BLOCKS
# Set the protections as in build_old_generation_cache(),
# but don't need to rebuild the cache.
  local inline void xmmprotect_old_generation_cache (uintL heapnr);
#endif

# Prepare the old generation for GC.
  local void prepare_old_generation (void);

#endif

# For debugging.
# CHECK_GC_CACHE();
# CHECK_GC_GENERATIONAL();
# SAVE_GC_DATA();

# ------------------------------ Implementation -------------------------------

#ifdef GENERATIONAL_GC
  #ifdef SPVW_PURE_BLOCKS
    #define in_old_generation(obj,type,heapnr)  \
      (canonaddr(obj) < mem.heaps[type].heap_start)
  #else # SPVW_MIXED_BLOCKS
    #ifdef SPVW_MIXED_BLOCKS_OPPOSITE
      #define in_old_generation_0(obj)  \
        (canonaddr(obj) < mem.varobjects.heap_start)
      #define in_old_generation_1(obj)  \
        (canonaddr(obj) >= mem.conses.heap_end)
      #define in_old_generation_general(obj)  \
        (in_old_generation_0(obj) || in_old_generation_1(obj))
      #ifdef GNU
        # heapnr is mostly constant, which makes optimization possible:
        #define in_old_generation(obj,type,heapnr)  \
          (__builtin_constant_p(heapnr)                                          \
           ? ((heapnr)==0 ? in_old_generation_0(obj) : in_old_generation_1(obj)) \
           : in_old_generation_general(obj)                                      \
          )
      #else
        #define in_old_generation(obj,type,heapnr)  \
          in_old_generation_general(obj)
      #endif
    #else # SPVW_MIXED_BLOCKS_STAGGERED
      #define in_old_generation(obj,type,heapnr)  \
        (canonaddr(obj) < mem.heaps[heapnr].heap_start)
    #endif
  #endif
#else
  #define in_old_generation(obj,type,heapnr)  false
#endif

#ifdef GENERATIONAL_GC

# For use with heap->physpages:
  # Just like realloc(), except that the pointer argument may be NULL.
  # local void* xrealloc (void* ptr, size_t size);
    #define xrealloc(ptr,size)  \
      (((ptr)==NULL) ? (void*)malloc(size) : (void*)realloc(ptr,size))
  # Just like free(), except that the pointer argument may be NULL.
  # local void xfree (void* ptr);
    #define xfree(ptr)  if ((ptr)!=NULL) free(ptr);

  # For the following walking functions, it is essential that
  # varobject_alignment is a multiple of sizeof(object).

  #define walk_area_cons(objptr,physpage_end,walkfun)          \
    do { var object* ptr = (object*)objptr;                    \
         while ((aint)ptr < physpage_end)                      \
           { walkfun(*ptr); ptr++; }                           \
    } while(0)
  #define walk_area_symbol(objptr,physpage_end,walkfun)                       \
    do { var object* ptr = (object*)(objptr+symbol_objects_offset);           \
      var uintC count;                                                        \
      dotimespC(count,(sizeof(symbol_)-symbol_objects_offset)/sizeof(object),{\
        if ((aint)ptr < physpage_end) { walkfun(*ptr); ptr++; }               \
        else break;                                                           \
      });                                                                     \
      objptr += size_symbol();                                                \
    } while(0)
  #define walk_area_iarray(objptr,physpage_end,walkfun)         \
    do { var object* ptr = &((Iarray)objptr)->data;             \
         if ((aint)ptr < physpage_end) { walkfun(*ptr); }       \
         objptr += objsize_iarray((Iarray)objptr);              \
    } while(0)
  #define walk_area_svector(objptr,physpage_end,walkfun)                \
    do { var uintL count = svector_length((Svector)objptr);             \
         var object* ptr = &((Svector)objptr)->data[0];                 \
         objptr += size_svector(count);                                 \
         dotimesL(count,count, {                                        \
           if ((aint)ptr < physpage_end) { walkfun(*ptr); ptr++; }      \
           else break;                                                  \
         });                                                            \
    } while(0)
  #define walk_area_record(objptr,physpage_end,walkfun)  \
    do { var uintC count;                                                   \
      var object* ptr = &((Record)objptr)->recdata[0];                      \
      objptr += (record_type((Record)objptr) < rectype_limit                \
                 ? (count = srecord_length((Srecord)objptr),                \
                    size_srecord(count))                                    \
                 : (count = xrecord_length((Xrecord)objptr),                \
                    size_xrecord(count,xrecord_xlength((Xrecord)objptr)))); \
      dotimesC(count,count,{                                                \
        if ((aint)ptr < physpage_end) { walkfun(*ptr); ptr++; }             \
        else break;                                                         \
      });                                                                   \
    } while(0)

  #ifdef SPVW_PURE
    #define walk_area(heapnr,physpage_start,physpage_end,walkfun)         \
      do { var aint objptr = physpage_start;                              \
        switch (heapnr) {                                                 \
          case_pair:                                                      \
            # Object with exactly 2 pointers (cons and similar)           \
            walk_area_cons(objptr,physpage_end,walkfun);                  \
            break;                                                        \
          case_symbol: # symbol                                           \
            while (objptr < physpage_end)                                 \
              walk_area_symbol(objptr,physpage_end,walkfun);              \
            break;                                                        \
          case_mdarray: case_obvector: case_ob2vector: case_ob4vector:    \
          case_ob8vector: case_ob16vector: case_ob32vector: case_ostring: \
          case_ovector: # Arrays that are not simple:                     \
            while (objptr < physpage_end)                                 \
              walk_area_iarray(objptr,physpage_end,walkfun);              \
            break;                                                        \
          case_weakkvt: # weak-key-value-table                            \
          case_svector: # simple-vector                                   \
            while (objptr < physpage_end)                                 \
              walk_area_svector(objptr,physpage_end,walkfun);             \
            break;                                                        \
          case_record: # Record                                           \
            while (objptr < physpage_end)                                 \
              walk_area_record(objptr,physpage_end,walkfun);              \
            break;                                                        \
          default: # Such objects do not occur.                           \
            /*NOTREACHED*/ abort();                                       \
      }} while(0)
  #endif
  #ifdef SPVW_MIXED
    #ifdef TYPECODES
      #define walk_area(heapnr,physpage_start,physpage_end,walkfun)          \
        do { var aint objptr = physpage_start;                               \
          switch (heapnr) {                                                  \
            case 0: # objects of variable length                             \
              while (objptr < physpage_end) {                                \
                switch (typecode_at(objptr)) { # type of the next object     \
                  case_symbolwithflags: # symbol                             \
                    walk_area_symbol(objptr,physpage_end,walkfun);           \
                    break;                                                   \
                  case_mdarray: case_obvector: case_ob2vector:               \
                  case_ob4vector: case_ob8vector: case_ob16vector:           \
                  case_ob32vector: case_ostring: case_ovector:               \
                    # arrays that are not simple:                            \
                    walk_area_iarray(objptr,physpage_end,walkfun);           \
                    break;                                                   \
                  case_weakkvt: # weak-key-value-table                       \
                  case_svector: # simple-vector                              \
                    walk_area_svector(objptr,physpage_end,walkfun);          \
                    break;                                                   \
                  case_record: # record                                      \
                    walk_area_record(objptr,physpage_end,walkfun);           \
                    break;                                                   \
                  default: # simple-bit-vector, simple-string, bignum, float \
                    objptr += objsize((Varobject)objptr);                    \
                    break;                                                   \
              }}                                                             \
              break;                                                         \
            case 1: # Two-Pointer-Objects                                    \
              walk_area_cons(objptr,physpage_end,walkfun);                   \
              break;                                                         \
            default: /*NOTREACHED*/ abort();                                 \
        }} while(0)
    #else
      #define walk_area(heapnr,physpage_start,physpage_end,walkfun)       \
        do { var aint objptr = physpage_start;                            \
          switch (heapnr) {                                               \
            case 0: # objects of variable length                          \
              while (objptr < physpage_end) {                             \
                switch (record_type((Record)objptr)) { # next object type \
                  case Rectype_mdarray:                                   \
                  case Rectype_bvector:                                   \
                  case Rectype_b2vector:                                  \
                  case Rectype_b4vector:                                  \
                  case Rectype_b8vector:                                  \
                  case Rectype_b16vector:                                 \
                  case Rectype_b32vector:                                 \
                  case Rectype_reallocstring:                             \
                  case Rectype_string:                                    \
                  case Rectype_vector:                                    \
                    # arrays that are not simple:                         \
                    walk_area_iarray(objptr,physpage_end,walkfun);        \
                    break;                                                \
                  case Rectype_WeakKVT: # weak-key-value-table            \
                  case Rectype_Svector: # simple-vector                   \
                    walk_area_svector(objptr,physpage_end,walkfun);       \
                    break;                                                \
                  case Rectype_Sbvector:                                  \
                  case Rectype_Sb2vector:                                 \
                  case Rectype_Sb4vector:                                 \
                  case Rectype_Sb8vector:                                 \
                  case Rectype_Sb16vector:                                \
                  case Rectype_Sb32vector:                                \
                  case Rectype_S8string: case Rectype_Imm_S8string:       \
                  case Rectype_S16string: case Rectype_Imm_S16string:     \
                  case Rectype_S32string: case Rectype_Imm_S32string:     \
                  case Rectype_Bignum:                                    \
                  case Rectype_Ffloat:                                    \
                  case Rectype_Dfloat:                                    \
                  case Rectype_Lfloat:                                    \
                    # simple-byte-vector, simple-string, bignum, float    \
                    objptr += objsize((Varobject)objptr);                 \
                    break;                                                \
                  default: # Srecord/Xrecord                              \
                    walk_area_record(objptr,physpage_end,walkfun);        \
                    break;                                                \
              }}                                                          \
              break;                                                      \
            case 1: # two-pointer-objects                                 \
              walk_area_cons(objptr,physpage_end,walkfun);                \
              break;                                                      \
            default: /*NOTREACHED*/ abort();                              \
        }} while(0)
    #endif
  #endif

  #define walk_physpage(heapnr,physpage,pageend,heapend,walkfun)         \
    do {{ var uintC count = physpage->continued_count;                   \
        if (count > 0) {                                                 \
          var object* ptr = physpage->continued_addr;                    \
          dotimespC(count,count, { walkfun(*ptr); ptr++; } );            \
        }}                                                               \
      { var aint physpage_end = (pageend < heapend ? pageend : heapend); \
        walk_area(heapnr,physpage->firstobject,physpage_end,walkfun);    \
    }} while(0)

  # Same thing as functions.

  local void walk_area_ (uintL heapnr, aint physpage_start, aint physpage_end,
                         walkstep_fun walkstep) {
    #define walkstep1(obj)  walkstep(&(obj))
    walk_area(heapnr,physpage_start,physpage_end,walkstep1);
    #undef walkstep1
  }

  local void walk_physpage_ (uintL heapnr, const physpage_state* physpage,
                             aint pageend, aint heapend,
                             walkstep_fun walkstep) {
    #define walkstep1(obj)  walkstep(&(obj))
    walk_physpage(heapnr,physpage,pageend,heapend,walkstep1);
    #undef walkstep1
  }

  local void build_old_generation_cache (uintL heapnr);
  local void build_old_generation_cache(heapnr)
    var uintL heapnr;
    { if (is_heap_containing_objects(heapnr)) { # objects that contain no pointers, need no cache.
        var Heap* heap = &mem.heaps[heapnr];
        var aint gen0_start = heap->heap_gen0_start;
        var aint gen0_end = heap->heap_gen0_end;
        var aint gen0_start_pa = gen0_start & -physpagesize; # page-aligned
        var aint gen0_end_pa = (gen0_end + (physpagesize-1)) & -physpagesize; # page-aligned
        var uintL physpage_count = (gen0_end_pa - gen0_start_pa) >> physpageshift;
        if (physpage_count==0) {
          xfree(heap->physpages); heap->physpages = NULL;
        } else {
          # NB: The algorithms below work in terms of "page boundary crossings".
          # An object occupying the memory range [objptr,nextptr) is considered to
          # cover the page boundaries  addr  with  physpagesize | addr  and
          # objptr < addr <= nextptr. (*Not* objptr <= addr < nextptr.) When a
          # page boundary is crossed, the continued_addr, continued_count, firstobject
          # fields of the physpage after it are set. Therefore, if gen0_end happens
          # to lie on a page boundary, we need room for one more physpage_state.
          # It will only be written to, never really be used (because the page after
          # this last page boundary doesn't really exist).
          heap->physpages = (physpage_state*) xrealloc(heap->physpages,(physpage_count+(gen0_end==gen0_end_pa))*sizeof(physpage_state));
          if (!(heap->physpages==NULL)) {
            #if defined(SELFMADE_MMAP) && !defined(SPVW_PURE_BLOCKS)
            # now at the latest the memory content has to be fetched from the mem-file.
            # (the conses could be delayed still further, but does that pay off?)
            {
              var uintL pageno;
              for (pageno = 0; pageno < heap->memfile_numpages; pageno++)
                if (handle_mmap_fault(heap->memfile_offset+(pageno<<physpageshift),
                                      gen0_start+(pageno<<physpageshift),
                                      &heap->memfile_pages[pageno])
                    <0)
                  abort();
            }
            #endif
            # When we are finished, both the cache and the memory content
            # will be valid:
            xmmprotect(heap, gen0_start_pa, gen0_end_pa-gen0_start_pa, PROT_READ);
            # fill heap->physpages[0..physpage_count-1] :
            {
              var physpage_state* physpage = heap->physpages;
              var uintL count;
              dotimespL(count,physpage_count, {
                physpage->protection = PROT_READ;
                physpage->cache_size = 0; physpage->cache = NULL;
                physpage++;
              });
            }
            if (is_cons_heap(heapnr)) {
              # conses and similar
              # from gen0_start to gen0_end everything is a pointer.
              var physpage_state* physpage = heap->physpages;
              var uintL count;
              #ifndef SPVW_MIXED_BLOCKS_OPPOSITE
              # all pages except the last are full, the last page is partly full.
              dotimesL(count,physpage_count-1, {
                # for i=0,1,...:
                #   gen0_start = heap->heap_gen0_start + i*physpagesize
                #   physpage = &heap->physpages[i]
                physpage->continued_addr = (object*)gen0_start;
                physpage->continued_count = physpagesize/sizeof(object);
                gen0_start += physpagesize;
                physpage->firstobject = gen0_start;
                physpage++;
              });
              physpage->continued_addr = (object*)gen0_start;
              physpage->continued_count = (gen0_end-gen0_start)/sizeof(object);
              physpage->firstobject = gen0_end;
              #else
              # all pages except the first are full, the first page is partly full.
              physpage->continued_addr = (object*)gen0_start;
              physpage->continued_count = ((gen0_start_pa+physpagesize)-gen0_start)/sizeof(object);
              physpage->firstobject = gen0_start = gen0_start_pa+physpagesize;
              dotimesL(count,physpage_count-1, {
                physpage++;
                # for i=1,...:
                #   gen0_start = (heap->heap_gen0_start & -physpagesize) + i*physpagesize
                #   physpage = &heap->physpages[i]
                physpage->continued_addr = (object*)gen0_start;
                physpage->continued_count = physpagesize/sizeof(object);
                gen0_start += physpagesize;
                physpage->firstobject = gen0_start;
              });
              #endif
            } else {
              # is_varobject_heap(heapnr), objects of variable length
              var physpage_state* physpage = heap->physpages;
              var aint objptr = gen0_start;
              # for i=0,1,...:
              #   gen0_start = heap->heap_gen0_start + i*physpagesize
              #   physpage = &heap->physpages[i]
              # with increasing i we move from one page to the next.
              # simultaneously, we move from one object to the next and mark
              # all pointers between objptr (pointer to the current object)
              # and nextptr (pointer to the next object). Fortunately,
              # in all our objects the pointers are adjacent to each other:
              # starting at ptr, there are count pointers.
              # the interval ptr...ptr+count*sizeof(object) will now be dissected.
              #ifdef SPVW_PURE
              switch (heapnr) {
                case_symbol: # symbol
                  physpage->continued_addr = (object*)gen0_start; # irrelevant
                  physpage->continued_count = 0;
                  physpage->firstobject = gen0_start;
                  gen0_start += physpagesize; physpage++;
                  while (objptr < gen0_end) {
                    var aint nextptr = objptr + size_symbol();
                    # here is gen0_start-physpagesize <= objptr < gen0_start.
                    if (nextptr >= gen0_start) {
                      var aint ptr = objptr+symbol_objects_offset;
                      var uintC count = (sizeof(symbol_)-symbol_objects_offset)/sizeof(object);
                      if (ptr < gen0_start) {
                        physpage->continued_addr = (object*)gen0_start;
                        physpage->continued_count = count - (gen0_start-ptr)/sizeof(object);
                      } else {
                        physpage->continued_addr = (object*)ptr;
                        physpage->continued_count = count;
                      }
                      physpage->firstobject = nextptr;
                      # At most one page boundary is crossed at a time.
                      gen0_start += physpagesize; physpage++;
                    }
                    objptr = nextptr;
                  }
                  if (!(objptr == gen0_end)) abort();
                  break;
                case_mdarray: case_obvector: case_ob2vector: case_ob4vector: case_ob8vector: case_ob16vector: case_ob32vector: case_ostring: case_ovector: # non-simple arrays:
                  physpage->continued_addr = (object*)gen0_start; # irrelevant
                  physpage->continued_count = 0;
                  physpage->firstobject = gen0_start;
                  gen0_start += physpagesize; physpage++;
                  while (objptr < gen0_end) {
                    var aint nextptr = objptr + objsize_iarray((Iarray)objptr);
                    # here is gen0_start-physpagesize <= objptr < gen0_start.
                    if (nextptr >= gen0_start) {
                      var aint ptr = (aint)&((Iarray)objptr)->data;
                      # count = 1;
                      if (ptr < gen0_start) {
                        physpage->continued_addr = (object*)gen0_start; # irrelevant
                        physpage->continued_count = 0;
                      } else {
                        physpage->continued_addr = (object*)ptr;
                        physpage->continued_count = 1;
                      }
                      # At most one page boundary has been crossed.
                      # Then, there are no more pointers (until nextptr).
                      loop {
                        physpage->firstobject = nextptr;
                        gen0_start += physpagesize; physpage++;
                        if (nextptr < gen0_start) break;
                        physpage->continued_addr = (object*)gen0_start; # irrelevant
                        physpage->continued_count = 0;
                      }
                    }
                    objptr = nextptr;
                  }
                  if (!(objptr == gen0_end)) abort();
                  break;
                case_weakkvt: # weak-key-value-table
                case_svector: # simple-vector
                  physpage->continued_addr = (object*)gen0_start; # irrelevant
                  physpage->continued_count = 0;
                  physpage->firstobject = gen0_start;
                  gen0_start += physpagesize; physpage++;
                  while (objptr < gen0_end) {
                    var uintL count = svector_length((Svector)objptr);
                    var aint nextptr = objptr + size_svector(count);
                    # here is gen0_start-physpagesize <= objptr < gen0_start.
                    if (nextptr >= gen0_start) {
                      var aint ptr = (aint)&((Svector)objptr)->data[0];
                      if (ptr < gen0_start) {
                        var uintL count_thispage = (gen0_start-ptr)/sizeof(object);
                        if ((varobject_alignment == sizeof(object)) # this enforces count >= count_thispage
                            || (count >= count_thispage)
                           )
                          count -= count_thispage;
                        else
                          count = 0;
                        ptr = gen0_start;
                      }
                      do {
                        physpage->continued_addr = (object*)ptr;
                        gen0_start += physpagesize;
                        var uintL count_thispage = (gen0_start-ptr)/sizeof(object);
                        if (count >= count_thispage) {
                          physpage->continued_count = count_thispage;
                          count -= count_thispage;
                        } else {
                          physpage->continued_count = count; count = 0;
                        }
                        physpage->firstobject = nextptr;
                        physpage++;
                        ptr = gen0_start;
                      } until (nextptr < gen0_start);
                    }
                    objptr = nextptr;
                  }
                  if (!(objptr == gen0_end)) abort();
                  break;
                case_record: # record
                  physpage->continued_addr = (object*)gen0_start; # irrelevant
                  physpage->continued_count = 0;
                  physpage->firstobject = gen0_start;
                  gen0_start += physpagesize; physpage++;
                  while (objptr < gen0_end) {
                    var uintC count;
                    var aint nextptr;
                    if (record_type((Record)objptr) < rectype_limit) {
                      count = srecord_length((Srecord)objptr);
                      nextptr = objptr + size_srecord(count);
                    } else {
                      count = xrecord_length((Xrecord)objptr);
                      nextptr = objptr + size_xrecord(count,xrecord_xlength((Xrecord)objptr));
                    }
                    if (nextptr >= gen0_start) {
                      var aint ptr = (aint)&((Record)objptr)->recdata[0];
                      if (ptr < gen0_start) {
                        var uintL count_thispage = (gen0_start-ptr)/sizeof(object);
                        if (count >= count_thispage)
                          count -= count_thispage;
                        else
                          count = 0;
                        ptr = gen0_start;
                      }
                      do {
                        physpage->continued_addr = (object*)ptr;
                        gen0_start += physpagesize;
                        var uintL count_thispage = (gen0_start-ptr)/sizeof(object);
                        if (count >= count_thispage) {
                          physpage->continued_count = count_thispage;
                          count -= count_thispage;
                        } else {
                          physpage->continued_count = count; count = 0;
                        }
                        physpage->firstobject = nextptr;
                        physpage++;
                        ptr = gen0_start;
                      } until (nextptr < gen0_start);
                    }
                    objptr = nextptr;
                  }
                  if (!(objptr == gen0_end)) abort();
                  break;
                default:
                  # such objects do not occur.
                  abort();
              }
              #else # SPVW_MIXED
              physpage->continued_addr = (object*)gen0_start; # irrelevant
              physpage->continued_count = 0;
              physpage->firstobject = gen0_start;
              gen0_start += physpagesize; physpage++;
              while (objptr < gen0_end) {
                #ifdef TYPECODES
                switch (typecode_at(objptr)) # type of the next object
                #else
                goto case_record;
                switch (0)
                #endif
                {
                  #ifdef TYPECODES
                  case_symbolwithflags: # symbol
                    {
                      var aint nextptr = objptr + size_symbol();
                      # here is gen0_start-physpagesize <= objptr < gen0_start.
                      if (nextptr >= gen0_start) {
                        var aint ptr = objptr+symbol_objects_offset;
                        var uintC count = (sizeof(symbol_)-symbol_objects_offset)/sizeof(object);
                        if (ptr < gen0_start) {
                          physpage->continued_addr = (object*)gen0_start;
                          physpage->continued_count = count - (gen0_start-ptr)/sizeof(object);
                        } else {
                          physpage->continued_addr = (object*)ptr;
                          physpage->continued_count = count;
                        }
                        physpage->firstobject = nextptr;
                        # At most one page boundary is crossed at a time.
                          gen0_start += physpagesize; physpage++;
                      }
                      objptr = nextptr;
                    }
                    break;
                  #endif
                  case_mdarray: case_obvector: case_ob2vector: case_ob4vector: case_ob8vector: case_ob16vector: case_ob32vector: case_ostring: case_ovector: # non-simple arrays:
                    {
                      var aint nextptr = objptr + objsize((Iarray)objptr);
                      # here is gen0_start-physpagesize <= objptr < gen0_start.
                      if (nextptr >= gen0_start) {
                        var aint ptr = (aint)&((Iarray)objptr)->data;
                        # count = 1;
                        if (ptr < gen0_start) {
                          physpage->continued_addr = (object*)gen0_start; # irrelevant
                          physpage->continued_count = 0;
                        } else {
                          physpage->continued_addr = (object*)ptr;
                          physpage->continued_count = 1;
                        }
                        # At most one page boundary has been crossed.
                        # Then, there are no more pointers (until nextptr).
                        loop {
                          physpage->firstobject = nextptr;
                          gen0_start += physpagesize; physpage++;
                          if (nextptr < gen0_start) break;
                          physpage->continued_addr = (object*)gen0_start; # irrelevant
                          physpage->continued_count = 0;
                        }
                      }
                      objptr = nextptr;
                    }
                    break;
                  case_weakkvt: # weak-key-value-table
                  case_svector: # simple-vector
                    {
                      var uintL count = svector_length((Svector)objptr);
                      var aint nextptr = objptr + size_svector(count);
                      # here is gen0_start-physpagesize <= objptr < gen0_start.
                      if (nextptr >= gen0_start) {
                        var aint ptr = (aint)&((Svector)objptr)->data[0];
                        if (ptr < gen0_start) {
                          var uintL count_thispage = (gen0_start-ptr)/sizeof(object);
                          if ((varobject_alignment == sizeof(object)) # that enforces count >= count_thispage
                              || (count >= count_thispage)
                             )
                            count -= count_thispage;
                          else
                            count = 0;
                          ptr = gen0_start;
                        }
                        do {
                          physpage->continued_addr = (object*)ptr;
                          gen0_start += physpagesize;
                          var uintL count_thispage = (gen0_start-ptr)/sizeof(object);
                          if (count >= count_thispage) {
                            physpage->continued_count = count_thispage;
                            count -= count_thispage;
                          } else {
                            physpage->continued_count = count; count = 0;
                          }
                          physpage->firstobject = nextptr;
                          physpage++;
                          ptr = gen0_start;
                        } until (nextptr < gen0_start);
                      }
                      objptr = nextptr;
                    }
                    break;
                  case_record: # record
                    #ifndef TYPECODES
                    switch (record_type((Record)objptr)) {
                      case_Rectype_mdarray_above;
                      case_Rectype_obvector_above;
                      case_Rectype_ob2vector_above;
                      case_Rectype_ob4vector_above;
                      case_Rectype_ob8vector_above;
                      case_Rectype_ob16vector_above;
                      case_Rectype_ob32vector_above;
                      case_Rectype_ostring_above;
                      case_Rectype_ovector_above;
                      case_Rectype_Svector_above;
                      case_Rectype_WeakKVT_above;
                      case Rectype_Sbvector:
                      case Rectype_Sb2vector:
                      case Rectype_Sb4vector:
                      case Rectype_Sb8vector:
                      case Rectype_Sb16vector:
                      case Rectype_Sb32vector:
                      case Rectype_S8string: case Rectype_Imm_S8string:
                      case Rectype_S16string: case Rectype_Imm_S16string:
                      case Rectype_S32string: case Rectype_Imm_S32string:
                      case Rectype_Bignum:
                      case Rectype_Ffloat: case Rectype_Dfloat: case Rectype_Lfloat:
                        goto case_nopointers;
                      default: ;
                    }
                    #endif
                    {
                      var uintC count;
                      var aint nextptr;
                      if (record_type((Record)objptr) < rectype_limit) {
                        count = srecord_length((Srecord)objptr);
                        nextptr = objptr + size_srecord(count);
                      } else {
                        count = xrecord_length((Xrecord)objptr);
                        nextptr = objptr + size_xrecord(count,xrecord_xlength((Xrecord)objptr));
                      }
                      if (nextptr >= gen0_start) {
                        var aint ptr = (aint)&((Record)objptr)->recdata[0];
                        if (ptr < gen0_start) {
                          var uintL count_thispage = (gen0_start-ptr)/sizeof(object);
                          if (count >= count_thispage)
                            count -= count_thispage;
                          else
                            count = 0;
                          ptr = gen0_start;
                        }
                        do {
                          physpage->continued_addr = (object*)ptr;
                          gen0_start += physpagesize;
                          var uintL count_thispage = (gen0_start-ptr)/sizeof(object);
                          if (count >= count_thispage) {
                            physpage->continued_count = count_thispage;
                            count -= count_thispage;
                          } else {
                            physpage->continued_count = count; count = 0;
                          }
                          physpage->firstobject = nextptr;
                          physpage++;
                          ptr = gen0_start;
                        } until (nextptr < gen0_start);
                      }
                      objptr = nextptr;
                    }
                    break;
                  case_nopointers:
                  default: # simple-bit-vector, simple-string, bignum, float
                    # no pointers.
                    objptr += objsize((Varobject)objptr);
                    while (objptr >= gen0_start) {
                      physpage->continued_addr = (object*)gen0_start; # irrelevant
                      physpage->continued_count = 0;
                      physpage->firstobject = objptr;
                      gen0_start += physpagesize; physpage++;
                    }
                    break;
                }
              }
              if (!(objptr == gen0_end)) abort();
              #endif
            }
          }
        }
      }
    }

  local void rebuild_old_generation_cache (uintL heapnr);
  local void rebuild_old_generation_cache(heapnr)
    var uintL heapnr;
    {
      if (is_heap_containing_objects(heapnr)) { # objects, that contain no pointers, need no cache.
        var Heap* heap = &mem.heaps[heapnr];
        var aint gen0_start = heap->heap_gen0_start;
        var aint gen0_end = heap->heap_gen0_end;
        if ((gen0_start < gen0_end) && !(heap->physpages==NULL)) {
          var DYNAMIC_ARRAY(cache_buffer,old_new_pointer,physpagesize/sizeof(object));
          var physpage_state* physpage = heap->physpages;
          gen0_start &= -physpagesize;
          do {
            if (physpage->protection == PROT_READ_WRITE) {
              var old_new_pointer* cache_ptr = &cache_buffer[0];
              #ifdef TYPECODES
                #define cache_at(obj)  \
                  { var tint type = mtypecode(obj);                                \
                    if (!gcinvariant_type_p(type)) # un-movable?                   \
                      if (!in_old_generation(obj,type,mem.heapnr_from_type[type])) \
                        # obj is a pointer into the new generation -> memorize     \
                        { cache_ptr->p = &(obj); cache_ptr->o = (obj); cache_ptr++; } \
                  }
              #else
                #define cache_at(obj)  \
                  { if (!gcinvariant_object_p(obj))                                \
                      if (!in_old_generation(obj,,(as_oint(obj)>>1)&1))            \
                        # obj is a pointer into the new generation -> memorize     \
                        { cache_ptr->p = &(obj); cache_ptr->o = (obj); cache_ptr++; } \
                  }
              #endif
              walk_physpage(heapnr,physpage,gen0_start+physpagesize,gen0_end,cache_at);
              #undef cache_at
              var uintL cache_size = cache_ptr - &cache_buffer[0];
              if (cache_size <= (physpagesize/sizeof(object))/4) {
                # we cache a page only, if at most 25% are occupied with pointers
                # to the new generation. Else, creating a cache
                # is a waste of space.
                physpage->cache_size = cache_size;
                if (cache_size == 0) {
                  xfree(physpage->cache); physpage->cache = NULL;
                } else {
                  physpage->cache = (old_new_pointer*) xrealloc(physpage->cache,cache_size*sizeof(old_new_pointer));
                  if (physpage->cache == NULL)
                    goto no_cache;
                  var old_new_pointer* ptr1 = &cache_buffer[0];
                  var old_new_pointer* ptr2 = physpage->cache;
                  dotimespL(cache_size,cache_size, { *ptr2++ = *ptr1++; } );
                }
                xmmprotect(heap,gen0_start,physpagesize,PROT_READ);
                physpage->protection = PROT_READ;
              } else {
                xfree(physpage->cache); physpage->cache = NULL;
               no_cache: ;
              }
            }
            gen0_start += physpagesize;
            physpage++;
          } while (gen0_start < gen0_end);
          FREE_DYNAMIC_ARRAY(cache_buffer);
        }
      }
    }

#ifdef SPVW_PURE_BLOCKS
  local inline void xmmprotect_old_generation_cache (uintL heapnr);
  local inline void xmmprotect_old_generation_cache(heapnr)
    var uintL heapnr;
    {
      if (is_heap_containing_objects(heapnr)) {
        var Heap* heap = &mem.heaps[heapnr];
        if (!(heap->physpages==NULL)) {
          var aint gen0_start_pa = heap->heap_gen0_start & -physpagesize;
          var aint gen0_end_pa = (heap->heap_gen0_end + (physpagesize-1)) & -physpagesize;
          xmmprotect(heap, gen0_start_pa, gen0_end_pa-gen0_start_pa, PROT_READ);
          var uintL physpage_count = (gen0_end_pa-gen0_start_pa)>>physpageshift;
          var physpage_state* physpage = heap->physpages;
          var uintL count;
          dotimespL(count,physpage_count, {
            physpage->protection = PROT_READ;
            physpage++;
          });
        }
      }
    }
#endif

  # update the old generation with the help of the cache:
  local void prepare_old_generation (void);
  local void prepare_old_generation()
    {
      var uintL heapnr;
      for (heapnr=0; heapnr<heapcount; heapnr++)
        if (is_heap_containing_objects(heapnr)) {
          var Heap* heap = &mem.heaps[heapnr];
          var aint gen0_start = heap->heap_gen0_start;
          var aint gen0_end = heap->heap_gen0_end;
          gen0_start = gen0_start & -physpagesize;
          gen0_end = (gen0_end + (physpagesize-1)) & -physpagesize;
          if (gen0_start < gen0_end) {
            if (!(heap->physpages==NULL)) {
              # first superimpose read-write:
              xmmprotect(heap, gen0_start, gen0_end-gen0_start, PROT_READ_WRITE);
              # then empty the cache:
              var physpage_state* physpage = heap->physpages;
              var uintL physpagecount;
              dotimespL(physpagecount, (gen0_end-gen0_start) >> physpageshift, {
                if (physpage->protection == PROT_NONE) {
                  var uintL count = physpage->cache_size;
                  if (count > 0) {
                    var old_new_pointer* ptr = physpage->cache;
                    dotimespL(count,count, { *(ptr->p) = ptr->o; ptr++; } );
                  }
                }
                physpage->protection = PROT_READ_WRITE;
                xfree(physpage->cache); physpage->cache = NULL;
                physpage++;
              });
              /* xfree(heap->physpages); heap->physpages = NULL; */
            }
            # then, fill the gap between the old and the new generation,
            # in order to have the compaction-algorithms functional:
            if (is_cons_heap(heapnr)) {
              var object* ptr;
              var uintL count;
              #ifdef SPVW_MIXED_BLOCKS_OPPOSITE
              ptr = (object*) heap->heap_gen1_end;
              count = (heap->heap_gen0_start - heap->heap_gen1_end)/sizeof(object);
              dotimesL(count,count, { *ptr++ = nullobj; } );
              #else # SPVW_PURE_BLOCKS || SPVW_MIXED_BLOCKS_STAGGERED
              ptr = (object*) heap->heap_gen0_end;
              count = (heap->heap_gen1_start - heap->heap_gen0_end)/sizeof(object);
              #ifndef SELFMADE_MMAP
              dotimesL(count,count, { *ptr++ = nullobj; } );
              #else
              if (count > 0) {
                var aint gen0_end = heap->heap_gen0_end;
                heap->heap_gen0_end = heap->heap_gen1_start; # temporary - for handle_fault() if SELFMADE_MMAP
                dotimespL(count,count, { *ptr++ = nullobj; } );
                heap->heap_gen0_end = gen0_end; # temporary - end
              }
              #endif
              #endif
            }
          }
        }
    }

#endif

#if defined(DEBUG_SPVW) && defined(GENERATIONAL_GC)
  # control of the cache of the old_new_pointer:
  #define CHECK_GC_CACHE()  gc_cache_check()
  local void gc_cache_check (void);
  local void gc_cache_check()
    {
      var uintL heapnr;
      for (heapnr=0; heapnr<heapcount; heapnr++)
        if (is_heap_containing_objects(heapnr)) {
          var Heap* heap = &mem.heaps[heapnr];
          var aint gen0_start = heap->heap_gen0_start;
          var aint gen0_end = heap->heap_gen0_end;
          var aint gen0_start_pa = gen0_start & -physpagesize; # page-aligned
          var aint gen0_end_pa = (gen0_end + (physpagesize-1)) & -physpagesize; # page-aligned
          var uintL physpage_count = (gen0_end_pa - gen0_start_pa) >> physpageshift;
          if (physpage_count > 0) {
            var physpage_state* physpage = heap->physpages;
            if (!(physpage==NULL)) {
              var uintL count;
              dotimespL(count,physpage_count, {
                var aint end = (gen0_start & -physpagesize) + physpagesize;
                if (gen0_end < end) { end = gen0_end; }
                if (physpage->firstobject < end) { end = physpage->firstobject; }
                if (!(gen0_start <= (aint)physpage->continued_addr)) abort();
                if (!((aint)physpage->continued_addr + physpage->continued_count*sizeof(object) <= end)) abort();
                gen0_start &= -physpagesize;
                gen0_start += physpagesize;
                physpage++;
              });
            }
          }
        }
    }
  # control, if all pointers are listed in the cache
  # and do not "point into the forest." (don't know which idiom is appropriate)
  #define CHECK_GC_GENERATIONAL()  gc_overall_check()
  local void gc_overall_check (void);
    # control of a single pointer:
    local bool gc_check_at (object* objptr);
    local bool gc_check_at(objptr)
      var object* objptr;
      {
        var object obj = *objptr;
        var tint type = typecode(obj);
        #ifdef SPVW_PURE
        if (is_unused_heap(type))
          return false;
        #else
        if (gcinvariant_type_p(type))
          return false;
        #endif
        var aint addr = canonaddr(obj);
        var Heap* heap;
        #ifdef SPVW_PURE
        heap = &mem.heaps[type];
        #else # SPVW_MIXED
        heap = &mem.heaps[mem.heapnr_from_type[type]];
        #endif
        if ((addr >= heap->heap_gen0_start) && (addr < heap->heap_gen0_end))
          return false;
        #ifdef SPVW_MIXED_BLOCKS_OPPOSITE
        if (is_cons_heap(mem.heapnr_from_type[type])) {
          if ((addr >= heap->heap_start) && (addr < heap->heap_gen1_end))
            return true; # pointer into the new generation
        } else
        #endif
        {
          if ((addr >= heap->heap_gen1_start) && (addr < heap->heap_end))
            return true; # pointer into the new generation
        }
        if ((type == symbol_type)
            && (as_oint(obj) - as_oint(symbol_tab_ptr_as_object(&symbol_tab))
                < (sizeof(symbol_tab)<<(oint_addr_shift-addr_shift))
           )   )
          return false;
        abort();
      }
  local void gc_overall_check()
    {
      var uintL heapnr;
      for (heapnr=0; heapnr<heapcount; heapnr++)
        if (is_heap_containing_objects(heapnr)) {
          var Heap* heap = &mem.heaps[heapnr];
          var aint gen0_start = heap->heap_gen0_start;
          var aint gen0_end = heap->heap_gen0_end;
          if (gen0_start < gen0_end)
            if (heap->physpages==NULL) {
              walk_area_(heapnr,gen0_start,gen0_end,gc_check_at); # fallback
            } else {
              var physpage_state* physpage = heap->physpages;
              gen0_start &= -physpagesize;
              do {
                if (physpage->protection == PROT_READ) {
                  # do the pointers in the Cache and in the page match?
                  var uintL count = physpage->cache_size;
                  if (count > 0) {
                    var old_new_pointer* ptr = physpage->cache;
                    var aint last_p = gen0_start-1;
                    dotimespL(count,count, {
                      if (!eq(*(ptr->p),ptr->o))
                        abort();
                      if (!(last_p < (aint)ptr->p))
                        abort();
                      last_p = (aint)ptr->p;
                      ptr++;
                    });
                  }
                }
                gen0_start += physpagesize;
                if (physpage->protection == PROT_NONE) {
                  # take advantage of cache, traverse cached pointers:
                  var uintL count = physpage->cache_size;
                  if (count > 0) {
                    var old_new_pointer* ptr = physpage->cache;
                    dotimespL(count,count, { gc_check_at(&ptr->o); ptr++; } );
                  }
                } else {
                  # traverse the whole page-content:
                  walk_physpage_(heapnr,physpage,gen0_start,gen0_end,gc_check_at);
                }
                physpage++;
              } while (gen0_start < gen0_end);
            }
        }
    }
  # For error discovery: save administrational data before and after GC.
  #define SAVE_GC_DATA()  save_gc_data()
  local void save_gc_data (void);
  typedef struct gc_data { struct gc_data * next; Heap heaps[heapcount]; } *
          gc_data_list;
  local var gc_data_list gc_history;
  local void save_gc_data()
    {
      # copy the current GC-data to the head of the list gc_history :
      var gc_data_list new_data = (struct gc_data *) malloc(sizeof(struct gc_data));
      if (!(new_data==NULL)) {
        var uintL heapnr;
        for (heapnr=0; heapnr<heapcount; heapnr++) {
          var Heap* heap = &new_data->heaps[heapnr];
          *heap = mem.heaps[heapnr];
          if (!(heap->physpages==NULL)) {
            var uintL physpagecount =
              (((heap->heap_gen0_end + (physpagesize-1)) & -physpagesize)
               - (heap->heap_gen0_start & -physpagesize)
              ) >> physpageshift;
            var physpage_state* physpages = NULL;
            if (physpagecount > 0)
              physpages = (physpage_state*) malloc(physpagecount*sizeof(physpage_state));
            if (!(physpages==NULL)) {
              var uintL i;
              for (i=0; i<physpagecount; i++) {
                physpages[i] = heap->physpages[i];
                if (!(physpages[i].cache==NULL)) {
                  var uintC cache_size = physpages[i].cache_size;
                  if (cache_size > 0) {
                    var old_new_pointer* cache = (old_new_pointer*) malloc(cache_size*sizeof(old_new_pointer));
                    if (!(cache==NULL)) {
                      var old_new_pointer* old_cache = physpages[i].cache;
                      var uintC j;
                      for (j=0; j<cache_size; j++)
                        cache[j] = old_cache[j];
                    }
                    physpages[i].cache = cache;
                  }
                }
              }
            }
            heap->physpages = physpages;
          }
        }
        new_data->next = gc_history;
        gc_history = new_data;
      }
    }
#else
  #define CHECK_GC_CACHE()
  #define CHECK_GC_GENERATIONAL()
  #define SAVE_GC_DATA()
#endif
