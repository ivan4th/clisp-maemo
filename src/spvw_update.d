# Updating all heap objects in the world (i.e. in the heap and stack).

# ------------------------------ Specification --------------------------------

# For the following macros, the macro update(objptr) must be defined, with the
# signature:  local void update (object* objptr);

# Update all the world, except the heaps and the stacks.
#   update_tables();

# Update the cons heaps.
#   #define update_conspage ...
#   update_conses();
#   #undef update_conspage
# Some possible implementation of update_conspage.
#   update_conspage_normal

# Update the varobject heaps.
#   #define update_ht_invalid ...
#   #define update_fpointer_invalid ...
#   #define update_fp_invalid ...
#   #define update_fsubr_function ...
#   #define update_fs_function ...
#   #define update_page ...
#   update_varobjects();
#   #undef update_page
#   #undef update_fs_function
#   #undef update_fsubr_function
#   #undef update_fp_invalid
#   #undef update_fpointer_invalid
#   #undef update_ht_invalid
# Some possible implementation of update_page.
#   update_page_normal

# Update the list of pending weak pointers.
#   update_weakpointers();
# Same, but here update(objptr) may modify *objptr. and the
# value before update should be taken while following the list.
#   update_weakpointers_mod();
# ditto for weak key-value tables:
#   update_weakkvtables() and update_weakkvtables_mod()

# Update the stacks.
#   #define update_stackobj ...
#   update_stacks();
#   #undef update_stackobj
# Some possible implementation of update_stackobj.
#   update_stackobj_normal

# ------------------------------ Implementation -------------------------------

# update program constants:
#define update_subr_tab()                                       \
  for_all_subrs({                                               \
    var object* p = (object*)((aint)ptr+subr_const_offset);     \
    var uintC c;                                                \
    dotimespC(c,subr_const_anz, { update(p); p++; } );          \
  })
#define update_symbol_tab()                     \
  for_all_constsyms({ # traverse symbol_tab     \
    var object* p;                              \
    p = &ptr->symvalue; update(p);              \
    p = &ptr->symfunction; update(p);           \
    p = &ptr->proplist; update(p);              \
    p = &ptr->pname; update(p);                 \
    p = &ptr->homepackage; update(p);           \
  })
#define update_object_tab()                                             \
  do { for_all_constobjs( update(objptr); ); # traverse object_tab      \
       for_all_threadobjs( update(objptr); ); # traverse threads        \
  } while(0)
#define update_tables()                         \
  do { update_subr_tab();                       \
       update_symbol_tab();                     \
       update_object_tab();                     \
  } while(0)

# update the pointers in the Cons-cells:
#define update_conspage_normal(page)                                          \
  do { var aint objptr = page->page_start;                                    \
       var aint objptrend = page->page_end;                                   \
       # update all pointers in the (new) CONS-region start <= address < end: \
       while (objptr != objptrend) {                                          \
         update((object*)objptr);                                             \
         objptr += sizeof(object);                                            \
         update((object*)objptr);                                             \
         objptr += sizeof(object);                                            \
  }} while(0)
#define update_conses() for_each_cons_page(page, update_conspage(page) )

# update pointers in the objects of variable length:
#define update_page_normal(page,updater)                        \
  do { var aint ptr = page->page_start;                         \
       var aint ptrend = page->page_end;                        \
       # traverse all objects with address >=ptr, <ptrend :     \
       while (ptr != ptrend) { # until ptr has reached the end  \
         # traverse next object with address ptr (< ptrend) :   \
         updater(typecode_at(ptr)); # and advance               \
  }} while(0)
# subroutines:
#define do_update_symbol()                                                    \
  do { var object* p = (object*)pointerplus(ptr,symbol_objects_offset);       \
    var uintC count;                                                          \
    dotimespC(count,((sizeof(symbol_)-symbol_objects_offset)/sizeof(object)), \
      { update(p); p++; } );                                                  \
  } while(0)
#define do_update_svector()                             \
  do { var uintL count = svector_length((Svector)ptr);  \
       if (count != 0) {                                \
         var object* p = &((Svector)ptr)->data[0];      \
         dotimespL(count,count, { update(p); p++; } );  \
  }} while(0)
#define do_update_iarray()  \
  do { var object* p = &((Iarray)ptr)->data; update(p); } while(0)
#define do_update_record()                                                    \
  do { # on update of pointers, the hash-tables are invalidated               \
       # (because the hash function of an object depends on its address,      \
       # which is now changed).                                               \
    if (record_type((Record)ptr) == Rectype_Hashtable) # a hash-table ?       \
      { update_ht_invalid((Hashtable)ptr); } # yes -> note for reorganisation \
    else if (update_fpointer_invalid &&  # foreign-pointer ?                  \
             (record_type((Record)ptr) == Rectype_Fpointer))                  \
      { update_fp_invalid((Record)ptr); } # yes -> poss. invalidate           \
    else if (update_fsubr_function &&  # Fsubr ?                              \
             (record_type((Record)ptr) == Rectype_Fsubr))                     \
      { update_fs_function((Fsubr)ptr); } # yes -> poss. update address       \
   {var uintC count = (record_type((Record)ptr) < rectype_limit               \
                       ? srecord_length((Srecord)ptr)                         \
                       : xrecord_length((Xrecord)ptr));                       \
    if (count != 0) {                                                         \
      var object* p = &((Record)ptr)->recdata[0];                             \
      dotimespC(count,count, { update(p); p++; } );                           \
  }}} while(0)
# updates the object at 'ptr', whose typecode is given by 'type_expr'
# and advances ptr:
#ifdef SPVW_MIXED
 #ifdef TYPECODES
  #define update_varobject(type_expr)                                     \
   do { var tint type = (type_expr); # typeinfo                           \
        var uintL laenge = objsize((Varobject)ptr); # determine length    \
        var aint newptr = ptr+laenge; # pointer to next object            \
        # fall differentiation according to:                              \
        # symbol; simple-vector; non-simple array;                        \
        # Record (esp. hash-table); rest.                                 \
        switch (type) {                                                   \
         case_symbolwithflags: # Symbol: update all pointers              \
           do_update_symbol();                                            \
           break;                                                         \
          case_svector: # Simple-vector: update all pointers              \
           do_update_svector();                                           \
           break;                                                         \
          case_mdarray: case_obvector: case_ob2vector: case_ob4vector:    \
          case_ob8vector: case_ob16vector: case_ob32vector: case_ostring: \
          case_ovector: # non-simple array: update data vector            \
           do_update_iarray();                                            \
           break;                                                         \
          case_record: # Record: update all pointers                      \
           do_update_record();                                            \
           break;                                                         \
          default:  # all others contain no pointer that need update      \
           break; # -> do nothing                                         \
        }                                                                 \
        # advance to the next object                                      \
        ptr = newptr;                                                     \
   } while(0)
 #else # TYPECODES
  #define update_varobject(type_expr)                                   \
   do { var uintL laenge = objsize((Varobject)ptr); # determine length  \
        var aint newptr = ptr+laenge; # pointer to the next object      \
        switch (record_type((Record)ptr)) { # type of the next object   \
         case Rectype_mdarray:                                          \
         case Rectype_bvector:                                          \
         case Rectype_b2vector:                                         \
         case Rectype_b4vector:                                         \
         case Rectype_b8vector:                                         \
         case Rectype_b16vector:                                        \
         case Rectype_b32vector:                                        \
         case Rectype_reallocstring:                                    \
         case Rectype_string:                                           \
         case Rectype_vector:                                           \
          # non-simple array: update data vector                        \
          do_update_iarray();                                           \
          break;                                                        \
         case Rectype_Svector:                                          \
          # Simple-vector: update all pointers                          \
          do_update_svector();                                          \
          break;                                                        \
         case Rectype_Sbvector:                                         \
         case Rectype_Sb2vector:                                        \
         case Rectype_Sb4vector:                                        \
         case Rectype_Sb8vector:                                        \
         case Rectype_Sb16vector:                                       \
         case Rectype_Sb32vector:                                       \
         case Rectype_Sstring: case Rectype_Imm_Sstring:                \
         case Rectype_SmallSstring: case Rectype_Imm_SmallSstring:      \
         case Rectype_Bignum: case Rectype_Ffloat:                      \
         case Rectype_Dfloat: case Rectype_Lfloat:                      \
          # these contain no pointers that need update -> do nothing    \
          break;                                                        \
         default: # Record: update all pointers                         \
          do_update_record();                                           \
          break;                                                        \
        }                                                               \
        # advance to the next object                                    \
        ptr = newptr;                                                   \
   } while(0)
 #endif # TYPECODES
 #define update_varobjects()  \
   for_each_varobject_page(page, update_page(page,update_varobject); )
#endif # SPVW_MIXED
#ifdef SPVW_PURE
 #define update_symbol(type_expr)  # ignores type_expr                    \
   do { var uintL laenge = objsize_symbol((void*)ptr); # determine length \
        var aint newptr = ptr+laenge; # pointer to the next object        \
        # Symbol: update all pointers                                     \
        do_update_symbol();                                               \
        ptr = newptr; # advance to the next object                        \
   } while(0)
 #define update_svector(type_expr)  # ignores type_expr                    \
   do { var uintL laenge = objsize_svector((void*)ptr); # determine length \
        var aint newptr = ptr+laenge; # pointer to the next object         \
        # Simple-vector: update all pointers                               \
        do_update_svector();                                               \
        ptr = newptr; # advance to the next object                         \
   } while(0)
 #define update_iarray(type_expr)  # ignores type_expr                    \
   do { var uintL laenge = objsize_iarray((void*)ptr); # determine length \
        var aint newptr = ptr+laenge; # pointer to the next object        \
        # non-simple array: update data vector                            \
        do_update_iarray();                                               \
        ptr = newptr; # advance to the next object                        \
   } while(0)
 #define update_record(type_expr)  # ignores type_expr                    \
   do { var uintL laenge = objsize_record((void*)ptr); # determine length \
        var aint newptr = ptr+laenge; # pointer to the next object        \
        # Record: update all pointers                                     \
        do_update_record();                                               \
        ptr = newptr; # advance to the next object                        \
   } while(0)
 #define update_varobjects()                                            \
   for_each_varobject_page(page,{                                       \
     # fall differentiation according to:                               \
     # symbol; simple-vector; non-simpler array;                        \
     # Record (esp. hash-table); rest.                                  \
     switch (heapnr) {                                                  \
      case_symbol: update_page(page,update_symbol); break;              \
      case_svector: update_page(page,update_svector); break;            \
      case_mdarray: case_obvector: case_ob2vector: case_ob4vector:      \
      case_ob8vector: case_ob16vector: case_ob32vector: case_ostring:   \
      case_ovector: update_page(page,update_iarray); break;             \
      case_record: update_page(page,update_record); break;              \
      default: # all others contain no pointer that need update         \
       break; # -> do nothing                                           \
   }})
#endif # SPVW_PURE

# update weak-pointer-list:
#define update_weakpointer(ww)                                      \
  do { var object* p = &TheRecord(ww)->recdata[weakpointer_length]; \
       var uintC count = weakpointer_xlength/sizeof(object);        \
       dotimespC(count,count,{ update(p); p++; });                  \
  } while(0)
#define update_weakpointers()                     \
  do { var object L = O(all_weakpointers);        \
       while (!eq(L,Fixnum_0)) {                  \
         update_weakpointer(L);                   \
         L = TheWeakpointer(L)->wp_cdr;           \
  }    } while(0)
#define update_weakpointers_mod()                         \
  do { var object L = O(all_weakpointers);                \
       while (!eq(L,Fixnum_0)) {                          \
         var object next = TheWeakpointer(L)->wp_cdr;     \
         update_weakpointer(L);                           \
         L = next;                                        \
  }    } while(0)

    # update weak key-value tables
#define update_weakkvtable(wkvt)                                  \
  do { # weak key-value table is just another fancy svector       \
    var object* p = TheSvector(wkvt)->data; # nothing GC-visible  \
    var uintL count = Svector_length(wkvt);                       \
    dotimespL(count,count,{ update(p); p++; });                   \
  } while(0)
#define update_weakkvtables()                     \
  do { var object L = O(all_weakkvtables);        \
       while (!eq(L,Fixnum_0)) {                  \
         update_weakkvtable(L);                   \
         L = TheWeakKVT(L)->wkvt_cdr;             \
  }    } while(0)
#define update_weakkvtables_mod()                         \
  do { var object L = O(all_weakkvtables);                \
       while (!eq(L,Fixnum_0)) {                          \
         var object next = TheWeakKVT(L)->wkvt_cdr;       \
         update_weakkvtable(L);                           \
         L = next;                                        \
  }    } while(0)


# update STACKs :
#define update_stackobj_normal(objptr)    update(objptr);
#define update_STACKs()                                                       \
  for_all_STACKs(while (!eq(*objptr,nullobj)) { # until STACK is finished:    \
    if ( as_oint(*objptr) & wbit(frame_bit_o) ) { # here starts a frame?      \
      if (( as_oint(*objptr) & wbit(skip2_bit_o) ) == 0) # without skip2-Bit? \
        objptr skipSTACKop 2; # yes -> advance by 2                           \
      else                                                                    \
        objptr skipSTACKop 1; # no -> advance by 1                            \
    } else { # normal object, update:                                         \
      update_stackobj(objptr);                                                \
      objptr skipSTACKop 1; # advance                                         \
   }                                                                          \
  })
