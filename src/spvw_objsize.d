# Determination of the object size (in bytes) of the various heap objects.

# ------------------------------ Specification --------------------------------

#ifdef TYPECODES

# Returns the typecode of the varobject at a given address.
# typecode_at(addr)

# Because the result of typecode_at may contain symbol flags, any switch
# statement on such a result must contain 'case_symbolwithflags:' instead of
# 'case_symbol:'.

#endif

# Computes the size (in bytes, including header and alignment) of the
# varobject starting at addr. The result is a multiple of varobject_alignment.
#  var uintL heapnr = ...;   [only needed if SPVW_PURE]
#  var_prepare_objsize;      [declaration of some variable, depends on heapnr]
#  objsize(addr)

# Returns the size (in bytes, including header and alignment) of an object.
# varobject_bytelength(obj)
# > obj: heap object of various length
# < result: number of occupied bytes
  global uintL varobject_bytelength (object obj);

# ------------------------------ Implementation -------------------------------

#ifdef TYPECODES

  # Varobjects contain in the first word a pointer to itself, except during GC.
  # (During GC it's a pointer to the new location, but with the same typecode.)
  #define typecode_at(addr)  mtypecode(((Varobject)(addr))->GCself)
  # or (equivalently):
  # define typecode_at(addr)  (((((Varobject)(addr))->header_flags)>>(oint_type_shift%8))&tint_type_mask)

  #define case_symbolwithflags  \
    case symbol_type:                                        \
    case symbol_type|bit(constant_bit_t):                    \
    case symbol_type|bit(special_bit_t):                     \
    case symbol_type|bit(special_bit_t)|bit(constant_bit_t)

#endif

# Varobject_aligned_size(HS,ES,C) returns the length of an object of variable
# length with HS=Header-Size, ES=Element-Size, C=Element-Count.
# Varobject_aligned_size(HS,ES,C) = round_up(HS+ES*C,varobject_alignment) .
#define Varobject_aligned_size(HS,ES,C)           \
  ((ES % varobject_alignment) == 0                \
   ? # ES is divisible by varobject_alignment     \
     round_up(HS,varobject_alignment) + (ES)*(C)  \
   : round_up((HS)+(ES)*(C),varobject_alignment)) \

# length of an object, according to type:
#ifdef TYPECODES
  #define size_symbol()  # symbol \
      round_up( sizeof(symbol_), varobject_alignment)
#endif
#define size_sbvector(length)  # simple-bit-vector              \
  ( ceiling( (uintL)(length) + 8*offsetofa(sbvector_,data),     \
             8*varobject_alignment ) * varobject_alignment )
#define size_sb2vector(length)  # simple-2bit-vector            \
  ( ceiling( (uintL)(length) + 4*offsetofa(sbvector_,data),     \
             4*varobject_alignment ) * varobject_alignment )
#define size_sb4vector(length)  # simple-4bit-vector            \
  ( ceiling( (uintL)(length) + 2*offsetofa(sbvector_,data),     \
             2*varobject_alignment ) * varobject_alignment )
#define size_sb8vector(length)  # simple-8bit-vector \
 Varobject_aligned_size(offsetofa(sbvector_,data),1,(uintL)(length))
#define size_sb16vector(length)  # simple-16bit-vector \
 Varobject_aligned_size(offsetofa(sbvector_,data),2,(uintL)(length))
#define size_sb32vector(length)  # simple-32bit-vector \
 Varobject_aligned_size(offsetofa(sbvector_,data),4,(uintL)(length))
#define size_s8string(length)  # simple-8bit-string     \
 Varobject_aligned_size(offsetofa(s8string_,data),      \
                        sizeof(cint8),(uintL)(length))
#define size_s16string(length)  # simple-16bit-string   \
 Varobject_aligned_size(offsetofa(s16string_,data),     \
                        sizeof(cint16),(uintL)(length))
#define size_s32string(length)  # simple-32bit-string   \
 Varobject_aligned_size(offsetofa(s32string_,data),     \
                        sizeof(cint32),(uintL)(length))
#ifdef UNICODE
#define size_sstring(length)  # normal-simple-string \
  size_s32string(length)
#else
#define size_sstring(length)  # normal-simple-string \
  size_s8string(length)
#endif
#define size_svector(length)  # simple-vector                   \
  Varobject_aligned_size(offsetofa(svector_,data),              \
                         sizeof(object),(uintL)(length))
#ifndef TYPECODES
#define size_siarray(xlength)  # simple indirect array          \
  size_xrecord(1,xlength)
#endif
#define size_iarray(size)  # non-simple array, with                           \
  # size = dimension number + (1 if fill-pointer) + (1 if displaced-offset)   \
  Varobject_aligned_size(offsetofa(iarray_,dims),sizeof(uintL),(uintL)(size))
#define size_srecord(length)  # Simple-Record                   \
  Varobject_aligned_size(offsetofa(record_,recdata),            \
                         sizeof(object),(uintL)(length))
#define size_xrecord(length,xlength)  # Extended-Record                 \
  Varobject_aligned_size(offsetofa(record_,recdata),sizeof(uintB),      \
                         (sizeof(object)/sizeof(uintB))                 \
                         *(uintL)(length)+(uintL)(xlength))
#define size_bignum(length)  # Bignum \
  Varobject_aligned_size(offsetofa(bignum_,data),sizeof(uintD),(uintL)(length))
#ifdef TYPECODES
 #ifndef WIDE
  #define size_ffloat()  # Single-Float \
      round_up( sizeof(ffloat_), varobject_alignment)
 #endif
 #define size_dfloat()  # Double-Float \
      round_up( sizeof(dfloat_), varobject_alignment)
#else
  #define size_ffloat()  # Single-Float \
      size_xrecord(0,sizeof(ffloat))
  #define size_dfloat()  # Double-Float \
      size_xrecord(0,sizeof(dfloat))
  #endif
  #define size_lfloat(length)  # Long-Float                     \
      Varobject_aligned_size(offsetofa(lfloat_,data),           \
                             sizeof(uintD),(uintL)(length))

#ifdef SPVW_MIXED

local uintL objsize (void* addr) {
 #ifdef TYPECODES
  switch (typecode_at(addr) & ~bit(garcol_bit_t)) # type of the object
 #else
  switch (record_type((Record)addr)) {
    case_Rectype_Sbvector_above;
    case_Rectype_Sb2vector_above;
    case_Rectype_Sb4vector_above;
    case_Rectype_Sb8vector_above;
    case_Rectype_Sb16vector_above;
    case_Rectype_Sb32vector_above;
    case_Rectype_Svector_above;
    case_Rectype_WeakKVT_above;
    case_Rectype_mdarray_above;
    case_Rectype_obvector_above;
    case_Rectype_ob2vector_above;
    case_Rectype_ob4vector_above;
    case_Rectype_ob8vector_above;
    case_Rectype_ob16vector_above;
    case_Rectype_ob32vector_above;
    case_Rectype_ostring_above;
    case_Rectype_ovector_above;
    case_Rectype_Bignum_above;
    case_Rectype_Lfloat_above;
   #ifdef UNICODE
    case Rectype_S32string: case Rectype_Imm_S32string:
   #else
    case Rectype_S8string: case Rectype_Imm_S8string:
   #endif
      goto case_sstring;
   #ifdef HAVE_SMALL_SSTRING
    case Rectype_Imm_S8string:
      return size_s8string(sstring_length((S8string)addr));
    case Rectype_S8string:
      {
        var uintL len = sstring_length((S8string)addr);
        var uintL size = size_s8string(len);
        # Some uprounding, for reallocate_small_string to work.
        if (size_s8string(1) < size_siarray(0)
            && size < size_siarray(0) && len > 0)
          size = size_siarray(0);
        return size;
      }
    case Rectype_Imm_S16string:
      return size_s16string(sstring_length((S16string)addr));
    case Rectype_S16string:
      {
        var uintL len = sstring_length((S16string)addr);
        var uintL size = size_s16string(len);
        # Some uprounding, for reallocate_small_string to work.
        if (size_s16string(1) < size_siarray(0)
            && size < size_siarray(0) && len > 0)
          size = size_siarray(0);
        return size;
      }
   #endif
    default: goto case_record;
  }
  switch (0)
 #endif
  {
   #ifdef TYPECODES
    case_symbolwithflags: # Symbol
      return size_symbol();
   #endif
    case_sbvector: # simple-bit-vector
      return size_sbvector(sbvector_length((Sbvector)addr));
    case_sb2vector: # simple-2bit-vector
      return size_sb2vector(sbvector_length((Sbvector)addr));
    case_sb4vector: # simple-4bit-vector
      return size_sb4vector(sbvector_length((Sbvector)addr));
    case_sb8vector: # simple-8bit-vector
      return size_sb8vector(sbvector_length((Sbvector)addr));
    case_sb16vector: # simple-16bit-vector
      return size_sb16vector(sbvector_length((Sbvector)addr));
    case_sb32vector: # simple-32bit-vector
      return size_sb32vector(sbvector_length((Sbvector)addr));
    case_sstring: # normal-simple-string
      return size_sstring(sstring_length((Sstring)addr));
    case_weakkvt: # weak-key-value-table
    case_svector: # simple-vector
      return size_svector(svector_length((Svector)addr));
    case_mdarray: case_obvector: case_ob2vector: case_ob4vector:
    case_ob8vector: case_ob16vector: case_ob32vector: case_ostring:
    case_ovector: { # non-simple array:
        var uintL size;
        size = (uintL)iarray_rank((Iarray)addr);
        if (iarray_flags((Iarray)addr) & bit(arrayflags_fillp_bit))
          size += 1;
        if (iarray_flags((Iarray)addr) & bit(arrayflags_dispoffset_bit))
          size += 1;
        # size = dimension number + (1 if fill-pointer) +
        #        (1 if displaced-offset)
        return size_iarray(size);
      }
    case_record: # Record
      if (record_type((Record)addr) < rectype_limit)
        return size_srecord(srecord_length((Srecord)addr));
      else
        return size_xrecord(xrecord_length((Xrecord)addr),
                            xrecord_xlength((Xrecord)addr));
    case_bignum: # Bignum
      return size_bignum(bignum_length((Bignum)addr));
  #ifdef TYPECODES
   #ifndef WIDE
    case_ffloat: # Single-Float
      return size_ffloat();
   #endif
    case_dfloat: # Double-Float
      return size_dfloat();
  #endif
    case_lfloat: # Long-Float
      return size_lfloat(lfloat_length((Lfloat)addr));
   #ifdef TYPECODES
    case_machine:
    #ifndef SIXBIT_TYPECODES
    case_char:
    case_subr:
    case_system:
    #endif
    case_fixnum:
    case_sfloat:
    #ifdef WIDE
    case_ffloat:
    #endif
      # these are direct objects, no pointers.
   #endif
      default: # these are no objects of variable length.
          /*NOTREACHED*/ abort();
  }
}

  #define var_prepare_objsize

#endif # SPVW_MIXED

# special functions for each type:
inline local uintL objsize_iarray (void* addr) { # non-simple array
  var uintL size;
  size = (uintL)iarray_rank((Iarray)addr);
  if (iarray_flags((Iarray)addr) & bit(arrayflags_fillp_bit))
    size += 1;
  if (iarray_flags((Iarray)addr) & bit(arrayflags_dispoffset_bit))
        size += 1;
  # size = dimension number + (1 if fill-pointer) + (1 if displaced-offset)
  return size_iarray(size);
}

#ifdef SPVW_PURE

inline local uintL objsize_symbol (void* addr) { # Symbol
  return size_symbol();
}
inline local uintL objsize_sbvector (void* addr) { # simple-bit-vector
  return size_sbvector(sbvector_length((Sbvector)addr));
}
inline local uintL objsize_sb2vector (void* addr) { # simple-2bit-vector
  return size_sb2vector(sbvector_length((Sbvector)addr));
}
inline local uintL objsize_sb4vector (void* addr) { # simple-4bit-vector
  return size_sb4vector(sbvector_length((Sbvector)addr));
}
inline local uintL objsize_sb8vector (void* addr) { # simple-8bit-vector
  return size_sb8vector(sbvector_length((Sbvector)addr));
}
inline local uintL objsize_sb16vector (void* addr) { # simple-16bit-vector
  return size_sb16vector(sbvector_length((Sbvector)addr));
}
inline local uintL objsize_sb32vector (void* addr) { # simple-32bit-vector
  return size_sb32vector(sbvector_length((Sbvector)addr));
}
inline local uintL objsize_sstring (void* addr) { # simple-string
  return size_sstring(sstring_length((Sstring)addr));
}
inline local uintL objsize_svector (void* addr) { # simple-vector
  return size_svector(svector_length((Svector)addr));
}
inline local uintL objsize_record (void* addr) { # Record
  if (record_type((Record)addr) < rectype_limit)
    return size_srecord(srecord_length((Srecord)addr));
  else
    return size_xrecord(xrecord_length((Xrecord)addr),
                        xrecord_xlength((Xrecord)addr));
}
inline local uintL objsize_bignum (void* addr) { # Bignum
  return size_bignum(bignum_length((Bignum)addr));
}
#ifndef WIDE
inline local uintL objsize_ffloat (void* addr) { # Single-Float
  return size_ffloat();
}
#endif
inline local uintL objsize_dfloat (void* addr) { # Double-Float
  return size_dfloat();
}
inline local uintL objsize_lfloat (void* addr) { # Long-Float
  return size_lfloat(lfloat_length((Lfloat)addr));
}

# table of functions:
typedef uintL (*objsize_func_t) (void* addr);
local objsize_func_t objsize_table[heapcount];

local void init_objsize_table (void) {
  var uintL heapnr;
  for (heapnr=0; heapnr<heapcount; heapnr++) {
    switch (heapnr) {
     case_symbol:
      objsize_table[heapnr] = &objsize_symbol; break;
     case_sbvector:
      objsize_table[heapnr] = &objsize_sbvector; break;
     case_sb2vector:
      objsize_table[heapnr] = &objsize_sb2vector; break;
     case_sb4vector:
      objsize_table[heapnr] = &objsize_sb4vector; break;
     case_sb8vector:
      objsize_table[heapnr] = &objsize_sb8vector; break;
     case_sb16vector:
      objsize_table[heapnr] = &objsize_sb16vector; break;
     case_sb32vector:
      objsize_table[heapnr] = &objsize_sb32vector; break;
     case_sstring:
      objsize_table[heapnr] = &objsize_sstring; break;
     case_svector: case_weakkvt:
      objsize_table[heapnr] = &objsize_svector; break;
     case_mdarray: case_obvector: case_ob2vector: case_ob4vector:
     case_ob8vector: case_ob16vector: case_ob32vector: case_ostring:
     case_ovector:
      objsize_table[heapnr] = &objsize_iarray; break;
     case_record:
      objsize_table[heapnr] = &objsize_record; break;
     case_bignum:
      objsize_table[heapnr] = &objsize_bignum; break;
    #ifndef WIDE
     case_ffloat:
      objsize_table[heapnr] = &objsize_ffloat; break;
    #endif
     case_dfloat:
      objsize_table[heapnr] = &objsize_dfloat; break;
     case_lfloat:
      objsize_table[heapnr] = &objsize_lfloat; break;
     case_machine:
     case_char:
     case_subr:
     case_system:
     case_fixnum:
     case_sfloat:
    #ifdef WIDE
     case_ffloat:
    #endif
      # these are direct objects, no pointers.
      /* case_ratio: */
      /* case_complex: */
      default:
        # these are no objects of variable length.
        objsize_table[heapnr] = (objsize_func_t)&abort; break;
    }
  }
}

#define var_prepare_objsize  \
    var objsize_func_t _objsize_func = objsize_table[heapnr];
#define objsize(addr)  (*_objsize_func)(addr)

#endif # SPVW_PURE

global uintL varobject_bytelength (object obj) {
 #ifdef SPVW_PURE
  var uintL heapnr = typecode(obj);
 #endif
  var_prepare_objsize;
  return objsize(TheVarobject(obj));
}
