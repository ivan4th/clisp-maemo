# Allocator functions for the various types.

# ------------------------------ Specification --------------------------------

# All these are declared in lispbibl.d.
  global object allocate_cons (void);
  global object make_symbol (object string);
  global object allocate_vector (uintL len);
  global object allocate_bit_vector (uintB atype, uintL len);
  global object allocate_string (uintL len);
  global object allocate_iarray (uintB flags, uintC rank, tint type);
  #ifdef TYPECODES
  global object allocate_srecord_ (uintW flags_rectype, uintC reclen, tint type);
  global object allocate_xrecord_ (uintW flags_rectype, uintC reclen, uintC recxlen, tint type);
  #else
  global object allocate_srecord_ (uintW flags_rectype, uintC reclen);
  global object allocate_xrecord_ (uintW flags_rectype, uintC reclen, uintC recxlen);
  #endif
  #ifndef case_stream
  global object allocate_stream (uintB strmflags, uintB strmtype, uintC reclen, uintC recxlen);
  #endif
  #ifdef FOREIGN
  global object allocate_fpointer (FOREIGN foreign);
  #endif
  #ifdef FOREIGN_HANDLE
  global object allocate_handle (Handle handle);
  #endif
  global object allocate_bignum (uintC len, sintB sign);
  global object allocate_ffloat (ffloat value);
  #ifdef intQsize
  global object allocate_dfloat (dfloat value);
  #else
  global object allocate_dfloat (uint32 semhi, uint32 mlo);
  #endif
  global object allocate_lfloat (uintC len, uintL expo, signean sign);
  global object make_ratio (object num, object den);
  global object make_complex (object real, object imag);

# ------------------------------ Implementation -------------------------------

# UP, provides a cons
# allocate_cons()
# < result: pointer to a new CONS, with CAR and CDR =NIL
# can trigger GC
global object allocate_cons (void) {
  allocate(cons_type,false,sizeof(cons_),Cons,ptr,
    { ptr->cdr = NIL; ptr->car = NIL; });
}

# UP: provides a freshly created uninterned symbol with given printname.
# make_symbol(string)
# > string: immutable Simple-String
# < result: new symbol with this name, with home-package=NIL.
# can trigger GC
global object make_symbol (object string) {
  pushSTACK(string); # save string
  #define FILL  \
    do { ptr->symvalue = unbound; # empty value cell        \
         ptr->symfunction = unbound; # empty function cell  \
         ptr->proplist = NIL; # empty property list         \
         ptr->pname = popSTACK(); # store name              \
         ptr->homepackage = NIL; # no home-package          \
    } while(0)
 #ifdef TYPECODES
  allocate(symbol_type,true,size_symbol(),Symbol,ptr,
    { FILL; });
 #else
  allocate(symbol_type,true,size_xrecord(5,0),Symbol,ptr,
  { ptr->tfl = xrecord_tfl(Rectype_Symbol,0,5,0); FILL; });
 #endif
  #undef FILL
}

# UP, provides vector
# allocate_vector(len)
# > len: length of the vector
# < result: new vector (elements are initialized with NIL)
# can trigger GC
global object allocate_vector (uintL len) {
  var uintL need = size_svector(len); # needed memory
 #ifdef TYPECODES
  #define SETTFL  ptr->length = len
 #else
  #define SETTFL  ptr->tfl = lrecord_tfl(Rectype_Svector,len)
 #endif
  allocate(svector_type,true,need,Svector,ptr,{
    SETTFL;
    if (len > 0) {
      var object* p = &ptr->data[0];
      dotimespL(len,len, { *p++ = NIL; } ); # write NIL to the elements
    }
  });
  #undef SETTFL
}

# allocate and init the weak kvtable
# > len:    the length of the data vector
# < result: a fresh weak key-value table
# can trigger GC
local inline object allocate_weakkvt_low (uintL len) {
  var uintL need = size_svector(len+1);
 #ifdef TYPECODES
  #define SETTFL  ptr->length = len+1
 #else
  #define SETTFL  ptr->tfl = lrecord_tfl(Rectype_WeakKVT,len+1)
 #endif
  allocate(weakkvt_type,true,need,WeakKVT,ptr,{
    SETTFL;
    ptr->wkvt_cdr = O(all_weakkvtables);
    if (len > 0) {
      var object* p = ptr->data;
      dotimespL(len,len, { *p++ = unbound; } );
    }
  });
 #undef SETTFL
}
global object allocate_weakkvt (uintL len) {
  return O(all_weakkvtables) = allocate_weakkvt_low(len);
}

# Function: Allocates a bit/byte vector.
# allocate_bit_vector(atype,len)
# > uintB atype: Atype_nBit
# > uintL len: length (number of n-bit blocks)
# < result: fresh simple bit/byte-vector of the given length
# can trigger GC
global object allocate_bit_vector (uintB atype, uintL len) {
  var uintL need = size_sbvector(len<<atype); # needed memory in bytes
 #ifdef TYPECODES
  #define SETTFL  ptr->length = len
 #else
  #define SETTFL  ptr->tfl = lrecord_tfl(Rectype_Sbvector+atype,len)
 #endif
  allocate(Array_type_simple_bit_vector(atype),true,need,Sbvector,ptr,
    { SETTFL; }); # no further initialization
  #undef SETTFL
}

# UP, provides string
# allocate_string(len)
# > len: length of the string (in characters)
# < result: new normal-simple-string (LISP-object)
# can trigger GC
global object allocate_string (uintL len) {
  var uintL need = size_sstring(len); # needed memory in bytes
 #ifdef TYPECODES
  #define SETTFL  ptr->length = len
 #else
  #define SETTFL  ptr->tfl = lrecord_tfl(Rectype_Sstring,len)
 #endif
  allocate(sstring_type,true,need,Sstring,ptr,
    { SETTFL; }); # no further initialization
  #undef SETTFL
}

#ifndef TYPECODES
# UP, provides immutable string
# allocate_imm_string(len)
# > len: length of the string (in characters)
# < result: new immutable normal-simple-string (LISP-object)
# can trigger GC
global object allocate_imm_string (uintL len) {
  var uintL need = size_sstring(len); # needed memory in bytes
 #define SETTFL  ptr->tfl = lrecord_tfl(Rectype_Imm_Sstring,len)
  allocate(sstring_type,true,need,Sstring,ptr,
    { SETTFL; }); # no further initialization
 #undef SETTFL
}
#endif

#ifdef HAVE_SMALL_SSTRING
# UP, provides immutable small-string
# allocate_imm_small_string(len)
# > len: length of the string (in characters)
# < result: new immutable small-simple-string (LISP-object)
# can trigger GC
global object allocate_imm_small_string (uintL len) {
  var uintL need = size_small_sstring(len); # needed memory in bytes
 #define SETTFL  ptr->tfl = lrecord_tfl(Rectype_Imm_SmallSstring,len)
  allocate(sstring_type,true,need,SmallSstring,ptr,
    { SETTFL; }); # no further initialization
 #undef SETTFL
}
#endif

# UP, provides indirect array
# allocate_iarray(flags,rank,type)
# > uintB flags: flags
# > uintC (actually uintWC) rank: rank
# > tint type: typeinfo
# < result: LISP-Object array
# can trigger GC
global object allocate_iarray (uintB flags, uintC rank, tint type) {
  var uintL need = rank;
  if (flags & bit(arrayflags_fillp_bit))
    need += 1;
  if (flags & bit(arrayflags_dispoffset_bit))
    need += 1;
  need = size_iarray(need);
 #ifdef TYPECODES
  #define SETTFL  ptr->flags = flags; ptr->rank = rank
 #else
  #define SETTFL  ptr->tfl = srecord_tfl(type,flags,rank)
 #endif
  allocate(type,true,need,Iarray,ptr,{
    SETTFL; # store flags and rank
    ptr->data = NIL; # initialize data vector with NIL
  });
  #undef SETTFL
}

# UP, provides simple-record
# allocate_srecord_(flags_rectype,reclen,type)
# > uintW flags_rectype: flags, further typeinfo
# > uintC reclen: length
# > tint type: typeinfo
# < result: LISP-Object record (elements are initialized with NIL)
# can trigger GC
#ifdef TYPECODES
global object allocate_srecord_ (uintW flags_rectype, uintC reclen, tint type)
{
  ASSERT((sintB)(flags_rectype >> (BIG_ENDIAN_P ? 0 : 8)) < rectype_limit);
  var uintL need = size_srecord(reclen);
  allocate(type,true,need,Srecord,ptr,{
    # store flags, type:
    *(uintW*)pointerplus(ptr,offsetof(record_,recflags)) = flags_rectype;
    ptr->reclength = reclen; # store length
    var object* p = &ptr->recdata[0];
    dotimespC(reclen,reclen, { *p++ = NIL; } ); # initialize elements with NIL
  });
}
#else
global object allocate_srecord_ (uintW flags_rectype, uintC reclen) {
  var uintL need = size_srecord(reclen);
  allocate(type,true,need,Srecord,ptr,{
    ptr->tfl = (uintL)flags_rectype + ((uintL)reclen << 16);
    var object* p = &ptr->recdata[0];
    dotimespC(reclen,reclen, { *p++ = NIL; } ); # initialize elements with NIL
  });
}
#endif

# UP, provides extended-record
# allocate_xrecord_(flags_rectype,reclen,recxlen,type)
# > uintW flags_rectype: flags, further typeinfo
# > uintC reclen: length
# > uintC recxlen: extra-length
# > tint type: typeinfo
# < result: LISP-Object Record (elements are initialized with NIL resp. 0)
# can trigger GC
#ifdef TYPECODES
global object allocate_xrecord_ (uintW flags_rectype, uintC reclen,
                                 uintC recxlen, tint type) {
  ASSERT((sintB)(flags_rectype >> (BIG_ENDIAN_P ? 0 : 8)) >= rectype_limit);
  var uintL need = size_xrecord(reclen,recxlen);
  allocate(type,true,need,Xrecord,ptr,{
    # store flags, type:
    *(uintW*)pointerplus(ptr,offsetof(record_,recflags)) = flags_rectype;
    ptr->reclength = reclen; ptr->recxlength = recxlen; # store lengths
    var object* p = &ptr->recdata[0];
    dotimesC(reclen,reclen, { *p++ = NIL; } ); # initialize elements with NIL
    if (recxlen > 0) {
      var uintB* q = (uintB*)p;
      # initialize extra-elements with 0:
      dotimespC(recxlen,recxlen, { *q++ = 0; } );
    }
  });
}
#else
global object allocate_xrecord_ (uintW flags_rectype, uintC reclen,
                                 uintC recxlen) {
  var uintL need = size_xrecord(reclen,recxlen);
  allocate(type,true,need,Xrecord,ptr,{
    ptr->tfl = # store flags, type, lengths
      (uintL)flags_rectype + ((uintL)reclen << 16) + ((uintL)recxlen << 24);
    var object* p = &ptr->recdata[0];
    dotimesC(reclen,reclen, { *p++ = NIL; } ); # initialize elements with NIL
    if (recxlen > 0) {
      var uintB* q = (uintB*)p;
      # initialize extra-elements with 0:
      dotimespC(recxlen,recxlen, { *q++ = 0; } );
    }
  });
}
#endif

#ifndef case_stream

# UP, provides stream
# allocate_stream(strmflags,strmtype,reclen)
# > uintB strmflags: flags
# > uintB strmtype: further typeinfo
# > uintC reclen: length in objects
# > uintC recxlen: extra-length in bytes
# < result: LISP-object stream (Elements are initialized with NIL)
# can trigger GC
global object allocate_stream (uintB strmflags, uintB strmtype,
                               uintC reclen, uintC recxlen) {
  var object obj =
    allocate_xrecord(0,Rectype_Stream,reclen,recxlen,orecord_type);
  # Fixnum as place for strmflags and strmtype:
  TheRecord(obj)->recdata[0] = Fixnum_0;
  TheStream(obj)->strmflags = strmflags; TheStream(obj)->strmtype = strmtype;
  return obj;
}

#endif

#ifdef FOREIGN

# UP, provides foreign-pointer-wrapping
# allocate_fpointer(foreign)
# > foreign: of type FOREIGN
# < result: LISP-object, that contains the foreign pointer
# can trigger GC
global object allocate_fpointer (FOREIGN foreign) {
  var object result = allocate_xrecord(0,Rectype_Fpointer,fpointer_length,
                                       fpointer_xlength,orecord_type);
  TheFpointer(result)->fp_pointer = foreign;
  return result;
}

#endif

#ifdef FOREIGN_HANDLE

# UP, provides handle-wrapping
# allocate_handle(handle)
# < result: LISP-object, that contains the handle
# can trigger GC
global object allocate_handle (Handle handle) {
  var object result = allocate_bit_vector(Atype_Bit,sizeof(Handle)*8);
  TheHandle(result) = handle;
  return result;
}

#endif

# UP, provides bignum
# allocate_bignum(len,sign)
# > uintC (actually uintWC) len: length of the number (in digits)
# > sintB sign: flag for the sign (0 = +, -1 = -)
# < result: new bignum (LISP-object)
# can trigger GC
global object allocate_bignum (uintC len, sintB sign) {
  var uintL need = size_bignum(len); # needed memory in bytes
 #ifdef TYPECODES
  #define SETTFL  ptr->length = len
 #else
  #define SETTFL  ptr->tfl = srecord_tfl(Rectype_Bignum,(uintB)sign,len)
 #endif
  allocate(bignum_type | (sign & bit(sign_bit_t)),true,need,Bignum,ptr,
    { SETTFL; }); # no further initialization
  #undef SETTFL
}

# UP, provides single-float
# allocate_ffloat(value)
# > ffloat value: number value (bit 31 = sign)
# < result: new single-float (LISP-object)
# can trigger GC
global object allocate_ffloat (ffloat value) {
 #ifndef WIDE
  #ifdef TYPECODES
   #define SETTFL
  #else
   #define SETTFL  ptr->tfl = xrecord_tfl(Rectype_Ffloat,((sint32)value<0 ? 0xFF : 0),0,sizeof(ffloat))
  #endif
  # sign bit from value:
  allocate(ffloat_type | ((sint32)value<0 ? bit(sign_bit_t) : 0),
           true,size_ffloat(),Ffloat,ptr,
    { SETTFL; ptr->float_value = value; });
  #undef SETTFL
 #else
  return # sign bit from value
    type_data_object(ffloat_type | ((sint32)value<0 ? bit(sign_bit_t) : 0),
                     value);
 #endif
}

# UP, provides double-float
#ifdef intQsize
# allocate_dfloat(value)
# > dfloat value: number value (bit 63 = sign)
# < result: new double-float (LISP-object)
# can trigger GC
global object allocate_dfloat (dfloat value) {
 #ifdef TYPECODES
  #define SETTFL
 #else
  #define SETTFL  ptr->tfl = xrecord_tfl(Rectype_Dfloat,((sint64)value<0 ? 0xFF : 0),0,sizeof(dfloat))
 #endif
  # sign bit from value
  allocate(dfloat_type | ((sint64)value<0 ? bit(sign_bit_t) : 0),
           true,size_dfloat(),Dfloat,ptr,
    { SETTFL; ptr->float_value = value; });
  #undef SETTFL
}
#else
# allocate_dfloat(semhi,mlo)
# > semhi,mlo: number value (bit 31 from semhi = sign)
# < result: new double-float (LISP-object)
# can trigger GC
global object allocate_dfloat (uint32 semhi, uint32 mlo) {
 #ifdef TYPECODES
  #define SETTFL
 #else
  #define SETTFL  ptr->tfl = xrecord_tfl(Rectype_Dfloat,((sint32)semhi<0 ? 0xFF : 0),0,sizeof(dfloat))
 #endif
  # sign bit from value
  allocate(dfloat_type | ((sint32)semhi<0 ? bit(sign_bit_t) : 0),
           true,size_dfloat(),Dfloat,ptr,
    { SETTFL; ptr->float_value.semhi = semhi; ptr->float_value.mlo = mlo; });
  #undef SETTFL
}
#endif # intQsize

# UP, provides long-float
# allocate_lfloat(len,expo,sign)
# > uintC (actually uintWC) len: length of the mantissa (in digits)
# > uintL expo: exponent
# > signean sign: sign (0 = +, -1 = -)
# < result: new long-float, still without mantissa
# A LISP-object is there, only if the mantissa is stored!
# can trigger GC
global object allocate_lfloat (uintC len, uintL expo, signean sign) {
  var uintL need = size_lfloat(len); # needed memory in bytes
 #ifdef TYPECODES
  #define SETTFL  ptr->len = len
 #else
  #define SETTFL  ptr->tfl = srecord_tfl(Rectype_Lfloat,(uintB)sign,len)
 #endif
  allocate(lfloat_type | ((tint)sign & bit(sign_bit_t)),true,need,Lfloat,ptr,
    { SETTFL; ptr->expo = expo; }); # no further initialization
  #undef SETTFL
}

# UP, provides ratio
# make_ratio(num,den)
# > object num: numerator (must be integer /= 0 , relatively prime to 'den')
# > object den: denominator (must be integer > 1 )
# < result: ratio
# can trigger GC
global object make_ratio (object num, object den) {
  pushSTACK(den); pushSTACK(num); # save arguments
 #ifdef TYPECODES
  var tint type = # take over sign from num
   #ifdef fast_mtypecode
    ratio_type | (mtypecode(STACK_0) & bit(sign_bit_t))
   #else
    ratio_type | (typecode(num) & bit(sign_bit_t))
   #endif
    ;
 #endif
  #define FILL  \
         ptr->rt_num = popSTACK(); # store numerator \
         ptr->rt_den = popSTACK()  # store denominator
 #ifdef SPVW_MIXED
  # see allocate_xrecord
  #ifdef TYPECODES
   #define SETTFL                                               \
     *(uintW*)pointerplus(ptr,offsetof(record_,recflags)) =     \
       ((uintW)Rectype_Ratio << (BIG_ENDIAN_P ? 0 : 8));        \
     ptr->reclength = 2; ptr->recxlength = 0
  #else
  var uintL tfl = xrecord_tfl(Rectype_Ratio,(positivep(num) ? 0 : 0xFF),2,0);
   #define SETTFL  ptr->tfl = tfl
  #endif # TYPECODES
  allocate(type,true,size_xrecord(2,0),Ratio,ptr,{ SETTFL; FILL; });
  #undef SETTFL
 #else
  allocate(type,false,sizeof(ratio_),Ratio,ptr,{ FILL; });
 #endif # SPVW_MIXED
  #undef FILL
}

# UP, provides complex number
# make_complex(real,imag)
# > real: real part (must be a real number)
# > imag: imaginary part (must be a real number /= Fixnum 0)
# < result: complex number
# can trigger GC
global object make_complex (object real, object imag) {
  pushSTACK(imag); pushSTACK(real);
  #define FILL  \
    ptr->c_real = popSTACK(); # store real part \
    ptr->c_imag = popSTACK()  # store imaginary part
 #ifdef SPVW_MIXED
  # see allocate_xrecord
  #ifdef TYPECODES
   #define SETTFL                                               \
     *(uintW*)pointerplus(ptr,offsetof(record_,recflags)) =     \
       ((uintW)Rectype_Complex << (BIG_ENDIAN_P ? 0 : 8));      \
     ptr->reclength = 2; ptr->recxlength = 0
  #else
   #define SETTFL ptr->tfl = xrecord_tfl(Rectype_Complex,0,2,0)
  #endif # TYPECODES
  allocate(complex_type,true,size_xrecord(2,0),Complex,ptr,{ SETTFL; FILL; });
  #undef SETTFL
 #else
  allocate(complex_type,false,sizeof(complex_),Complex,ptr,{ FILL; });
 #endif # SPVW_MIXED
  #undef FILL
}
