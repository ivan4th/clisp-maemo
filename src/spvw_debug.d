/* Debugging utilities. */

/* Output a memory range in hexadecimal notation */
local const char hex_table[] = "0123456789ABCDEF";
local void mem_hex_out (const void* buf, uintL count) {
  if (count > 0) {
    var DYNAMIC_ARRAY(cbuf,char,3*count+1);
    var const uintB* ptr1 = (const uintB*) buf;
    var char* ptr2 = &cbuf[0];
    dotimespL(count,count, {
      *ptr2++ = ' ';
      *ptr2++ = hex_table[floor(*ptr1,16)]; *ptr2++ = hex_table[*ptr1 % 16];
      ptr1++;
    });
    *ptr2 = '\0';
    fputs(cbuf,stdout);
    FREE_DYNAMIC_ARRAY(cbuf);
  }
}

/* Output a lisp object in lisp notation to standard output.
 can trigger GC */
global object object_out (object obj) {
  pushSTACK(obj);
  pushSTACK(var_stream(S(terminal_io),strmflags_wr_ch_B)); # *TERMINAL-IO*
  prin1(&STACK_0,STACK_1); # output the object
  terpri(&STACK_0); # output a newline
  skipSTACK(1);
  return popSTACK(); # return the same object
}

#ifdef UNICODE
/* see string_to_asciz() */
local void string_out_ (FILE* out, object str, object encoding) {
  var uintL len;
  var uintL offset;
  var object string = unpack_string_ro(str,&len,&offset);
  var const chart* srcptr;
  unpack_sstring_alloca(string,len,offset, srcptr=);
  var uintL bytelen = cslen(encoding,srcptr,len);
  var DYNAMIC_ARRAY(buffer,uintB,bytelen+1);
  cstombs(encoding,srcptr,len,buffer,bytelen);
  buffer[bytelen] = 0;
  fputs((const char*)buffer,out);
  FREE_DYNAMIC_ARRAY(buffer);
}
#define string_out(o,s) string_out_(o,s,O(terminal_encoding))
#else /* no UNICODE */
local void string_out (FILE* out, object str) {
  var uintL len;
  var uintL offset;
  var object string = unpack_string_ro(str,&len,&offset);
  var const chart* srcptr= &TheSstring(string)->data[offset];
  var DYNAMIC_ARRAY(buffer,uintB,len+1);
  var uintB* destptr = buffer;
  while (len--) *destptr++ = as_cint(*srcptr++);
  *destptr++ = '\0'; /* append NULL byte */
  fputs((const char*)buffer,out);
  FREE_DYNAMIC_ARRAY(buffer);
}
#endif

/* non-consing, STACK non-modifying */
global object nobject_out (FILE* out, object obj) {
  begin_system_call();
  if (out == NULL) out = stdout;
  if (stringp(obj)) {
    fputc('"',out);
    string_out(out,obj);
    fputc('\"',out);
  } else if (charp(obj)) {
    var object name = char_name(char_code(obj));
    fprintf(out,"[%c]",as_cint(char_code(obj)));
    if (!nullp(name)) {
      fputs("=#\\",out);
      string_out(out,name);
    }
  } else if (symbolp(obj)) {
    var object pack = Symbol_package(obj);
    if (nullp(pack)) fputs("#:",out); /* uninterned symbol */
    else if (eq(pack,O(keyword_package))) fputc(':',out);
    else {
      string_out(out,ThePackage(pack)->pack_name);
      fputs("::",out);
    }
    string_out(out,Symbol_name(obj));
  } else if (simple_vector_p(obj)) {
    var uintL len = vector_length(obj);
    var uintL idx = 0;
    fputs("#(",out);
    while (idx < len) {
      if (idx) fputc(' ',out);
      nobject_out(out,TheSvector(obj)->data[idx++]);
    }
    fputc(')',out);
  } else if (consp(obj)) {
    fputc('(',out);
    loop {
      nobject_out(out,Car(obj));
      obj = Cdr(obj);
      if (atomp(obj)) break;
      fputc(' ',out);
    }
    if (!nullp(obj)) {
      fputs(" . ",out);
      nobject_out(out,obj);
    }
    fputc(')',out);
  } else if (functionp(obj)) {
    fputs("#<",out);
    if (subrp(obj)) {
      string_out(out, (((as_oint(subr_tab_ptr_as_object(&subr_tab)) <=
                         as_oint(obj))
                        && (as_oint(obj) <
                            as_oint(subr_tab_ptr_as_object(&subr_tab+1))))
                       ? O(printstring_subr) : O(printstring_addon_subr)));
      obj = TheSubr(obj)->name;
    } else if (cclosurep(obj)) {
      string_out(out, (genericfunctionp(obj)
                       ? O(printstring_generic_function)
                       : O(printstring_compiled_closure)));
      obj = TheClosure(obj)->clos_name;
    }
    #ifdef DYNAMIC_FFI
      else if (ffunctionp(obj)) {
      string_out(out,O(printstring_ffunction));
      obj = TheFfunction(obj)->ff_name;
    }
    #endif
      else { /* interpreted closure */
      string_out(out,O(printstring_closure));
      obj = TheIclosure(obj)->clos_name;
    }
    fputc(' ',out);
    nobject_out(out,obj);
    fputc('>',out);
  } else if (fsubrp(obj)) {
    fputs("#<",out);
    string_out(out,O(printstring_fsubr));
    fputc(' ',out);
    nobject_out(out,TheFsubr(obj)->name);
    fputc('>',out);
  } else if (pathnamep(obj)) {
    fputs("#(",out); nobject_out(out,S(pathname));
   #define SLOT(s) fputc(' ',out); nobject_out(out,S(K##s)); fputc(' ',out); \
     nobject_out(out,ThePathname(obj)->pathname_##s)
   #if HAS_HOST
    SLOT(host);
   #endif
   #if HAS_DEVICE
    SLOT(device);
   #endif
    SLOT(directory); SLOT(name); SLOT(type);
   #if HAS_VERSION
    SLOT(version);
   #endif
   #undef SLOT
    fputs(")",out);
  } else if (logpathnamep(obj)) {
   #ifdef LOGICAL_PATHNAMES
    fputs("#(",out); nobject_out(out,S(logical_pathname));
   #define SLOT(s) fputc(' ',out); nobject_out(out,S(K##s)); fputc(' ',out); \
     nobject_out(out,TheLogpathname(obj)->pathname_##s)
    SLOT(host); SLOT(directory); SLOT(name); SLOT(type); SLOT(version);
   #undef SLOT
    fputc(')',out);
   #endif
  } else if (hash_table_p(obj)) {
    fputs("#(",out); nobject_out(out,S(hash_table));
    fprintf(out," size=%d maxcount=%d count=%d mincount=%d free=",
            posfixnum_to_L(TheHashtable(obj)->ht_size),
            posfixnum_to_L(TheHashtable(obj)->ht_maxcount),
            posfixnum_to_L(TheHashtable(obj)->ht_count),
            posfixnum_to_L(TheHashtable(obj)->ht_mincount));
    nobject_out(out,TheHashtable(obj)->ht_freelist);
    fputs("\n  test=",out);
    switch (ht_test_code(record_flags(TheHashtable(obj)))) {
      case bit(0): nobject_out(out,S(eq)); break;
      case bit(1): nobject_out(out,S(eql)); break;
      case bit(2): nobject_out(out,S(equal)); break;
      case bit(3): nobject_out(out,S(equalp)); break;
      default:
        nobject_out(out,TheHashtable(obj)->ht_test); fputc('/',out);
        nobject_out(out,TheHashtable(obj)->ht_hash);
        break;
    }
    fputs("\n  I=",out); nobject_out(out,TheHashtable(obj)->ht_itable);
    fputs("\n  N=",out); nobject_out(out,TheHashtable(obj)->ht_ntable);
    fputs("\n  KV=",out); nobject_out(out,TheHashtable(obj)->ht_kvtable);
    fputc(')',out);
  } else if (fixnump(obj)) fprintf(out,"%d",fixnum_to_L(obj));
  else if (eq(obj,unbound))   string_out(out,O(printstring_unbound));
  else if (eq(obj,nullobj))   fputs("#<NULLOBJ>",out);
  else if (eq(obj,disabled))  string_out(out,O(printstring_disabled_pointer));
  else if (eq(obj,specdecl))  string_out(out,O(printstring_special_reference));
  else if (eq(obj,eof_value)) string_out(out,O(printstring_eof));
  else if (eq(obj,dot_value)) string_out(out,O(printstring_dot));
  else if (as_oint(obj) & wbit(frame_bit_o)) {
    fputs("#<frame ",out);
    switch (framecode(obj)) {
      case DYNBIND_frame_info: fputs("DYNBIND",out); break;
      case ENV1V_frame_info: fputs("ENV1V",out); break;
      case ENV1F_frame_info: fputs("ENV1F",out); break;
      case ENV1B_frame_info: fputs("ENV1B",out); break;
      case ENV1G_frame_info: fputs("ENV1G",out); break;
      case ENV1D_frame_info: fputs("ENV1D",out); break;
      case ENV2VD_frame_info: fputs("ENV2VD",out); break;
      case ENV5_frame_info: fputs("ENV5",out); break;
     #ifdef HAVE_SAVED_REGISTERS
      case CALLBACK_frame_info: fputs("CALLBACK",out); break;
     #endif
      case VAR_frame_info: fputs("VAR",out); break;
      case FUN_frame_info: fputs("FUN",out); break;
      case IBLOCK_frame_info: fputs("IBLOCK",out); break;
      case NESTED_IBLOCK_frame_info: fputs("NESTED_IBLOCK",out); break;
      case ITAGBODY_frame_info: fputs("ITAGBODY",out); break;
      case NESTED_ITAGBODY_frame_info: fputs("NESTED_ITAGBODY",out); break;
      case CBLOCK_CTAGBODY_frame_info: fputs("CBLOCK_CTAGBODY",out); break;
      case APPLY_frame_info: fputs("APPLY",out); break;
      case TRAPPED_APPLY_frame_info: fputs("TRAPPED_APPLY",out); break;
      case EVAL_frame_info: fputs("EVAL",out); break;
      case TRAPPED_EVAL_frame_info: fputs("TRAPPED_EVAL",out); break;
      case CATCH_frame_info: fputs("CATCH",out); break;
      case HANDLER_frame_info: fputs("HANDLER",out); break;
      case UNWIND_PROTECT_frame_info: fputs("UNWIND_PROTECT",out); break;
      case DRIVER_frame_info: fputs("DRIVER",out); break;
      default: fputs("**UNKNOWN**",out);
    }
    fprintf(out," 0x%X>",as_oint(obj));
  } else if (varobjectp(obj))
    fprintf(out,"#<varobject type=%d address=0x%X>",
            varobject_type(TheVarobject(obj)),ThePointer(obj));
  else fprintf(out,"#<huh?! address=0x%X>",ThePointer(obj));
  fflush(out);
  end_system_call();
  return obj;
}

/* use (struct backtrace_t*) and not p_backtrace_t
   so that this is useable from the p_backtrace_t C++ definition */
local int back_trace_depth (const struct backtrace_t *bt) {
  var uintL index = 0;
  var const struct backtrace_t *bt_fast = (bt ? bt : back_trace);
  var const struct backtrace_t *bt_slow = bt_fast;
  while (bt_fast) {
    bt_fast = bt_fast->bt_next; index++;
    if (bt_fast == bt_slow) return -index;
    if (bt_fast) { bt_fast = bt_fast->bt_next; index++; }
    if (bt_fast == bt_slow) return -index;
    bt_slow = bt_slow->bt_next;
  }
  return index;
}

/* print a single struct backtrace_t object
 the caller must do begin_system_call()/end_system_call() ! */
local void bt_out (FILE* out, const struct backtrace_t *bt, uintL index) {
  fprintf(out,"[%d/0x%X]%s ",index,bt,bt_beyond_stack_p(bt,STACK)?"<":">");
  nobject_out(out,bt->bt_caller);
  if (bt->bt_num_arg >= 0)
    fprintf(out," %d args",bt->bt_num_arg);
  if (bt->bt_next)
    fprintf(out," delta: STACK=%d; SP=%d",
            STACK_item_count(bt->bt_stack,bt->bt_next->bt_stack),
            /* SP and STACK grow in the opposite directions: */
            STACK_item_count(bt->bt_next,bt));
  fputc('\n',out);
}

/* print the whole backtrace stack */
local uintL back_trace_out (FILE* out, const struct backtrace_t *bt) {
  var uintL index = 0;
  var const struct backtrace_t *bt_fast = (bt ? bt : back_trace);
  var const struct backtrace_t *bt_slow = bt_fast;
  if (out == NULL) out = stdout;
  begin_system_call();
  while (bt_fast) {
    bt_out(out,bt_fast,index++); bt_fast = bt_fast->bt_next;
    if (bt_fast == bt_slow) {
     circular:
      fprintf(out,"*** error: backtrace circularity detected!\n");
      index = -index;
      break;
    }
    if (bt_fast) { bt_out(out,bt_fast,index++); bt_fast = bt_fast->bt_next; }
    if (bt_fast == bt_slow) goto circular;
    bt_slow = bt_slow->bt_next;
  }
  end_system_call();
  return index;
}

global void back_trace_check (const struct backtrace_t *bt,
                              char* label,char* file,int line) {
  if (bt && back_trace_depth(bt)<0) {
    fprintf(stderr,"\n%s:%d:%s: circularity!\n",file,line,label);
    back_trace_out(stderr,bt);
    abort();
  }
}

#ifdef DEBUG_SPVW
#define FUN(from,to,name) local to CONCAT(name,_) (from x) { return name(x); }
FUN(chart,cint,as_cint)
FUN(cint,chart,as_chart)
FUN(object,chart,char_code)
FUN(chart,object,code_char)
FUN(object,cint,char_int)
FUN(cint,object,int_char)
FUN(object,oint,as_oint)
FUN(oint,object,as_object)
FUN(object,sintB,Record_type)
FUN(object,uintB,Record_flags)
FUN(object,sintB,Array_type)
FUN(object,uintL,Srecord_length)
FUN(object,uintL,Xrecord_length)
FUN(object,uintL,Xrecord_xlength)
#undef FUN
#endif
