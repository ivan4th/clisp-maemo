# Ausgabe aller Definitionen aus lispbibl.d, die an externe Module
# exportiert werden.
# Bruno Haible 1994-2002
# Sam Steingold 1998-2002

#include "lispbibl.c"

# Ausgabe von Strings mit eingebetteten Zahlen, wie printf().
# Nur dass die Zahlen auch vom Typ `unsigned long long' sein können.
# Wir vermeiden es, <stdarg.h> oder <varargs.h> vorauszusetzen.

typedef struct {
  char base; # 'd' für dezimal, 'x' für hexadezimal
  int size;
  union {
    uint8 val8;
    uint16 val16;
    uint32 val32;
    #ifdef HAVE_LONGLONG
    uint64 val64;
    #endif
  } value;
} printf_arg;

#ifdef HAVE_LONGLONG
  #define fill_printf_arg(where,expr)  \
    where.size = sizeof(expr); \
    if (sizeof(expr) == sizeof(uint8)) { where.value.val8 = (uint8)(expr); } \
    elif (sizeof(expr) == sizeof(uint16)) { where.value.val16 = (uint16)(expr); } \
    elif (sizeof(expr) == sizeof(uint32)) { where.value.val32 = (uint32)(expr); } \
    elif (sizeof(expr) == sizeof(uint64)) { where.value.val64 = (uint64)(expr); } \
    else abort();
#else
  #define fill_printf_arg(where,expr)  \
    where.size = sizeof(expr); \
    if (sizeof(expr) == sizeof(uint8)) { where.value.val8 = (uint8)(expr); } \
    elif (sizeof(expr) == sizeof(uint16)) { where.value.val16 = (uint16)(expr); } \
    elif (sizeof(expr) == sizeof(uint32)) { where.value.val32 = (uint32)(expr); } \
    else abort();
#endif

local const char* Lsuffix = "L";
local const char* ULsuffix = "UL";
#ifdef HAVE_LONGLONG
local const char* ULLsuffix = "ULL";
#endif

global void print_printf_arg (const printf_arg* arg);
global void print_printf_arg(arg)
  var const printf_arg* arg;
  {
    switch (arg->size) {
      case sizeof(uint8):
        printf(arg->base=='d' ? "%u" : "0x%X", (unsigned int)(arg->value.val8));
        break;
      case sizeof(uint16):
        printf(arg->base=='d' ? "%u" : "0x%X", (unsigned int)(arg->value.val16));
        break;
      case sizeof(uint32):
        printf(arg->base=='d' ? "%lu%s" : "0x%lX%s", (unsigned long)(arg->value.val32), ULsuffix);
        break;
      #ifdef HAVE_LONGLONG
      case sizeof(uint64):
        #if (long_bitsize == 64)
          if (!(sizeof(uint64) == sizeof(unsigned long))) abort();
          printf("0x%lX%s", (unsigned long)(arg->value.val64), ULsuffix);
        #else
          if (!(sizeof(uint32) == sizeof(unsigned long))) abort();
          printf("0x%lX%08lX%s",
                 (unsigned long)(arg->value.val64 >> 32),
                 (unsigned long)(arg->value.val64 & 0xFFFFFFFFUL),
                 ULLsuffix
                );
        #endif
        break;
      #endif
      default:
        abort();
    }
  }

global void printf_with_args (const char* string, int argcount, printf_arg* args);
global void printf_with_args(string,argcount,args)
  var const char* string;
  var int argcount;
  var printf_arg* args;
  {
    while (*string) {
      if (string[0]=='%') {
        if (!(string[1]=='d' || string[1]=='x')) abort();
        if (!(argcount > 0)) abort();
        args->base = string[1]; print_printf_arg(args);
        string+=2; args++; argcount--;
      } else {
        putchar(*string); string++;
      }
    }
  }

#define printf0(string)  printf(string)
#define printf1(string,arg0)  \
  { var printf_arg args[1]; \
    fill_printf_arg(args[0],arg0); \
    printf_with_args(string,1,args); \
  }
#define printf2(string,arg0,arg1)  \
  { var printf_arg args[2]; \
    fill_printf_arg(args[0],arg0); \
    fill_printf_arg(args[1],arg1); \
    printf_with_args(string,2,args); \
  }
#define printf3(string,arg0,arg1,arg2)  \
  { var printf_arg args[3]; \
    fill_printf_arg(args[0],arg0); \
    fill_printf_arg(args[1],arg1); \
    fill_printf_arg(args[2],arg2); \
    printf_with_args(string,3,args); \
  }
#define printf4(string,arg0,arg1,arg2,arg3)  \
  { var printf_arg args[4]; \
    fill_printf_arg(args[0],arg0); \
    fill_printf_arg(args[1],arg1); \
    fill_printf_arg(args[2],arg2); \
    fill_printf_arg(args[3],arg3); \
    printf_with_args(string,4,args); \
  }
#define printf5(string,arg0,arg1,arg2,arg3,arg4)  \
  { var printf_arg args[5]; \
    fill_printf_arg(args[0],arg0); \
    fill_printf_arg(args[1],arg1); \
    fill_printf_arg(args[2],arg2); \
    fill_printf_arg(args[3],arg3); \
    fill_printf_arg(args[4],arg4); \
    printf_with_args(string,5,args); \
  }
#define printf6(string,arg0,arg1,arg2,arg3,arg4,arg5)  \
  { var printf_arg args[6]; \
    fill_printf_arg(args[0],arg0); \
    fill_printf_arg(args[1],arg1); \
    fill_printf_arg(args[2],arg2); \
    fill_printf_arg(args[3],arg3); \
    fill_printf_arg(args[4],arg4); \
    fill_printf_arg(args[5],arg5); \
    printf_with_args(string,6,args); \
  }
#define printf7(string,arg0,arg1,arg2,arg3,arg4,arg5,arg6)  \
  { var printf_arg args[7]; \
    fill_printf_arg(args[0],arg0); \
    fill_printf_arg(args[1],arg1); \
    fill_printf_arg(args[2],arg2); \
    fill_printf_arg(args[3],arg3); \
    fill_printf_arg(args[4],arg4); \
    fill_printf_arg(args[5],arg5); \
    fill_printf_arg(args[6],arg6); \
    printf_with_args(string,7,args); \
  }

global void print_file (const char* fname) {
  char buf[BUFSIZ];
  FILE* includefile = fopen(fname,"r");
  char* line;
  if (includefile == NULL) { perror(fname); exit(1); }
  while ((line = fgets(buf,BUFSIZ,includefile)) != NULL)
    fputs(line,stdout);
  if (ferror(includefile) || fclose(includefile)) { perror(fname); exit(1); }
}

global int main()
{
  # Was hier ausgegeben wird, kann voraussetzen, dass unixconf.h und intparam.h
  # schon includet wurden. (intparam.h z.Zt. nicht nötig, aber was soll's.)
# #ifdef LANGUAGE_STATIC
#   printf1("#define ENGLISH  %d\n",ENGLISH);
# #endif
# printf1("#define BIG_ENDIAN_P  %d\n",BIG_ENDIAN_P);
  #ifdef HAVE_SAVED_REGISTERS
    printf("#ifndef IN_MODULE_CC\n");
    #ifdef STACK_register
      printf("register long STACK_reg __asm__(\"%s\");\n",STACK_register);
    #endif
    #ifdef mv_count_register
      printf("register long mv_count_reg __asm__(\"%s\");\n",mv_count_register);
    #endif
    #ifdef value1_register
      printf("register long value1_reg __asm__(\"%s\");\n",value1_register);
    #endif
    #ifdef back_trace_register
      printf("register long back_trace_reg __asm__(\"%s\");\n",back_trace_register);
    #endif
    printf("struct registers { ");
    #ifdef STACK_register
      printf("long STACK_register_contents; ");
    #endif
    #ifdef mv_count_register
      printf("long mv_count_register_contents; ");
    #endif
    #ifdef value1_register
      printf("long value1_register_contents; ");
    #endif
    #ifdef back_trace_register
      printf("long back_trace_register_contents; ");
    #endif
    printf("};\n");
    printf("extern struct registers * callback_saved_registers;\n");
    printf("#endif\n");
  #endif
# #if !defined(GNU) && !defined(UNIXCONF)
#   printf("#define inline\n");
# #endif
  printf("#ifdef __cplusplus\n");
  printf("#define BEGIN_DECLS  extern \"C\" {\n");
  printf("#define END_DECLS    }\n");
  printf("#else\n");
  printf("#define BEGIN_DECLS\n");
  printf("#define END_DECLS\n");
  printf("#endif\n");
  printf("#define CONCAT_(xxx,yyy)  xxx##yyy\n");
  printf("#define CONCAT3_(aaa,bbb,ccc)  aaa##bbb##ccc\n");
# printf("#define CONCAT4_(aaa,bbb,ccc,ddd)  aaa##bbb##ccc##ddd\n");
# printf("#define CONCAT5_(aaa,bbb,ccc,ddd,eee)  aaa##bbb##ccc##ddd##eee\n");
  printf("#define CONCAT(xxx,yyy)  CONCAT_(xxx,yyy)\n");
  printf("#define CONCAT3(aaa,bbb,ccc)  CONCAT3_(aaa,bbb,ccc)\n");
# printf("#define CONCAT4(aaa,bbb,ccc,ddd)  CONCAT4_(aaa,bbb,ccc,ddd)\n");
# printf("#define CONCAT5(aaa,bbb,ccc,ddd,eee)  CONCAT5_(aaa,bbb,ccc,ddd,eee)\n");
  printf("#define STRING(token) #token\n");
  printf("#define STRINGIFY(token) STRING(token)\n");
  printf("#define global\n");
# printf("#define local  static\n");
  #ifdef GNU
    #if (__GNUC__ >= 3) || ((__GNUC__ == 2) && (__GNUC_MINOR__ >= 7))
      printf("#define nonreturning_function(storclass,funname,arguments)  \\\n");
      printf("  storclass void __attribute__((__noreturn__)) funname arguments\n");
    #else
      printf("#define nonreturning_function(storclass,funname,arguments)  \\\n");
      printf("  storclass void funname arguments\n");
    #endif
  #elif defined(MICROSOFT)
    printf("#define nonreturning_function(storclass,funname,arguments)  \\\n");
    printf("  __declspec(noreturn) storclass void funname arguments\n");
  #else
    printf("#define nonreturning_function(storclass,funname,arguments)  \\\n");
    printf("  storclass void funname arguments\n");
  #endif
  printf("#define var\n");
# printf("#define elif  else if\n");
# printf("#define loop  while (1)\n");
# printf("#define until(expression)  while(!(expression))\n");
# printf("#define NOTREACHED  fehler_notreached(__FILE__,__LINE__)\n");
# printf("#define ASSERT(expr)  do { if (!(expr)) NOTREACHED; } while(0)\n");
# #if defined(GNU) && !defined(RISCOS) && !defined(CONVEX)
#   printf("#define alloca  __builtin_alloca\n");
# #elif defined(MICROSOFT)
#   printf("#include <malloc.h>\n");
#   printf("#define alloca _alloca\n");
# #elif defined(HAVE_ALLOCA_H) || defined(RISCOS)
#   printf("#include <alloca.h>\n");
#   #ifndef alloca
#     #ifdef UNIX_OSF
#       printf("extern char* alloca (int size);\n");
#     #else
#       printf("extern void* alloca (int size);\n");
#     #endif
#   #endif
# #elif defined(_AIX)
#   printf("#pragma alloca\n");
# #elif !defined(NO_ALLOCA)
#   printf("extern void* alloca (int size);\n");
# #endif
  #ifdef __CHAR_UNSIGNED__
    printf("typedef signed char  SBYTE;\n");
  #else
    printf("typedef char         SBYTE;\n");
  #endif
  printf("typedef unsigned char  UBYTE;\n");
  printf("typedef short          SWORD;\n");
  printf("typedef unsigned short UWORD;\n");
  #if (long_bitsize==32)
    printf("typedef long           SLONG;\n");
    printf("typedef unsigned long  ULONG;\n");
  #elif (int_bitsize==32)
    printf("typedef int            SLONG;\n");
    printf("typedef unsigned int   ULONG;\n");
  #endif
  #if (long_bitsize==64)
    printf("typedef long           SLONGLONG;\n");
    printf("typedef unsigned long  ULONGLONG;\n");
  #elif defined(MICROSOFT)
    # lispbibl.d defines HAVE_LONGLONG for MICROSOFT,
    # so MICROSOFT has to come before HAVE_LONGLONG here
    printf("typedef __int64           SLONGLONG;\n");
    printf("typedef unsigned __int64  ULONGLONG;\n");
  #elif defined(HAVE_LONGLONG)
    printf("typedef long long           SLONGLONG;\n");
    printf("typedef unsigned long long  ULONGLONG;\n");
  #endif
  #ifdef HAVE_STDBOOL_H
    printf("#include <stdbool.h>\n");
  #else
    print_file("stdbool.h");
  #endif
  printf("#undef NULL\n");
  #ifdef __cplusplus
    printf("#define NULL  0\n");
  #else
    printf("#define NULL  ((void*) 0L)\n");
  #endif
  #if defined(GNU)
    printf("#define unspecified 0\n");
  #else
    printf("#define unspecified 1\n");
  #endif
  #if !(defined(GNU) || (pointer_bitsize > 32))
    printf("#define pointerplus(pointer,offset)  ((void*)((ULONG)(pointer)+(offset)))\n");
  #else
    printf("#define pointerplus(pointer,offset)  ((UBYTE*)(pointer)+(offset))\n");
  #endif
  printf("#define bit(n)  (1%s<<(n))\n",Lsuffix);
# printf("#define bitm(n)  (2%s<<((n)-1))\n",Lsuffix);
  #if !defined(SPARC)
    printf("#define bit_test(x,n)  ((x) & bit(n))\n");
  #else
    #if !defined(GNU)
      printf("#define bit_test(x,n)  ((n)<12 ? ((x) & bit(n)) : ((sint32)((uint32)(x) << (31-(n))) < 0))\n");
    #else
      printf("#define bit_test(x,n)  ((((n)<12) && ((x) & bit(n))) || (((n)>=12) && ((sint32)((uint32)(x) << (31-(n))) < 0)))\n");
    #endif
  #endif
  printf("#define minus_bit(n)  (-1%s<<(n))\n",Lsuffix);
# printf("#define minus_bitm(n)  (-2%s<<((n)-1))\n",Lsuffix);
# printf("#define floor(a_from_floor,b_from_floor)  ((a_from_floor) / (b_from_floor))\n");
# printf("#define ceiling(a_from_ceiling,b_from_ceiling)  (((a_from_ceiling) + (b_from_ceiling) - 1) / (b_from_ceiling))\n");
# printf("#define round_down(a_from_round,b_from_round)  (floor(a_from_round,b_from_round)*(b_from_round))\n");
# printf("#define round_up(a_from_round,b_from_round)  (ceiling(a_from_round,b_from_round)*(b_from_round))\n");
# #if defined(GNU)
#   #ifdef DECALPHA
#     printf("#define DYNAMIC_ARRAY(arrayvar,arrayeltype,arraysize)  arrayeltype arrayvar[(arraysize)+1]\n");
#   #else
#     printf("#define DYNAMIC_ARRAY(arrayvar,arrayeltype,arraysize)  arrayeltype arrayvar[arraysize]\n");
#   #endif
#   printf("#define FREE_DYNAMIC_ARRAY(arrayvar)\n");
# #elif (defined(UNIX) && (defined(HAVE_ALLOCA_H) || defined(_AIX) || !defined(NO_ALLOCA))) || defined(MICROSOFT) || defined(RISCOS)
#   printf("#define DYNAMIC_ARRAY(arrayvar,arrayeltype,arraysize)  arrayeltype* arrayvar = (arrayeltype*)alloca((arraysize)*sizeof(arrayeltype))\n");
#   printf("#define FREE_DYNAMIC_ARRAY(arrayvar)\n");
# #else
#   printf("#include <stdlib.h>\n");
#   printf("extern void* malloca (size_t size);\n");
#   printf("extern void freea (void* ptr);\n");
#   printf("#define DYNAMIC_ARRAY(arrayvar,arrayeltype,arraysize)  arrayeltype* arrayvar = (arrayeltype*)malloca((arraysize)*sizeof(arrayeltype))\n");
#   printf("#define FREE_DYNAMIC_ARRAY(arrayvar)  freea(arrayvar)\n");
# #endif
  { int i;
    for (i=1; i<=8; i++)
      { printf("typedef UBYTE   uint%d;\n",i);
        printf("typedef SBYTE   sint%d;\n",i);
      }
    for (i=9; i<=16; i++)
      { printf("typedef UWORD   uint%d;\n",i);
        printf("typedef SWORD   sint%d;\n",i);
      }
    for (i=17; i<=32; i++)
      { printf("typedef ULONG   uint%d;\n",i);
        printf("typedef SLONG   sint%d;\n",i);
      }
    #ifdef HAVE_LONGLONG
      for (i=33; i<=64; i++)
        if ((i==33) || (i==48) || (i==64))
          { printf("typedef ULONGLONG  uint%d;\n",i);
            printf("typedef SLONGLONG  sint%d;\n",i);
          }
    #endif
  }
  printf("typedef sint%d sintB;\n",intBsize);
  printf("typedef uint%d uintB;\n",intBsize);
# printf("typedef sint%d sintW;\n",intWsize);
  printf("typedef uint%d uintW;\n",intWsize);
  printf("typedef sint%d sintL;\n",intLsize);
  printf("typedef uint%d uintL;\n",intLsize);
# #ifdef intQsize
#   printf("typedef sint%d sintQ;\n",intQsize);
#   printf("typedef uint%d uintQ;\n",intQsize);
# #else
#   printf("typedef struct { sintL hi; uintL lo; } sintL2;\n");
#   printf("typedef struct { uintL hi; uintL lo; } uintL2;\n");
# #endif
  printf("typedef sint%d sintP;\n",pointer_bitsize);
  printf("typedef uint%d uintP;\n",pointer_bitsize);
# printf("typedef sint%d sintBW;\n",intBWsize);
# printf("typedef uint%d uintBW;\n",intBWsize);
# printf("typedef sint%d sintWL;\n",intWLsize);
  printf("typedef uint%d uintWL;\n",intWLsize);
# printf("typedef sint%d sintBWL;\n",intBWLsize);
  printf("typedef uint%d uintBWL;\n",intBWLsize);
# #ifdef fast_dotimesW
#   #if (__GNUC__<2)
#     printf("#define dotimesW(countvar_from_dotimesW,count_from_dotimesW,statement_from_dotimesW)  \\\n");
#     printf("  { countvar_from_dotimesW = (count_from_dotimesW);     \\\n");
#     printf("    if (!(countvar_from_dotimesW==0))                   \\\n");
#     printf("      { countvar_from_dotimesW--;                       \\\n");
#     printf("        do {statement_from_dotimesW}                    \\\n");
#     printf("           until ((sintW)--countvar_from_dotimesW==-1); \\\n");
#     printf("  }   }\n");
#     printf("#define dotimespW(countvar_from_dotimespW,count_from_dotimespW,statement_from_dotimespW)  \\\n");
#     printf("  { countvar_from_dotimespW = (count_from_dotimespW)-1;                         \\\n");
#     printf("    do {statement_from_dotimespW} until ((sintW)--countvar_from_dotimespW==-1); \\\n");
#     printf("  }\n");
#   #else
#     printf("#define dotimesW(countvar_from_dotimesW,count_from_dotimesW,statement_from_dotimesW)  \\\n");
#     printf("  { countvar_from_dotimesW = (count_from_dotimesW);        \\\n");
#     printf("    if (!(countvar_from_dotimesW==0))                      \\\n");
#     printf("      { countvar_from_dotimesW--;                          \\\n");
#     printf("        do {statement_from_dotimesW}                       \\\n");
#     printf("           until ((sintW)(--countvar_from_dotimesW)+1==0); \\\n");
#     printf("  }   }\n");
#     printf("#define dotimespW(countvar_from_dotimespW,count_from_dotimespW,statement_from_dotimespW)  \\\n");
#     printf("  { countvar_from_dotimespW = (count_from_dotimespW)-1;                            \\\n");
#     printf("    do {statement_from_dotimespW} until ((sintW)(--countvar_from_dotimespW)+1==0); \\\n");
#     printf("  }\n");
#   #endif
# #else
#   printf("#define dotimesW(countvar_from_dotimesW,count_from_dotimesW,statement_from_dotimesW)  \\\n");
#   printf("  { countvar_from_dotimesW = (count_from_dotimesW);         \\\n");
#   printf("    until (countvar_from_dotimesW==0)                       \\\n");
#   printf("      {statement_from_dotimesW; countvar_from_dotimesW--; } \\\n");
#   printf("  }\n");
#   printf("#define dotimespW(countvar_from_dotimespW,count_from_dotimespW,statement_from_dotimespW)  \\\n");
#   printf("  { countvar_from_dotimespW = (count_from_dotimespW);                   \\\n");
#   printf("    do {statement_from_dotimespW} until (--countvar_from_dotimespW==0); \\\n");
#   printf("  }\n");
# #endif
# #ifdef fast_dotimesL
#   printf("#define dotimesL(countvar_from_dotimesL,count_from_dotimesL,statement_from_dotimesL)  \\\n");
#   printf("  { countvar_from_dotimesL = (count_from_dotimesL);           \\\n");
#   printf("    if (!(countvar_from_dotimesL==0))                         \\\n");
#   printf("      { countvar_from_dotimesL--;                             \\\n");
#   printf("        do {statement_from_dotimesL}                          \\\n");
#   printf("           until ((sintL)(--countvar_from_dotimesL) == -1);   \\\n");
#   printf("  }   }\n");
#   printf("#define dotimespL(countvar_from_dotimespL,count_from_dotimespL,statement_from_dotimespL)  \\\n");
#   printf("  { countvar_from_dotimespL = (count_from_dotimespL)-1;                             \\\n");
#   printf("    do {statement_from_dotimespL} until ((sintL)(--countvar_from_dotimespL) == -1); \\\n");
#   printf("  }\n");
# #else
#   printf("#define dotimesL(countvar_from_dotimesL,count_from_dotimesL,statement_from_dotimesL)  \\\n");
#   printf("  { countvar_from_dotimesL = (count_from_dotimesL);         \\\n");
#   printf("    until (countvar_from_dotimesL==0)                       \\\n");
#   printf("      {statement_from_dotimesL; countvar_from_dotimesL--; } \\\n");
#   printf("  }\n");
#   printf("#define dotimespL(countvar_from_dotimespL,count_from_dotimespL,statement_from_dotimespL)  \\\n");
#   printf("  { countvar_from_dotimespL = (count_from_dotimespL);                   \\\n");
#   printf("    do {statement_from_dotimespL} until (--countvar_from_dotimespL==0); \\\n");
#   printf("  }\n");
# #endif
  printf("#define uintC uintWL\n");
# printf("#define sintC sintWL\n");
# #if (intCsize==intWsize)
#   printf("#define dotimesC dotimesW\n");
#   printf("#define dotimespC dotimespW\n");
# #endif
# #if (intCsize==intLsize)
#   printf("#define dotimesC dotimesL\n");
#   printf("#define dotimespC dotimespL\n");
# #endif
# printf("typedef sint%d sintD;\n",intDsize);
  printf("typedef uint%d uintD;\n",intDsize);
# #ifdef WIDE_HARD
#   printf("#define WIDE_HARD\n");
# #endif
# #ifdef WIDE_SOFT
#   printf("#define WIDE_SOFT\n");
# #endif
# #ifdef WIDE
#   printf("#define WIDE\n");
# #endif
  #if !defined(WIDE)
    #ifdef OBJECT_STRUCT
      printf("typedef struct { uintL one; } object;\n");
    #else
      printf("typedef  void *  object;\n");
    #endif
    printf("typedef  uintL  oint;\n");
#   printf("typedef  sintL  soint;\n");
  #else
    printf("typedef  uint64  oint;\n");
#   printf("typedef  sint64  soint;\n");
    #ifdef WIDE_STRUCT
      printf("typedef  struct { union {\n");
      #if BIG_ENDIAN_P==WIDE_ENDIANNESS
        printf("  struct { /* tint */ uintL type; /* aint */ uintL addr; } both;\n");
      #else
        printf("  struct { /* aint */ uintL addr; /* tint */ uintL type; } both;\n");
      #endif
      printf("  oint one");
      #ifdef GENERATIONAL_GC
        printf(" __attribute__ ((aligned(8)))");
      #endif
      printf("; } u; }\n");
      printf("  object;\n");
    #else
      printf("typedef  oint  object;\n");
    #endif
  #endif
  #if defined(WIDE_STRUCT) || defined(OBJECT_STRUCT)
    printf("#define as_oint(expr)  ((expr).one)\n");
    #if defined(WIDE_STRUCT)
      printf("#define as_object(o)  ((object){u:{one_u:(o)}})\n");
    #elif defined(OBJECT_STRUCT)
      printf("#define as_object(o)  ((object){one_o:(o)})\n");
    #endif
  #else
    printf("#define as_oint(expr)  (oint)(expr)\n");
    printf("#define as_object(o)  (object)(o)\n");
  #endif
# printf1("#define addressbus_mask  %x\n",(oint)addressbus_mask);
# printf("#define oint_type_shift  %d\n",oint_type_shift);
# printf("#define oint_type_len  %d\n",oint_type_len);
# printf1("#define oint_type_mask  %x\n",(oint)oint_type_mask);
# printf("#define oint_addr_shift  %d\n",oint_addr_shift);
# printf("#define oint_addr_len  %d\n",oint_addr_len);
# printf1("#define oint_addr_mask  %x\n",(oint)oint_addr_mask);
# printf("#define oint_data_shift  %d\n",oint_data_shift);
# printf("#define oint_data_len  %d\n",oint_data_len);
# printf1("#define oint_data_mask  %x\n",(oint)oint_data_mask);
# printf("#define addr_shift  %d\n",addr_shift);
  printf("typedef uint%d tint;\n",oint_type_len);
  printf("typedef uint%d aint;\n",oint_addr_len);
# printf("typedef sint%d saint;\n",oint_addr_len);
# printf1("#define tint_type_mask  %x\n",(tint)tint_type_mask);
  #if !(defined(WIDE_SOFT) || defined(OBJECT_STRUCT))
    printf("#define objectplus(obj,offset)  ((object)pointerplus(obj,offset))\n");
  #else
    printf("#define objectplus(obj,offset)  as_object(as_oint(obj)+(soint)(offset))\n");
  #endif
  #if !defined(WIDE_SOFT)
#   printf("#define wbit  bit\n");
#   printf("#define wbitm  bitm\n");
    printf("#define wbit_test  bit_test\n");
    printf("#define minus_wbit  minus_bit\n");
  #else
    printf("#define wbit(n)  (1LL<<(n))\n");
#   printf("#define wbitm(n)  (2LL<<((n)-1))\n");
    printf("#define wbit_test(x,n)  ((x) & wbit(n))\n");
    printf("#define minus_wbit(n)  (-1LL<<(n))\n");
  #endif
  #ifdef TYPECODES
    #if !(exact_uint_size_p(oint_type_len) && (tint_type_mask == bit(oint_type_len)-1))
      printf2("#define typecode(expr)  ((tint)(as_oint(expr) >> %d) & %x)\n",oint_type_shift,(oint)(oint_type_mask >> oint_type_shift));
      printf("#define mtypecode(expr)  typecode(expr)\n");
    #else
      #if defined(MC68000) && defined(GNU) && !defined(NO_ASM) && (oint_type_shift==24) && (oint_type_len==8)
        printf("#define typecode(expr)  ({var tint __typecode; __asm__ (\"roll #8,%%0\" : \"=d\" (__typecode) : \"0\" (as_oint(expr)) ); __typecode; })\n");
      #elif defined(SPARC) && !defined(WIDE)
        printf("#define typecode(expr)  ((as_oint(expr) << %d) >> %d)\n",32-oint_type_len-oint_type_shift,32-oint_type_len);
      #elif defined(WIDE) && defined(WIDE_STRUCT)
        printf("#define typecode(expr)  ((expr).u.both.type)\n");
      #else
        printf("#define typecode(expr)  ((tint)(as_oint(expr) >> %d))\n",oint_type_shift);
      #endif
      #ifdef fast_mtypecode
        #ifndef WIDE
          printf("#define mtypecode(expr)  (*(tint*)&(expr)+%d)\n",3*((oint_type_shift==0)==BIG_ENDIAN_P));
        #endif
        #ifdef WIDE
          #ifdef WIDE_STRUCT
            printf("#define mtypecode(expr)  ((expr).u.both.type)\n");
          #elif (oint_type_len==16)
            printf("#define mtypecode(expr)  (*((tint*)&(expr)+%d))\n",3*((oint_type_shift==0)==BIG_ENDIAN_P));
          #elif (oint_type_len==32)
            printf("#define mtypecode(expr)  (*((tint*)&(expr)+%d))\n",((oint_type_shift==0)==BIG_ENDIAN_P));
          #endif
        #endif
      #else
        printf("#define mtypecode(expr)  typecode(expr)\n");
      #endif
    #endif
#   #if defined(WIDE) && defined(WIDE_STRUCT)
#     printf("#define untype(expr)  ((expr).u.both.addr)\n");
#   #elif !(defined(SPARC) && (oint_addr_len+oint_addr_shift<32))
#     printf2("#define untype(expr)  ((aint)(as_oint(expr) >> %d) & %x)\n",oint_addr_shift,(oint)(oint_addr_mask >> oint_addr_shift));
#   #else
#     printf("#define untype(expr)  ((aint)((as_oint(expr) << %d) >> %d))\n",32-oint_addr_len-oint_addr_shift,32-oint_addr_len);
#   #endif
    #if defined(WIDE) && defined(WIDE_STRUCT)
      #if BIG_ENDIAN_P==WIDE_ENDIANNESS
        printf("#define type_untype_object(type,address)  ((object){{(tint)(type),(aint)(address)}})\n");
      #else
        printf("#define type_untype_object(type,address)  ((object){{(aint)(address),(tint)(type)}})\n");
      #endif
    #elif !(oint_addr_shift==0)
      printf("#define type_untype_object(type,address)  (as_object(((oint)(tint)(type) << %d) + ((oint)(aint)(address) << %d)))\n",oint_type_shift,oint_addr_shift);
    #else
      #if defined(WIDE_SOFT)
        printf("#define type_untype_object(type,address)  objectplus((oint)(aint)(address),(oint)(tint)(type)<<%d)\n",oint_type_shift);
      #elif defined(OBJECT_STRUCT)
        printf("#define type_untype_object(type,address)  as_object((oint)pointerplus((address),(oint)(tint)(type)<<%d))\n",oint_type_shift);
      #else
        printf("#define type_untype_object(type,address)  as_object(pointerplus((address),(oint)(tint)(type)<<%d))\n",oint_type_shift);
      #endif
    #endif
    #if defined(WIDE) && defined(WIDE_STRUCT)
      #if BIG_ENDIAN_P==WIDE_ENDIANNESS
        printf("#define type_data_object(type,address)  ((object){{(tint)(type),(aint)(address)}})\n");
      #else
        printf("#define type_data_object(type,address)  ((object){{(aint)(address),(tint)(type)}})\n");
      #endif
    #elif !(oint_addr_shift==0)
      printf("#define type_data_object(type,data)  (as_object(((oint)(tint)(type) << %d) + ((oint)(aint)(data) << %d)))\n",oint_type_shift,oint_addr_shift);
    #else
      printf("#define type_data_object(type,data)  (as_object(((oint)(tint)(type) << %d) + (oint)(aint)(data)))\n",oint_type_shift);
    #endif
    #if (addr_shift==0)
      printf("#define upointer  untype\n");
    #else
      printf("#define optimized_upointer(obj)  ((aint)((as_oint(obj) << %d) >> %d))\n",32-oint_addr_len-oint_addr_shift,32-oint_addr_len-addr_shift);
      printf("#define upointer(obj)  (untype(obj)<<%d)\n",addr_shift);
    #endif
    #if (addr_shift==0)
      printf("#define type_pointer_object(type,address)  type_untype_object(type,address)\n");
    #elif defined(WIDE_SOFT) && !defined(WIDE_STRUCT)
      printf("#define type_pointer_object(type,address)    type_untype_object(type,(aint)(address)>>%d)\n",addr_shift);
    #else
      printf("#define type_pointer_object(type,address)  (as_object(((oint)(tint)(type) << %d) + ((oint)(aint)(address) << %d)))\n",oint_type_shift,oint_addr_shift-addr_shift);
    #endif
    printf("#define type_constpointer_object(type,address)  type_pointer_object(type,address)\n");
    #if defined(WIDE_SOFT) && defined(WIDE_STRUCT)
      printf("#define type_zero_oint(type)  as_oint(type_untype_object(type,0))\n");
    #else
      printf("#define type_zero_oint(type)  ((oint)(tint)(type) << %d)\n",oint_type_shift);
    #endif
  #else
    printf("#define type_data_object(type,data)  (as_object(((oint)(tint)(type) << %d) + ((oint)(aint)(data) << %d)))\n",oint_type_shift,oint_addr_shift);
    printf("#define type_zero_oint(type)  ((oint)(tint)(type) << %d)\n",oint_type_shift);
  #endif
  printf("typedef object gcv_object_t;\n");
  #ifdef TYPECODES
    printf("#define VAROBJECT_HEADER  object GCself;\n");
  #else
    printf("#define VAROBJECT_HEADER  object GCself; uintL tfl;\n");
  #endif
  #ifndef TYPECODES
    printf("#define varobject_type(ptr) ((sintB)((ptr)->tfl & 0xFF))\n");
  #endif
  #ifdef TYPECODES
    printf("typedef struct { VAROBJECT_HEADER uintB recflags; sintB rectype; uintW recfiller; gcv_object_t recdata[unspecified]; } record_;\n");
  #else
    printf("typedef struct { VAROBJECT_HEADER gcv_object_t recdata[unspecified]; } record_;\n");
  #endif
  printf("typedef record_ *  Record;\n");
  #ifdef TYPECODES
    printf("#define record_type(ptr)  ((ptr)->rectype)\n");
  #else
    printf("#define record_type(ptr)  varobject_type(ptr)\n");
  #endif
  printf("#define Record_type(obj)  record_type(TheRecord(obj))\n");
  #ifdef TYPECODES
    printf("#define record_flags(ptr)  ((ptr)->recflags)\n");
  #else
    printf("#define record_flags(ptr)  (((ptr)->tfl >> 8) & 0xFF)\n");
  #endif
  printf("#define Record_flags(obj)  record_flags(TheRecord(obj))\n");
# #ifdef TYPECODES
#   printf("#define LRECORD_HEADER  VAROBJECT_HEADER uintL length;\n");
# #else
#   printf("#define LRECORD_HEADER  VAROBJECT_HEADER\n");
# #endif
# printf("typedef struct { LRECORD_HEADER } lrecord_;\n");
# printf("typedef lrecord_ *  Lrecord;\n");
# #ifdef TYPECODES
#   printf("#define SRECORD_HEADER  VAROBJECT_HEADER uintB recflags; sintB rectype; uintW reclength;\n");
# #else
#   printf("#define SRECORD_HEADER  VAROBJECT_HEADER\n");
# #endif
# printf("typedef struct { SRECORD_HEADER object recdata[unspecified]; } srecord_;\n");
# printf("typedef srecord_ *  Srecord;\n");
  #ifdef TYPECODES
    printf("#define srecord_length(ptr)  ((ptr)->reclength)\n");
  #else
    printf("#define srecord_length(ptr)  ((ptr)->tfl >> 16)\n");
  #endif
# #ifdef TYPECODES
#   printf("#define XRECORD_HEADER  VAROBJECT_HEADER uintB recflags; sintB rectype; uintB reclength; uintB recxlength;\n");
# #else
#   printf("#define XRECORD_HEADER  VAROBJECT_HEADER\n");
# #endif
# printf("typedef struct { XRECORD_HEADER object recdata[unspecified]; } xrecord_;\n");
# printf("typedef xrecord_ *  Xrecord;\n");
# printf("typedef struct { object cdr; object car; } cons_;\n");
# printf("typedef cons_ *  Cons;\n");
# #ifdef SPVW_MIXED
#   printf("typedef struct { XRECORD_HEADER object rt_num; object rt_den; } ratio_;\n");
# #else
#   printf("typedef struct { object rt_num; object rt_den; } ratio_;\n");
# #endif
# printf("typedef ratio_ *  Ratio;\n");
# #ifdef SPVW_MIXED
#   printf("typedef struct { XRECORD_HEADER object c_real; object c_imag; } complex_;\n");
# #else
#   printf("typedef struct { object c_real; object c_imag; } complex_;\n");
# #endif
# printf("typedef complex_ *  Complex;\n");
  printf("typedef struct { VAROBJECT_HEADER gcv_object_t symvalue; gcv_object_t symfunction; gcv_object_t proplist; gcv_object_t pname; gcv_object_t homepackage; } symbol_;\n");
# printf("typedef symbol_ *  Symbol;\n");
  printf("typedef uint%d cint;\n",char_int_len);
  printf1("#define int_char(int_from_int_char)  type_data_object(%d,(aint)(cint)(int_from_int_char))\n",(tint)char_type);
  #if !((oint_data_shift==0) && (char_int_len<=oint_data_len) && (exact_uint_size_p(char_int_len)))
    #ifdef TYPECODES
      printf("#define char_int(char_from_char_int)  ((cint)(untype(char_from_char_int)))\n");
    #else
      printf1("#define char_int(char_from_char_int)  ((cint)(as_oint(char_from_char_int)>>%d))\n",oint_data_shift);
    #endif
  #else
    printf("#define char_int(char_from_char_int)  ((cint)as_oint(char_from_char_int))\n");
  #endif
  #ifdef CHART_STRUCT
    printf("typedef struct { cint one; } chart;\n");
    printf("#define as_cint(ch)  ((ch).one)\n");
    printf("#define as_chart(c)  ((chart){one:(c)})\n");
  #else
    printf("typedef cint chart;\n");
    printf("#define as_cint(ch)  (ch)\n");
    printf("#define as_chart(c)  (c)\n");
  #endif
  printf("#define code_char(ch)  int_char(as_cint(ch))\n");
  printf("#define char_code(obj)  as_chart(char_int(obj))\n");
  printf1("#define fixnum(x)  type_data_object(%d,x)\n",(tint)fixnum_type);
# printf("#define Fixnum_0  fixnum(0)\n");
# printf("#define Fixnum_1  fixnum(1)\n");
# printf2("#define Fixnum_minus1  type_data_object(%d,%x)\n",(tint)(fixnum_type | bit(sign_bit_t)),(aint)(bitm(oint_data_len)-1));
  #if !(defined(SPARC) && (oint_data_len+oint_data_shift<32))
    printf2("#define posfixnum_to_L(obj)  ((uintL)((as_oint(obj)&%x)>>%d))\n",(oint)wbitm(oint_data_len+oint_data_shift)-1,oint_data_shift);
  #else
    printf("#define posfixnum_to_L(obj)  ((uintL)((as_oint(obj) << %d) >> %d))\n",32-oint_data_len-oint_data_shift,32-oint_data_len);
  #endif
# printf1("#define negfixnum_to_L(obj)  (posfixnum_to_L(obj) | %x)\n",(uintL)(-bitm(oint_data_len)));
  #if (oint_data_len>=intLsize)
    printf("#define fixnum_to_L(obj)  (sintL)posfixnum_to_L(obj)\n");
  #elif (sign_bit_o == oint_data_len+oint_data_shift)
    printf("#define fixnum_to_L(obj)  (((sintL)as_oint(obj) << %d) >> %d)\n",intLsize-1-sign_bit_o,intLsize-1-sign_bit_o+oint_data_shift);
  #else
    #if !defined(SPARC)
      printf5("#define fixnum_to_L(obj)  (sintL)( ((((sintL)as_oint(obj) >> %d) << %d) >> %d) | ((uintL)((as_oint(obj) & %x) >> %d)) )\n",sign_bit_o,intLsize-1,intLsize-1-oint_data_len,(oint)wbitm(oint_data_len+oint_data_shift)-1,oint_data_shift);
    #else
      printf("#define fixnum_to_L(obj)  (sintL)( ((((sintL)as_oint(obj) >> %d) << %d) >> %d) | (((uintL)as_oint(obj) << %d) >> %d) )\n",sign_bit_o,intLsize-1,intLsize-1-oint_data_len,intLsize-oint_data_len-oint_data_shift,intLsize-oint_data_len);
    #endif
  #endif
# printf("#define fixnum_inc(obj,delta)  objectplus(obj, (soint)(delta) << %d)\n",oint_data_shift);
# printf("#define posfixnum(x)  fixnum_inc(Fixnum_0,x)\n");
# printf("#define negfixnum(x)  fixnum_inc(fixnum_inc(Fixnum_minus1,1),x)\n");
# printf("#define sfixnum(x) ((x)>=0 ? posfixnum(x) : negfixnum(x))\n");
  #ifdef TYPECODES
    printf("typedef struct { VAROBJECT_HEADER uintC length; uintD data[unspecified]; } bignum_;\n");
  #else
    printf("typedef struct { VAROBJECT_HEADER uintD data[unspecified]; } bignum_;\n");
  #endif
  printf("typedef bignum_ *  Bignum;\n");
  #ifdef TYPECODES
    printf("#define bignum_length(ptr)  ((ptr)->length)\n");
  #else
    printf("#define bignum_length(ptr)  srecord_length(ptr)\n");
  #endif
  printf("#define Bignum_length(obj)  bignum_length(TheBignum(obj))\n");
  printf("typedef uint32 ffloat;\n");
  printf("typedef union { ffloat eksplicit; } ffloatjanus;\n");
  #ifdef intQsize
    printf("typedef uint64 dfloat;\n");
  #else
    #if BIG_ENDIAN_P
      printf("typedef struct {uint32 semhi,mlo;} dfloat;\n");
    #else
      printf("typedef struct {uint32 mlo,semhi;} dfloat;\n");
    #endif
  #endif
  printf("typedef union { dfloat eksplicit; } dfloatjanus;\n");
# printf("typedef struct { LRECORD_HEADER uintL  length; } sarray_;\n");
# printf("typedef sarray_ *  Sarray;\n");
# printf("typedef struct { LRECORD_HEADER uintL  length; uint8  data[unspecified]; } sbvector_;\n");
# printf("typedef sbvector_ *  Sbvector;\n");
# #ifdef UNICODE
#   printf("typedef struct { LRECORD_HEADER uintL  length; uint32  data[unspecified]; } sstring_;\n");
# #else
#   printf("typedef struct { LRECORD_HEADER uintL  length; uint8  data[unspecified]; } sstring_;\n");
# #endif
# printf("typedef sstring_ *  Sstring;\n");
# printf("typedef struct { LRECORD_HEADER uintL  length; object data[unspecified]; } svector_;\n");
# printf("typedef svector_ *  Svector;\n");
# #ifdef TYPECODES
#   printf("#define Array_type_simple_bit_vector(atype)  (%d+((atype)<<%d)",Array_type_sbvector,TB0);
#   if (TB0+1 != TB1) printf("+((atype)&%d)",bit(TB0+1)-bit(TB1));
#   if (TB1+1 != TB2) printf("+((atype)&%d)",bit(TB1+1)-bit(TB2));
#   printf(");\n");
# #endif
# printf("typedef struct { XRECORD_HEADER object pack_external_symbols; object pack_internal_symbols; object pack_shadowing_symbols; object pack_use_list; object pack_used_by_list; object pack_name; object pack_nicknames; } *  Package;\n");
# printf("typedef Srecord  Structure;\n");
# printf("#define structure_types   recdata[0]\n");
# printf("typedef struct { SRECORD_HEADER object class; object other[unspecified]; } *  Instance;\n");
  printf("typedef void Values;\n");
  printf("typedef Values (*lisp_function_t)();\n");
  printf("typedef struct { lisp_function_t function; gcv_object_t name; gcv_object_t keywords; uintW argtype; uintW req_anz; uintW opt_anz; uintB rest_flag; uintB key_flag; uintW key_anz; } subr_t");
  #if defined(NO_TYPECODES) && (alignment_long < 4) && defined(GNU)
    printf(" __attribute__ ((aligned (4)))");
  #endif
  printf(";\n");
# printf("typedef subr_t *  Subr;\n");
  printf("typedef enum { subr_norest, subr_rest } subr_rest_t;\n");
  printf("typedef enum { subr_nokey, subr_key, subr_key_allow } subr_key_t;\n");
  #ifdef TYPECODES
    printf1("#define make_machine(ptr)  type_pointer_object(%d,ptr)\n",(tint)machine_type);
  #else
    printf1("#define make_machine(ptr)  as_object((oint)(ptr)+%d)\n",machine_bias)
  #endif
# printf3("#define make_system(data)  type_data_object(%d,%x | (%x & (data)))\n",(tint)system_type,(oint)(bit(oint_data_len-1) | bit(0)),(oint)(bit(oint_data_len)-1));
# printf1("#define unbound  make_system(%x)\n",0xFFFFFFUL);
  printf("#define nullobj  make_machine(0)\n");
  #ifdef TYPECODES
    #if !((oint_addr_shift==0) && (addr_shift==0))
      printf("#define pointable(obj)  ((void*)upointer(obj))\n");
    #else
      #if !(((tint_type_mask<<oint_type_shift) & addressbus_mask) == 0)
        printf1("#define pointable(obj)  ((void*)((aint)as_oint(obj) & %x))\n",(aint)oint_addr_mask | ~addressbus_mask);
      #else
        printf("#define pointable(obj)  ((void*)as_oint(obj))\n");
      #endif
    #endif
    #if defined(WIDE_STRUCT)
      #define printf_type_pointable(type)  printf("((void*)((obj).u.both.addr))");
    #elif !((oint_addr_shift==0) && (addr_shift==0) && (((tint_type_mask<<oint_type_shift) & addressbus_mask) == 0))
      #if (addr_shift==0)
        #define printf_type_pointable(type)  \
          if ((oint_addr_shift==0) && ((type_zero_oint(type) & addressbus_mask) == 0)) \
            printf("((void*)(aint)as_oint(obj))"); \
            else \
            printf("((void*)(aint)pointable(obj))");
      #elif !(addr_shift==0)
        #define printf_type_pointable(type)  \
          if (optimized_upointer(type_data_object(type,0)) == 0) \
            printf("((void*)(aint)optimized_upointer(obj))"); \
            else \
            printf("((void*)(aint)pointable(obj))");
      #endif
    #else
      #define printf_type_pointable(type)  printf("((void*)(aint)as_oint(obj))");
    #endif
#   printf("#define TheCons(obj)  ((Cons)("); printf_type_pointable(cons_type); printf("))\n");
#   printf("#define TheRatio(obj)  ((Ratio)("); printf_type_pointable(ratio_type|bit(sign_bit_t)); printf("))\n");
#   printf("#define TheComplex(obj)  ((Complex)("); printf_type_pointable(complex_type); printf("))\n");
#   printf("#define TheSymbol(obj)  ((Symbol)("); printf_type_pointable(symbol_type); printf("))\n");
    printf("#define TheBignum(obj)  ((Bignum)("); printf_type_pointable(bignum_type|bit(sign_bit_t)); printf("))\n");
#   printf("#define TheSarray(obj)  ((Sarray)("); printf_type_pointable(sbvector_type|sb2vector_type|sb4vector_type|sb8vector_type|sb16vector_type|sb32vector_type|sstring_type|svector_type); printf("))\n");
#   printf("#define TheSbvector(obj)  ((Sbvector)("); printf_type_pointable(sbvector_type|sb2vector_type|sb4vector_type|sb8vector_type|sb16vector_type|sb32vector_type); printf("))\n");
#   printf("#define TheSstring(obj)  ((Sstring)("); printf_type_pointable(sstring_type); printf("))\n");
#   printf("#define TheSvector(obj)  ((Svector)("); printf_type_pointable(svector_type); printf("))\n");
    printf("#define TheRecord(obj)  ((Record)("); printf_type_pointable(closure_type|structure_type|stream_type|orecord_type|instance_type); printf("))\n");
#   printf("#define TheSrecord(obj)  ((Srecord)("); printf_type_pointable(closure_type|structure_type|orecord_type|instance_type); printf("))\n");
#   printf("#define TheXrecord(obj)  ((Xrecord)("); printf_type_pointable(stream_type|orecord_type); printf("))\n");
#   printf("#define ThePackage(obj)  ((Package)("); printf_type_pointable(orecord_type); printf("))\n");
#   printf("#define TheStructure(obj)  ((Structure)("); printf_type_pointable(structure_type); printf("))\n");
#   printf("#define TheInstance(obj)  ((Instance)("); printf_type_pointable(instance_type); printf("))\n");
#   printf("#define TheSubr(obj)  ((Subr)("); printf_type_pointable(subr_type); printf("))\n");
#   printf("#define TheMachine(obj)  ((void*)("); printf_type_pointable(machine_type); printf("))\n");
  #else
#   printf1("#define TheCons(obj)  ((Cons)(as_oint(obj)-%d))\n",cons_bias);
#   printf1("#define TheRatio(obj)  ((Ratio)(as_oint(obj)-%d))\n",varobject_bias);
#   printf1("#define TheComplex(obj)  ((Complex)(as_oint(obj)-%d))\n",varobject_bias);
#   printf1("#define TheSymbol(obj)  ((Symbol)(as_oint(obj)-%d))\n",varobject_bias);
    printf1("#define TheBignum(obj)  ((Bignum)(as_oint(obj)-%d))\n",varobject_bias);
#   printf1("#define TheSarray(obj)  ((Sarray)(as_oint(obj)-%d))\n",varobject_bias);
#   printf1("#define TheSbvector(obj)  ((Sbvector)(as_oint(obj)-%d))\n",varobject_bias);
#   printf1("#define TheSstring(obj)  ((Sstring)(as_oint(obj)-%d))\n",varobject_bias);
#   printf1("#define TheSvector(obj)  ((Svector)(as_oint(obj)-%d))\n",varobject_bias);
    printf1("#define TheRecord(obj)  ((Record)(as_oint(obj)-%d))\n",varobject_bias);
#   printf1("#define TheSrecord(obj)  ((Srecord)(as_oint(obj)-%d))\n",varobject_bias);
#   printf1("#define TheXrecord(obj)  ((Xrecord)(as_oint(obj)-%d))\n",varobject_bias);
#   printf1("#define ThePackage(obj)  ((Package)(as_oint(obj)-%d))\n",varobject_bias);
#   printf1("#define TheStructure(obj)  ((Structure)(as_oint(obj)-%d))\n",varobject_bias);
#   printf1("#define TheInstance(obj)  ((Instance)(as_oint(obj)-%d))\n",varobject_bias);
#   printf1("#define TheSubr(obj)  ((Subr)(as_oint(obj)-%d))\n",subr_bias);
#   printf1("#define TheMachine(obj)  ((void*)(as_oint(obj)-%d))\n",machine_bias);
  #endif
# printf("#define Car(obj)  (TheCons(obj)->car)\n");
# printf("#define Cdr(obj)  (TheCons(obj)->cdr)\n");
# printf("#define Symbol_value(obj)  (TheSymbol(obj)->symvalue)\n");
# printf("#define Symbol_function(obj)  (TheSymbol(obj)->symfunction)\n");
# printf("#define Symbol_plist(obj)  (TheSymbol(obj)->proplist)\n");
# printf("#define Symbol_name(obj)  (TheSymbol(obj)->pname)\n");
# printf("#define Symbol_package(obj)  (TheSymbol(obj)->homepackage)\n");
  #if defined(WIDE_STRUCT) || defined(OBJECT_STRUCT)
    printf("#define eq(obj1,obj2)  (as_oint(obj1) == as_oint(obj2))\n");
  #else
    printf("#define eq(obj1,obj2)  ((obj1) == (obj2))\n");
  #endif
  printf("#define nullp(obj)  (eq(obj,NIL))\n");
# #ifdef TYPECODES
#   #if defined(cons_bit_o)
#     #ifdef fast_mtypecode
#       #ifdef WIDE_STRUCT
#         printf("#define consp(obj)  (typecode(obj) & bit(%d))\n",cons_bit_t);
#         printf("#define atomp(obj)  ((typecode(obj) & bit(%d))==0)\n",cons_bit_t);
#       #else
#         printf("#define consp(obj)  (wbit_test(as_oint(obj),%d))\n",cons_bit_o);
#         printf("#define atomp(obj)  (!wbit_test(as_oint(obj),%d))\n",cons_bit_o);
#       #endif
#       printf("#define mconsp(obj)  (mtypecode(obj) & bit(%d))\n",cons_bit_t);
#       printf("#define matomp(obj)  ((mtypecode(obj) & bit(%d))==0)\n",cons_bit_t);
#     #else
#       printf("#define consp(obj)  (wbit_test(as_oint(obj),%d))\n",cons_bit_o);
#       printf("#define atomp(obj)  (!wbit_test(as_oint(obj),%d))\n",cons_bit_o);
#       printf("#define mconsp(obj)  consp(obj)\n");
#       printf("#define matomp(obj)  atomp(obj)\n");
#     #endif
#   #else
#     printf2("#define consp(obj)  (typecode(obj) == %d)\n",(tint)cons_type);
#     printf2("#define atomp(obj)  (!(typecode(obj) == %d))\n",(tint)cons_type);
#     printf2("#define mconsp(obj)  (mtypecode(obj) == %d)\n",(tint)cons_type);
#     printf2("#define matomp(obj)  (!(mtypecode(obj) == %d))\n",(tint)cons_type);
#   #endif
# #else
#   printf2("#define consp(obj)  ((as_oint(obj) & %d) == %d)\n",7,cons_bias);
#   printf("#define mconsp(obj)  consp(obj)\n");
#   printf("#define atomp(obj)  (!consp(obj))\n");
#   printf("#define matomp(obj)  atomp(obj)\n");
# #endif
# printf("#define listp(obj)  (nullp(obj) || consp(obj))\n");
  #ifndef TYPECODES
    printf2("#define varobjectp(obj)  ((as_oint(obj) & %d) == %d)\n",3,varobject_bias);
  #endif
# #ifdef TYPECODES
#   #if defined(symbol_bit_o)
#     #ifdef WIDE_STRUCT
#       printf("#define symbolp(obj)  (typecode(obj) & bit(%d))\n",symbol_bit_t);
#     #else
#       printf("#define symbolp(obj)  (wbit_test(as_oint(obj),%d))\n",symbol_bit_o);
#     #endif
#   #else
#     printf1("#define symbolp(obj)  (typecode(obj) == %d)\n",(tint)symbol_type);
#   #endif
# #else
#   printf1("#define symbolp(obj)  (varobjectp(obj) && (Record_type(obj) == %d))\n",Rectype_Symbol);
# #endif
# #ifdef TYPECODES
#   #ifdef WIDE_STRUCT
#     printf("#define numberp(obj)  (typecode(obj) & bit(%d))\n",number_bit_t);
#   #else
#     printf("#define numberp(obj)  (wbit_test(as_oint(obj),%d))\n",number_bit_o);
#   #endif
# #else
#   printf2("#define immediate_number_p(obj)  ((as_oint(obj) & %d) == %d)\n",(4 << imm_type_shift) | immediate_bias,(fixnum_type&sfloat_type));
# #endif
# #ifdef TYPECODES
#   printf2("#define vectorp(obj)  ((tint)(typecode(obj) - %d) <= (tint)%d)\n",(tint)sbvector_type,(tint)(vector_type-sbvector_type));
# #else
#   printf1("#define vectorp(obj)  (varobjectp(obj) && ((uintB)(Record_type(obj) - 1) <= %d))\n",23-1);
# #endif
# #ifdef TYPECODES
#   printf2("#define simple_vector_p(obj)  (typecode(obj) == %d)\n",(tint)svector_type);
# #else
#   printf1("#define simple_vector_p(obj)  (varobjectp(obj) && (Record_type(obj) == %d))\n",Rectype_Svector);
# #endif
# #ifdef TYPECODES
#   printf2("#define general_vector_p(obj)  ((typecode(obj) & ~%d) == %d)\n",(tint)bit(notsimple_bit_t),(tint)svector_type);
# #else
#   printf2("#define general_vector_p(obj)  (varobjectp(obj) && ((Record_type(obj) & ~%d) == %d))\n",Rectype_Svector^Rectype_vector,Rectype_Svector&Rectype_vector);
# #endif
# #ifdef TYPECODES
#   printf2("#define simple_string_p(obj)  (typecode(obj) == %d)\n",(tint)sstring_type);
# #else
#   printf1("#define simple_string_p(obj)  (varobjectp(obj) && ((uintB)(Record_type(obj) - 16) <= %d))\n",22-16);
# #endif
# #ifdef TYPECODES
#   printf2("#define stringp(obj)  ((typecode(obj) & ~%d) == %d)\n",(tint)bit(notsimple_bit_t),(tint)sstring_type);
# #else
#   printf1("#define stringp(obj)  (varobjectp(obj) && ((uintB)(Record_type(obj) - 16) == %d))\n",23-16);
# #endif
# #ifdef TYPECODES
#   printf1("#define simple_bit_vector_p(atype,obj)  (typecode(obj) == Array_type_simple_bit_vector(atype))\n");
# #else
#   printf1("#define simple_bit_vector_p(atype,obj)  (varobjectp(obj) && (Record_type(obj) == %d+(atype)))\n",Rectype_Sbvector);
# #endif
# #ifdef TYPECODES
#   printf2("#define bit_vector_p(atype,obj)  ((typecode(obj) & ~%d) == Array_type_simple_bit_vector(atype))\n",(tint)bit(notsimple_bit_t));
# #else
#   printf2("#define bit_vector_p(atype,obj)  (varobjectp(obj) && ((Record_type(obj) & ~%d) == %d+(atype)))\n",Rectype_Sbvector^Rectype_bvector,Rectype_Sbvector&Rectype_bvector);
# #endif
# #ifdef TYPECODES
#   printf2("#define arrayp(obj)  ((tint)(typecode(obj) - %d) <= (tint)%d)\n",(tint)mdarray_type,(tint)(vector_type-mdarray_type));
# #else
#   printf1("#define arrayp(obj)  (varobjectp(obj) && ((uintB)(Record_type(obj)-1) <= %d))\n",24-1);
# #endif
# #ifdef TYPECODES
#   printf1("#define instancep(obj)  (typecode(obj)==%d)\n",(tint)instance_type);
# #else
#   printf1("#define instancep(obj)  (varobjectp(obj) && (Record_type(obj) == %d))\n",Rectype_Instance);
# #endif
# #ifdef TYPECODES
#   printf1("#define orecordp(obj)  (typecode(obj)==%d)\n",(tint)orecord_type);
# #else
#   printf("#define orecordp(obj)  varobjectp(obj)\n");
# #endif
# #ifdef case_structure
#   printf1("#define structurep(obj)  (typecode(obj)==%d)\n",(tint)structure_type);
# #else
#   printf("#define structurep(obj)  (orecordp(obj) && (Record_type(obj) == %d))\n",Rectype_Structure);
# #endif
# printf("#define packagep(obj)  (orecordp(obj) && (Record_type(obj) == %d))\n",Rectype_Package);
# #ifdef TYPECODES
#   printf1("#define charp(obj)  (typecode(obj)==%d)\n",(tint)char_type);
# #else
#   printf2("#define charp(obj)  ((as_oint(obj) & %d) == %d)\n",(7 << imm_type_shift) | immediate_bias,char_type);
# #endif
# #ifdef TYPECODES
#   printf2("#define integerp(obj)  ((typecode(obj) & ~%d) == %d)\n",(tint)((fixnum_type|bignum_type|bit(sign_bit_t)) & ~(fixnum_type&bignum_type)),(tint)(fixnum_type&bignum_type));
# #else
#   printf3("#define integerp(obj)  (((as_oint(obj) & %d) == %d) || (varobjectp(obj) && (Record_type(obj) == %d)))\n",(6 << imm_type_shift) | immediate_bias,fixnum_type,Rectype_Bignum);
# #endif
  #ifdef TYPECODES
    printf2("#define fixnump(obj)  ((typecode(obj) & ~%d) == %d)\n",(tint)bit(sign_bit_t),(tint)fixnum_type);
  #else
    printf2("#define fixnump(obj)  ((as_oint(obj) & %d) == %d)\n",(6 << imm_type_shift) | immediate_bias,fixnum_type);
  #endif
  #ifdef TYPECODES
    printf1("#define posfixnump(obj)  (typecode(obj) == %d)\n",(tint)fixnum_type);
  #else
    printf2("#define posfixnump(obj)  ((as_oint(obj) & %d) == %d)\n",(7 << imm_type_shift) | immediate_bias,fixnum_type);
  #endif
  #ifdef TYPECODES
    printf2("#define bignump(obj)  ((typecode(obj) & ~%d) == %d)\n",(tint)bit(sign_bit_t),(tint)bignum_type);
  #else
    printf1("#define bignump(obj)  (varobjectp(obj) && (Record_type(obj) == %d))\n",Rectype_Bignum);
  #endif
  #ifdef TYPECODES
    printf1("#define posbignump(obj)  (typecode(obj) == %d)\n",(tint)bignum_type);
  #else
    printf1("#define posbignump(obj)  (varobjectp(obj) && (Record_type(obj) == %d) && ((Record_flags(obj) & bit(7)) == 0))\n",Rectype_Bignum);
  #endif
# #ifdef TYPECODES
#   printf2("#define ratiop(obj)  ((typecode(obj) & ~%d) == %d)\n",(tint)bit(sign_bit_t),(tint)ratio_type);
# #else
#   printf1("#define ratiop(obj)  (varobjectp(obj) && (Record_type(obj) == %d))\n",Rectype_Ratio);
# #endif
# #ifdef TYPECODES
#   printf2("#define floatp(obj)  ((typecode(obj) & ~%d) == %d)\n",(tint)((sfloat_type|ffloat_type|dfloat_type|lfloat_type|bit(sign_bit_t)) & ~(sfloat_type&ffloat_type&dfloat_type&lfloat_type)),(tint)(sfloat_type&ffloat_type&dfloat_type&lfloat_type));
# #else
#   printf4("#define floatp(obj)  (((as_oint(obj) & %d) == %d) || (varobjectp(obj) && ((uintB)(Record_type(obj)-%d) <= %d)))\n",(6 << imm_type_shift) | immediate_bias,sfloat_type,Rectype_Lfloat,Rectype_Ffloat-Rectype_Lfloat);
# #endif
# #ifdef TYPECODES
#   printf2("#define short_float_p(obj)  ((typecode(obj) & ~%d) == %d)\n",(tint)bit(sign_bit_t),(tint)sfloat_type);
# #else
#   printf2("#define short_float_p(obj)  ((as_oint(obj) & &d) == %d)\n",(6 << imm_type_shift) | immediate_bias,sfloat_type);
# #endif
# #ifdef TYPECODES
#   printf2("#define single_float_p(obj)  ((typecode(obj) & ~%d) == %d)\n",(tint)bit(sign_bit_t),(tint)ffloat_type);
# #else
#   printf1("#define single_float_p(obj)  (varobjectp(obj) && (Record_type(obj) == %d))\n",Rectype_Ffloat);
# #endif
# #ifdef TYPECODES
#   printf2("#define double_float_p(obj)  ((typecode(obj) & ~%d) == %d)\n",(tint)bit(sign_bit_t),(tint)dfloat_type);
# #else
#   printf1("#define double_float_p(obj)  (varobjectp(obj) && (Record_type(obj) == %d))\n",Rectype_Dfloat);
# #endif
# #ifdef TYPECODES
#   printf2("#define long_float_p(obj)  ((typecode(obj) & ~%d) == %d)\n",(tint)bit(sign_bit_t),(tint)lfloat_type);
# #else
#   printf1("#define long_float_p(obj)  (varobjectp(obj) && (Record_type(obj) == %d))\n",Rectype_Lfloat);
# #endif
# #ifdef TYPECODES
#   printf1("#define complexp(obj)  (typecode(obj) == %d)\n",(tint)complex_type);
# #else
#   printf1("#define complexp(obj)  (varobjectp(obj) && (Record_type(obj) == %d))\n",Rectype_Complex);
# #endif
  #ifdef TYPECODES
    #ifdef WIDE_STRUCT
      printf("#define positivep(obj)  ((typecode(obj) & bit(%d)) == 0)\n",sign_bit_t);
    #else
      printf("#define positivep(obj)  (!wbit_test(as_oint(obj),%d))\n",sign_bit_o);
    #endif
  #else
    printf2("#define positivep(obj)  ((as_oint(obj) & wbit(1)) ? (as_oint(obj) & %d) == 0 : (Record_flags(obj) & %d) == 0)\n",wbit(sign_bit_o),bit(7));
  #endif
  #ifdef TYPECODES
    printf("#define FN_positivep(obj)  positivep(obj)\n");
  #else
    printf1("#define FN_positivep(obj)  ((as_oint(obj) & %d) == 0)\n",wbit(sign_bit_o));
  #endif
  #ifdef TYPECODES
    printf("#define BN_positivep(obj)  positivep(obj)\n");
  #else
    printf1("#define BN_positivep(obj)  ((Record_flags(obj) & %d) == 0)\n",bit(7));
  #endif
  printf2("#define uint8_p(obj)  ((as_oint(obj) & ~%x) == %x)\n",(oint)0xFF << oint_data_shift,as_oint(Fixnum_0));
  printf3("#define sint8_p(obj)  (((as_oint(obj) ^ (FN_positivep(obj) ? 0 : %x)) & ~%x) == %x)\n",as_oint(Fixnum_minus1)^as_oint(Fixnum_0),(oint)0x7F << oint_data_shift,as_oint(Fixnum_0));
  printf2("#define uint16_p(obj)  ((as_oint(obj) & ~%x) == %x)\n",(oint)0xFFFF << oint_data_shift,as_oint(Fixnum_0));
  printf3("#define sint16_p(obj)  (((as_oint(obj) ^ (FN_positivep(obj) ? 0 : %x)) & ~%x) == %x)\n",as_oint(Fixnum_minus1)^as_oint(Fixnum_0),(oint)0x7FFF << oint_data_shift,as_oint(Fixnum_0));
  #if (oint_data_len>=32)
    printf2("#define uint32_p(obj)  ((as_oint(obj) & ~%x) == %x)\n",(oint)0xFFFFFFFF << oint_data_shift,as_oint(Fixnum_0));
  #else
    printf3("#define uint32_p(obj)  (posfixnump(obj) || (posbignump(obj) && (Bignum_length(obj) <= %d) && ((Bignum_length(obj) < %d) || (TheBignum(obj)->data[0] < (uintD)bit(%d)) )))\n",ceiling(33,intDsize),ceiling(33,intDsize),32%intDsize);
  #endif
  #if (oint_data_len>=31)
    printf3("#define sint32_p(obj)  (((as_oint(obj) ^ (FN_positivep(obj) ? 0 : %x)) & ~%x) == %x)\n",as_oint(Fixnum_minus1)^as_oint(Fixnum_0),(oint)0x7FFFFFFF << oint_data_shift,as_oint(Fixnum_0));
  #else
    printf3("#define sint32_p(obj)  (fixnump(obj) || (bignump(obj) && (Bignum_length(obj) <= %d) && ((Bignum_length(obj) < %d) || ((TheBignum(obj)->data[0] ^ (BN_positivep(obj) ? (uintD)0 : ~(uintD)0)) < (uintD)bit(%d)) )))\n",ceiling(32,intDsize),ceiling(32,intDsize),31%intDsize);
  #endif
  printf3("#define uint64_p(obj)  (posfixnump(obj) || (posbignump(obj) && (Bignum_length(obj) <= %d) && ((Bignum_length(obj) < %d) || (TheBignum(obj)->data[0] < (uintD)bit(%d)) )))\n",ceiling(65,intDsize),ceiling(65,intDsize),64%intDsize);
  printf3("#define sint64_p(obj)  (fixnump(obj) || (bignump(obj) && (Bignum_length(obj) <= %d) && ((Bignum_length(obj) < %d) || ((TheBignum(obj)->data[0] ^ (BN_positivep(obj) ? (uintD)0 : ~(uintD)0)) < (uintD)bit(%d)) )))\n",ceiling(64,intDsize),ceiling(64,intDsize),63%intDsize);
# #if (int_bitsize==16)
#   printf("#define uint_p  uint16_p\n");
#   printf("#define sint_p  sint16_p\n");
# #else
#   printf("#define uint_p  uint32_p\n");
#   printf("#define sint_p  sint32_p\n");
# #endif
# #if (long_bitsize==32)
#   printf("#define ulong_p  uint32_p\n");
#   printf("#define slong_p  sint32_p\n");
# #else
#   printf("#define ulong_p  uint64_p\n");
#   printf("#define slong_p  sint64_p\n");
# #endif
  #if (defined(GNU) || defined(INTEL)) && defined(I80386) && !defined(NO_ASM)
    printf("%s\n","#define SP()  ({var aint __SP; __asm__ __volatile__ (\"movl %%esp,%0\" : \"=g\" (__SP) : ); __SP; })");
  #endif
  #if !defined(STACK_register)
    printf("extern gcv_object_t* STACK;\n");
  #else
    printf("#ifndef IN_MODULE_CC\n");
    printf("register gcv_object_t* STACK __asm__(\"%s\");\n",STACK_register);
    printf("#endif\n");
  #endif
  #ifdef HAVE_SAVED_mv_count
    printf("extern uintC saved_mv_count;\n");
  #endif
  #ifdef HAVE_SAVED_value1
    printf("extern object saved_value1;\n");
  #endif
  #ifdef HAVE_SAVED_back_trace
    printf("extern p_backtrace_t saved_back_trace;\n");
  #endif
  #if defined(HAVE_SAVED_STACK)
    printf("extern gcv_object_t* saved_STACK;\n");
  #endif
  printf("#define begin_call()");
         #ifdef HAVE_SAVED_mv_count
           printf(" saved_mv_count = mv_count;");
         #endif
         #ifdef HAVE_SAVED_value1
           printf(" saved_value1 = value1;");
         #endif
         #ifdef HAVE_SAVED_back_trace
           printf(" saved_back_trace = back_trace;");
         #endif
         #ifdef HAVE_SAVED_STACK
           printf(" saved_STACK = STACK;");
         #endif
         printf("\n");
  printf("#define end_call()");
         #ifdef HAVE_SAVED_mv_count
           printf(" mv_count = saved_mv_count;");
         #endif
         #ifdef HAVE_SAVED_value1
           printf(" value1 = saved_value1;");
         #endif
         #ifdef HAVE_SAVED_back_trace
           printf(" back_trace = saved_back_trace;");
         #endif
         #ifdef HAVE_SAVED_STACK
           printf(" saved_STACK = (object*)NULL;");
         #endif
         printf("\n");
  printf("#define begin_callback()  ");
         #ifdef HAVE_SAVED_REGISTERS
           printf("{ struct registers * registers = alloca(sizeof(struct registers));");
           #ifdef STACK_register
             printf(" registers->STACK_register_contents = STACK_reg;");
           #endif
           #ifdef mv_count_register
             printf(" registers->mv_count_register_contents = mv_count_reg;");
           #endif
           #ifdef value1_register
             printf(" registers->value1_register_contents = value1_reg;");
           #endif
           #ifdef back_trace_register
             printf(" registers->back_trace_register_contents = back_trace_reg;");
           #endif
           #ifdef HAVE_SAVED_STACK
             printf(" STACK = saved_STACK;");
           #endif
           printf(" { var gcv_object_t* top_of_frame = STACK; pushSTACK(as_object((aint)callback_saved_registers)); finish_frame(CALLBACK); } callback_saved_registers = registers; } ");
         #endif
         printf("end_call()\n");
  printf("#define end_callback() ");
         #ifdef HAVE_SAVED_mv_count
           printf(" saved_mv_count = mv_count;");
         #endif
         #ifdef HAVE_SAVED_value1
           printf(" saved_value1 = value1;");
         #endif
         #ifdef HAVE_SAVED_back_trace
           printf(" saved_back_trace = back_trace;");
         #endif
         #ifdef HAVE_SAVED_REGISTERS
           printf(" { struct registers * registers = callback_saved_registers; if (!(framecode(STACK_(0)) == CALLBACK_frame_info)) abort(); callback_saved_registers = (struct registers *)(aint)as_oint(STACK_(1)); skipSTACK(2);");
           #ifdef HAVE_SAVED_STACK
             printf(" saved_STACK = STACK;");
           #endif
           #ifdef STACK_register
             printf(" STACK_reg = registers->STACK_register_contents;");
           #endif
           #ifdef mv_count_register
             printf(" mv_count_reg = registers->mv_count_register_contents;");
           #endif
           #ifdef value1_register
             printf(" value1_reg = registers->value1_register_contents;");
           #endif
           #ifdef back_trace_register
             printf(" back_trace_reg = registers->back_trace_register_contents;");
           #endif
           printf(" }");
         #endif
         printf("\n");
# #if defined(AMIGAOS) || defined(NO_ASYNC_INTERRUPTS)
#   printf("#define begin_system_call()\n");
#   printf("#define end_system_call()\n");
# #else
#   printf("#define begin_system_call()  begin_call()\n");
#   printf("#define end_system_call()  end_call()\n");
# #endif
# printf("#define check_STACK()  if (STACK_overflow()) STACK_ueber()\n");
# #ifdef STACK_DOWN
#   printf("#define STACK_overflow()  ( (aint)STACK < (aint)STACK_bound )\n");
#   printf("#define get_space_on_STACK(n)  if ( (aint)STACK < (aint)STACK_bound + (aint)(n) ) STACK_ueber()\n");
# #else
#   printf("#define STACK_overflow()  ( (aint)STACK > (aint)STACK_bound )\n");
#   printf("#define get_space_on_STACK(n)  if ( (aint)STACK + (aint)(n) > (aint)STACK_bound ) STACK_ueber()\n");
# #endif
# printf("extern void* STACK_bound;\n");
# printf("nonreturning_function(extern, STACK_ueber, (void));\n");
# printf("nonreturning_function(extern, fehler_notreached, (const char * file, uintL line));\n");
# #ifndef LANGUAGE_STATIC
#   #ifndef GNU_GETTEXT
#     printf("extern uintL language;\n");
#     printf1("#define ENGLISH  (language==%d)\n",language_english);
#   #else
#     printf("extern const char * clgettext (const char * msgid);\n");
#     printf("#define GETTEXT clgettext\n");
#   #endif
# #endif
# printf("extern object allocate_cons (void);\n");
# printf("extern object make_symbol (object string);\n");
# printf("extern object allocate_vector (uintL len);\n");
# printf("extern object allocate_bit_vector (uintB atype, uintL len);\n");
# #ifdef UNICODE
#   printf("extern object allocate_s32string (uintL len);\n");
#   printf("#define allocate_string(len)  allocate_s32string(len)\n");
# #else
#   printf("extern object allocate_s8string (uintL len);\n");
#   printf("#define allocate_string(len)  allocate_s8string(len)\n");
# #endif
# #ifdef asciz_length
#   #if defined(GNU) && (SAFETY < 2) && (__GNUC__ >= 2)
#     printf("#define asciz_length(a)  ((uintL)__builtin_strlen(a))\n");
#   #else
#     printf("#define asciz_length(a)  ((uintL)strlen(a))\n");
#   #endif
# #else
#   printf("extern uintL asciz_length (const char * asciz);\n");
# #endif
# #ifdef asciz_length
#   printf("#define asciz_equal(a1,a2)  (__builtin_strcmp(a1,a2)==0)\n");
# #else
#   printf("extern bool asciz_equal (const char * asciz1, const char * asciz2);\n");
# #endif
# printf("typedef Values subr_norest_function_t (void);\n");
# printf("typedef Values subr_rest_function_t (uintC argcount, object* rest_args_pointer);\n");
  printf("extern struct subr_tab_ {\n");
  #undef LISPFUN
  #define LISPFUN(name,req_anz,opt_anz,rest_flag,key_flag,key_anz,keywords)  \
    printf("  subr_t %s;\n",STRING(D_##name));
  #include "subr.c"
  #undef LISPFUN
  printf("} subr_tab_data;\n");
# #if !defined(MAP_MEMORY_TABLES)
#   printf("#define subr_tab  subr_tab_data\n");
#   #ifdef TYPECODES
#     printf1("#define subr_tab_ptr_as_object(subr_addr)  (type_constpointer_object(%d,subr_addr))\n",(tint)subr_type);
#   #else
#     printf1("#define subr_tab_ptr_as_object(subr_addr)  as_object((oint)(subr_addr)+%d)\n",subr_bias);
#   #endif
#   printf("#define L(name)  subr_tab_ptr_as_object(&subr_tab.D_##name)\n");
# #else
#   printf1("#define subr_tab_addr  ((struct subr_tab_ *)type_zero_oint(%d))\n",(tint)subr_type);
#   printf("#define subr_tab  (*subr_tab_addr)\n");
#   printf("#define subr_tab_ptr_as_object(subr_addr)  (as_object((oint)(subr_addr)))\n");
#   printf("#define L(name)  subr_tab_ptr_as_object(&subr_tab_addr->D_##name)\n");
# #endif
  printf("extern struct symbol_tab_ {\n");
  #define LISPSYM(name,printname,package)  \
    printf("  symbol_ %s;\n",STRING(S_##name));
  #include "constsym.c"
  #undef LISPSYM
  printf("} symbol_tab_data;\n");
  printf("#define S(name)  S_help_(S_##name)\n");
  #if !defined(MAP_MEMORY_TABLES)
    printf("#define symbol_tab  symbol_tab_data\n");
    #ifdef TYPECODES
      printf1("#define S_help_(name)  (type_constpointer_object(%d,&symbol_tab.name))\n",(tint)symbol_type);
    #else
      #if defined(OBJECT_STRUCT)
        printf1("#define S_help_(name)  as_object((oint)&symbol_tab.name+%d)\n",varobject_bias);
      #else
        printf1("#define S_help_(name)  objectplus(&symbol_tab.name,%d)\n",varobject_bias);
      #endif
    #endif
  #else
    printf1("#define symbol_tab_addr ((struct symbol_tab_ *)type_zero_oint(%d))\n",(tint)symbol_type);
#   printf("#define symbol_tab  (*symbol_tab_addr)\n");
    printf("#define S_help_(name)  (as_object((oint)(&symbol_tab_addr->name)))\n");
  #endif
  printf("#define NIL  S(nil)\n");
  printf("#define T    S(t)\n");
  printf("extern struct object_tab_ object_tab;\n");
  printf("extern uintC module_count;\n");
  printf("typedef struct { const char* packname; const char* symname; } subr_initdata_t;\n");
  printf("typedef struct { const char* initstring; } object_initdata_t;\n");
  printf("typedef struct module_t { const char* name; subr_t* stab; const uintC* stab_size; object* otab; const uintC* otab_size; bool initialized; const subr_initdata_t* stab_initdata; const object_initdata_t* otab_initdata; void (*initfunction1) (struct module_t *); void (*initfunction2) (struct module_t *);");
  #ifdef DYNAMIC_MODULES
    printf(" struct module_t * next;");
  #endif
  printf(" } module_t;\n");
  #ifdef DYNAMIC_MODULES
    printf("BEGIN_DECLS\n");
    printf("extern void add_module (module_t * new_module);\n");
    printf("END_DECLS\n");
  #else
    printf("extern module_t modules[];\n");
  #endif
  #ifdef STACK_DOWN
    printf("#define STACK_(n)  (STACK[(sintP)(n)])\n");
    printf("#define skipSTACKop  +=\n");
    printf("#define STACKop      +\n");
  #else
    printf("#define STACK_(n)  (STACK[-1-(sintP)(n)])\n");
    printf("#define skipSTACKop  -=\n");
    printf("#define STACKop      -\n");
  #endif
  #if defined(GNU) && defined(MC680X0) && !defined(NO_ASM) && !defined(WIDE) && defined(STACK_register)
    #ifdef STACK_DOWN
      printf("#define pushSTACK(obj)  ({ __asm__ __volatile__ (\"movel %%0,%s%s@-\" : : \"g\" ((object)(obj)) : \"%s\" ); })\n",REGISTER_PREFIX,STACK_register,STACK_register);
      printf("#define popSTACK()  ({var object __result; __asm__ __volatile__ (\"movel %s%s@+,%%0\" : \"=g\" (__result) : : \"%s\" ); __result; })\n",REGISTER_PREFIX,STACK_register,STACK_register);
    #else
      printf("#define pushSTACK(obj)  ({ __asm__ __volatile__ (\"movel %%0,%s%s@+\" : : \"g\" ((object)(obj)) : \"%s\" ); })\n",REGISTER_PREFIX,STACK_register,STACK_register);
      printf("#define popSTACK()  ({var object __result; __asm__ __volatile__ (\"movel %s%s@-,%%0\" : \"=g\" (__result) : : \"%s\" ); __result; })\n",REGISTER_PREFIX,STACK_register,STACK_register);
    #endif
  #else
    printf("#define pushSTACK(obj)  (STACK_(-1) = (obj), STACK skipSTACKop -1)\n");
    printf("#define popSTACK()  (STACK skipSTACKop 1, STACK_(-1))\n");
  #endif
  printf("#define skipSTACK(n)  (STACK skipSTACKop (sintP)(n))\n");
# {
#   var int i;
#   for (i=0; i<=10; i++) printf("#define STACK_%d  (STACK_(%d))\n",i,i);
# }
# printf("#define mv_limit %d\n",mv_limit);
  #if !defined(mv_count_register)
    printf("extern uintC mv_count;\n");
  #else
    printf("#ifndef IN_MODULE_CC\n");
    printf("register uintC mv_count __asm__(\"%s\");\n",mv_count_register);
    printf("#endif\n");
  #endif
  printf("extern object mv_space [%d];\n",mv_limit-1);
  #if !defined(value1_register)
    printf("#define value1  mv_space[0]\n");
  #else
    printf("#ifndef IN_MODULE_CC\n");
    printf("register object value1 __asm__(\"%s\");\n",value1_register);
    printf("#endif\n");
  #endif
# printf("#define value2  mv_space[1]\n");
# printf("#define value3  mv_space[2]\n");
# printf("nonreturning_function(extern, fehler_mv_zuviel, (object caller));\n");
    printf("struct backtrace_t {\n  struct backtrace_t* bt_next;\n  gcv_object_t bt_caller;\n  gcv_object_t *bt_stack;\n  int bt_num_arg;\n};\n");
    printf("typedef struct backtrace_t * p_backtrace_t;\n");
    printf("#define subr_self  back_trace->bt_caller\n");
  #if !defined(back_trace_register)
    printf("extern p_backtrace_t back_trace;\n");
  #else
    printf("#ifndef IN_MODULE_CC\n");
    printf("register p_backtrace_t back_trace __asm__(\"%s\");\n",back_trace_register);
    printf("#endif\n");
  #endif
# printf("#define args_end_pointer  STACK\n");
# printf("#define set_args_end_pointer(new_args_end_pointer)  STACK = (new_args_end_pointer)\n");
# #ifdef STACK_DOWN
#   printf("#define NEXT(argpointer)  (*(--(argpointer)))\n");
#   printf("#define BEFORE(argpointer)  (*((argpointer)++))\n");
# #else
#   printf("#define NEXT(argpointer)  (*((argpointer)++))\n");
#   printf("#define BEFORE(argpointer)  (*(--(argpointer)))\n");
# #endif
# printf("#define Next(pointer)  (*(STACKpointable(pointer) STACKop -1))\n");
# printf("#define Before(pointer)  (*(STACKpointable(pointer) STACKop 0))\n");
  #ifdef HAVE_SAVED_REGISTERS
    printf1("#define CALLBACK_frame_info  %d\n",CALLBACK_frame_info);
  #endif
  #ifdef TYPECODES
    printf("#define framecode(bottomword)  mtypecode(bottomword)\n");
  #else
    printf1("#define framecode(bottomword)  (as_oint(bottomword) & minus_wbit(%d))\n",FB1);
  #endif
  #ifdef TYPECODES
    #if !defined(SINGLEMAP_MEMORY_STACK)
      printf("#define framebottomword(type,top_of_frame,bot_of_frame)  type_pointer_object(type,top_of_frame)\n");
    #else
      printf1("#define framebottomword(type,top_of_frame,bot_of_frame)  as_object(type_zero_oint(type)-type_zero_oint(%d)+(oint)(top_of_frame))\n",(tint)system_type);
    #endif
    printf("#define finish_frame(frametype)  pushSTACK(framebottomword(frametype##_frame_info,top_of_frame,bot_of_frame_ignored))\n");
  #else
    #ifdef STACK_UP
      printf("#define framebottomword(type,top_of_frame,bot_of_frame)  as_object((oint)(type)+(oint)((uintP)(bot_of_frame)-(uintP)(top_of_frame)))\n");
    #endif
    #ifdef STACK_DOWN
      printf("#define framebottomword(type,top_of_frame,bot_of_frame)  as_object((oint)(type)+(oint)((uintP)(top_of_frame)-(uintP)(bot_of_frame)))\n");
    #endif
    printf("#define finish_frame(frametype)  (STACK_(-1) = framebottomword(frametype##_frame_info,top_of_frame,STACK STACKop -1), skipSTACK(-1))\n");
  #endif
# printf("extern Values apply (object fun, uintC args_on_stack, object other_args);\n");
  printf("extern Values funcall (object fun, uintC argcount);\n");
# printf("extern Values eval (object form);\n");
  printf("#define LISPFUNN(name,req_anz)  LISPFUN(name,req_anz,0,norest,nokey,0,NIL)\n");
  printf("#define LISPFUN_B(name,req_anz,opt_anz,rest_flag,key_flag,key_anz,keywords)  global Values C_##name subr_##rest_flag##_function_args\n");
  printf("#define subr_norest_function_args  (void)\n");
  printf("#define subr_rest_function_args  (uintC argcount, object* rest_args_pointer)\n");
  printf("#define LISPFUN_F(name,req_anz,opt_anz,rest_flag,key_flag,key_anz,keywords)  { (lisp_function_t)(&C_##name), nullobj, nullobj, 0, req_anz, opt_anz, (uintB)subr_##rest_flag, (uintB)subr_##key_flag, key_anz, },\n");
  printf("#define LISPFUN  LISPFUN_B\n");
# #ifdef UNICODE
#   printf("extern object n_char_to_string (const char* charptr, uintL len, object encoding);\n");
# #else
#   printf("#define n_char_to_string(charptr,len,encoding)  n_char_to_string_(charptr,len)\n");
#   printf("extern object n_char_to_string_ (const char* charptr, uintL len);\n");
# #endif
# #ifdef UNICODE
#   printf("extern object asciz_to_string (const char * asciz, object encoding);\n");
# #else
#   printf("#define asciz_to_string(asciz,encoding)  asciz_to_string_(asciz)\n");
#   printf("extern object asciz_to_string_ (const char * asciz);\n");
# #endif
  printf("extern object ascii_to_string (const char * asciz);\n");
# #ifdef UNICODE
#   printf("extern object string_to_asciz (object obj, object encoding);\n");
# #else
#   printf("#define string_to_asciz(obj,encoding)  string_to_asciz_(obj)\n");
#   printf("extern object string_to_asciz_ (object obj);\n");
# #endif
# printf("#define TheAsciz(obj)  ((char*)(&TheSbvector(obj)->data[0]))\n");
# printf("extern object vectorof (uintC len);\n");
# printf("extern object allocate_bit_vector_0 (uintL len);\n");
# printf("extern chart up_case (chart ch);\n");
# printf("extern chart down_case (chart ch);\n");
# printf("extern chart* unpack_string (object string, uintL* len);\n");
# printf("extern object make_list (uintL len);\n");
# printf("extern object listof (uintC len);\n");
# printf("typedef enum { condition, serious_condition, error, program_error, source_program_error, control_error, arithmetic_error, division_by_zero, floating_point_overflow, floating_point_underflow, cell_error, unbound_variable, undefined_function, unbound_slot, type_error, keyword_error, charset_type_error, package_error, print_not_readable, parse_error, stream_error, end_of_file, reader_error, file_error, storage_condition, interrupt_condition, warning, } condition_t;\n");
# printf("nonreturning_function(extern, fehler, (condition_t errortype, const char * errorstring));\n");
# printf("nonreturning_function(extern, fehler_list, (object obj));\n");
# printf("nonreturning_function(extern, fehler_symbol, (object obj));\n");
# printf("nonreturning_function(extern, fehler_kein_svector, (object caller, object obj));\n");
# printf("nonreturning_function(extern, fehler_vector, (object obj));\n");
# printf("nonreturning_function(extern, fehler_char, (object obj));\n");
# printf("nonreturning_function(extern, fehler_string, (object obj));\n");
# printf("nonreturning_function(extern, fehler_sstring, (object obj));\n");
  printf("#define check_char(obj)  if (!charp(obj)) { fehler_char(obj); }\n");
  printf("#define check_uint8(obj)  if (!uint8_p(obj)) { fehler_uint8(obj); }\n");
  printf("#define check_sint8(obj)  if (!sint8_p(obj)) { fehler_sint8(obj); }\n");
  printf("#define check_uint16(obj)  if (!uint16_p(obj)) { fehler_uint16(obj); }\n");
  printf("#define check_sint16(obj)  if (!sint16_p(obj)) { fehler_sint16(obj); }\n");
  printf("#define check_uint32(obj)  if (!uint32_p(obj)) { fehler_uint32(obj); }\n");
  printf("#define check_sint32(obj)  if (!sint32_p(obj)) { fehler_sint32(obj); }\n");
  printf("#define check_uint64(obj)  if (!uint64_p(obj)) { fehler_uint64(obj); }\n");
  printf("#define check_sint64(obj)  if (!sint64_p(obj)) { fehler_sint64(obj); }\n");
  printf("#define check_uint(obj)  if (!uint_p(obj)) { fehler_uint(obj); }\n");
  printf("#define check_sint(obj)  if (!sint_p(obj)) { fehler_sint(obj); }\n");
  printf("#define check_ulong(obj)  if (!ulong_p(obj)) { fehler_ulong(obj); }\n");
  printf("#define check_slong(obj)  if (!slong_p(obj)) { fehler_slong(obj); }\n");
  printf("#define check_ffloat(obj)  if (!single_float_p(obj)) { fehler_ffloat(obj); }\n");
  printf("#define check_dfloat(obj)  if (!double_float_p(obj)) { fehler_dfloat(obj); }\n");
  printf("nonreturning_function(extern, fehler_uint8, (object obj));\n");
  printf("nonreturning_function(extern, fehler_sint8, (object obj));\n");
  printf("nonreturning_function(extern, fehler_uint16, (object obj));\n");
  printf("nonreturning_function(extern, fehler_sint16, (object obj));\n");
  printf("nonreturning_function(extern, fehler_uint32, (object obj));\n");
  printf("nonreturning_function(extern, fehler_sint32, (object obj));\n");
  printf("nonreturning_function(extern, fehler_uint64, (object obj));\n");
  printf("nonreturning_function(extern, fehler_sint64, (object obj));\n");
  printf("nonreturning_function(extern, fehler_uint, (object obj));\n");
  printf("nonreturning_function(extern, fehler_sint, (object obj));\n");
  printf("nonreturning_function(extern, fehler_ulong, (object obj));\n");
  printf("nonreturning_function(extern, fehler_slong, (object obj));\n");
  printf("nonreturning_function(extern, fehler_sfloat, (object obj));\n");
  printf("nonreturning_function(extern, fehler_dfloat, (object obj));\n");
# printf("extern object find_package (object string);\n");
# printf("extern uintBWL intern (object string, object pack, object* sym_);\n");
# printf("extern object intern_keyword (object string);\n");
# printf("extern bool eql (object obj1, object obj2);\n");
# printf("extern bool equal (object obj1, object obj2);\n");
# printf("extern bool equalp (object obj1, object obj2);\n");
# printf("extern object get (object symbol, object key);\n");
  printf("extern object L_to_I (sint32 wert);\n");
  #if (intLsize<=oint_data_len)
    printf("#define UL_to_I(wert)  fixnum((uintL)(wert))\n");
  #else
    printf("extern object UL_to_I (uintL wert);\n");
  #endif
  printf("extern object L2_to_I (sint32 wert_hi, uint32 wert_lo);\n");
  printf("extern object UL2_to_I (uint32 wert_hi, uint32 wert_lo);\n");
  #ifdef intQsize
    printf("extern object Q_to_I (sint64 wert);\n");
    printf("extern object UQ_to_I (uint64 wert);\n");
  #endif
  printf("#define uint8_to_I(val)  fixnum((uint8)(val))\n");
  printf("#define sint8_to_I(val)  L_to_I((sint32)(sint8)(val))\n");
  printf("#define uint16_to_I(val)  fixnum((uint16)(val))\n");
  printf("#define sint16_to_I(val)  L_to_I((sint32)(sint16)(val))\n");
  printf("#define uint32_to_I(val)  UL_to_I((uint32)(val))\n");
  printf("#define sint32_to_I(val)  L_to_I((sint32)(val))\n");
  #ifdef intQsize
    printf("#define uint64_to_I(val)  UQ_to_I((uint64)(val))\n");
    printf("#define sint64_to_I(val)  Q_to_I((sint64)(val))\n");
  #else
    printf("#define uint64_to_I(val)  UL2_to_I((uint32)((val)>>32),(uint32)(val))\n");
    printf("#define sint64_to_I(val)  L2_to_I((sint32)((val)>>32),(uint32)(val))\n");
  #endif
  #if (int_bitsize==16)
    printf("#define uint_to_I(val)  uint16_to_I(val)\n");
    printf("#define sint_to_I(val)  sint16_to_I(val)\n");
  #else # (int_bitsize==32)
    printf("#define uint_to_I(val)  uint32_to_I(val)\n");
    printf("#define sint_to_I(val)  sint32_to_I(val)\n");
  #endif
  #if (long_bitsize==32)
    printf("#define ulong_to_I(val)  uint32_to_I(val)\n");
    printf("#define slong_to_I(val)  sint32_to_I(val)\n");
  #else # (long_bitsize==64)
    printf("#define ulong_to_I(val)  uint64_to_I(val)\n");
    printf("#define slong_to_I(val)  sint64_to_I(val)\n");
  #endif
  printf("extern uintL I_to_UL (object obj);\n");
  printf("extern sintL I_to_L (object obj);\n");
  #ifdef HAVE_LONGLONG
    printf("extern uint64 I_to_UQ (object obj);\n");
    printf("extern sint64 I_to_Q (object obj);\n");
  #endif
  printf("#define I_to_uint8(obj)  (uint8)(as_oint(obj) >> %d)\n",oint_data_shift);
  printf("#define I_to_sint8(obj)  (sint8)(as_oint(obj) >> %d)\n",oint_data_shift);
  printf("#define I_to_uint16(obj)  (uint16)(as_oint(obj) >> %d)\n",oint_data_shift);
  printf("#define I_to_sint16(obj)  (sint16)(as_oint(obj) >> %d)\n",oint_data_shift);
  #if (oint_data_len>=32)
    printf("#define I_to_uint32(obj)  (uint32)(as_oint(obj) >> %d)\n",oint_data_shift);
  #else
    printf("#define I_to_uint32(obj)  I_to_UL(obj)\n");
  #endif
  #if (oint_data_len>=31)
    printf("#define I_to_sint32(obj)  (sint32)(as_oint(obj) >> %d)\n",oint_data_shift);
  #else
    printf("#define I_to_sint32(obj)  I_to_L(obj)\n");
  #endif
  printf("#define I_to_uint64(obj)  I_to_UQ(obj)\n");
  printf("#define I_to_sint64(obj)  I_to_Q(obj)\n");
  #if (int_bitsize==16)
    printf("#define I_to_uint  I_to_uint16\n");
    printf("#define I_to_sint  I_to_sint16\n");
  #else # (int_bitsize==32)
    printf("#define I_to_uint  I_to_uint32\n");
    printf("#define I_to_sint  I_to_sint32\n");
  #endif
  #if (long_bitsize==32)
    printf("#define I_to_ulong  I_to_uint32\n");
    printf("#define I_to_slong  I_to_sint32\n");
  #else # (long_bitsize==64)
    printf("#define I_to_ulong  I_to_uint64\n");
    printf("#define I_to_slong  I_to_sint64\n");
  #endif
# printf("extern object I_1_plus_I (object x);\n");
# printf("extern object I_minus1_plus_I (object x);\n");
# printf("extern object I_I_plus_I (object x, object y);\n");
# printf("extern object I_I_minus_I (object x, object y);\n");
  printf("extern object c_float_to_FF (const ffloatjanus* val_);\n");
  printf("extern void FF_to_c_float (object obj, ffloatjanus* val_);\n");
  printf("extern object c_double_to_DF (const dfloatjanus* val_);\n");
  printf("extern void DF_to_c_double (object obj, dfloatjanus* val_);\n");
  #ifdef DYNAMIC_FFI
    printf("extern void register_foreign_variable (void* address, const char * name, uintBWL flags, uintL size);\n");
    printf("extern void register_foreign_function (void* address, const char * name, uintWL flags);\n");
    printf("extern object convert_from_foreign (object fvd, const void* data);\n");
    printf("extern void convert_to_foreign_mallocing (object fvd, object obj, void* data);\n");
    printf("extern void convert_to_foreign_nomalloc (object fvd, object obj, void* data);\n");
  #endif
# Additional stuff for modules.
  printf("#define DEFMODULE(module_name,package_name)\n");
  printf("#define DEFUN(funname,lambdalist,signature) LISPFUN signature\n");
  printf("#define DEFVAR(varname)\n");
  if (ferror(stdout)) { exit(1); }
  exit(0);
}
