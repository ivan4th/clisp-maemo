# Deklarationen zur Arithmetik

# Typenhierarchie:
# Number (N) =
#    Real (R) =
#       Float (F) =
#          Short float (SF)
#          Single float (FF)
#          Double float (DF)
#          Long float (LF)
#       Rational (RA) =
#          Integer (I) =
#             Fixnum (FN)
#             Bignum (BN)
#          Ratio (RT)
#    Complex (C)

# Anmerkungen:
# - Complex d�rfen aus zwei Real-Komponenten bestehen, die von verschiedenem
#   Typ sind. Falls der Imagin�rteil EQ zu 0 ist, wird ein Real draus gemacht.
#   (Vgl. CLTL S. 195)
#   Vorteil: Dann liefert (let ((x (sqrt -9.0))) (* x x))
#     (statt x = #C(0.0 3.0)  -> Wert #C(-9.0 0.0) )
#     x = #C(0 3.0)  -> Wert #C(-9.0 0) = -9.0
# - Coercionen bei Operationen, wo verschiedene Typen auftreten:
#     Rational -> Long-float -> Double-float -> Single-float -> Short-float
#     (abweichend von CLTL S. 195)
#     Grund: mathematisch gesehen, ist
#            (1.0 +- 1e-8) + (1.0 +- 1e-16) = (2.0 +- 1e-8),
#            also ist (+ 1.0s0 1.0d0) ==> 2.0s0 gerechtfertigt.
#     Kurz: Nicht vorhandene Genauigkeit (accuracy) soll nicht (durch precision)
#           vorget�uscht werden.
# - Bei Single und Double Float halte ich mich an den IEEE-Standard (1981),
#     allerdings ohne solche Features wie +0,-0, +inf,-inf, gradual underflow,
#     NAN, ...,  da COMMON LISP f�r sie sowieso keine Verwendung hat.
# - Die Genauigkeit der Long Floats wird durch die Place (LONG-FLOAT-DIGITS)
#   gegeben.


# Datenstrukturen:

# Fixnum (FN) : 1 Langwort, direkt:
#             Bits 30..24: Typinfo und Vorzeichen.
#             Bits 23..0: Wert (mit dem Vorzeichen zusammen eine
#                               Zweierkomplementdarstellung)
# Maske f�r den Wert:
  #define FN_value_mask  ((oint)wbitm(oint_data_len+oint_data_shift)-(oint)wbit(oint_data_shift))
# Maske f�r Wert und Vorzeichen:
  #define FN_value_vz_mask  (FN_value_mask|wbit(sign_bit_o))
# Typinfo f�r FN >=0:  fixnum_type
# Typinfo f�r FN <0:
  #define fixnum_vz_type  (fixnum_type|bit(sign_bit_t))
# (defconstant most-positive-fixnum (- (expt 2 oint_data_len) 1))
# (defconstant most-negative-fixnum (- (expt 2 oint_data_len)))
# Fixnum Null:
# #define Fixnum_0  fixnum(0)
# Fixnum Eins:
# #define Fixnum_1  fixnum(1)
# Fixnum Minus eins:
# #define Fixnum_minus1  type_data_object(fixnum_vz_type,FN_value_mask>>oint_data_shift)
# most-positive-fixnum:
  #define Fixnum_mpos  type_data_object(fixnum_type,FN_value_mask>>oint_data_shift)
# most-negative-fixnum:
  #define Fixnum_mneg  type_data_object(fixnum_vz_type,0)
# maximal n�tige L�nge einer Digit sequence zu einem Fixnum:
  #define FN_maxlength  ceiling(oint_data_len+1,intDsize)
# maximal n�tige L�nge (ohne Vorzeichen) einer Digit sequence zu einem Fixnum:
  #define pFN_maxlength  ceiling(oint_data_len,intDsize)
# Es gilt pFN_maxlength <= FN_maxlength <= bn_minlength.

# Langwort (L) - nur intern verwendet -
# ein Langwort als signed integer, in Zweierkomplementdarstellung (sint32).

# Bignum (BN) : 1 Langwort, indirekt:
#             Bits 30..24: Typinfo und Vorzeichen
#             Bits 23..0: Pointer X
#             X^.length = L�nge n (uintC), >= bn_minlength
#             X^.data = n Digits (als normalisierte Digit sequence)
  #define bn_minlength  ceiling(oint_data_len+2,intDsize)
  # denn Bignums mit n < ceiling((oint_data_len+2)/intDsize) Digits
  # sind Integers mit h�chstens intDsize*n < oint_data_len+2 Bits, also
  # Integers mit h�chstens oint_data_len+1 Bits (incl. Vorzeichen),
  # und die passen in Fixnums. 1 <= bn_minlength <= 5.

# Ratio (RT) = faktisch ein record aus zwei Komponenten:
#              NUM = Z�hler (Integer), DEN = Nenner (Integer > 0)
#              mit teilerfremdem Z�hler und Nenner.
# (ausf�hrlich: Bits 30..24 = Typinfo und Vorzeichen
#               Bits 23..0 = Pointer X
#               X^.rt_num = NUM, X^.rt_den = DEN. )

# Rational (RA) = Integer oder Ratio.

# Bei allen Floating points:
# Vorzeichen s, Exponent e, Mantisse mk-1,...,m0
# bedeutet die Zahl (-1)^s * 2^(e-_EXP_MID) * [0 . 1 mk-1 ... m0]
# e=0 bedeutet die Zahl 0, stets mit Vorzeichen s=0 (und Mantisse =0).
# _exp_low und _exp_high sind Schranken (inklusive) f�r e.
# Bitzahlen f�r   Vorzeichen s    Exponent e    Mantisse m (= k)
# SF                   1              8             16
# FF                   1              8             23
# DF                   1              11            52
# LF                   1              32            uintDsize*n >= 53

# Short float (SF)  : 1 Langwort, direkt:
#             Bits 30..24: Typinfo und Vorzeichen s.
#             Bits 23..16: Exponent e (8 Bits)
#             Bits 15..0: Mantisse m (16 Bits)
#             Die Zahl 0.0 wird durch s=0, e=0, m=0 repr�sentiert.
  #define SF_exp_len    8  # Anzahl der Bits des Exponenten
  #define SF_mant_len  16  # Anzahl der Bits der Mantisse
  #define SF_exp_low   1                    # minimaler Exponent
  #define SF_exp_mid   bit(SF_exp_len-1)    # "Nullstellung" des Exponenten
  #define SF_exp_high  (bit(SF_exp_len)-1)  # maximaler Exponent
  #define SF_exp_shift  (SF_mant_len+SF_mant_shift) # unterstes Bit des Exponenten im oint
  #define SF_mant_shift  oint_data_shift            # unterstes Bit der Mantisse im oint
# Typinfo-Byte f�r SF >=0 :
  #define SF_type     sfloat_type
# Typinfo-Byte f�r SF <0, mit gesetztem Vorzeichen-Bit:
  #define SF_vz_type  (sfloat_type|bit(sign_bit_t))
# Baut ein Float aus Vorzeichen (0 oder -1), Exponent und Mantisse zusammen:
  #define make_SF(sign,exp,mant)  \
    type_data_object(SF_type | (bit(sign_bit_t) & (sign)), \
      (((exp) & (bit(SF_exp_len)-1)) << SF_mant_len) | ((mant) & (bit(SF_mant_len)-1)) \
      )
# Short Float 0.0 :
  #define SF_0  make_SF(0,0,0)
# Short Float 1.0 :
  #define SF_1  make_SF(0,SF_exp_mid+1,bit(SF_mant_len))
# Short Float -1.0 :
  #define SF_minus1  make_SF(-1,SF_exp_mid+1,bit(SF_mant_len))

# Single float (FF) : 1 Langwort, indirekt:
#             Bits 30..24: Typinfo und Vorzeichen
#             Bits 23..0: Pointer X
#             X^.float_value = 1 Langwort:
#                  Bit 31 = s, Bits 30..23 = e, Bits 22..0 = m.
#             Die Zahl 0.0 wird durch s=0, e=0, m=0 repr�sentiert.
  #define FF_exp_len    8  # Anzahl der Bits des Exponenten
  #define FF_mant_len  23  # Anzahl der Bits der Mantisse
  #ifdef FAST_FLOAT # M�ssen wir uns die Parameter vom Standard diktieren lassen?
    #define FF_exp_low  1
    #define FF_exp_mid  126  # Warum das die "Mitte" sein soll, ist mir unklar...
    #define FF_exp_high 254  # Exponent 255 wird als NaN/Inf interpretiert!
  #else # Ich w�hle die Parameter liefer sch�n symmetrisch
    #define FF_exp_low  1
    #define FF_exp_mid  128
    #define FF_exp_high 255
  #endif
#ifdef TYPECODES
  # Typinfo-Byte f�r FF >=0 :
    #define FF_type     ffloat_type
  # Typinfo-Byte f�r FF <0, mit gesetztem Vorzeichen-Bit:
    #define FF_vz_type  (ffloat_type|bit(vorz_bit_t))
#endif
#ifdef WIDE
# Baut ein Float aus Vorzeichen (0 oder -1), Exponent und Mantisse zusammen:
  #define make_FF(sign,exp,mant)  \
    type_data_object(FF_type | (bit(vorz_bit_t) & (sign)), \
      (sign) << (FF_exp_len+FF_mant_len)                   \
      | (((exp) & (bit(FF_exp_len)-1)) << FF_mant_len)     \
      | ((mant) & (bit(FF_mant_len)-1))                    \
      )
# Single Float 0.0 :
  #define FF_0  make_FF(0,0,0)
# Single Float 1.0 :
  #define FF_1  make_FF(0,FF_exp_mid+1,bit(FF_mant_len))
# Single Float -1.0 :
  #define FF_minus1  make_FF(-1,FF_exp_mid+1,bit(FF_mant_len))
#else
# Single Float 0.0 :
  #define FF_0  O(FF_zero)
# Single Float 1.0 :
  #define FF_1  O(FF_one)
# Single Float -1.0 :
  #define FF_minus1  O(FF_minusone)
#endif

# Double float (DF) : 1 Langwort, indirekt:
#             Bits 30..24: Typinfo und Vorzeichen
#             Bits 23..0: Pointer X
#             X^.float_value = 2 Langworte:
#                  Bit 63 = s, Bits 62..52 = e, Bits 51..0 = m.
#             Die Zahl 0.0 wird durch s=0, e=0, m=0 repr�sentiert.
  #define DF_exp_len   11  # Anzahl der Bits des Exponenten
  #define DF_mant_len  52  # Anzahl der Bits der Mantisse
  #ifdef FAST_DOUBLE # M�ssen wir uns die Parameter vom Standard diktieren lassen?
    #define DF_exp_low  1
    #define DF_exp_mid  1022 # Warum das die "Mitte" sein soll, ist mir unklar...
    #define DF_exp_high 2046 # Exponent 2047 wird als NaN/Inf interpretiert!
  #else # Ich w�hle die Parameter liefer sch�n symmetrisch
    #define DF_exp_low  1
    #define DF_exp_mid  1024
    #define DF_exp_high 2047
  #endif
#ifdef TYPECODES
  # Typinfo-Byte f�r DF >=0 :
    #define DF_type     dfloat_type
  # Typinfo-Byte f�r DF <0, mit gesetztem Vorzeichen-Bit:
    #define DF_vz_type  (dfloat_type|bit(vorz_bit_t))
#endif
# Double Float 0.0 :
  #define DF_0  O(DF_zero)
# Double Float 1.0 :
  #define DF_1  O(DF_one)
# Double Float -1.0 :
  #define DF_minus1  O(DF_minusone)

# Long float (LF) : 1 Langwort, indirekt:
#             Bits 30..24: Typinfo und Vorzeichen
#             Bits 23..0: Pointer X
#             X^.len = n = Anzahl der dahinter kommenden Mantissenworte, n>=ceiling(53/intDsize)
#             X^.expo = e (32 Bits)
#             X^.data[0] ... X^.data[n-1] = intDsize*n Mantissenbits (MSD ... LSD)
#             Die Zahl 0.0 wird durch e=0, Mantisse=0 repr�sentiert.
#             Bei e /= 0 ist das h�chstwertige Bit =1.
#             n>=ceiling(53/intDsize), damit ein LF nicht weniger Mantissenbits hat als ein DF.
  #define LF_minlen  ceiling(53,intDsize)
  #define LF_exp_low  1
  #define LF_exp_mid  0x80000000UL
  #define LF_exp_high 0xFFFFFFFFUL
#ifdef TYPECODES
  # Typinfo-Byte f�r LF >=0 :
    #define LF_type     lfloat_type
  # Typinfo-Byte f�r LF <0, mit gesetztem Vorzeichen-Bit:
    #define LF_vz_type  (lfloat_type|bit(vorz_bit_t))
#endif

# Byte (BYTE) : Record mit den Komponenten size und position:
#             1 Langwort, indirekt:
#             Bits 30..24: Typinfo
#             Bits 23..0: Pointer X
#             X^.byte_size = size, ein Fixnum >=0.
#             X^.byte_position = position, ein Fixnum >=0.
# Typtest mit bytep und if_bytep, Konstruktion mit allocate_byte().


# NUM_STACK ist eine Art Zahlen-Stack-Pointer.
# Verwendung:
#   {SAVE_NUM_STACK
#    ...
#    num_stack_need(...);
#    ...
#    num_stack_need(...);
#    RESTORE_NUM_STACK
#    ...
#   }
# SAVE_NUM_STACK rettet den aktuellen Wert von NUM_STACK.
# Dann darf beliebig oft mit num_stack_need Platz auf dem Zahlen-Stack
# belegt werden.
# Mit RESTORE_NUM_STACK wird NUM_STACK wieder auf den vorigen Wert gesetzt.
# Auf dem belegten Platz darf noch bis zum Ende der aktuellen C-Funktion
# gearbeitet werden (allerdings ohne eine andere C-Funktion aufzurufen, die
# selbst wieder Platz auf dem Zahlen-Stack belegt). Mit Beendigung der
# aktuellen C-Funktion gilt der Platz als wieder freigegeben.
# In jeder C-Funktion sollte SAVE_NUM_STACK/RESTORE_NUM_STACK nur einmal
# aufgerufen werden.

# num_stack_need(need, low_addr = , high_addr = );
# belegt need Digits auf dem Zahlen-Stack und legt die untere Grenze des
# allozierten Bereichs (den MSDptr) in low_addr und die obere Grenze (den
# LSDptr) in high_addr ab. Jedes von beiden ist optional.

# num_stack_need_1(need, low_addr = , high_addr = );
# wie num_stack_need, nur da� unterhalb von low_addr noch ein Digit Platz
# zus�tzlich belegt wird.

# Deklarationen f�r SPVW:
#if !((defined(GNU) && !defined(RISCOS) && !defined(CONVEX)) || (defined(UNIX) && !defined(NO_ALLOCA) && !defined(SPARC)) || defined(WATCOM) || defined(BORLAND) || defined(MICROSOFT)) # siehe unten
  #define HAVE_NUM_STACK
  extern uintD*  NUM_STACK;
  extern uintD*  NUM_STACK_bound;
  extern uintD*  NUM_STACK_normal;
  #define NUM_STACK_DOWN  # NUM_STACK w�chst abw�rts
#endif

#ifdef LISPARIT

#if defined(GNU) && !defined(RISCOS) && !defined(CONVEX)
  #if 0
    # verkraftet dynamisch allozierte Arrays im Maschinenstack
    #define SAVE_NUM_STACK
    #define RESTORE_NUM_STACK  ;
    #define num_stack_need(need,low_zuweisung,high_zuweisung)  \
      {var uintL __need = (uintL)(need);                           \
       var uintD __array [__need];                                 \
       check_SP_notUNIX();                                         \
       low_zuweisung &__array[0]; high_zuweisung &__array[__need]; \
      }
    #define num_stack_need_1(need,low_zuweisung,high_zuweisung)  \
      {var uintL __need = (uintL)(need)+1;                         \
       var uintD __array [__need];                                 \
       check_SP_notUNIX();                                         \
       low_zuweisung &__array[1]; high_zuweisung &__array[__need]; \
      }
    # Funktioniert aber nicht, da der bereitgestellte Speicherplatz
    # sofort wieder freigegeben wird!
  #else
    # Fast identisch, nur da� der belegte Platz erst bei Beendigung
    # der C-Funktion freigegeben wird:
    #define SAVE_NUM_STACK
    #define RESTORE_NUM_STACK  ;
    #define num_stack_need(need,low_zuweisung,high_zuweisung)  \
      {var uintL __need = (uintL)(need);                                             \
       var uintD* __array = (uintD*)__builtin_alloca(__need*sizeof(uintD));          \
       check_SP_notUNIX();                                                           \
       unused (low_zuweisung &__array[0]); unused (high_zuweisung &__array[__need]); \
      }
    #define num_stack_need_1(need,low_zuweisung,high_zuweisung)  \
      {var uintL __need = (uintL)(need)+1;                                           \
       var uintD* __array = (uintD*)__builtin_alloca(__need*sizeof(uintD));          \
       check_SP_notUNIX();                                                           \
       unused (low_zuweisung &__array[1]); unused (high_zuweisung &__array[__need]); \
      }
  #endif
#elif (defined(UNIX) && !defined(NO_ALLOCA) && !defined(SPARC)) || defined(WATCOM) || defined(BORLAND) || defined(MICROSOFT)
  # Platz im Maschinenstack reservieren.
  #define SAVE_NUM_STACK
  #define RESTORE_NUM_STACK  ;
  #define num_stack_need(need,low_zuweisung,high_zuweisung)  \
    {var uintL __need = (uintL)(need);                           \
     var uintD* __array = (uintD*)alloca(__need*sizeof(uintD));  \
     low_zuweisung &__array[0]; high_zuweisung &__array[__need]; \
    }
  #define num_stack_need_1(need,low_zuweisung,high_zuweisung)  \
    {var uintL __need = (uintL)(need)+1;                         \
     var uintD* __array = (uintD*)alloca(__need*sizeof(uintD));  \
     low_zuweisung &__array[1]; high_zuweisung &__array[__need]; \
    }
#else
  # Verwende eine globale Variable als Zahlen-Stack-Pointer.
  global uintD*  NUM_STACK;
  global uintD*  NUM_STACK_bound;
  # Dieser Zahlen-Stack-Pointer wird nur von den arithmetischen Funktionen
  # benutzt und hat nach Beendigung einer solchen Funktion wieder denselben
  # Wert wie bei Eintritt in diese Funktion.
  # Arithmetische Funktionen k�nnen aber (z.B. durch die Tastaturabfrage
  # bei der Garbage-Collection) rekursiv einen Driver und damit weitere
  # arithmetische Funktionen aufrufen.
  # Zur�cksetzen von NUM_STACK bei Fehlerbehandlung: Beim nichtfortsetzenden
  # Verlassen eines Drivers (und auch bei der Aufl�sung eines Driver-Frames)
  # erh�lt NUM_STACK den Wert, den es im vorigen Driver hatte. Beim
  # fortsetzenden Verlassen eines Drivers dagegen bleibt NUM_STACK unver-
  # �ndert auf dem Wert, den es bei Eintritt in diesen Driver hatte.
  # (Dies funktioniert, da die Arithmetik-Funktionen keine Frames aufmachen,
  # an die man unwinden k�nnte.)
  global uintD*  NUM_STACK_normal;  # Wert von NUM_STACK im letzten Driver
  #
  #define SAVE_NUM_STACK  var uintD* old_num_stack = NUM_STACK;
  #define RESTORE_NUM_STACK  NUM_STACK = old_num_stack;
  #
  # Fehlermeldung, wenn zuwenig Platz f�r num_stack:
    nonreturning_function(local, arith_ueberlauf, (void));
    local void arith_ueberlauf()
      { fehler(storage_condition,
               DEUTSCH ? "Stack�berlauf beim Hantieren mit langen Zahlen" :
               ENGLISH ? "stack overflow during bignum arithmetic" :
               FRANCAIS ? "D�bordement de pile lors d'op�rations avec de longs nombres" :
               ""
              );
      }
  #
  # Error liefern, wenn eine Adresse NUM_STACK_bound unterschritten hat:
  # compare_NUM_STACK_bound(addr);
    #if 1
      #ifdef NUM_STACK_DOWN
        #define compare_NUM_STACK_bound(addr)  \
          ( (aint)(addr) < (aint)NUM_STACK_bound ? (arith_ueberlauf(),0) : 0 )
      #endif
      #ifdef NUM_STACK_UP
        #define compare_NUM_STACK_bound(addr)  \
          ( (aint)(addr) > (aint)NUM_STACK_bound ? (arith_ueberlauf(),0) : 0 )
      #endif
    #else # Wenn nichts zu �berpr�fen ist: trotzdem 'addr' auswerten!
      #define compare_NUM_STACK_bound(addr)  (addr)
    #endif
  #
  # num_stack_need(need, low_addr = , high_addr = );
  # zieht von num_stack need Digits ab, testet dabei auf Stack-�berlauf und
  # liefert die untere Grenze des so allozierten Bereiches in low_addr
  # und die obere Grenze in high_addr. Jedes von beiden ist optional.
    #ifdef NUM_STACK_DOWN
      #define num_stack_need(need,low_zuweisung,high_zuweisung)  \
        (high_zuweisung NUM_STACK,                        \
         NUM_STACK -= (aint)(need),                       \
         compare_NUM_STACK_bound(low_zuweisung NUM_STACK) \
        )
      #define num_stack_need_1(need,low_zuweisung,high_zuweisung)  \
        (high_zuweisung NUM_STACK,                                                           \
         compare_NUM_STACK_bound(NUM_STACK = (low_zuweisung (NUM_STACK - (aint)(need))) - 1) \
        )
    #endif
    #ifdef NUM_STACK_UP
      #define num_stack_need(need,low_zuweisung,high_zuweisung)  \
        (low_zuweisung NUM_STACK,                          \
         NUM_STACK += (aint)(need),                        \
         compare_NUM_STACK_bound(high_zuweisung NUM_STACK) \
        )
      #define num_stack_need_1(need,low_zuweisung,high_zuweisung)  \
        (low_zuweisung NUM_STACK += 1,                     \
         NUM_STACK += (aint)(need),                        \
         compare_NUM_STACK_bound(high_zuweisung NUM_STACK) \
        )
    #endif
#endif

#endif # LISPARIT


# Liefert 2^n, n eine Constant expression.
# Ergebnis dasselbe wie bit(n), jedoch undefiniert falls n<0 oder n>=32.
  #define bitc(n)  (1UL << (((n) >= 0 && (n) < intLsize) ? (n) : 0))


#ifdef LISPARIT

# Fehlermeldung wegen Division durch Null
  nonreturning_function(local, divide_0, (void));
  local void divide_0()
    { fehler(division_by_zero,
             DEUTSCH ? "Division durch Null" :
             ENGLISH ? "division by zero" :
             FRANCAIS ? "Division par z�ro" :
             ""
            );
    }

# Fehlermeldung wegen Floating-Point-�berlauf
# fehler_overflow();
  nonreturning_function(local, fehler_overflow, (void));
  local void fehler_overflow()
    { fehler(floating_point_overflow,
             DEUTSCH ? "Floating-Point �berlauf" :
             ENGLISH ? "floating point overflow" :
             FRANCAIS ? "D�bordement de nombre � virgule flottante" :
             ""
            );
    }

# Fehlermeldung wegen Floating-Point-Unterlauf
# fehler_underflow();
  nonreturning_function(local, fehler_underflow, (void));
  local void fehler_underflow()
    { fehler(floating_point_underflow,
             DEUTSCH ? "Floating-Point Unterlauf" :
             ENGLISH ? "floating point underflow" :
             FRANCAIS ? "D�bordement vers z�ro de nombre � virgule flottante" :
             ""
            );
    }

# Stellt fest, ob Floating-Point-Unterlauf erlaubt ist
# underflow_allowed()
  #define underflow_allowed()  \
    (nullp(Symbol_value(S(inhibit_floating_point_underflow))))

#endif # LISPARIT

