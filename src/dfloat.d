# Grundfunktionen für Double-Floats

# Entpacken eines Double-Float:
#ifdef intQsize
# DF_decode(obj, zero_statement, sign=,exp=,mant=);
# zerlegt ein Double-Float obj.
# Ist obj=0.0, wird zero_statement ausgeführt.
# Sonst: signean sign = Vorzeichen (0 = +, -1 = -),
#        sintWL exp = Exponent (vorzeichenbehaftet),
#        uintQ mant = Mantisse (>= 2^DF_mant_len, < 2^(DF_mant_len+1))
  #define float_value_semhi  float_value
  #define DF_uexp(x)  (((x) >> DF_mant_len) & (bit(DF_exp_len)-1))
  #define DF_decode(obj, zero_statement, sign_zuweisung,exp_zuweisung,mant_zuweisung)  \
    {                                                                    \
      var dfloat _x = TheDfloat(obj)->float_value;                       \
      var uintWL uexp = DF_uexp(_x);                                     \
      if (uexp==0) {                                                     \
        zero_statement # e=0 -> Zahl 0.0                                 \
      } else {                                                           \
        exp_zuweisung (sintWL)(uexp - DF_exp_mid); # Exponent            \
        unused (sign_zuweisung ((sint64)_x >> 63));  # Vorzeichen        \
        mant_zuweisung (bit(DF_mant_len) | (_x & (bit(DF_mant_len)-1))); \
      }                                                                  \
    }
#else
# DF_decode2(obj, zero_statement, sign=,exp=,manthi=,mantlo=);
# zerlegt ein Double-Float obj.
# Ist obj=0.0, wird zero_statement ausgeführt.
# Sonst: signean sign = Vorzeichen (0 = +, -1 = -),
#        sintWL exp = Exponent (vorzeichenbehaftet),
#        uintL manthi,mantlo = Mantisse 2^32*manthi+mantlo
#                              (>= 2^DF_mant_len, < 2^(DF_mant_len+1))
  #define float_value_semhi  float_value.semhi
  #define DF_uexp(semhi)  (((semhi) >> (DF_mant_len-32)) & (bit(DF_exp_len)-1))
  #define DF_decode2(obj, zero_statement, sign_zuweisung,exp_zuweisung,manthi_zuweisung,mantlo_zuweisung)  \
    {                                                                         \
      var uint32 semhi = TheDfloat(obj)->float_value.semhi;                   \
      var uint32 mlo = TheDfloat(obj)->float_value.mlo;                       \
      var uintWL uexp = DF_uexp(semhi);                                       \
      if (uexp==0) {                                                          \
        zero_statement # e=0 -> Zahl 0.0                                      \
      } else {                                                                \
        exp_zuweisung (sintWL)(uexp - DF_exp_mid);             # Exponent     \
        unused (sign_zuweisung sign_of_sint32((sint32)(semhi))); # Vorzeichen \
        manthi_zuweisung (bit(DF_mant_len-32) | (semhi & (bit(DF_mant_len-32)-1))); \
        mantlo_zuweisung mlo;                                                 \
      }                                                                       \
    }
#endif

# Einpacken eines Double-Float:
#ifdef intQsize
# encode_DF(sign,exp,mant, ergebnis=);
# liefert ein Double-Float.
# > signean sign: Vorzeichen, 0 für +, -1 für negativ.
# > sintWL exp: Exponent
# > uintQ mant: Mantisse, sollte >= 2^DF_mant_len und < 2^(DF_mant_len+1) sein.
# < object ergebnis: ein Double-Float
# Der Exponent wird auf Überlauf/Unterlauf getestet.
# can trigger GC
  #define encode_DF(sign,exp,mant, erg_zuweisung)  \
    {                                                               \
      if ((exp) < (sintWL)(DF_exp_low-DF_exp_mid)) {                \
        if (underflow_allowed()) {                                  \
          fehler_underflow();                                       \
        } else {                                                    \
          erg_zuweisung DF_0;                                       \
        }                                                           \
      } else                                                        \
      if ((exp) > (sintWL)(DF_exp_high-DF_exp_mid)) {               \
        fehler_overflow();                                          \
      } else                                                        \
      erg_zuweisung allocate_dfloat                                 \
        (  ((sint64)(sign) & bit(63))                  # Vorzeichen \
         | ((uint64)((exp)+DF_exp_mid) << DF_mant_len) # Exponent   \
         | ((uint64)(mant) & (bit(DF_mant_len)-1))     # Mantisse   \
        );                                                          \
    }
#else
# encode2_DF(sign,exp,manthi,mantlo, ergebnis=);
# liefert ein Double-Float.
# > signean sign: Vorzeichen, 0 für +, -1 für negativ.
# > sintWL exp: Exponent
# > uintL manthi,mantlo: Mantisse 2^32*manthi+mantlo,
#                        sollte >= 2^DF_mant_len und < 2^(DF_mant_len+1) sein.
# < object ergebnis: ein Double-Float
# Der Exponent wird auf Überlauf/Unterlauf getestet.
# can trigger GC
  #define encode2_DF(sign,exp,manthi,mantlo, erg_zuweisung)  \
    {                                                                    \
      if ((exp) < (sintWL)(DF_exp_low-DF_exp_mid)) {                     \
        if (underflow_allowed()) {                                       \
          fehler_underflow();                                            \
        } else {                                                         \
          erg_zuweisung DF_0;                                            \
        }                                                                \
      } else                                                             \
      if ((exp) > (sintWL)(DF_exp_high-DF_exp_mid)) {                    \
        fehler_overflow();                                               \
      } else                                                             \
      erg_zuweisung allocate_dfloat                                      \
        (  ((sint32)(sign) & bit(31))                       # Vorzeichen \
         | ((uint32)((exp)+DF_exp_mid) << (DF_mant_len-32)) # Exponent   \
         | ((uint32)(manthi) & (bit(DF_mant_len-32)-1))     # Mantisse   \
         , mantlo                                                        \
        );                                                               \
    }
#endif

#ifdef FAST_DOUBLE
# Auspacken eines Double:
  #define DF_to_double(obj)  (TheDfloat(obj)->representation.machine_double)
# Überprüfen und Einpacken eines von den 'double'-Routinen gelieferten
# IEEE-Floats.
# Klassifikation:
#   1 <= e <= 2046 : normalisierte Zahl
#   e=0, m/=0: subnormale Zahl
#   e=0, m=0: vorzeichenbehaftete 0.0
#   e=2047, m=0: vorzeichenbehaftete Infinity
#   e=2047, m/=0: NaN
# Angabe der möglicherweise auftretenden Sonderfälle:
#   maybe_overflow: Operation läuft über, liefert IEEE-Infinity
#   maybe_subnormal: Ergebnis sehr klein, liefert IEEE-subnormale Zahl
#   maybe_underflow: Ergebnis sehr klein und /=0, liefert IEEE-Null
#   maybe_divide_0: Ergebnis unbestimmt, liefert IEEE-Infinity
#   maybe_nan: Ergebnis unbestimmt, liefert IEEE-NaN
#ifdef intQsize
  #define double_to_DF(expr,ergebnis_zuweisung,maybe_overflow,maybe_subnormal,maybe_underflow,maybe_divide_0,maybe_nan)  \
    {                                                                    \
      var dfloatjanus _erg; _erg.machine_double = (expr);                \
      if ((_erg.eksplicit & ((uint64)bit(DF_exp_len+DF_mant_len)-bit(DF_mant_len))) == 0) { # e=0 ? \
        if ((maybe_underflow                                             \
             || (maybe_subnormal && !((_erg.eksplicit << 1) == 0))       \
            )                                                            \
            && underflow_allowed()                                       \
           ) {                                                           \
          fehler_underflow(); # subnormal oder noch kleiner -> Underflow \
        } else {                                                         \
          ergebnis_zuweisung DF_0; # +/- 0.0 -> 0.0                      \
        }                                                                \
      } elif ((maybe_overflow || maybe_divide_0)                         \
              && (((~_erg.eksplicit) & ((uint64)bit(DF_exp_len+DF_mant_len)-bit(DF_mant_len))) == 0) # e=2047 ? \
             ) {                                                         \
        if (maybe_nan && !((_erg.eksplicit<<(64-DF_mant_len)) == 0)) {   \
          # NaN, also Singularität -> "Division durch 0"                 \
          divide_0();                                                    \
        } else {                                                         \
          # Infinity                                                     \
          if (!maybe_overflow || maybe_divide_0)                         \
            divide_0(); # Infinity, Division durch 0                     \
          else                                                           \
            fehler_overflow(); # Infinity, Overflow                      \
        }                                                                \
      } else {                                                           \
        ergebnis_zuweisung allocate_dfloat(_erg.eksplicit);              \
      }                                                                  \
    }
#else
  #define double_to_DF(expr,ergebnis_zuweisung,maybe_overflow,maybe_subnormal,maybe_underflow,maybe_divide_0,maybe_nan)  \
    {                                                                    \
      var dfloatjanus _erg; _erg.machine_double = (expr);                \
      if ((_erg.eksplicit.semhi & ((uint32)bit(DF_exp_len+DF_mant_len-32)-bit(DF_mant_len-32))) == 0) { # e=0 ? \
        if ((maybe_underflow                                             \
             || (maybe_subnormal                                         \
                 && !(((_erg.eksplicit.semhi << 1) == 0) && (_erg.eksplicit.mlo == 0)) \
            )   )                                                        \
            && underflow_allowed()                                       \
           ) {                                                           \
          fehler_underflow(); # subnormal oder noch kleiner -> Underflow \
        } else {                                                         \
          ergebnis_zuweisung DF_0; # +/- 0.0 -> 0.0                      \
        }                                                                \
      } elif ((maybe_overflow || maybe_divide_0)                         \
              && (((~_erg.eksplicit.semhi) & ((uint32)bit(DF_exp_len+DF_mant_len-32)-bit(DF_mant_len-32))) == 0) # e=2047 ? \
             ) {                                                         \
        if (maybe_nan && !(((_erg.eksplicit.semhi<<(64-DF_mant_len)) == 0) && (_erg.eksplicit.mlo==0))) { \
          # NaN, also Singularität -> "Division durch 0"                 \
          divide_0();                                                    \
        } else {                                                         \
          # Infinity                                                     \
          if (!maybe_overflow || maybe_divide_0)                         \
            divide_0(); # Infinity, Division durch 0                     \
          else                                                           \
            fehler_overflow(); # Infinity, Overflow                      \
        }                                                                \
      } else {                                                           \
        ergebnis_zuweisung allocate_dfloat(_erg.eksplicit.semhi,_erg.eksplicit.mlo); \
      }                                                                  \
    }
#endif
#endif

# DF_zerop(x) stellt fest, ob ein Double-Float x = 0.0 ist.
  # define DF_zerop(x)  (DF_uexp(TheDfloat(x)->float_value_semhi) == 0)
  #define DF_zerop(x)  (TheDfloat(x)->float_value_semhi == 0)

# Liefert zu einem Double-Float x : (ftruncate x), ein DF.
# DF_ftruncate_DF(x)
# x wird zur 0 hin zur nächsten ganzen Zahl gerundet.
# can trigger GC
  local object DF_ftruncate_DF (object x);
# Methode:
# x = 0.0 oder e<=0 -> Ergebnis 0.0
# 1<=e<=52 -> letzte (53-e) Bits der Mantisse auf 0 setzen,
#             Exponent und Vorzeichen beibehalten
# e>=53 -> Ergebnis x
#ifdef intQsize
  local object DF_ftruncate_DF(x)
    var object x;
    {
      var dfloat x_ = TheDfloat(x)->float_value;
      var uintWL uexp = DF_uexp(x_); # e + DF_exp_mid
      if (uexp <= DF_exp_mid) { # 0.0 oder e<=0 ?
        return DF_0;
      } else {
        if (uexp > DF_exp_mid+DF_mant_len) # e > 52 ?
          return x;
        else
          # 1<=e<=52
          return allocate_dfloat
            ( x_ & # Bitmaske: Bits 52-e..0 gelöscht, alle anderen gesetzt
              ~(bit(DF_mant_len+1+DF_exp_mid-uexp)-1)
            );
      }
    }
#else
  local object DF_ftruncate_DF(x)
    var object x;
    {
      var uint32 semhi = TheDfloat(x)->float_value.semhi;
      var uint32 mlo = TheDfloat(x)->float_value.mlo;
      var uintWL uexp = DF_uexp(semhi); # e + DF_exp_mid
      if (uexp <= DF_exp_mid) { # 0.0 oder e<=0 ?
        return DF_0;
      } else {
        if (uexp > DF_exp_mid+DF_mant_len) { # e > 52 ?
          return x;
        } else {
          # 1<=e<=52
          if (uexp > DF_exp_mid+DF_mant_len+1-32) # e > 21 ?
            return allocate_dfloat
              ( semhi,
                mlo & # Bitmaske: Bits 52-e..0 gelöscht, alle anderen gesetzt
                ~(bit(DF_mant_len+1+DF_exp_mid-uexp)-1)
              );
          else
            return allocate_dfloat
              ( semhi & # Bitmaske: Bits 20-e..0 gelöscht, alle anderen gesetzt
                ~(bit(DF_mant_len+1+DF_exp_mid-32-uexp)-1),
                0
              );
        }
      }
    }
#endif

# Liefert zu einem Double-Float x : (futruncate x), ein DF.
# DF_futruncate_DF(x)
# x wird von der 0 weg zur nächsten ganzen Zahl gerundet.
# can trigger GC
  local object DF_futruncate_DF (object x);
# Methode:
# x = 0.0 -> Ergebnis 0.0
# e<=0 -> Ergebnis 1.0 oder -1.0, je nach Vorzeichen von x.
# 1<=e<=52 -> Greife die letzten (53-e) Bits von x heraus.
#             Sind sie alle =0 -> Ergebnis x.
#             Sonst setze sie alle und erhöhe dann die letzte Stelle um 1.
#             Kein Überlauf der 52 Bit -> fertig.
#             Sonst (Ergebnis eine Zweierpotenz): Mantisse := .1000...000,
#               e:=e+1. (Test auf Überlauf wegen e<=53 überflüssig)
# e>=53 -> Ergebnis x.
#ifdef intQsize
  local object DF_futruncate_DF(x)
    var object x;
    {
      var dfloat x_ = TheDfloat(x)->float_value;
      var uintWL uexp = DF_uexp(x_); # e + DF_exp_mid
      if (uexp==0) # 0.0 ?
        return x;
      if (uexp <= DF_exp_mid) { # e<=0 ?
        # Exponent auf 1, Mantisse auf .1000...000 setzen.
        return ((x_ & bit(63))==0 ? DF_1 : DF_minus1);
      } else {
        if (uexp > DF_exp_mid+DF_mant_len) { # e > 52 ?
          return x;
        } else {
          var uint64 mask = # Bitmaske: Bits 52-e..0 gesetzt, alle anderen gelöscht
            bit(DF_mant_len+1+DF_exp_mid-uexp)-1;
          if ((x_ & mask)==0) # alle diese Bits =0 ?
            return x;
          return allocate_dfloat
            ((x_ | mask) # alle diese Bits setzen
             + 1 # letzte Stelle erhöhen, dabei evtl. Exponenten incrementieren
            );
        }
      }
    }
#else
  local object DF_futruncate_DF(x)
    var object x;
    {
      var uint32 semhi = TheDfloat(x)->float_value.semhi;
      var uint32 mlo = TheDfloat(x)->float_value.mlo;
      var uintWL uexp = DF_uexp(semhi); # e + DF_exp_mid
      if (uexp==0) # 0.0 ?
        return x;
      if (uexp <= DF_exp_mid) { # e<=0 ?
        # Exponent auf 1, Mantisse auf .1000...000 setzen.
        return ((semhi & bit(31))==0 ? DF_1 : DF_minus1);
      } else {
        if (uexp > DF_exp_mid+DF_mant_len) { # e > 52 ?
          return x;
        } else {
          if (uexp > DF_exp_mid+DF_mant_len+1-32) { # e > 21 ?
            var uint32 mask = # Bitmaske: Bits 52-e..0 gesetzt, alle anderen gelöscht
              bit(DF_mant_len+1+DF_exp_mid-uexp)-1;
            if ((mlo & mask)==0) # alle diese Bits =0 ?
              return x;
            mlo = (mlo | mask) # alle diese Bits setzen
                  + 1; # letzte Stelle erhöhen,
            if (mlo==0)
              semhi += 1; # dabei evtl. Exponenten incrementieren
            return allocate_dfloat(semhi,mlo);
          } else {
            var uint32 mask = # Bitmaske: Bits 20-e..0 gesetzt, alle anderen gelöscht
              bit(DF_mant_len+1+DF_exp_mid-32-uexp)-1;
            if ((mlo==0) && ((semhi & mask)==0)) # alle diese Bits und mlo =0 ?
              return x;
            return allocate_dfloat
              ((semhi | mask) # alle diese Bits setzen
               + 1, # letzte Stelle erhöhen, dabei evtl. Exponenten incrementieren
               0
              );
          }
        }
      }
    }
#endif

# Liefert zu einem Double-Float x : (fround x), ein DF.
# DF_fround_DF(x)
# x wird zur nächsten ganzen Zahl gerundet.
# can trigger GC
  local object DF_fround_DF (object x);
# Methode:
# x = 0.0 oder e<0 -> Ergebnis 0.0
# 0<=e<=52 -> letzte (53-e) Bits der Mantisse wegrunden,
#             Exponent und Vorzeichen beibehalten.
# e>52 -> Ergebnis x
#ifdef intQsize
  local object DF_fround_DF(x)
    var object x;
    {
      var dfloat x_ = TheDfloat(x)->float_value;
      var uintWL uexp = DF_uexp(x_); # e + DF_exp_mid
      if (uexp < DF_exp_mid) { # x = 0.0 oder e<0 ?
        return DF_0;
      } else {
        if (uexp > DF_exp_mid+DF_mant_len) { # e > 52 ?
          return x;
        } else {
          if (uexp > DF_exp_mid+1) { # e>1 ?
            var uint64 bitmask = # Bitmaske: Bit 52-e gesetzt, alle anderen gelöscht
              bit(DF_mant_len+DF_exp_mid-uexp);
            var uint64 mask = # Bitmaske: Bits 51-e..0 gesetzt, alle anderen gelöscht
              bitmask-1;
            if ( ((x_ & bitmask) ==0) # Bit 52-e =0 -> abrunden
                 || ( ((x_ & mask) ==0) # Bit 52-e =1 und Bits 51-e..0 >0 -> aufrunden
                      # round-to-even, je nach Bit 53-e :
                      && ((x_ & (bitmask<<1)) ==0)
               )    ) {
              # abrunden
              mask |= bitmask; # Bitmaske: Bits 52-e..0 gesetzt, alle anderen gelöscht
              return allocate_dfloat( x_ & ~mask );
            } else {
              # aufrunden
              return allocate_dfloat
                ((x_ | mask) # alle diese Bits 51-e..0 setzen (Bit 52-e schon gesetzt)
                 + 1 # letzte Stelle erhöhen, dabei evtl. Exponenten incrementieren
                );
            }
          } elif (uexp == DF_exp_mid+1) { # e=1 ?
            # Wie bei 1 < e <= 52, nur dass Bit 53-e stets gesetzt ist.
            if ((x_ & bit(DF_mant_len-1)) ==0) # Bit 52-e =0 -> abrunden
              # abrunden
              return allocate_dfloat( x_ & ~(bit(DF_mant_len)-1) );
            else
              # aufrunden
              return allocate_dfloat
                ((x_ | (bit(DF_mant_len)-1)) # alle diese Bits 52-e..0 setzen
                 + 1 # letzte Stelle erhöhen, dabei evtl. Exponenten incrementieren
                );
          } else { # e=0 ?
            # Wie bei 1 < e <= 52, nur dass Bit 52-e stets gesetzt
            # und Bit 53-e stets gelöscht ist.
            if ((x_ & (bit(DF_mant_len)-1)) ==0)
              # abrunden von +-0.5 zu 0.0
              return DF_0;
            else
              # aufrunden
              return allocate_dfloat
                ((x_ | (bit(DF_mant_len)-1)) # alle Bits 51-e..0 setzen
                 + 1 # letzte Stelle erhöhen, dabei Exponenten incrementieren
                );
          }
        }
      }
    }
#else
  local object DF_fround_DF(x)
    var object x;
    {
      var uint32 semhi = TheDfloat(x)->float_value.semhi;
      var uint32 mlo = TheDfloat(x)->float_value.mlo;
      var uintWL uexp = DF_uexp(semhi); # e + DF_exp_mid
      if (uexp < DF_exp_mid) { # x = 0.0 oder e<0 ?
        return DF_0;
      } else {
        if (uexp > DF_exp_mid+DF_mant_len) { # e > 52 ?
          return x;
        } else {
          if (uexp > DF_exp_mid+1) { # e>1 ?
            if (uexp > DF_exp_mid+DF_mant_len-32) { # e > 20 ?
              var uint32 bitmask = # Bitmaske: Bit 52-e gesetzt, alle anderen gelöscht
                bit(DF_mant_len+DF_exp_mid-uexp);
              var uint32 mask = # Bitmaske: Bits 51-e..0 gesetzt, alle anderen gelöscht
                bitmask-1;
              if ( ((mlo & bitmask) ==0) # Bit 52-e =0 -> abrunden
                   || ( ((mlo & mask) ==0) # Bit 52-e =1 und Bits 51-e..0 >0 -> aufrunden
                        # round-to-even, je nach Bit 53-e :
                        && ( ((bitmask<<1) == 0) # e=21 ?
                              ? ((semhi & bit(0)) ==0)
                              : ((mlo & (bitmask<<1)) ==0)
                 )    )    ) {
                # abrunden
                mask |= bitmask; # Bitmaske: Bits 52-e..0 gesetzt, alle anderen gelöscht
                return allocate_dfloat(semhi, mlo & ~mask );
              } else {
                # aufrunden
                mlo = (mlo | mask) # alle diese Bits 51-e..0 setzen (Bit 52-e schon gesetzt)
                      + 1; # letzte Stelle erhöhen,
                if (mlo==0)
                  semhi += 1; # dabei evtl. Exponenten incrementieren
                return allocate_dfloat(semhi,mlo);
              }
            } else {
              var uint32 bitmask = # Bitmaske: Bit 20-e gesetzt, alle anderen gelöscht
                bit(DF_mant_len+DF_exp_mid-32-uexp);
              var uint32 mask = # Bitmaske: Bits 19-e..0 gesetzt, alle anderen gelöscht
                bitmask-1;
              if ( ((semhi & bitmask) ==0) # Bit 52-e =0 -> abrunden
                   || ( (mlo==0) && ((semhi & mask) ==0) # Bit 52-e =1 und Bits 51-e..0 >0 -> aufrunden
                        # round-to-even, je nach Bit 53-e :
                        && ((semhi & (bitmask<<1)) ==0)
                 )    ) {
                # abrunden
                mask |= bitmask; # Bitmaske: Bits 20-e..0 gesetzt, alle anderen gelöscht
                return allocate_dfloat( semhi & ~mask, 0 );
              } else {
                # aufrunden
                return allocate_dfloat
                  ((semhi | mask) # alle diese Bits 19-e..0 setzen (Bit 20-e schon gesetzt)
                   + 1, # letzte Stelle erhöhen, dabei evtl. Exponenten incrementieren
                   0
                  );
              }
            }
          } elif (uexp == DF_exp_mid+1) { # e=1 ?
            # Wie bei 1 < e <= 20, nur dass Bit 53-e stets gesetzt ist.
            if ((semhi & bit(DF_mant_len-32-1)) ==0) # Bit 52-e =0 -> abrunden
              # abrunden
              return allocate_dfloat( semhi & ~(bit(DF_mant_len-32)-1) , 0 );
            else
              # aufrunden
              return allocate_dfloat
                ((semhi | (bit(DF_mant_len-32)-1)) # alle diese Bits 52-e..0 setzen
                 + 1, # letzte Stelle erhöhen, dabei evtl. Exponenten incrementieren
                 0
                );
          } else { # e=0 ?
            # Wie bei 1 < e <= 20, nur dass Bit 52-e stets gesetzt
            # und Bit 53-e stets gelöscht ist.
            if ((mlo==0) && ((semhi & (bit(DF_mant_len-32)-1)) ==0))
              # abrunden von +-0.5 zu 0.0
              return DF_0;
            else
              # aufrunden
              return allocate_dfloat
                ((semhi | (bit(DF_mant_len-32)-1)) # alle Bits 51-e..0 setzen
                 + 1, # letzte Stelle erhöhen, dabei Exponenten incrementieren
                 0
                );
          }
        }
      }
    }
#endif

# Liefert zu einem Double-Float x : (- x), ein DF.
# DF_minus_DF(x)
# can trigger GC
  local object DF_minus_DF (object x);
# Methode:
# Falls x=0.0, fertig. Sonst Vorzeichenbit umdrehen.
#ifdef intQsize
  local object DF_minus_DF(x)
    var object x;
    {
      var dfloat x_ = TheDfloat(x)->float_value;
      return (DF_uexp(x_) == 0
              ? x
              : allocate_dfloat( x_ ^ bit(63) )
             );
    }
#else
  local object DF_minus_DF(x)
    var object x;
    {
      var uint32 semhi = TheDfloat(x)->float_value.semhi;
      var uint32 mlo = TheDfloat(x)->float_value.mlo;
      return (DF_uexp(semhi) == 0
              ? x
              : allocate_dfloat( semhi ^ bit(31), mlo )
             );
    }
#endif

# DF_DF_comp(x,y) vergleicht zwei Double-Floats x und y.
# Ergebnis: 0 falls x=y, +1 falls x>y, -1 falls x<y.
  local signean DF_DF_comp (object x, object y);
# Methode:
# x und y haben verschiedenes Vorzeichen ->
#    x < 0 -> x < y
#    x >= 0 -> x > y
# x und y haben gleiches Vorzeichen ->
#    x >=0 -> vergleiche x und y (die rechten 53 Bits)
#    x <0 -> vergleiche y und x (die rechten 53 Bits)
#ifdef intQsize
  local signean DF_DF_comp(x,y)
    var object x;
    var object y;
    {
      var dfloat x_ = TheDfloat(x)->float_value;
      var dfloat y_ = TheDfloat(y)->float_value;
      if ((sint64)y_ >= 0) {
        # y>=0
        if ((sint64)x_ >= 0) {
          # y>=0, x>=0
          if (x_ < y_)
            return signean_minus; # x<y
          if (x_ > y_)
            return signean_plus; # x>y
          return signean_null;
        } else {
          # y>=0, x<0
          return signean_minus; # x<y
        }
      } else {
        if ((sint64)x_ >= 0) {
          # y<0, x>=0
          return signean_plus; # x>y
        } else {
          # y<0, x<0
          if (x_ > y_)
            return signean_minus; # |x|>|y| -> x<y
          if (x_ < y_)
            return signean_plus; # |x|<|y| -> x>y
          return signean_null;
        }
      }
    }
#else
  local signean DF_DF_comp(x,y)
    var object x;
    var object y;
    {
      var uint32 x_semhi = TheDfloat(x)->float_value.semhi;
      var uint32 y_semhi = TheDfloat(y)->float_value.semhi;
      var uint32 x_mlo = TheDfloat(x)->float_value.mlo;
      var uint32 y_mlo = TheDfloat(y)->float_value.mlo;
      if ((sint32)y_semhi >= 0) {
        # y>=0
        if ((sint32)x_semhi >= 0) {
          # y>=0, x>=0
          if (x_semhi < y_semhi)
            return signean_minus; # x<y
          if (x_semhi > y_semhi)
            return signean_plus; # x>y
          if (x_mlo < y_mlo)
            return signean_minus; # x<y
          if (x_mlo > y_mlo)
            return signean_plus; # x>y
          return signean_null;
        } else {
          # y>=0, x<0
          return signean_minus; # x<y
        }
      } else {
        if ((sint32)x_semhi >= 0) {
          # y<0, x>=0
          return signean_plus; # x>y
        } else {
          # y<0, x<0
          if (x_semhi > y_semhi)
            return signean_minus; # |x|>|y| -> x<y
          if (x_semhi < y_semhi)
            return signean_plus; # |x|<|y| -> x>y
          if (x_mlo > y_mlo)
            return signean_minus; # |x|>|y| -> x<y
          if (x_mlo < y_mlo)
            return signean_plus; # |x|<|y| -> x>y
          return signean_null;
        }
      }
    }
#endif

# Liefert zu zwei Double-Float x und y : (+ x y), ein DF.
# DF_DF_plus_DF(x,y)
# can trigger GC
  local object DF_DF_plus_DF (object x, object y);
# Methode (nach [Knuth, II, Seminumerical Algorithms, Abschnitt 4.2.1., S.200]):
# x1=0.0 -> Ergebnis x2.
# x2=0.0 -> Ergebnis x1.
# Falls e1<e2, vertausche x1 und x2.
# Also e1 >= e2.
# Falls e1 - e2 >= 52 + 3, Ergebnis x1.
# Schiebe beide Mantissen um 3 Bits nach links (Vorbereitung der Rundung:
#   Bei e1-e2=0,1 ist keine Rundung nötig, bei e1-e2>1 ist der Exponent des
#   Ergebnisses =e1-1, =e1 oder =e1+1. Brauche daher 1 Schutzbit und zwei
#   Rundungsbits: 00 exakt, 01 1.Hälfte, 10 exakte Mitte, 11 2.Hälfte.)
# Schiebe die Mantisse von x2 um e0-e1 Bits nach rechts. (Dabei die Rundung
# ausführen: Bit 0 ist das logische Oder der Bits 0,-1,-2,...)
# Falls x1,x2 selbes Vorzeichen haben: Addiere dieses zur Mantisse von x1.
# Falls x1,x2 verschiedenes Vorzeichen haben: Subtrahiere dieses von der
#   Mantisse von x1. <0 -> (Es war e1=e2) Vertausche die Vorzeichen, negiere.
#                    =0 -> Ergebnis 0.0
# Exponent ist e1.
# Normalisiere, fertig.
#ifdef FAST_DOUBLE
  local object DF_DF_plus_DF(x1,x2)
    var object x1;
    var object x2;
    {
      double_to_DF(DF_to_double(x1) + DF_to_double(x2), return ,
                   true, true, # Overflow und subnormale Zahl abfangen
                   false, # kein Underflow mit Ergebnis +/- 0.0 möglich
                          # (nach Definition der subnormalen Zahlen)
                   false, false # keine Singularität, kein NaN als Ergebnis möglich
                  );
    }
#else
#ifdef intQsize
  local object DF_DF_plus_DF(x1,x2)
    var object x1;
    var object x2;
    {
      # x1,x2 entpacken:
      var signean sign1;
      var sintWL exp1;
      var uint64 mant1;
      var signean sign2;
      var sintWL exp2;
      var uint64 mant2;
      DF_decode(x1, { return x2; }, sign1=,exp1=,mant1=);
      DF_decode(x2, { return x1; }, sign2=,exp2=,mant2=);
      if (exp1 < exp2) {
        swap(object,  x1   ,x2   );
        swap(signean, sign1,sign2);
        swap(sintWL,  exp1 ,exp2 );
        swap(uint64,   mant1,mant2);
      }
      # Nun ist exp1>=exp2.
      var uintL expdiff = exp1 - exp2; # Exponentendifferenz
      if (expdiff >= DF_mant_len+3) # >= 52+3 ?
        return x1;
      mant1 = mant1 << 3; mant2 = mant2 << 3;
      # Nun 2^(DF_mant_len+3) <= mant1,mant2 < 2^(DF_mant_len+4).
      {
        var uint64 mant2_last = mant2 & (bit(expdiff)-1); # letzte expdiff Bits von mant2
        mant2 = mant2 >> expdiff; if (!(mant2_last==0)) { mant2 |= bit(0); }
      }
      # mant2 = um expdiff Bits nach rechts geschobene und gerundete Mantisse
      # von x2.
      if (!(sign1==sign2)) {
        # verschiedene Vorzeichen -> Mantissen subtrahieren
        if (mant1 > mant2) {
          mant1 = mant1 - mant2;
          goto norm_2;
        }
        if (mant1 == mant2) # Ergebnis 0 ?
          return DF_0;
        # negatives Subtraktionsergebnis
        mant1 = mant2 - mant1; sign1 = sign2; goto norm_2;
      } else {
        # gleiche Vorzeichen -> Mantissen addieren
        mant1 = mant1 + mant2;
      }
      # mant1 = Ergebnis-Mantisse >0, sign1 = Ergebnis-Vorzeichen,
      # exp1 = Ergebnis-Exponent.
      # Außerdem: Bei expdiff=0,1 sind die zwei letzten Bits von mant1 Null,
      # bei expdiff>=2 ist mant1 >= 2^(DF_mant_len+2).
      # Stets ist mant1 < 2^(DF_mant_len+5). (Daher werden die 2 Rundungsbits
      # nachher um höchstens eine Position nach links geschoben werden.)
      # [Knuth, S.201, leicht modifiziert:
      #   N1. m>=1 -> goto N4.
      #   N2. [Hier m<1] m>=1/2 -> goto N5.
      #       N3. m:=2*m, e:=e-1, goto N2.
      #   N4. [Hier 1<=m<2] m:=m/2, e:=e+1.
      #   N5. [Hier 1/2<=m<1] Runde m auf 53 Bits hinterm Komma.
      #       Falls hierdurch m=1 geworden, setze m:=m/2, e:=e+1.
      # ]
      # Bei uns ist m=mant1/2^(DF_mant_len+4),
      # ab Schritt N5 ist m=mant1/2^(DF_mant_len+1).
     norm_1: # [Knuth, S.201, Schritt N1]
      if (mant1 >= bit(DF_mant_len+4))
        goto norm_4;
     norm_2: # [Knuth, S.201, Schritt N2]
             # Hier ist mant1 < 2^(DF_mant_len+4)
      if (mant1 >= bit(DF_mant_len+3))
        goto norm_5;
      # [Knuth, S.201, Schritt N3]
      mant1 = mant1 << 1; exp1 = exp1-1; # Mantisse links schieben
      goto norm_2;
     norm_4: # [Knuth, S.201, Schritt N4]
             # Hier ist 2^(DF_mant_len+4) <= mant1 < 2^(DF_mant_len+5)
      exp1 = exp1+1;
      mant1 = (mant1>>1) | (mant1 & bit(0)); # Mantisse rechts schieben
     norm_5: # [Knuth, S.201, Schritt N5]
             # Hier ist 2^(DF_mant_len+3) <= mant1 < 2^(DF_mant_len+4)
      # Auf DF_mant_len echte Mantissenbits runden, d.h. rechte 3 Bits
      # wegrunden, und dabei mant1 um 3 Bits nach rechts schieben:
      {
        var uint64 rounding_bits = mant1 & (bit(3)-1);
        mant1 = mant1 >> 3;
        if ( (rounding_bits < bit(2)) # 000,001,010,011 werden abgerundet
             || ( (rounding_bits == bit(2)) # 100 (genau halbzahlig)
                  && ((mant1 & bit(0)) ==0) # -> round-to-even
           )    ) {
          # abrunden
        } else {
          # aufrunden
          mant1 = mant1+1;
          if (mant1 >= bit(DF_mant_len+1)) {
            # Bei Überlauf während der Rundung nochmals rechts schieben
            # (Runden ist hier überflüssig):
            mant1 = mant1>>1; exp1 = exp1+1; # Mantisse rechts schieben
          }
        }
      }# Runden fertig
      encode_DF(sign1,exp1,mant1, return);
    }
#else
  local object DF_DF_plus_DF(x1,x2)
    var object x1;
    var object x2;
    {
      # x1,x2 entpacken:
      var signean sign1;
      var sintWL exp1;
      var uintL manthi1;
      var uintL mantlo1;
      var signean sign2;
      var sintWL exp2;
      var uintL manthi2;
      var uintL mantlo2;
      DF_decode2(x1, { return x2; }, sign1=,exp1=,manthi1=,mantlo1=);
      DF_decode2(x2, { return x1; }, sign2=,exp2=,manthi2=,mantlo2=);
      if (exp1 < exp2) {
        swap(object,  x1   ,x2   );
        swap(signean, sign1,sign2);
        swap(sintWL,  exp1 ,exp2 );
        swap(uintL,   manthi1,manthi2);
        swap(uintL,   mantlo1,mantlo2);
      }
      # Nun ist exp1>=exp2.
      var uintL expdiff = exp1 - exp2; # Exponentendifferenz
      if (expdiff >= DF_mant_len+3) # >= 52+3 ?
        return x1;
      manthi1 = (manthi1 << 3) | (mantlo1 >> (32-3)); mantlo1 = mantlo1 << 3;
      manthi2 = (manthi2 << 3) | (mantlo2 >> (32-3)); mantlo2 = mantlo2 << 3;
      # Nun 2^(DF_mant_len+3) <= mant1,mant2 < 2^(DF_mant_len+4).
      if (expdiff<32) {
        if (!(expdiff==0)) {
          var uintL mant2_last = mantlo2 & (bit(expdiff)-1); # letzte expdiff Bits von mant2
          mantlo2 = (mantlo2 >> expdiff) | (manthi2 << (32-expdiff));
          manthi2 = manthi2 >> expdiff;
          if (!(mant2_last==0))
            mantlo2 |= bit(0);
        }
      } else {
        var uintL mant2_last = (manthi2 & (bit(expdiff-32)-1)) | mantlo2; # letzte expdiff Bits von mant2
        mantlo2 = manthi2 >> (expdiff-32); manthi2 = 0;
        if (!(mant2_last==0))
          mantlo2 |= bit(0);
      }
      # mant2 = um expdiff Bits nach rechts geschobene und gerundete Mantisse
      # von x2.
      if (!(sign1==sign2)) {
        # verschiedene Vorzeichen -> Mantissen subtrahieren
        if (manthi1 > manthi2) {
          manthi1 = manthi1 - manthi2;
          if (mantlo1 < mantlo2)
            manthi1 -= 1;
          mantlo1 = mantlo1 - mantlo2;
          goto norm_2;
        }
        if (manthi1 == manthi2) {
          if (mantlo1 > mantlo2) {
            manthi1 = 0; mantlo1 = mantlo1 - mantlo2;
            goto norm_2;
          }
          if (mantlo1 == mantlo2) # Ergebnis 0 ?
            return DF_0;
        }
        # Hier ((manthi1 < manthi2) || ((manthi1 == manthi2) && (mantlo1 < mantlo2))).
        # negatives Subtraktionsergebnis
        manthi1 = manthi2 - manthi1;
        if (mantlo2 < mantlo1)
          manthi1 -= 1;
        mantlo1 = mantlo2 - mantlo1;
        sign1 = sign2;
        goto norm_2;
      } else {
        # gleiche Vorzeichen -> Mantissen addieren
        manthi1 = manthi1 + manthi2;
        if ((mantlo1 = mantlo1 + mantlo2) < mantlo2)
          manthi1 += 1;
      }
      # mant1 = Ergebnis-Mantisse >0, sign1 = Ergebnis-Vorzeichen,
      # exp1 = Ergebnis-Exponent.
      # Außerdem: Bei expdiff=0,1 sind die zwei letzten Bits von mant1 Null,
      # bei expdiff>=2 ist mant1 >= 2^(DF_mant_len+2).
      # Stets ist mant1 < 2^(DF_mant_len+5). (Daher werden die 2 Rundungsbits
      # nachher um höchstens eine Position nach links geschoben werden.)
      # [Knuth, S.201, leicht modifiziert:
      #   N1. m>=1 -> goto N4.
      #   N2. [Hier m<1] m>=1/2 -> goto N5.
      #       N3. m:=2*m, e:=e-1, goto N2.
      #   N4. [Hier 1<=m<2] m:=m/2, e:=e+1.
      #   N5. [Hier 1/2<=m<1] Runde m auf 53 Bits hinterm Komma.
      #       Falls hierdurch m=1 geworden, setze m:=m/2, e:=e+1.
      # ]
      # Bei uns ist m=mant1/2^(DF_mant_len+4),
      # ab Schritt N5 ist m=mant1/2^(DF_mant_len+1).
     norm_1: # [Knuth, S.201, Schritt N1]
      if (manthi1 >= bit(DF_mant_len-32+4))
        goto norm_4;
     norm_2: # [Knuth, S.201, Schritt N2]
             # Hier ist mant1 < 2^(DF_mant_len+4)
      if (manthi1 >= bit(DF_mant_len-32+3))
        goto norm_5;
      # [Knuth, S.201, Schritt N3]
      manthi1 = (manthi1 << 1) | (mantlo1 >> 31); # Mantisse links schieben
      mantlo1 = mantlo1 << 1;
      exp1 = exp1-1;
      goto norm_2;
     norm_4: # [Knuth, S.201, Schritt N4]
             # Hier ist 2^(DF_mant_len+4) <= mant1 < 2^(DF_mant_len+5)
      exp1 = exp1+1;
      mantlo1 = (mantlo1 >> 1) | (manthi1 << 31) | (mantlo1 & bit(0)); # Mantisse rechts schieben
      manthi1 = (manthi1 >> 1);
     norm_5: # [Knuth, S.201, Schritt N5]
             # Hier ist 2^(DF_mant_len+3) <= mant1 < 2^(DF_mant_len+4)
      # Auf DF_mant_len echte Mantissenbits runden, d.h. rechte 3 Bits
      # wegrunden, und dabei mant1 um 3 Bits nach rechts schieben:
      {
        var uintL rounding_bits = mantlo1 & (bit(3)-1);
        mantlo1 = (mantlo1 >> 3) | (manthi1 << (32-3)); manthi1 = manthi1 >> 3;
        if ( (rounding_bits < bit(2)) # 000,001,010,011 werden abgerundet
             || ( (rounding_bits == bit(2)) # 100 (genau halbzahlig)
                  && ((mantlo1 & bit(0)) ==0) # -> round-to-even
           )    ) {
          # abrunden
        } else {
          # aufrunden
          mantlo1 = mantlo1+1;
          if (mantlo1==0) {
            manthi1 = manthi1+1;
            if (manthi1 >= bit(DF_mant_len-32+1)) {
              # Bei Überlauf während der Rundung nochmals rechts schieben
              # (Runden ist hier überflüssig):
              manthi1 = manthi1>>1; exp1 = exp1+1; # Mantisse rechts schieben
            }
          }
        }
      }# Runden fertig
      encode2_DF(sign1,exp1,manthi1,mantlo1, return);
    }
#endif
#endif

# Liefert zu zwei Double-Float x und y : (- x y), ein DF.
# DF_DF_minus_DF(x,y)
# can trigger GC
  local object DF_DF_minus_DF (object x, object y);
# Methode:
# (- x1 x2) = (+ x1 (- x2))
#ifdef FAST_DOUBLE
  local object DF_DF_minus_DF(x1,x2)
    var object x1;
    var object x2;
    {
      double_to_DF(DF_to_double(x1) - DF_to_double(x2), return ,
                   true, true, # Overflow und subnormale Zahl abfangen
                   false, # kein Underflow mit Ergebnis +/- 0.0 möglich
                          # (nach Definition der subnormalen Zahlen)
                   false, false # keine Singularität, kein NaN als Ergebnis möglich
                  );
    }
#else
#ifdef intQsize
  local object DF_DF_minus_DF(x1,x2)
    var object x1;
    var object x2;
    {
      var dfloat x2_ = TheDfloat(x2)->float_value;
      if (DF_uexp(x2_) == 0) {
        return x1;
      } else {
        pushSTACK(x1);
        x2 = allocate_dfloat(x2_ ^ bit(63));
        return DF_DF_plus_DF(popSTACK(),x2);
      }
    }
#else
  local object DF_DF_minus_DF(x1,x2)
    var object x1;
    var object x2;
    {
      var uint32 x2_semhi = TheDfloat(x2)->float_value.semhi;
      var uint32 x2_mlo = TheDfloat(x2)->float_value.mlo;
      if (DF_uexp(x2_semhi) == 0) {
        return x1;
      } else {
        pushSTACK(x1);
        x2 = allocate_dfloat(x2_semhi ^ bit(31), x2_mlo);
        return DF_DF_plus_DF(popSTACK(),x2);
      }
    }
#endif
#endif

# Liefert zu zwei Double-Float x und y : (* x y), ein DF.
# DF_DF_mal_DF(x,y)
# can trigger GC
  local object DF_DF_mal_DF (object x, object y);
# Methode:
# Falls x1=0.0 oder x2=0.0 -> Ergebnis 0.0
# Sonst: Ergebnis-Vorzeichen = VZ von x1 xor VZ von x2.
#        Ergebnis-Exponent = Summe der Exponenten von x1 und x2.
#        Ergebnis-Mantisse = Produkt der Mantissen von x1 und x2, gerundet:
#          2^-53 * mant1  *  2^-53 * mant2  =  2^-106 * (mant1*mant2),
#          die Klammer ist >=2^104, <=(2^53-1)^2<2^106 .
#          Falls die Klammer >=2^105 ist, um 53 Bit nach rechts schieben und
#            runden: Falls Bit 52 Null, abrunden; falls Bit 52 Eins und
#            Bits 51..0 alle Null, round-to-even; sonst aufrunden.
#          Falls die Klammer <2^105 ist, um 52 Bit nach rechts schieben und
#            runden: Falls Bit 51 Null, abrunden; falls Bit 51 Eins und
#            Bits 50..0 alle Null, round-to-even; sonst aufrunden. Nach
#            Aufrunden: Falls =2^53, um 1 Bit nach rechts schieben. Sonst
#            Exponenten um 1 erniedrigen.
#ifdef FAST_DOUBLE
  local object DF_DF_mal_DF(x1,x2)
    var object x1;
    var object x2;
    {
      double_to_DF(DF_to_double(x1) * DF_to_double(x2), return ,
                   true, true, # Overflow und subnormale Zahl abfangen
                   !(DF_zerop(x1) || DF_zerop(x2)), # ein Ergebnis +/- 0.0
                               # ist genau dann in Wirklichkeit ein Underflow
                   false, false # keine Singularität, kein NaN als Ergebnis möglich
                  );
    }
#else
  local object DF_DF_mal_DF(x1,x2)
    var object x1;
    var object x2;
    {
      # x1,x2 entpacken:
      var signean sign1;
      var sintWL exp1;
      var uintL manthi1;
      var uintL mantlo1;
      var signean sign2;
      var sintWL exp2;
      var uintL manthi2;
      var uintL mantlo2;
      #ifdef intQsize
      {
        var uint64 mant1;
        DF_decode(x1, { return x1; }, sign1=,exp1=,mant1=);
        manthi1 = (uint32)(mant1>>32); mantlo1 = (uint32)mant1;
      }
      {
        var uint64 mant2;
        DF_decode(x2, { return x2; }, sign2=,exp2=,mant2=);
        manthi2 = (uint32)(mant2>>32); mantlo2 = (uint32)mant2;
      }
      #else
      DF_decode2(x1, { return x1; }, sign1=,exp1=,manthi1=,mantlo1=);
      DF_decode2(x2, { return x2; }, sign2=,exp2=,manthi2=,mantlo2=);
      #endif
      exp1 = exp1 + exp2; # Summe der Exponenten
      sign1 = sign1 ^ sign2; # Ergebnis-Vorzeichen
      # Mantissen mant1 und mant2 multiplizieren (64x64-Bit-Multiplikation):
      var uintD mant1 [64/intDsize];
      var uintD mant2 [64/intDsize];
      var uintD mant [128/intDsize];
      #if (intDsize==32) || (intDsize==16) || (intDsize==8)
      set_32_Dptr(mant1,manthi1); set_32_Dptr(&mant1[32/intDsize],mantlo1);
      set_32_Dptr(mant2,manthi2); set_32_Dptr(&mant2[32/intDsize],mantlo2);
      #else
      {
        var uintD* ptr;
        ptr = &mant1[64/intDsize];
        doconsttimes(32/intDsize, { *--ptr = (uintD)mantlo1; mantlo1 = mantlo1>>intDsize; } );
        doconsttimes(32/intDsize, { *--ptr = (uintD)manthi1; manthi1 = manthi1>>intDsize; } );
      }
      {
        var uintD* ptr;
        ptr = &mant2[64/intDsize];
        doconsttimes(32/intDsize, { *--ptr = (uintD)mantlo2; mantlo2 = mantlo2>>intDsize; } );
        doconsttimes(32/intDsize, { *--ptr = (uintD)manthi2; manthi2 = manthi2>>intDsize; } );
      }
      #endif
      begin_arith_call();
      mulu_2loop_down(&mant1[64/intDsize],64/intDsize,
                      &mant2[64/intDsize],64/intDsize,
                      &mant[128/intDsize]
                     );
      end_arith_call();
      #ifdef intQsize
      var uint64 manterg;
      #else
      var uintL manthi;
      var uintL mantlo;
      #endif
      # Produkt mant = mant1 * mant2 ist >= 2^104, < 2^106. Bit 105 abtesten:
      #define mant_bit(k)  (mant[128/intDsize - 1 - floor(k,intDsize)] & bit((k)%intDsize))
      if (mant_bit(2*DF_mant_len+1)) {
        # mant>=2^(2*DF_mant_len+1), um DF_mant_len+1 Bits nach rechts schieben:
        # Bits 105..53 holen:
        #if defined(intQsize) # && (intDsize==32)
          manterg = ((uint64)mant[0] << 43) | ((uint64)mant[1] << 11) | ((uint64)mant[2] >> 21); # Bits 116..53
          #define mantrest() ((mant[2] & (bit(21)-1)) || mant[3])
        #elif (intDsize==32)
          manthi = ((uint32)mant[0] << 11) | ((uint32)mant[1] >> 21); # Bits 116..85
          mantlo = ((uint32)mant[1] << 11) | ((uint32)mant[2] >> 21); # Bits 84..53
          #define mantrest() ((mant[2] & (bit(21)-1)) || mant[3])
        #elif (intDsize==16)
          manthi = # ((uint32)mant[0] << 27) | ((uint32)mant[1] << 11) | ((uint32)mant[2] >> 5); # Bits 116..85
                   (highlow32_at(&mant[0])<<11) | ((uint32)mant[2] >> 5); # Bits 116..85
          mantlo = # ((uint32)mant[2] << 27) | ((uint32)mant[3] << 11) | ((uint32)mant[4] >> 5); # Bits 84..53
                   (highlow32_at(&mant[2])<<11) | ((uint32)mant[4] >> 5); # Bits 84..53
          #define mantrest() ((mant[4] & (bit(5)-1)) || mant[5] || mant[6] || mant[7])
        #elif (intDsize==8)
          manthi = ((uint32)mant[1] << 27) | ((uint32)mant[2] << 19) | ((uint32)mant[3] << 11) | ((uint32)mant[4] << 3) | ((uint32)mant[5] >> 5); # Bits 116..85
          mantlo = ((uint32)mant[5] << 27) | ((uint32)mant[6] << 19) | ((uint32)mant[7] << 11) | ((uint32)mant[8] << 3) | ((uint32)mant[9] >> 5); # Bits 84..53
          #define mantrest() ((mant[9] & (bit(5)-1)) || mant[10] || mant[11] || mant[12] || mant[13] || mant[14] || mant[15])
        #endif
        if ( (mant_bit(DF_mant_len) ==0) # Bit DF_mant_len =0 -> abrunden
             || ( !mantrest() # Bit DF_mant_len =1 und Bits DF_mant_len-1..0 >0 -> aufrunden
                  # round-to-even, je nach Bit DF_mant_len+1 :
                  && (mant_bit(DF_mant_len+1) ==0)
           )    )
          # abrunden
          goto ab;
        else
          # aufrunden
          goto auf;
        #undef mantrest
      } else {
        # mant<2^(2*DF_mant_len+1), um DF_mant_len Bits nach rechts schieben:
        exp1 = exp1-1; # Exponenten decrementieren
        # Bits 104..52 holen:
        #if defined(intQsize) # && (intDsize==32)
          manterg = ((uint64)mant[0] << 44) | ((uint64)mant[1] << 12) | ((uint64)mant[2] >> 20); # Bits 115..52
          #define mantrest() ((mant[2] & (bit(20)-1)) || mant[3])
        #elif (intDsize==32)
          manthi = ((uint32)mant[0] << 12) | ((uint32)mant[1] >> 20); # Bits 115..84
          mantlo = ((uint32)mant[1] << 12) | ((uint32)mant[2] >> 20); # Bits 83..52
          #define mantrest() ((mant[2] & (bit(20)-1)) || mant[3])
        #elif (intDsize==16)
          manthi = # ((uint32)mant[0] << 28) | ((uint32)mant[1] << 12) | ((uint32)mant[2] >> 4); # Bits 115..84
                   (highlow32_at(&mant[0])<<12) | ((uint32)mant[2] >> 4); # Bits 115..84
          mantlo = # ((uint32)mant[2] << 28) | ((uint32)mant[3] << 12) | ((uint32)mant[4] >> 4); # Bits 83..52
                   (highlow32_at(&mant[2])<<12) | ((uint32)mant[4] >> 4); # Bits 83..52
          #define mantrest() ((mant[4] & (bit(4)-1)) || mant[5] || mant[6] || mant[7])
        #elif (intDsize==8)
          manthi = ((uint32)mant[1] << 28) | ((uint32)mant[2] << 20) | ((uint32)mant[3] << 12) | ((uint32)mant[4] << 4) | ((uint32)mant[5] >> 4); # Bits 115..84
          mantlo = ((uint32)mant[5] << 28) | ((uint32)mant[6] << 20) | ((uint32)mant[7] << 12) | ((uint32)mant[8] << 4) | ((uint32)mant[9] >> 4); # Bits 83..52
          #define mantrest() ((mant[9] & (bit(4)-1)) || mant[10] || mant[11] || mant[12] || mant[13] || mant[14] || mant[15])
        #endif
        if ( (mant_bit(DF_mant_len-1) ==0) # Bit DF_mant_len-1 =0 -> abrunden
             || ( !mantrest() # Bit DF_mant_len-1 =1 und Bits DF_mant_len-2..0 >0 -> aufrunden
                  # round-to-even, je nach Bit DF_mant_len :
                  && (mant_bit(DF_mant_len) ==0)
           )    )
          # abrunden
          goto ab;
        else
          # aufrunden
          goto auf;
        #undef mantrest
      }
      #undef mant_bit
     auf:
      #ifdef intQsize
      manterg = manterg+1;
      # Hier ist 2^DF_mant_len <= manterg <= 2^(DF_mant_len+1)
      if (manterg >= bit(DF_mant_len+1)) { # rounding overflow?
        manterg = manterg>>1; exp1 = exp1+1; # Shift nach rechts
      }
      #else
      mantlo = mantlo+1;
      if (mantlo==0) {
        manthi = manthi+1;
        # Hier ist 2^(DF_mant_len-32) <= manthi <= 2^(DF_mant_len-32+1)
        if (manthi >= bit(DF_mant_len-32+1)) { # rounding overflow?
          manthi = manthi>>1; exp1 = exp1+1; # Shift nach rechts
        }
      }
      #endif
     ab:
      # Runden fertig, 2^DF_mant_len <= manterg < 2^(DF_mant_len+1)
      #ifdef intQsize
      encode_DF(sign1,exp1,manterg, return);
      #else
      encode2_DF(sign1,exp1,manthi,mantlo, return);
      #endif
    }
#endif

# Liefert zu zwei Double-Float x und y : (/ x y), ein DF.
# DF_DF_durch_DF(x,y)
# can trigger GC
  local object DF_DF_durch_DF (object x, object y);
# Methode:
# x2 = 0.0 -> Error
# x1 = 0.0 -> Ergebnis 0.0
# Sonst:
# Ergebnis-Vorzeichen = xor der beiden Vorzeichen von x1 und x2
# Ergebnis-Exponent = Differenz der beiden Exponenten von x1 und x2
# Ergebnis-Mantisse = Mantisse mant1 / Mantisse mant2, gerundet.
#   mant1/mant2 > 1/2, mant1/mant2 < 2;
#   nach Rundung mant1/mant2 >=1/2, <=2*mant1<2.
#   Bei mant1/mant2 >=1 brauche 52 Nachkommabits,
#   bei mant1/mant2 <1 brauche 53 Nachkommabits.
#   Fürs Runden: brauche ein Rundungsbit (Rest gibt an, ob exakt).
#   Brauche daher insgesamt 54 Nachkommabits von mant1/mant2.
#   Dividiere daher (als Unsigned Integers) 2^54*(2^53*mant1) durch (2^53*mant2).
#   Falls der Quotient >=2^54 ist, runde die letzten zwei Bits weg und
#     erhöhe den Exponenten um 1.
#   Falls der Quotient <2^54 ist, runde das letzte Bit weg. Bei rounding
#     overflow schiebe um ein weiteres Bit nach rechts, incr. Exponenten.
#if defined(FAST_DOUBLE) && !defined(I80386)
  local object DF_DF_durch_DF(x1,x2)
    var object x1;
    var object x2;
    {
      double_to_DF(DF_to_double(x1) / DF_to_double(x2), return ,
                   true, true, # Overflow und subnormale Zahl abfangen
                   !DF_zerop(x1), # ein Ergebnis +/- 0.0
                               # ist genau dann in Wirklichkeit ein Underflow
                   DF_zerop(x2), # Division durch Null abfangen
                   false # kein NaN als Ergebnis möglich
                  );
    }
#else
  local object DF_DF_durch_DF(x1,x2)
    var object x1;
    var object x2;
    {
      # x1,x2 entpacken:
      var signean sign1;
      var sintWL exp1;
      var uintL manthi1;
      var uintL mantlo1;
      var signean sign2;
      var sintWL exp2;
      var uintL manthi2;
      var uintL mantlo2;
      #ifdef intQsize
      var uint64 mant1;
      var uint64 mant2;
      DF_decode(x2, { divide_0(); }, sign2=,exp2=,mant2=);
      DF_decode(x1, { return x1; }, sign1=,exp1=,mant1=);
      #else
      DF_decode2(x2, { divide_0(); }, sign2=,exp2=,manthi2=,mantlo2=);
      DF_decode2(x1, { return x1; }, sign1=,exp1=,manthi1=,mantlo1=);
      #endif
      exp1 = exp1 - exp2; # Differenz der Exponenten
      sign1 = sign1 ^ sign2; # Ergebnis-Vorzeichen
      # Dividiere 2^54*mant1 durch mant2 oder (äquivalent)
      # 2^i*2^54*mant1 durch 2^i*mant2 für irgendein i mit 0 <= i <= 64-53 :
      # wähle i = 64-(DF_mant_len+1), also i+(DF_mant_len+2) = 65.
      #ifdef intQsize
      mant1 = mant1 << 1;
      mant2 = mant2 << (64-(DF_mant_len+1));
      manthi1 = (uint32)(mant1>>32); mantlo1 = (uint32)mant1;
      manthi2 = (uint32)(mant2>>32); mantlo2 = (uint32)mant2;
      #else
      manthi1 = (manthi1 << 1) | (mantlo1 >> 31); mantlo1 = mantlo1 << 1;
      manthi2 = (manthi2 << (64-(DF_mant_len+1))) | (mantlo2 >> ((DF_mant_len+1)-32)); mantlo2 = mantlo2 << (64-(DF_mant_len+1));
      #endif
      var uintD mant1 [128/intDsize];
      var uintD mant2 [64/intDsize];
      #if (intDsize==32) || (intDsize==16) || (intDsize==8)
      set_32_Dptr(mant1,manthi1); set_32_Dptr(&mant1[32/intDsize],mantlo1);
        set_32_Dptr(&mant1[2*32/intDsize],0); set_32_Dptr(&mant1[3*32/intDsize],0);
      set_32_Dptr(mant2,manthi2); set_32_Dptr(&mant2[32/intDsize],mantlo2);
      #else
      {
        var uintD* ptr;
        ptr = &mant1[128/intDsize];
        doconsttimes(64/intDsize, { *--ptr = 0; } );
        doconsttimes(32/intDsize, { *--ptr = (uintD)mantlo1; mantlo1 = mantlo1>>intDsize; } );
        doconsttimes(32/intDsize, { *--ptr = (uintD)manthi1; manthi1 = manthi1>>intDsize; } );
      }
      {
        var uintD* ptr;
        ptr = &mant2[64/intDsize];
        doconsttimes(32/intDsize, { *--ptr = (uintD)mantlo2; mantlo2 = mantlo2>>intDsize; } );
        doconsttimes(32/intDsize, { *--ptr = (uintD)manthi2; manthi2 = manthi2>>intDsize; } );
      }
      #endif
      var uintL mantlo;
      #ifdef intQsize
      var uint64 manthi;
      #else
      var uintL manthi;
      #endif
      { SAVE_NUM_STACK # save num_stack
      {
        var DS q;
        var DS r;
        begin_arith_call();
        UDS_divide(&mant1[0],128/intDsize,&mant1[128/intDsize],
                   &mant2[0],64/intDsize,&mant2[64/intDsize],
                   &q, &r
                  );
        end_arith_call();
        # Es ist 2^53 <= q < 2^55, also q.len = ceiling(54/intDsize)=ceiling(55/intDsize),
        # und r=0 genau dann, wenn r.len=0.
        ASSERT(q.len==ceiling(54,intDsize));
        {
          var uintD* ptr = q.MSDptr;
          manthi = get_max32_Dptr(23,ptr);
          mantlo = get_32_Dptr(&ptr[ceiling(23,intDsize)]);
        }
        # q = 2^32*manthi+mantlo.
        #ifdef intQsize
        manthi = (manthi<<32) | (uint64)mantlo;
        if (manthi >= bit(DF_mant_len+2)) {
          # Quotient >=2^54 -> 2 Bits wegrunden
          var uint64 rounding_bits = manthi & (bit(2)-1);
          exp1 += 1; # Exponenten incrementieren
          manthi = manthi >> 2;
          if ( (rounding_bits < bit(1)) # 00,01 werden abgerundet
               || ( (rounding_bits == bit(1)) # 10
                    && (r.len == 0) # und genau halbzahlig
                    && ((manthi & bit(0)) ==0) # -> round-to-even
             )    ) {
            # abrunden
          } else {
            # aufrunden
            manthi += 1;
          }
        } else {
          # Quotient <2^54 -> 1 Bit wegrunden
          var uint64 rounding_bit = manthi & bit(0);
          manthi = manthi >> 1;
          if ( (rounding_bit == 0) # 0 wird abgerundet
               || ( (r.len == 0) # genau halbzahlig
                    && ((manthi & bit(0)) ==0) # -> round-to-even
             )    ) {
            # abrunden
          } else {
            # aufrunden
            manthi += 1;
            if (manthi >= bit(DF_mant_len+1)) { # rounding overflow?
              manthi = manthi>>1; exp1 = exp1+1;
            }
          }
        }
        #else
        if (manthi >= bit(DF_mant_len-32+2)) {
          # Quotient >=2^54 -> 2 Bits wegrunden
          var uintL rounding_bits = mantlo & (bit(2)-1);
          exp1 += 1; # Exponenten incrementieren
          mantlo = (mantlo >> 2) | (manthi << 30); manthi = manthi >> 2;
          if ( (rounding_bits < bit(1)) # 00,01 werden abgerundet
               || ( (rounding_bits == bit(1)) # 10
                    && (r.len == 0) # und genau halbzahlig
                    && ((mantlo & bit(0)) ==0) # -> round-to-even
             )    ) {
            # abrunden
          } else {
            # aufrunden
            mantlo += 1;
            if (mantlo==0)
              manthi += 1;
          }
        } else {
          # Quotient <2^54 -> 1 Bit wegrunden
          var uintL rounding_bit = mantlo & bit(0);
          mantlo = (mantlo >> 1) | (manthi << 31); manthi = manthi >> 1;
          if ( (rounding_bit == 0) # 0 wird abgerundet
               || ( (r.len == 0) # genau halbzahlig
                    && ((mantlo & bit(0)) ==0) # -> round-to-even
             )    ) {
            # abrunden
          } else {
            # aufrunden
            mantlo += 1;
            if (mantlo==0) {
              manthi += 1;
              if (manthi >= bit(DF_mant_len-32+1)) { # rounding overflow?
                manthi = manthi>>1; exp1 = exp1+1;
              }
            }
          }
        }
        #endif
      }
      RESTORE_NUM_STACK } # num_stack back
      #ifdef intQsize
      encode_DF(sign1,exp1,manthi, return);
      #else
      encode2_DF(sign1,exp1,manthi,mantlo, return);
      #endif
    }
#endif

# Liefert zu einem Double-Float x>=0 : (sqrt x), ein DF.
# DF_sqrt_DF(x)
# can trigger GC
  local object DF_sqrt_DF (object x);
# Methode:
# x = 0.0 -> Ergebnis 0.0
# Ergebnis-Vorzeichen := positiv,
# Ergebnis-Exponent := ceiling(e/2),
# Ergebnis-Mantisse:
#   Bilde aus [1,m51,...,m0,(55 Nullbits)] bei geradem e,
#         aus [0,1,m51,...,m0,(54 Nullbits)] bei ungeradem e
#   die Ganzzahl-Wurzel, eine 54-Bit-Zahl mit einer führenden 1.
#   Runde das letzte Bit weg:
#     Bit 0 = 0 -> abrunden,
#     Bit 0 = 1 und Wurzel exakt -> round-to-even,
#     Bit 0 = 1 und Rest >0 -> aufrunden.
#   Dabei um ein Bit nach rechts schieben.
#   Bei Aufrundung auf 2^53 (rounding overflow) Mantisse um 1 Bit nach rechts
#     schieben und Exponent incrementieren.
#ifdef intQsize # && (intDsize==32)
  local object DF_sqrt_DF(x)
    var object x;
    {
      # x entpacken:
      var sintWL exp;
      var uint64 mantx;
      DF_decode(x, { return x; }, _EMA_,exp=,mantx=);
      # Um die 128-Bit-Ganzzahl-Wurzel ausnutzen zu können, fügen wir beim
      # Radikanden 74 bzw. 75 statt 54 bzw. 55 Nullbits an.
      if (exp & bit(0)) {
        # e ungerade
        mantx = mantx << (63-(DF_mant_len+1)); exp = exp+1;
      } else {
        # e gerade
        mantx = mantx << (64-(DF_mant_len+1));
      }
      exp = exp >> 1; # exp := exp/2
      {
        var uintD mant [128/intDsize];
        set_32_Dptr(mant,(uint32)(mantx>>32)); set_32_Dptr(&mant[32/intDsize],(uint32)mantx);
        set_32_Dptr(&mant[2*32/intDsize],0); set_32_Dptr(&mant[3*32/intDsize],0);
        { SAVE_NUM_STACK # save num_stack
        var DS wurzel;
        var bool exactp;
        UDS_sqrt(&mant[0],128/intDsize,&mant[128/intDsize], &wurzel, exactp=);
        # wurzel = isqrt(2^74_75 * mant), eine 64-Bit-Zahl.
        {
          var uintD* ptr = wurzel.MSDptr;
          mantx = ((uint64)get_32_Dptr(ptr) << 32) | (uint64)get_32_Dptr(&ptr[32/intDsize]);
        }
        # Die hinteren 63-DF_mant_len Bits wegrunden:
        if ( ((mantx & bit(62-DF_mant_len)) ==0) # Bit 10 =0 -> abrunden
             || ( ((mantx & (bit(62-DF_mant_len)-1)) ==0) # Bit 10 =1 und Bits 9..0 >0 -> aufrunden
                  && exactp                   # Bit 10 =1 und Bits 9..0 =0, aber Rest -> aufrunden
                  # round-to-even, je nach Bit 11 :
                  && ((mantx & bit(63-DF_mant_len)) ==0)
           )    ) {
          # abrunden
          mantx = mantx >> (63-DF_mant_len);
        } else {
          # aufrunden
          mantx = mantx >> (63-DF_mant_len);
          mantx += 1;
          if (mantx >= bit(DF_mant_len+1)) { # rounding overflow?
            mantx = mantx>>1; exp = exp+1;
          }
        }
        RESTORE_NUM_STACK } # num_stack back
      }
      encode_DF(0,exp,mantx, return);
    }
#else
  local object DF_sqrt_DF(x)
    var object x;
    {
      # x entpacken:
      var sintWL exp;
      var uint32 manthi;
      var uint32 mantlo;
      DF_decode2(x, { return x; }, _EMA_,exp=,manthi=,mantlo=);
      # Um die 128-Bit-Ganzzahl-Wurzel ausnutzen zu können, fügen wir beim
      # Radikanden 74 bzw. 75 statt 54 bzw. 55 Nullbits an.
      if (exp & bit(0)) {
        # e ungerade
        manthi = (manthi << (63-(DF_mant_len+1))) | (mantlo >> ((DF_mant_len+1)-31));
        mantlo = mantlo << (63-(DF_mant_len+1));
        exp = exp+1;
      } else {
        # e gerade
        manthi = (manthi << (64-(DF_mant_len+1))) | (mantlo >> ((DF_mant_len+1)-32));
        mantlo = mantlo << (64-(DF_mant_len+1));
      }
      exp = exp >> 1; # exp := exp/2
      {
        var uintD mant [128/intDsize];
        #if (intDsize==32) || (intDsize==16) || (intDsize==8)
        set_32_Dptr(mant,manthi); set_32_Dptr(&mant[32/intDsize],mantlo);
          set_32_Dptr(&mant[2*32/intDsize],0); set_32_Dptr(&mant[3*32/intDsize],0);
        #else
        {
          var uintD* ptr;
          ptr = &mant[128/intDsize];
          doconsttimes(64/intDsize, { *--ptr = 0; } );
          doconsttimes(32/intDsize, { *--ptr = (uintD)mantlo; mantlo = mantlo>>intDsize; } );
          doconsttimes(32/intDsize, { *--ptr = (uintD)manthi; manthi = manthi>>intDsize; } );
        }
        #endif
        {
          SAVE_NUM_STACK # num_stack retten
          var DS wurzel;
          var bool exactp;
          UDS_sqrt(&mant[0],128/intDsize,&mant[128/intDsize], &wurzel, exactp=);
          # wurzel = isqrt(2^74_75 * mant), eine 64-Bit-Zahl.
          {
            var uintD* ptr = wurzel.MSDptr;
            manthi = get_32_Dptr(ptr); mantlo = get_32_Dptr(&ptr[32/intDsize]);
          }
          # Die hinteren 63-DF_mant_len Bits wegrunden:
          if ( ((mantlo & bit(62-DF_mant_len)) ==0) # Bit 10 =0 -> abrunden
               || ( ((mantlo & (bit(62-DF_mant_len)-1)) ==0) # Bit 10 =1 und Bits 9..0 >0 -> aufrunden
                    && exactp                   # Bit 10 =1 und Bits 9..0 =0, aber Rest -> aufrunden
                    # round-to-even, je nach Bit 11 :
                    && ((mantlo & bit(63-DF_mant_len)) ==0)
             )    ) {
            # abrunden
            mantlo = (mantlo >> (63-DF_mant_len)) | (manthi << (DF_mant_len-32+1));
            manthi = manthi >> (63-DF_mant_len);
          } else {
            # aufrunden
            mantlo = (mantlo >> (63-DF_mant_len)) | (manthi << (DF_mant_len-32+1));
            manthi = manthi >> (63-DF_mant_len);
            mantlo += 1;
            if (mantlo==0) {
              manthi += 1;
              if (manthi >= bit(DF_mant_len-32+1)) { # rounding overflow?
                manthi = manthi>>1; exp = exp+1;
              }
            }
          }
          RESTORE_NUM_STACK # num_stack zurück
        }
      }
      encode2_DF(0,exp,manthi,mantlo, return);
    }
#endif

# DF_to_I(x) wandelt ein Double-Float x, das eine ganze Zahl darstellt,
# in ein Integer um.
# can trigger GC
  local object DF_to_I (object x);
# Methode:
# Falls x=0.0, Ergebnis 0.
# Sonst (ASH Vorzeichen*Mantisse (e-53)).
#ifdef intQsize
  local object DF_to_I(x)
    var object x;
    {
      # x entpacken:
      var signean sign;
      var sintWL exp;
      var uint64 mant;
      DF_decode(x, { return Fixnum_0; }, sign=,exp=,mant=);
      exp = exp-(DF_mant_len+1);
      # mant mit Vorzeichen versehen:
      if (!(sign==0))
        mant = -mant;
      # in ein Bignum umwandeln und shiften:
      return I_I_ash_I( Q_to_I(mant), L_to_FN(exp) );
    }
#else
  local object DF_to_I(x)
    var object x;
    {
      # x entpacken:
      var signean sign;
      var sintWL exp;
      var uint32 manthi;
      var uint32 mantlo;
      DF_decode2(x, { return Fixnum_0; }, sign=,exp=,manthi=,mantlo=);
      exp = exp-(DF_mant_len+1);
      # mant mit Vorzeichen versehen:
      if (!(sign==0)) {
        manthi = -manthi;
        mantlo = -mantlo;
        if (!(mantlo==0))
          manthi -= 1;
      }
      # in ein Bignum umwandeln und shiften:
      return I_I_ash_I( L2_to_I(manthi,mantlo), L_to_FN(exp) );
    }
#endif

# I_to_DF(x) wandelt ein Integer x in ein Double-Float um und rundet dabei.
# can trigger GC
  local object I_to_DF (object x);
# Methode:
# x=0 -> Ergebnis 0.0
# Merke Vorzeichen von x.
# x:=(abs x)
# Exponent:=(integer-length x)
#   Greife die 54 höchstwertigen Bits heraus (angeführt von einer 1).
#   Runde das letzte Bit weg:
#     Bit 0 = 0 -> abrunden,
#     Bit 0 = 1 und Rest =0 -> round-to-even,
#     Bit 0 = 1 und Rest >0 -> aufrunden.
#   Dabei um ein Bit nach rechts schieben.
#   Bei Aufrundung auf 2^53 (rounding overflow) Mantisse um 1 Bit nach rechts
#     schieben und Exponent incrementieren.
  local object I_to_DF(x)
    var object x;
    {
      if (eq(x,Fixnum_0))
        return DF_0;
      var signean sign = R_sign(x); # Vorzeichen
      if (!(sign==0))
        x = I_minus_I(x); # bei x<0: x := (- x)
      var uintL exp = I_integer_length(x); # (integer-length x)
      # NDS zu x>0 bilden:
      var uintD* MSDptr;
      var uintC len;
      I_to_NDS_nocopy(x, MSDptr=,len=,);
      # MSDptr/len/LSDptr ist die NDS zu x, len>0.
      # Führende Digits holen: Brauche DF_mant_len+1 Bits, dazu intDsize
      # Bits (die NDS kann mit bis zu intDsize Nullbits anfangen).
      # Dann werden diese Bits um (exp mod intDsize) nach rechts geschoben.
      var uintD msd = *MSDptr++; # erstes Digit
      var uint32 msdd = 0; # weitere min(len-1,32/intDsize) Digits
      var uint32 msddf = 0; # weitere maximal 32/intDsize Digits
      #define NEXT_DIGIT(i)  \
        {                                                     \
          if (--len == 0) goto ok;                            \
          msdd |= (uint32)(*MSDptr++) << (32-(i+1)*intDsize); \
        }
      DOCONSTTIMES(32/intDsize,NEXT_DIGIT);
      #undef NEXT_DIGIT
      #define NEXT_DIGIT(i)  \
        {                                                      \
          if (--len == 0) goto ok;                             \
          msddf |= (uint32)(*MSDptr++) << (32-(i+1)*intDsize); \
        }
      DOCONSTTIMES(32/intDsize,NEXT_DIGIT);
      #undef NEXT_DIGIT
      --len; ok:
      # Die NDS besteht aus msd, msdd, msddf und len weiteren Digits.
      # Das höchste in 2^64*msd+2^32*msdd+msddf gesetzte Bit ist Bit Nummer
      # 63 + (exp mod intDsize).
      var uintL shiftcount = exp % intDsize;
      #ifdef intQsize
      var uint64 mant = # führende 64 Bits
        (shiftcount==0
          ? (((uint64)msdd << 32) | (uint64)msddf)
          : (((uint64)msd << (64-shiftcount)) | ((uint64)msdd << (32-shiftcount)) | ((uint64)msddf >> shiftcount))
        );
      # Das höchste in mant gesetzte Bit ist Bit Nummer 63.
      if ( ((mant & bit(62-DF_mant_len)) ==0) # Bit 10 =0 -> abrunden
           || ( ((mant & (bit(62-DF_mant_len)-1)) ==0) # Bit 10 =1 und Bits 9..0 =0
                && ((msddf & (bit(shiftcount)-1)) ==0) # und weitere Bits aus msddf =0
                && (!test_loop_up(MSDptr,len)) # und alle weiteren Digits =0
                # round-to-even, je nach Bit 11 :
                && ((mant & bit(63-DF_mant_len)) ==0)
         )    ) {
        # abrunden
        mant = mant >> (63-DF_mant_len);
      } else {
        # aufrunden
        mant = mant >> (63-DF_mant_len);
        mant += 1;
        if (mant >= bit(DF_mant_len+1)) { # rounding overflow?
          mant = mant>>1; exp = exp+1;
        }
      }
      encode_DF(sign,(sintL)exp,mant, return);
      #else
      var uint32 manthi; # führende 32 Bits
      var uint32 mantlo; # nächste 32 Bits
      if (shiftcount==0) {
        manthi = msdd; mantlo = msddf;
      } else {
        manthi = ((uint32)msd << (32-shiftcount)) | (msdd >> shiftcount);
        mantlo = (msdd << (32-shiftcount)) | (msddf >> shiftcount);
      }
      # Das höchste in mant gesetzte Bit ist Bit Nummer 63.
      if ( ((mantlo & bit(62-DF_mant_len)) ==0) # Bit 10 =0 -> abrunden
           || ( ((mantlo & (bit(62-DF_mant_len)-1)) ==0) # Bit 10 =1 und Bits 9..0 =0
                && ((msddf & (bit(shiftcount)-1)) ==0) # und weitere Bits aus msddf =0
                && (!test_loop_up(MSDptr,len)) # und alle weiteren Digits =0
                # round-to-even, je nach Bit 11 :
                && ((mantlo & bit(63-DF_mant_len)) ==0)
         )    ) {
        # abrunden
        mantlo = (mantlo >> (63-DF_mant_len)) | (manthi << (DF_mant_len-32+1));
        manthi = manthi >> (63-DF_mant_len);
      } else {
        # aufrunden
        mantlo = (mantlo >> (63-DF_mant_len)) | (manthi << (DF_mant_len-32+1));
        manthi = manthi >> (63-DF_mant_len);
        mantlo += 1;
        if (mantlo==0) {
          manthi += 1;
          if (manthi >= bit(DF_mant_len-32+1)) { # rounding overflow?
            manthi = manthi>>1; exp = exp+1;
          }
        }
      }
      encode2_DF(sign,(sintL)exp,manthi,mantlo, return);
      #endif
    }

# RA_to_DF(x) wandelt eine rationale Zahl x in ein Double-Float um
# und rundet dabei.
# can trigger GC
  local object RA_to_DF (object x);
# Methode:
# x ganz -> klar.
# x = +/- a/b mit Integers a,b>0:
#   Seien n,m so gewählt, dass
#     2^(n-1) <= a < 2^n, 2^(m-1) <= b < 2^m.
#   Dann ist 2^(n-m-1) < a/b < 2^(n-m+1).
#   Berechne n=(integer-length a) und m=(integer-length b) und
#   floor(2^(-n+m+54)*a/b) :
#   Bei n-m>=54 dividiere a durch (ash b (n-m-54)),
#   bei n-m<54 dividiere (ash a (-n+m+54)) durch b.
#   Der erste Wert ist >=2^53, <2^55.
#   Falls er >=2^54 ist, runde 2 Bits weg,
#   falls er <2^54 ist, runde 1 Bit weg.
  local object RA_to_DF(x)
    var object x;
    {
      if (RA_integerp(x))
        return I_to_DF(x);
      # x Ratio
      pushSTACK(TheRatio(x)->rt_den); # b
      var signean sign = RT_sign(x); # Vorzeichen
      x = TheRatio(x)->rt_num; # +/- a
      if (!(sign==0))
        x = I_minus_I(x); # Betrag nehmen, liefert a
      pushSTACK(x);
      # Stackaufbau: b, a.
      var sintL lendiff = I_integer_length(x) # (integer-length a)
                          - I_integer_length(STACK_1); # (integer-length b)
      if (lendiff > DF_exp_high-DF_exp_mid) # Exponent >= n-m > Obergrenze ?
        fehler_overflow(); # -> Overflow
      if (lendiff < DF_exp_low-DF_exp_mid-2) { # Exponent <= n-m+2 < Untergrenze ?
        if (underflow_allowed()) {
          fehler_underflow(); # -> Underflow
        } else {
          skipSTACK(2); return DF_0;
        }
      }
      var object zaehler;
      var object nenner;
      if (lendiff >= DF_mant_len+2) {
        # n-m-54>=0
        nenner = I_I_ash_I(STACK_1,fixnum((uint32)(lendiff - (DF_mant_len+2)))); # (ash b n-m-54)
        zaehler = popSTACK(); # a
        skipSTACK(1);
      } else {
        zaehler = I_I_ash_I(popSTACK(),fixnum((uint32)((DF_mant_len+2) - lendiff))); # (ash a -n+m+54)
        nenner = popSTACK(); # b
      }
      # Division zaehler/nenner durchführen:
      I_I_divide_I_I(zaehler,nenner);
      # Stackaufbau: q, r.
      # 2^53 <= q < 2^55, also ist q Bignum mit ceiling(55/intDsize) Digits.
      var uintD* ptr = &TheBignum(STACK_1)->data[0];
      #ifdef intQsize
      var uint64 mant =
        ((uint64)get_max32_Dptr(23,ptr) << 32)
        | (uint64)get_32_Dptr(&ptr[ceiling(23,intDsize)]);
      if (mant >= bit(DF_mant_len+2)) {
        # 2^54 <= q < 2^55, schiebe um 2 Bits nach rechts
        var uint64 rounding_bits = mant & (bit(2)-1);
        lendiff = lendiff+1; # Exponent := n-m+1
        mant = mant >> 2;
        if ( (rounding_bits < bit(1)) # 00,01 werden abgerundet
             || ( (rounding_bits == bit(1)) # 10
                  && (eq(STACK_0,Fixnum_0)) # und genau halbzahlig (r=0)
                  && ((mant & bit(0)) ==0) # -> round-to-even
           )    )
          # abrunden
          goto ab;
        else
          # aufrunden
          goto auf;
      } else {
        var uint64 rounding_bit = mant & bit(0);
        mant = mant >> 1;
        if ( (rounding_bit == 0) # 0 wird abgerundet
             || ( (eq(STACK_0,Fixnum_0)) # genau halbzahlig (r=0)
                  && ((mant & bit(0)) ==0) # -> round-to-even
           )    )
          # abrunden
          goto ab;
        else
          # aufrunden
          goto auf;
      }
     auf:
      mant += 1;
      if (mant >= bit(DF_mant_len+1)) { # rounding overflow?
        mant = mant>>1; lendiff = lendiff+1;
      }
     ab:
      skipSTACK(2);
      # Fertig.
      encode_DF(sign,lendiff,mant, return);
      #else
      var uint32 manthi = get_max32_Dptr(23,ptr);
      var uint32 mantlo = get_32_Dptr(&ptr[ceiling(23,intDsize)]);
      if (manthi >= bit(DF_mant_len-32+2)) {
        # 2^54 <= q < 2^55, schiebe um 2 Bits nach rechts
        var uintL rounding_bits = mantlo & (bit(2)-1);
        lendiff = lendiff+1; # Exponent := n-m+1
        mantlo = (mantlo >> 2) | (manthi << 30); manthi = manthi >> 2;
        if ( (rounding_bits < bit(1)) # 00,01 werden abgerundet
             || ( (rounding_bits == bit(1)) # 10
                  && (eq(STACK_0,Fixnum_0)) # und genau halbzahlig (r=0)
                  && ((mantlo & bit(0)) ==0) # -> round-to-even
           )    )
          # abrunden
          goto ab;
        else
          # aufrunden
          goto auf;
      } else {
        var uintL rounding_bit = mantlo & bit(0);
        mantlo = (mantlo >> 1) | (manthi << 31); manthi = manthi >> 1;
        if ( (rounding_bit == 0) # 0 wird abgerundet
             || ( (eq(STACK_0,Fixnum_0)) # genau halbzahlig (r=0)
                  && ((mantlo & bit(0)) ==0) # -> round-to-even
           )    )
          # abrunden
          goto ab;
        else
          # aufrunden
          goto auf;
      }
     auf:
      mantlo += 1;
      if (mantlo==0) {
        manthi += 1;
        if (manthi >= bit(DF_mant_len-32+1)) { # rounding overflow?
          manthi = manthi>>1; lendiff = lendiff+1;
        }
      }
     ab:
      skipSTACK(2);
      # Fertig.
      encode2_DF(sign,lendiff,manthi,mantlo, return);
      #endif
    }

