# BYTE-Operationen auf Integers

# Konstruktor: (I_I_Byte size position), wo size und position Integers sind.
# kann GC ausl�sen
  local object I_I_Byte (object size, object position);
  local object I_I_Byte(size,position)
    var object size;
    var object position;
    { if (!(I_fixnump(size) && !R_minusp(size)))
        { pushSTACK(size); # Wert f�r Slot DATUM von TYPE-ERROR
          bad_args:
          pushSTACK(O(type_posfixnum)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
          pushSTACK(position); pushSTACK(size);
          fehler(type_error,
                 DEUTSCH ? "Die Argumente zu BYTE m�ssen Fixnums >=0 sein: ~, ~" :
                 ENGLISH ? "The arguments to BYTE must be fixnums >=0: ~, ~" :
                 FRANCAIS ? "Les arguments de BYTE doivent �tre des entiers FIXNUM >=0 : ~, ~" :
                 ""
                );
        }
      elif (!(I_fixnump(position) && !R_minusp(position)))
        { pushSTACK(position); # Wert f�r Slot DATUM von TYPE-ERROR
          goto bad_args;
        }
      else
        { # size, position sind Fixnums >=0, brauchen nicht gerettet zu werden
          var object new_byte = allocate_byte(); # neues Byte allozieren
          # und f�llen:
          TheByte(new_byte)->byte_size = size;
          TheByte(new_byte)->byte_position = position;
          return new_byte;
    }   }

# Fehler, wenn Argument kein Byte.
  nonreturning_function(local, fehler_byte, (object bad));
  local void fehler_byte(bad)
    var object bad;
    { pushSTACK(bad); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(S(byte)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(bad);
      fehler(type_error,
             DEUTSCH ? "~ ist kein BYTE-Specifier." :
             ENGLISH ? "~ is not a BYTE specifier" :
             FRANCAIS ? "~ n'est pas une sp�cification de BYTE." :
             ""
            );
    }

# Zugriffsfunktionen:

# Liefert (BYTE-SIZE byte). Das Argument wird �berpr�ft.
  local object Byte_size (object obj);
  local object Byte_size(obj)
    var object obj;
    { if (bytep(obj))
        return TheByte(obj)->byte_size;
        else
        fehler_byte(obj);
    }

# Liefert (BYTE-POSITION byte). Das Argument wird �berpr�ft.
  local object Byte_position (object obj);
  local object Byte_position(obj)
    var object obj;
    { if (bytep(obj))
        return TheByte(obj)->byte_position;
        else
        fehler_byte(obj);
    }

# Byte_to_L_L(byte, size=,position=); wandelt das Byte byte (eine Variable)
# um in size und position, beides uintL >=0, <2^oint_data_len.
  #define Byte_to_L_L(byte, size_zuweisung,position_zuweisung)  \
    { if bytep(byte)                                            \
        { size_zuweisung posfixnum_to_L(TheByte(byte)->byte_size); \
          position_zuweisung posfixnum_to_L(TheByte(byte)->byte_position); \
        }                                                       \
        else                                                    \
        fehler_byte(byte);                                      \
    }

# fullbyte_I(p,q) liefert zu p,q die Zahl 2^q-2^p als Integer,
# wobei p und q uintL sind. Bei p<=q ist das Ergebnis also
# ein Integer >=0, bei dem genau die Bits p,...,q-1 gesetzt sind.
# kann GC ausl�sen
  local object fullbyte_I (uintL p, uintL q);
  local object fullbyte_I(p,q)
    var uintL p;
    var uintL q;
    { if (p==q)
        return Fixnum_0; # p=q -> 0 als Ergebnis
        else
        { var object Iq = UL_to_I(q); # q als Integer >=0
          var object I2q = I_I_ash_I(Fixnum_1,Iq); # 2^q als Integer
          pushSTACK(I2q); # retten
         {var object Ip = UL_to_I(p); # p als Integer >=0
          var object I2p = I_I_ash_I(Fixnum_minus1,Ip); # - 2^p als Integer
          I2q = popSTACK();
          return I_I_plus_I(I2p,I2q); # 2^q und -2^p addieren
    }   }}

# Extrahiere die Bits p,...,q-1 der Zahl x,
# wobei 0 <= p <= q <= l = (integer-length x).
# Ergebnis (wie bei LDB) ein Integer >=0.
# kann GC ausl�sen
  local object ldb_extract (object x, uintL p, uintL q);
  local object ldb_extract(x,p,q)
    var object x;
    var uintL p;
    var uintL q;
    { SAVE_NUM_STACK # num_stack retten
      var uintD* MSDptr;
      var uintC len;
      var uintD* LSDptr;
      I_to_NDS_nocopy(x, MSDptr=,len=,LSDptr=); # NDS zu x bilden
      begin_arith_call();
      # MSDptr erh�hen und len erniedrigen, so da� len = ceiling(q/intDsize) wird:
      { var uintL qD = ceiling(q,intDsize); # ceiling(q/intDsize)
        # wegen q<=l ist qD = ceiling(q/intDsize) <= ceiling((l+1)/intDsize) = len, also
        # pa�t qD ebenso wie len in ein uintC.
        MSDptr += ((uintL)len - qD); # MSDptr um len-qD Digits erh�hen
        len = qD; # len um len-qD erniedrigen
      }
      # LSDptr und len um floor(p/intDsize) erniedrigen:
      { var uintL pD = floor(p,intDsize); # floor(p/intDsize)
        LSDptr -= pD;
        len -= pD;
      }
      # Jetzt enth�lt MSDptr/len/LSDptr genau die ma�geblichen Digits.
     {var uintD* newMSDptr;
      { var uintL i = p%intDsize; # p mod intDsize
        # Kopiere sie und schiebe sie dabei um i Bits nach rechts:
        num_stack_need_1((uintL)len, newMSDptr=,); # neue UDS newMSDptr/len/..
        if (i==0)
          { copy_loop_up(MSDptr,newMSDptr,len); }
          else
          { shiftrightcopy_loop_up(MSDptr,newMSDptr,len,i,0); }
      }
      # newMSDptr/len/.. = geschobene Kopie der ma�geblichen Digits
      # Ausblenden der Bits mit Nummern >= q-p:
      { var uintL bitcount = intDsize*(uintL)len - (q-p);
        # Anzahl vorne auszublendender Bits ( >=0, <= intDsize-1 + intDsize-1 )
        if (bitcount>=intDsize)
          { bitcount -= intDsize; newMSDptr += 1; len -= 1; } # intDsize Bits ausblenden
        # Noch 0 <= bitcount < intDsize Bits auszublenden:
        newMSDptr[0] &= (uintD)(bitm(intDsize-bitcount)-1);
      }
      # Jetzt enth�lt die UDS newMSDptr/len/.. die extrahierten Bits.
      end_arith_call();
      RESTORE_NUM_STACK # num_stack (vorzeitig) zur�ck
      return UDS_to_I(newMSDptr,len); # UDS in Integer umwandeln
    }}

# (LDB byte n), wo n ein Integer ist.
# kann GC ausl�sen
  local object I_Byte_ldb_I (object n, object b);
  local object I_Byte_ldb_I(n,b)
    var object n;
    var object b;
    { # Methode:
      # (ldb (byte s p) n) extrahiere die Bits p,...,p+s-1 von n.
      # l:=(integer-length n)
      # Falls l <= p :
      #   Falls n>=0: 0, falls n<0: 2^s - 1 (s Einsenbits).
      # Falls p <= l :
      #   q:=min(p+s,l).
      #   Extrahiere die Bits p,...,q-1 von n.
      #   Falls p+s>l und n<0, f�ge p+s-l Einsenbits an (addiere 2^s-2^(l-p)).
      var uintL s;
      var uintL p;
      var uintL l;
      Byte_to_L_L(b, s=,p=); # size s und position p bestimmen
      l = I_integer_length(n); # l = (integer-length n)
      if (l<=p)
        # l<=p
        if (!(R_minusp(n)))
          # n>=0
          return Fixnum_0; # 0 als Ergebnis
          else
          # n<0
          return fullbyte_I(0,s); # 2^s-2^0 als Ergebnis
        else
        # l>p
        { var object erg;
          pushSTACK(n); # n retten
         {var uintL ps = p+s;
          # Bits p,...,q-1 mit q = min(p+s,l) extrahieren:
          erg = ldb_extract(n,p,(ps<l ? ps : l));
          n = popSTACK(); # n zur�ck
         }
         {var uintL lp = l-p;
          if ((s>lp)&&(R_minusp(n))) # s>l-p und n<0 ?
            { pushSTACK(erg); # erg retten
             {var object erg2 = fullbyte_I(lp,s);
              # erg2 = Integer-Zahl mit gesetzten Bits l-p,...,s-1
              erg = popSTACK(); # erg zur�ck
              return I_I_logior_I(erg,erg2); # logisches Oder aus beiden
              # (logisches Exklusiv-Oder oder Addition ginge auch)
            }}
            else
            return erg;
      } }}

# Teste, ob eines der Bits p,...,q-1 der Zahl x /=0 ist,
# wobei 0 <= p <= q <= l = (integer-length x).
# Ergebnis (wie bei LDB-TEST) FALSE wenn nein, TRUE wenn ja.
  local boolean ldb_extract_test (object x, uintL p, uintL q);
  local boolean ldb_extract_test(x,p,q)
    var object x;
    var uintL p;
    var uintL q;
    { var uintD* MSDptr;
      var uintC len;
      var uintD* LSDptr;
      I_to_NDS_nocopy(x, MSDptr=,len=,LSDptr=); # NDS zu x bilden
      # MSDptr erh�hen und len erniedrigen, so da� len = ceiling(q/intDsize) wird:
      { var uintL qD = ceiling(q,intDsize); # ceiling(q/intDsize)
        # wegen q<=l ist qD = ceiling(q/intDsize) <= ceiling((l+1)/intDsize) = len, also
        # pa�t qD ebenso wie len in ein uintC.
        MSDptr += ((uintL)len - qD); # MSDptr um len-qD Digits erh�hen
        len = qD; # len um len-qD erniedrigen
      }
      # LSDptr und len um floor(p/intDsize) erniedrigen:
      { var uintL pD = p/intDsize; # floor(p/intDsize)
        LSDptr -= pD;
        len -= pD;
      }
      # Jetzt enth�lt MSDptr/len/LSDptr genau die ma�geblichen Digits.
      if (len==0) return FALSE; # len=0 -> keine Bits abzutesten
      q = ((q-1)%intDsize); # q := intDsize - (intDsize*ceiling(q/intDsize) - q) - 1
      p = p%intDsize; # p := p - intDsize*floor(p/intDsize)
      # Jetzt ist 0 <= q < intDsize, 0 <= p < intDsize.
      # Vom ersten Digit m�ssen die vorderen intDsize-1-q Bits unber�cksichtigt bleiben.
      # Ein AND 2^(q+1)-1 erreicht dies.
      # Vom letzten Digit m�ssen die hinteren p Bits unber�cksichtigt bleiben.
      # Ein AND -2^p erreicht dies.
      if (--len==0)
        # 1 Digit ma�geblich, wird von beiden Seiten angeschnitten:
        # Ein AND 2^(q+1)-2^p erreicht dies.
        if (!(((uintD)(bitm(q+1)-bit(p)) & *MSDptr) == 0))
          return TRUE;
          else
          return FALSE;
      # mindestens 2 Digits. Teste erst die Randdigits, dann die inneren:
      if (!(((*MSDptr++ & (uintD)(bitm(q+1)-1)) == 0) &&
            ((*--LSDptr & (uintD)(minus_bit(p))) == 0)
         ) )
        return TRUE;
      len--; # die beiden Randdigits sind jetzt abgezogen.
      if (test_loop_up(MSDptr,len)) { return TRUE; } else { return FALSE; }
    }

# I_Byte_ldb_test(n,byte) f�hrt (LDB-TEST byte n) aus, wobei n ein Integer ist.
# Ergebnis: FALSE wenn nein (also alle fraglichen Bits =0), TRUE wenn ja.
  local boolean I_Byte_ldb_test (object n, object b);
  local boolean I_Byte_ldb_test(n,b)
    var object n;
    var object b;
    { # Methode:
      # (ldb-test (byte s p) n)
      # Falls s=0: =0.
      # Falls s>0:
      #   l:=(integer-length n)
      #   Falls l <= p : Falls n>=0, =0, denn Bits p+s-1..p sind =0.
      #                  Falls n<0, /=0, denn Bits p+s-1..p sind =1.
      #   Falls p < l :
      #     Falls p+s>l, /=0, denn bei n>=0 ist Bit l-1 =1,
      #                       und bei n<0 sind Bits p+s-1..l =1.
      #     Falls p+s<=l,
      #       extrahiere die Bits p,...,p+s-1 von n und teste sie.
      var uintL s;
      var uintL p;
      var uintL l;
      Byte_to_L_L(b, s=,p=); # size s und position p bestimmen
      if (s==0) return FALSE;
      l = I_integer_length(n); # l = (integer-length n)
      if (l<=p)
        # l<=p
        if (!(R_minusp(n)))
          return FALSE; # n>=0
          else
          return TRUE; # n<0
        else
        # l>p
        { var uintL ps = p+s;
          if (ps>l) # p+s>l ?
            return TRUE;
          # Bits p,...,q-1 mit q = min(p+s,l) = p+s extrahieren und testen:
          return ldb_extract_test(n,p,ps);
    }   }

# Extrahiere die Bits p,...,q-1 der Zahl x,
# wobei 0 <= p <= q <= l = (integer-length x).
# Ergebnis (wie bei MASK-FIELD) ein Integer >=0.
# kann GC ausl�sen
  local object mkf_extract (object x, uintL p, uintL q);
  local object mkf_extract(x,p,q)
    var object x;
    var uintL p;
    var uintL q;
    { SAVE_NUM_STACK # num_stack retten
      var uintD* MSDptr;
      var uintC len;
      var uintD* LSDptr;
      I_to_NDS_nocopy(x, MSDptr=,len=,LSDptr=); # NDS zu x bilden
      # MSDptr erh�hen und len erniedrigen, so da� len = ceiling(q/intDsize) wird:
      { var uintL qD = ceiling(q,intDsize); # ceiling(q/intDsize)
        # wegen q<=l ist qD = ceiling(q/intDsize) <= ceiling((l+1)/intDsize) = len, also
        # pa�t qD ebenso wie len in ein uintC.
        MSDptr += ((uintL)len - qD); # MSDptr um len-qD Digits erh�hen
        len = qD; # len um len-qD erniedrigen
      }
     {# Platz (len Digits) f�r die neue UDS bereitstellen:
      var uintD* newMSDptr;
      num_stack_need_1((uintL)len, newMSDptr = ,); # Platz belegen
      {var uintL pD = p/intDsize; # floor(p/intDsize), pa�t in ein uintC
       # Kopiere len-pD Digits aus der DS zu x heraus:
       var uintD* midptr = copy_loop_up(MSDptr,newMSDptr,len-(uintC)pD);
       # L�sche p-intDsize*floor(p/intDsize) Bits im Digit unterhalb von midptr:
       {var uintL p_D = p%intDsize;
        if (!(p_D==0)) { midptr[-1] &= minus_bit(p_D); }
       }
       # L�sche pD Digits dar�ber:
       clear_loop_up(midptr,pD);
      }
      # L�sche intDsize*ceiling(q/intDsize)-q Bits im ersten Digit:
      {var uintL q_D = q%intDsize;
       if (!(q_D==0))
         { newMSDptr[0] &= (uintD)((1L<<q_D)-1); } # intDsize-q_D Bits l�schen
      }
      # Jetzt enth�lt die UDS newMSDptr/len/.. die extrahierten Bits.
      RESTORE_NUM_STACK # num_stack (vorzeitig) zur�ck
      return UDS_to_I(newMSDptr,len);
    }}

# (MASK-FIELD byte n), wo n ein Integer ist.
# kann GC ausl�sen
  local object I_Byte_mask_field_I (object n, object b);
  local object I_Byte_mask_field_I(n,b)
    var object n;
    var object b;
    { # Methode:
      # (mask-field (byte s p) n) extrahiere die Bits p,...,p+s-1 von n.
      # l:=(integer-length n)
      # Falls l <= p :
      #   Falls n>=0: 0, falls n<0: 2^(p+s) - 2^p (s Einsenbits).
      # Falls p <= l :
      #   q:=min(p+s,l).
      #   Extrahiere die Bits p,...,q-1 von n.
      #   Falls p+s>l und n<0, f�ge p+s-l Einsenbits an (addiere 2^(p+s)-2^l).
      var uintL s;
      var uintL p;
      var uintL l;
      Byte_to_L_L(b, s=,p=); # size s und position p bestimmen
     {var uintL ps = p+s;
      l = I_integer_length(n); # l = (integer-length n)
      if (l<=p)
        # l<=p
        if (!(R_minusp(n)))
          # n>=0
          return Fixnum_0; # 0 als Ergebnis
          else
          # n<0
          return fullbyte_I(p,ps); # 2^(p+s)-2^p als Ergebnis
        else
        # l>p
        { var object erg;
          pushSTACK(n); # n retten
          # Bits p,...,q-1 mit q = min(p+s,l) extrahieren:
          erg = mkf_extract(n,p,(ps<l ? ps : l));
          n = popSTACK(); # n zur�ck
          if ((ps>l)&&(R_minusp(n))) # p+s>l und n<0 ?
            { pushSTACK(erg); # erg retten
             {var object erg2 = fullbyte_I(l,ps);
              # erg2 = Integer-Zahl mit gesetzten Bits l,...,p+s-1
              erg = popSTACK(); # erg zur�ck
              return I_I_logior_I(erg,erg2); # logisches Oder aus beiden
              # (logisches Exklusiv-Oder oder Addition ginge auch)
            }}
            else
            return erg;
    }}  }

# (DEPOSIT-FIELD new byte n), wo n und new Integers sind.
# kann GC ausl�sen
  local object I_I_Byte_deposit_field_I (object newbyte, object n, object b);
  local object I_I_Byte_deposit_field_I(newbyte,n,b)
    var object newbyte;
    var object n;
    var object b;
    { # Methode:
      # (DEPOSIT-FIELD newbyte (byte s p) integer)
      #  = (logxor integer
      #            (ash (logxor (ldb (byte s p) newbyte) (ldb (byte s p) integer))
      #                 p
      #    )       )
      pushSTACK(n); # integer in den Stack
      pushSTACK(b); # (byte s p) in den Stack
     {var object temp1 = I_Byte_ldb_I(newbyte,b); # (ldb (byte s p) newbyte)
      pushSTACK(temp1); # in den Stack
      temp1 = I_Byte_ldb_I(STACK_2,STACK_1); # (ldb (byte s p) integer)
      temp1 = I_I_logxor_I(popSTACK(),temp1); # beides mit LOGXOR verkn�pfen
      temp1 = I_I_ash_I(temp1,Byte_position(popSTACK())); # (ash ... p)
      return I_I_logxor_I(popSTACK(),temp1); # mit integer LOGXORen
    }}

# (DPB new byte n), wo n und new Integers sind.
# kann GC ausl�sen
  local object I_I_Byte_dpb_I (object newbyte, object n, object b);
  local object I_I_Byte_dpb_I(newbyte,n,b)
    var object newbyte;
    var object n;
    var object b;
    { # Methode:
      # (DPB newbyte (byte s p) integer)
      # = (DEPOSIT-FIELD (ASH newbyte p) (byte s p) integer)
      pushSTACK(n); # integer in den Stack
      pushSTACK(b); # (byte s p) in den Stack
     {var object temp1 = I_I_ash_I(newbyte,Byte_position(b));
      b = popSTACK();
      n = popSTACK();
      return I_I_Byte_deposit_field_I(temp1,n,b);
    }}

