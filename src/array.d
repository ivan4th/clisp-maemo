# Arrayfunktionen von CLISP
# Bruno Haible 2.9.1997

#include "lispbibl.c"
#include "arilev0.c" # f�r bit_op, definiert auch mulu24 und mulu32_unchecked

# UP: Kopiert einen Simple-Vector
# copy_svector(vector)
# > vector : Simple-Vector
# < ergebnis : neuer Simple-Vector desselben Inhalts
# kann GC ausl�sen
  global object copy_svector (object vector);
  global object copy_svector(vector)
    var object vector;
    { var uintL length = Svector_length(vector);
      pushSTACK(vector);
     {var object newvector = allocate_vector(length); # gleichlanger Vektor
      vector = popSTACK();
      # Inhalt von vector in newvector kopieren:
      if (!(length==0))
        { var object* ptr1 = &TheSvector(vector)->data[0];
          var object* ptr2 = &TheSvector(newvector)->data[0];
          dotimespL(length,length, { *ptr2++ = *ptr1++; } );
        }
      return newvector;
    }}

# UP: Kopiert einen Simple-Bit-Vector
# copy_sbvector(vector)
# > vector : Simple-Bit-Vector
# < ergebnis : neuer Simple-Bit-Vector desselben Inhalts
# kann GC ausl�sen
  global object copy_sbvector (object vector);
  global object copy_sbvector(vector)
    var object vector;
    { var uintL length = Sbvector_length(vector);
      pushSTACK(vector);
     {var object newvector = allocate_bit_vector(length); # gleichlanger Vektor
      vector = popSTACK();
      if (!(length==0))
        { var uintB* ptr1 = &TheSbvector(vector)->data[0];
          var uintB* ptr2 = &TheSbvector(newvector)->data[0];
          dotimespL(length,ceiling(length,8), { *ptr2++ = *ptr1++; } );
        }
      return newvector;
    }}

LISPFUNN(copy_simple_vector,1)
# (SYS::%COPY-SIMPLE-VECTOR vector) liefert eine Kopie des Simple-Vektor vector.
  { var object obj = popSTACK();
    if (!simple_vector_p(obj)) { fehler_kein_svector(S(copy_simple_vector),obj); }
    value1 = copy_svector(obj); mv_count=1;
  }

# UP: Bestimmt die aktive L�nge eines Vektors (wie in LENGTH)
# vector_length(vector)
# > vector: ein Vektor
# < ergebnis: seine L�nge als uintL
  global uintL vector_length (object vector);
  global uintL vector_length(vector)
    var object vector;
    { if (array_simplep(vector))
        return Sarray_length(vector);
      # Nicht-simpler Array
      { var Iarray addr = TheIarray(vector);
        var uintL offset = offsetofa(iarray_,dims);
        if (iarray_flags(addr) & bit(arrayflags_dispoffset_bit))
          offset += sizeof(uintL);
        # Bei addr+offset fangen die Dimensionen an.
        if (iarray_flags(addr) & bit(arrayflags_fillp_bit)) # evtl. Fillpointer
          offset += sizeof(uintL);
        return *(uintL*)pointerplus(addr,offset);
    } }

# Wandelt element-type in einen der Standard-Typen um
# und liefert seinen Elementtyp-Code.
# eltype_code(element_type)
# > element_type: Type-Specifier
# < ergebnis: Elementtyp-Code Atype_xxx
# Standard-Typen sind die m�glichen Ergebnisse von ARRAY-ELEMENT-TYPE
# (Symbole T, BIT, STRING-CHAR und Listen (UNSIGNED-BYTE n)).
# Das Ergebnis ist ein Obertyp von element-type.
# kann GC ausl�sen
  global uintB eltype_code (object element_type);
  global uintB eltype_code(obj)
    var object obj;
    # Bei jeder Modifikation auch upgraded-array-element-type in type.lsp anpassen!
    {
      #if 0
      # Vorl�ufige Methode:
      # obj mit den Symbolen BIT, STRING-CHAR vergleichen.
      # Default ist T (garantiert ein Obertyp von allem).
      # Besser w�re:
      # (subtypep obj 'BIT) und (subtypep obj 'STRING-CHAR) abfragen.
      if (eq(obj,S(bit))) { return Atype_Bit; } # Symbol BIT ?
      elif (eq(obj,S(string_char))) { return Atype_String_Char; } # Symbol STRING-CHAR ?
      else # alles andere wird als T interpretiert
        { STACK_5 = S(t); return Atype_T; }
      #else
      # (cond ((eq obj 'BIT) Atype_Bit)
      #       ((eq obj 'STRING-CHAR) Atype_String_Char)
      #       ((eq obj 'T) Atype_T)
      #       (t (multiple-value-bind (low high) (sys::subtype-integer obj))
      #            ; Es gilt (or (null low) (subtypep obj `(INTEGER ,low ,high)))
      #            (if (and (integerp low) (not (minusp low)) (integerp high))
      #              (let ((l (integer-length high)))
      #                ; Es gilt (subtypep obj `(UNSIGNED-BYTE ,l))
      #                (cond ((<= l 1) Atype_Bit)
      #                      ((<= l 2) Atype_2Bit)
      #                      ((<= l 4) Atype_4Bit)
      #                      ((<= l 8) Atype_8Bit)
      #                      ((<= l 16) Atype_16Bit)
      #                      ((<= l 32) Atype_32Bit)
      #                      (t Atype_T)
      #              ) )
      #              Atype_T
      # )     )  ) )
      if (eq(obj,S(bit))) { return Atype_Bit; } # Symbol BIT ?
      elif (eq(obj,S(string_char))) { return Atype_String_Char; } # Symbol STRING-CHAR ?
      elif (eq(obj,S(t))) { return Atype_T; } # Symbol T ?
      pushSTACK(subr_self); # subr_self retten
      pushSTACK(obj); funcall(S(subtype_integer),1); # (SYS::SUBTYPE-INTEGER obj)
      subr_self = popSTACK(); # subr_self zur�ck
      if ((mv_count>1) && integerp(value1) && positivep(value1) && integerp(value2))
        { var uintL l = I_integer_length(value2); # (INTEGER-LENGTH high)
          if (l<=1) return Atype_Bit;
          if (l<=2) return Atype_2Bit;
          if (l<=4) return Atype_4Bit;
          if (l<=8) return Atype_8Bit;
          if (l<=16) return Atype_16Bit;
          if (l<=32) return Atype_32Bit;
        }
      return Atype_T;
      #endif
    }

# UP: erzeugt einen Bytevektor
# allocate_byte_vector(atype,len)
# > uintB atype: Atype_nBit
# > uintL len: L�nge (in n-Bit-Bl�cken)
# < ergebnis: neuer Semi-Simple-Bytevektor dieser L�nge
# kann GC ausl�sen
  global object allocate_byte_vector (uintB atype, uintL len);
  global object allocate_byte_vector(atype,len)
    var uintB atype;
    var uintL len;
    { {var object new_sbvector = allocate_bit_vector(len<<atype);
       # neuer Simple-Bit-Vektor passender L�nge
       pushSTACK(new_sbvector); # retten
      }
      {var object new_array = allocate_iarray(atype,1,Array_type_bvector);
                                   # Flags: keine, Elementtyp Atype_nBit, Rang=1
       TheIarray(new_array)->totalsize =
         TheIarray(new_array)->dims[0] = len; # L�nge und Total-Size eintragen
       TheIarray(new_array)->data = popSTACK(); # Datenvektor eintragen
       return new_array;
    } }

# UP: Bildet einen Simple-Vektor mit gegebenen Elementen.
# vectorof(len)
# > uintC len: gew�nschte Vektorl�nge
# > auf STACK: len Objekte, erstes zuoberst
# < ergebnis: Simple-Vektor mit diesen Objekten
# Erh�ht STACK
# ver�ndert STACK, kann GC ausl�sen
  global object vectorof (uintC len);
  global object vectorof(len)
    var uintC len;
    { var object new_vector = allocate_vector(len);
      if (len > 0)
        { var object* topargptr = STACK STACKop len;
          var object* argptr = topargptr;
          var object* ptr = &TheSvector(new_vector)->data[0];
          dotimespC(len,len, { *ptr++ = NEXT(argptr); } );
          set_args_end_pointer(topargptr);
        }
      return new_vector;
    }

LISPFUN(vector,0,0,rest,nokey,0,NIL) # (VECTOR {object}), CLTL S. 290
  { value1 = vectorof(argcount); mv_count=1; }

# Vom Standpunkt der Speicherstruktur her ist "der Datenvektor" eines
# nicht-simplen Arrays  TheIarray(array)->data.
# Vom Standpunkt der Arrayfunktionen her bekommt man "den Datenvektor" eines
# Arrays, indem man so lange  TheIarray(array)->data  nimmt, bis
# (bei Elementtypen T, BIT, STRING-CHAR) array ein simpler Vektor oder
# (bei Byte-Arrays) array ein nicht-simpler Vektor ohne arrayflags_..._bits,
# aber TheIarray(array)->data ein Simple-Bit-Vektor ist.

# UP: verfolgt Kette von displaced-Arrays und addiert displaced-Offsets
#     f�r Zugriff auf ein einzelnes Array-Element
# notsimple_displace(array,&index);
# > array: Nicht-simpler Array
# > index: Row-major-index
# < ergebnis: Datenvektor
# < index: absoluter Index in den Datenvektor
# Es wird �berpr�ft, ob das adressierte Array-Element in jedem der Arrays liegt.
# Es wird nicht �berpr�ft, ob die Kette in einen Zyklus l�uft.
  local object notsimple_displace (object array, uintL* index);
  local object notsimple_displace(array,index)
    var object array;
    var uintL* index;
    { loop
        { if (*index >= TheIarray(array)->totalsize) goto fehler_bad_index;
          if (!(Iarray_flags(array) & bit(arrayflags_displaced_bit)))
            goto notdisplaced;
          # Array ist displaced
          *index += TheIarray(array)->dims[0]; # displaced-Offset addieren
          array = TheIarray(array)->data; # n�chster Array
          if (array_simplep(array)) goto simple; # n�chster Array simple?
        }
      notdisplaced:
        # Array ist nicht displaced, aber auch nicht simple
        if (Iarray_flags(array) & bit(arrayflags_notbytep_bit))
          { array = TheIarray(array)->data; # Datenvektor ist garantiert simple
            simple:
            # Array ist simple
            if (*index >= Sarray_length(array)) goto fehler_bad_index;
            return array;
          }
          else
          # Byte-Array
          { if (!simple_bit_vector_p(TheIarray(array)->data))
              array = TheIarray(array)->data;
            # letzter Datenvektor erreicht
            if (*index >= TheIarray(array)->totalsize) goto fehler_bad_index;
            return array;
          }
      fehler_bad_index:
        fehler(error, # ausf�hrlicher??
               DEUTSCH ? "Index in Array zu gro�." :
               ENGLISH ? "index too large" :
               FRANCAIS ? "Index dans matrice trop grand." :
               ""
              );
    }

# Fehler, wenn ein displaced Array nicht mehr in seinen Ziel-Array pa�t
  nonreturning_function(local, fehler_displaced_inconsistent, (void));
  local void fehler_displaced_inconsistent()
    { fehler(error,
             DEUTSCH ? "Der Ziel-Array eines Displaced-Array wurde durch Adjustieren verkleinert." :
             ENGLISH ? "An array has been shortened by adjusting it while another array was displaced to it." :
             FRANCAIS ? "La matrice cible d'un �displaced-array� a �t� rapetiss�e par ajustement." :
             ""
            );
    }

# UP: Liefert zu einem Array gegebener Gr��e den Datenvektor und den Offset.
# �berpr�ft auch, ob alle Elemente des Arrays physikalisch vorhanden sind.
# iarray_displace_check(array,size,&index)
# > object array: indirekter Array
# > uintL size: Gr��e
# < ergebnis: Datenvektor
# < index: wird um den Offset in den Datenvektor erh�ht.
  global object iarray_displace_check (object array, uintL size, uintL* index);
  global object iarray_displace_check(array,size,index)
    var object array;
    var uintL size;
    var uintL* index;
    { loop
        { if (*index+size > TheIarray(array)->totalsize) goto fehler_bad_index;
          if (!(Iarray_flags(array) & bit(arrayflags_displaced_bit)))
            goto notdisplaced;
          # Array ist displaced
          *index += TheIarray(array)->dims[0]; # displaced-Offset addieren
          array = TheIarray(array)->data; # n�chster Array
          if (array_simplep(array)) goto simple; # n�chster Array simple?
        }
      notdisplaced:
        # Array ist nicht displaced, aber auch nicht simple
        if (Iarray_flags(array) & bit(arrayflags_notbytep_bit))
          { array = TheIarray(array)->data; # Datenvektor ist garantiert simple
            simple:
            # Array ist simple
            if (*index+size > Sarray_length(array)) goto fehler_bad_index;
            return array;
          }
          else
          # Byte-Array
          { if (!simple_bit_vector_p(TheIarray(array)->data))
              array = TheIarray(array)->data;
            # letzter Datenvektor erreicht
            if (*index+size > TheIarray(array)->totalsize) goto fehler_bad_index;
            return array;
          }
      fehler_bad_index:
        fehler_displaced_inconsistent();
    }

# UP: Liefert zu einem Array gegebener Gr��e den Datenvektor und den Offset.
# �berpr�ft auch, ob alle Elemente des Arrays physikalisch vorhanden sind.
# array_displace_check(array,size,&index)
# > object array: Array
# > uintL size: Gr��e
# < ergebnis: Datenvektor
# < index: wird um den Offset in den Datenvektor erh�ht.
  global object array_displace_check (object array, uintL size, uintL* index);
  global object array_displace_check(array,size,index)
    var object array;
    var uintL size;
    var uintL* index;
    { if (array_simplep(array)) goto simple; # Array simple?
      loop
        { if (*index+size > TheIarray(array)->totalsize) goto fehler_bad_index;
          if (!(Iarray_flags(array) & bit(arrayflags_displaced_bit)))
            goto notdisplaced;
          # Array ist displaced
          *index += TheIarray(array)->dims[0]; # displaced-Offset addieren
          array = TheIarray(array)->data; # n�chster Array
          if (array_simplep(array)) goto simple; # n�chster Array simple?
        }
      notdisplaced:
        # Array ist nicht displaced, aber auch nicht simple
        if (Iarray_flags(array) & bit(arrayflags_notbytep_bit))
          { array = TheIarray(array)->data; # Datenvektor ist garantiert simple
            simple:
            # Array ist simple
            if (*index+size > Sarray_length(array)) goto fehler_bad_index;
            return array;
          }
          else
          # Byte-Array
          { if (!simple_bit_vector_p(TheIarray(array)->data))
              array = TheIarray(array)->data;
            # letzter Datenvektor erreicht
            if (*index+size > TheIarray(array)->totalsize) goto fehler_bad_index;
            return array;
          }
      fehler_bad_index:
        fehler_displaced_inconsistent();
    }

# Fehlermeldung
# > obj: Nicht-Array
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(local, fehler_array, (object obj));
  local void fehler_array(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(S(array)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist kein Array." :
             ENGLISH ? "~: ~ is not an array" :
             FRANCAIS ? "~ : ~ n'est pas une matrice." :
             ""
            );
    }

# �berpr�ft Array-Argument.
# > object: Argument
# > subr_self: Aufrufer (ein SUBR)
# test_array(object)
  #define test_array(object_from_test_array)  \
    if (!arrayp(object_from_test_array)) { fehler_array(object_from_test_array); }

# Liefert den Rang eines Arrays.
# > array: ein Array
# < ergebnis: Rang als Fixnum
# arrayrank(array)
  #define arrayrank(array)  \
    (mdarrayp(array)                                         \
     ? fixnum((uintL)Iarray_rank(array)) # allgemeiner Array \
     : Fixnum_1 # Vektor hat Rang 1                          \
    )

# Fehlermeldung
# > array : Array
# > argcount : (fehlerhafte) Anzahl Subscripts
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(local, fehler_subscript_anz, (object array, uintC argcount));
  local void fehler_subscript_anz(array,argcount)
    var object array;
    var uintC argcount;
    { pushSTACK(arrayrank(array));
      pushSTACK(array);
      pushSTACK(fixnum(argcount));
      pushSTACK(TheSubr(subr_self)->name);
      fehler(error,
             DEUTSCH ? "~: Es wurden ~ Subscripts angegeben, ~ hat aber den Rang ~." :
             ENGLISH ? "~: got ~ subscripts, but ~ has rank ~" :
             FRANCAIS ? "~: ~ indices donn�s mais ~ est de rang ~." :
             ""
            );
    }

# Fehlermeldung
# > argcount : Anzahl der Subscripts, �ber ihnen der Array
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(local, fehler_subscript_type, (uintC argcount));
  local void fehler_subscript_type(argcount)
    var uintC argcount;
    { var object list = listof(argcount); # Subscript-Liste
      # Nun ist STACK_0 der Array.
      pushSTACK(list);
      pushSTACK(TheSubr(subr_self)->name);
      fehler(error,
             DEUTSCH ? "~: Subscripts ~ f�r ~ sind nicht vom Typ `(INTEGER 0 (,ARRAY-DIMENSION-LIMIT))." :
             ENGLISH ? "~: subscripts ~ for ~ are not of type `(INTEGER 0 (,ARRAY-DIMENSION-LIMIT))" :
             FRANCAIS ? "~: Les indices ~ pour ~ ne sont pas de type `(INTEGER 0 (,ARRAY-DIMENSION-LIMIT))." :
             ""
            );
    }

# Fehlermeldung
# > argcount : Anzahl der Subscripts, �ber ihnen der Array
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(local, fehler_subscript_range, (uintC argcount, uintL subscript, uintL bound));
  local void fehler_subscript_range(argcount,subscript,bound)
    var uintC argcount;
    var uintL subscript;
    var uintL bound;
    { var object list = listof(argcount); # Subscript-Liste
      pushSTACK(list);
      # Stackaufbau: Array, subscript-list.
      pushSTACK(UL_to_I(subscript)); # Wert f�r Slot DATUM von TYPE-ERROR
      { var object tmp;
        pushSTACK(S(integer)); pushSTACK(Fixnum_0); pushSTACK(UL_to_I(bound));
        tmp = listof(1); pushSTACK(tmp); tmp = listof(3);
        pushSTACK(tmp); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      }
      pushSTACK(STACK_(1+2));
      pushSTACK(STACK_(0+3));
      pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: Subscripts ~ f�r ~ liegen nicht im erlaubten Bereich." :
             ENGLISH ? "~: subscripts ~ for ~ are out of range" :
             FRANCAIS ? "~: Les indices ~ pour ~ ne sont pas dans l'intervalle permis." :
             ""
            );
    }

# �berpr�ft Subscripts f�r einen AREF/STORE-Zugriff, entfernt sie vom STACK
# und liefert den Row-Major-Index (>=0, <arraysize_limit).
# test_subscripts(array,argptr,argcount)
# > array : nicht-simpler Array
# > argptr : Pointer �ber die Subscripts
# > argcount : Anzahl der Subscripts
# < ergebnis : row-major-index
  local uintL test_subscripts (object array, object* argptr, uintC argcount);
  local uintL test_subscripts(array,argptr,argcount)
    var object array;
    var object* argptr;
    var uintC argcount;
    { var object* args_pointer = argptr; # argptr retten f�r sp�ter
      # Anzahl der Subscripts �berpr�fen:
      if (!(argcount == Iarray_rank(array))) # sollte = Rang sein
        fehler_subscript_anz(array,argcount);
      # Subscripts selbst �berpr�fen:
     {var uintL row_major_index = 0;
      var const uintL* dimptr = &TheIarray(array)->dims[0]; # Zeiger auf Dimensionen
      if (Iarray_flags(array) & bit(arrayflags_dispoffset_bit))
        dimptr++; # evtl. Displaced-Offset �berspringen
      { var uintC count;
        dotimesC(count,argcount,
          { var object subscriptobj = NEXT(argptr); # Subscript als Objekt
            if (!(posfixnump(subscriptobj))) # Subscript mu� Fixnum>=0 sein.
              fehler_subscript_type(argcount);
           {var uintL subscript = posfixnum_to_L(subscriptobj); # als uintL
            var uintL dim = *dimptr++; # entsprechende Dimension
            if (!(subscript<dim)) # Subscript mu� kleiner als Dimension sein
              fehler_subscript_range(argcount,subscript,dim);
            # Bilde row_major_index := row_major_index*dim+subscript:
            row_major_index =
              mulu32_unchecked(row_major_index,dim)+subscript;
            # Das gibt keinen �berlauf, weil dies
            # < Produkt der bisherigen Dimensionen
            # <= Produkt aller Dimensionen < arraysize_limit <= 2^32
            # ist. (Ausnahme: Falls eine sp�tere Dimension =0 ist.
            # Aber dann gibt's nachher sowieso eine Fehlermeldung.)
          }});
      }
      set_args_end_pointer(args_pointer);
      return row_major_index;
    }}

# Fehlermeldung
# > STACK_1: Array (meist Vektor)
# > STACK_0: (fehlerhafter) Index
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(local, fehler_index_type, (void));
  local void fehler_index_type()
    { pushSTACK(STACK_0); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(O(type_array_index)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(STACK_(1+2));
      pushSTACK(STACK_(0+3));
      pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: Index ~ f�r ~ ist nicht vom Typ `(INTEGER 0 (,ARRAY-DIMENSION-LIMIT))." :
             ENGLISH ? "~: index ~ for ~ is not of type `(INTEGER 0 (,ARRAY-DIMENSION-LIMIT))" :
             FRANCAIS ? "~: L'indice ~ pour ~ n'est pas de type `(INTEGER 0 (,ARRAY-DIMENSION-LIMIT))." :
             ""
            );
    }

# Fehlermeldung
# > STACK_1: Array (meist Vektor)
# > STACK_0: (fehlerhafter) Index
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(local, fehler_index_range, (uintL bound));
  local void fehler_index_range(bound)
    var uintL bound;
    { var object tmp;
      pushSTACK(STACK_0); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(S(integer)); pushSTACK(Fixnum_0); pushSTACK(UL_to_I(bound));
      tmp = listof(1); pushSTACK(tmp); tmp = listof(3);
      pushSTACK(tmp); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(STACK_(1+2));
      pushSTACK(STACK_(0+3));
      pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: Index ~ f�r ~ ist zu gro�." :
             ENGLISH ? "~: index ~ for ~ is out of range" :
             FRANCAIS ? "~: L'index ~ pour ~ est trop grand." :
             ""
            );
    }

# �berpr�ft einen Index f�r einen AREF/STORE-Zugriff in einen simplen Vektor.
# test_index()
# > STACK_1: simpler Vektor
# > STACK_0: Index
# < ergebnis: Index als uintL
  local uintL test_index (void);
  local uintL test_index()
    { if (!posfixnump(STACK_0)) # Index mu� Fixnum>=0 sein.
        fehler_index_type();
     {var uintL index = posfixnum_to_L(STACK_0); # Index als uintL
      if (!(index < Sarray_length(STACK_1))) # Index mu� kleiner als L�nge sein
        fehler_index_range(Sarray_length(STACK_1));
      return index;
    }}

# �berpr�ft Subscripts f�r einen AREF/STORE-Zugriff, entfernt sie vom STACK
# und liefert den Row-Major-Index (>=0, <arraysize_limit) und den Datenvektor.
# subscripts_to_index(array,argptr,argcount, &index)
# > array : nicht-simpler Array
# > argptr : Pointer �ber die Subscripts
# > argcount : Anzahl der Subscripts
# < index : Index in den Datenvektor
# < ergebnis : der Datenvektor
  local object subscripts_to_index (object array, object* argptr, uintC argcount, uintL* index_);
  local object subscripts_to_index(array,argptr,argcount,index_)
    var object array;
    var object* argptr;
    var uintC argcount;
    var uintL* index_;
    { test_array(array); # Array �berpr�fen
      if (array_simplep(array))
        # simpler Vektor, wird getrennt behandelt:
        { # Anzahl der Subscripts �berpr�fen:
          if (!(argcount == 1)) # sollte = 1 sein
            fehler_subscript_anz(array,argcount);
          # Subscript selbst �berpr�fen:
          *index_ = test_index(); # Index = Row-Major-Index = Subscript
          skipSTACK(1); return array;
        }
        else
        # nicht-simpler Array
        { # Subscripts �berpr�fen, Row-Major-Index errechnen, STACK aufr�umen:
          *index_ = test_subscripts(array,argptr,argcount);
          # Datenvektor und absoluten Index holen:
          return notsimple_displace(array,&(*index_));
        }
    }

# F�hrt einen AREF-Zugriff aus.
# datenvektor_aref(datenvektor,index)
# > datenvektor : ein Datenvektor (simpler Vektor oder semi-simpler Byte-Vektor)
# > index : (gepr�fter) Index in den Datenvektor
# < ergebnis : (AREF datenvektor index)
# kann GC ausl�sen (nur bei 32Bit-Byte-Vektoren)
  global object datenvektor_aref (object datenvektor, uintL index);
  global object datenvektor_aref(datenvektor,index)
    var object datenvektor;
    var uintL index;
    { switch (Array_type(datenvektor))
        { case Array_type_svector: # Simple-Vector
            return TheSvector(datenvektor)->data[index];
          case Array_type_sbvector: # Simple-Bit-Vector
            return ( sbvector_btst(datenvektor,index) ? Fixnum_1 : Fixnum_0 );
          case Array_type_sstring: # Simple-String
            return code_char(TheSstring(datenvektor)->data[index]);
          case Array_type_bvector: # Byte-Vector
            { var uintB* ptr = &TheSbvector(TheIarray(datenvektor)->data)->data[0];
              switch (Iarray_flags(datenvektor) /* & arrayflags_atype_mask */ )
                { case Atype_2Bit:
                    return fixnum((ptr[index/4]>>(2*((~index)%4)))&(bit(2)-1));
                  case Atype_4Bit:
                    return fixnum((ptr[index/2]>>(4*((~index)%2)))&(bit(4)-1));
                  case Atype_8Bit:
                    return fixnum(ptr[index]);
                  case Atype_16Bit:
                    return fixnum(((uint16*)ptr)[index]);
                  case Atype_32Bit:
                    return UL_to_I(((uint32*)ptr)[index]);
                  default: NOTREACHED
            }   }
          default: NOTREACHED
    }   }

# F�hrt einen STORE-Zugriff aus.
# datenvektor_store(datenvektor,index,element)
# > datenvektor : ein Datenvektor (simpler Vektor oder semi-simpler Byte-Vektor)
# > index : (gepr�fter) Index in den Datenvektor
# > element : (ungepr�ftes) einzutragendes Objekt
# > STACK_0 : array (f�r Fehlermeldung)
# > subr_self: Aufrufer (ein SUBR)
  local void datenvektor_store (object datenvektor, uintL index, object element);
  local void datenvektor_store(datenvektor,index,element)
    var object datenvektor;
    var uintL index;
    var object element;
    { switch (Array_type(datenvektor))
        { case Array_type_svector: # Simple-Vector
            { TheSvector(datenvektor)->data[index] = element; return; }
          case Array_type_sbvector: # Simple-Bit-Vector
            { var uintB* addr = &TheSbvector(datenvektor)->data[index/8];
              var uintL bitnummer = (~index)%8; # 7 - (index mod 8)
              if (eq(element,Fixnum_0)) { *addr &= ~bit(bitnummer); return; }
              elif (eq(element,Fixnum_1)) { *addr |= bit(bitnummer); return; }
              else break;
            }
          case Array_type_sstring: # Simple-String
            if (string_char_p(element))
              { TheSstring(datenvektor)->data[index] = char_code(element);
                return;
              }
            else break;
          case Array_type_bvector: # Byte-Vector
            { var uintB* ptr = &TheSbvector(TheIarray(datenvektor)->data)->data[0];
              var uintL wert;
              switch (Iarray_flags(datenvektor) /* & arrayflags_atype_mask */ )
                { case Atype_2Bit:
                    if (posfixnump(element) && ((wert = posfixnum_to_L(element)) < bit(2)))
                      { ptr[index/4] ^= (ptr[index/4] ^ (wert<<(2*((~index)%4)))) & ((bit(2)-1)<<(2*((~index)%4)));
                        return;
                      }
                      else break;
                  case Atype_4Bit:
                    if (posfixnump(element) && ((wert = posfixnum_to_L(element)) < bit(4)))
                      { ptr[index/2] ^= (ptr[index/2] ^ (wert<<(4*((~index)%2)))) & ((bit(4)-1)<<(4*((~index)%2)));
                        return;
                      }
                      else break;
                  case Atype_8Bit:
                    if (posfixnump(element) && ((wert = posfixnum_to_L(element)) < bit(8)))
                      { ptr[index] = wert; return; }
                      else break;
                  case Atype_16Bit:
                    if (posfixnump(element) && ((wert = posfixnum_to_L(element)) < bit(16)))
                      { ((uint16*)ptr)[index] = wert; return; }
                      else break;
                  case Atype_32Bit:
                    ((uint32*)ptr)[index] = I_to_UL(element); # evtl. Fehlermeldung macht I_to_UL
                    return;
                  default: NOTREACHED
                }
              break;
            }
          default: NOTREACHED
        }
      # Objekt war vom falschen Typ.
      { # array bereits in STACK_0
        pushSTACK(element); # Wert f�r Slot DATUM von TYPE-ERROR
        pushSTACK(array_element_type(STACK_(0+1))); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
        pushSTACK(STACK_(0+2)); # array
        pushSTACK(STACK_2); # element
        pushSTACK(TheSubr(subr_self)->name);
        fehler(type_error,
               DEUTSCH ? "~: ~ hat nicht den richtigen Typ f�r ~" :
               ENGLISH ? "~: ~ does not fit into ~, bad type" :
               FRANCAIS ? "~: ~ n'est pas de type correct pour ~." :
               ""
              );
    } }

LISPFUN(aref,1,0,rest,nokey,0,NIL) # (AREF array {subscript}), CLTL S. 290
  { var object array = Before(rest_args_pointer); # Array holen
    # Subscripts verarbeiten und Datenvektor und Index holen:
    var uintL index;
    var object datenvektor = subscripts_to_index(array,rest_args_pointer,argcount, &index);
    # Element des Datenvektors holen:
    value1 = datenvektor_aref(datenvektor,index); mv_count=1;
    skipSTACK(1);
  }

LISPFUN(store,2,0,rest,nokey,0,NIL) # (SYS::STORE array {subscript} object)
                     # = (SETF (AREF array {subscript}) object), CLTL S. 291
  { rest_args_pointer skipSTACKop 1; # Pointer �ber ersten Subscript
   {var object element = popSTACK();
    var object array = Before(rest_args_pointer); # Array holen
    # Subscripts verarbeiten und Datenvektor und Index holen:
    var uintL index;
    var object datenvektor = subscripts_to_index(array,rest_args_pointer,argcount, &index);
    # Element in den Datenvektor eintragen:
    datenvektor_store(datenvektor,index,element);
    value1 = element; mv_count=1;
    skipSTACK(1);
  }}

# Fehlermeldung
# > STACK_1: Nicht-Simple-Vector
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(local, fehler_svector, (void));
  local void fehler_svector()
    { fehler_kein_svector(TheSubr(subr_self)->name,STACK_1); }

LISPFUNN(svref,2) # (SVREF simple-vector index), CLTL S. 291
  { # simple-vector �berpr�fen:
    if (!simple_vector_p(STACK_1)) fehler_svector();
   {# index �berpr�fen:
    var uintL index = test_index();
    # Element holen:
    value1 = TheSvector(STACK_1)->data[index]; mv_count=1;
    skipSTACK(2);
  }}

LISPFUNN(svstore,3) # (SYS::SVSTORE simple-vector index element)
                    # = (SETF (SVREF simple-vector index) element), CLTL S. 291
  { var object element = popSTACK();
    # simple-vector �berpr�fen:
    if (!simple_vector_p(STACK_1)) fehler_svector();
   {# index �berpr�fen:
    var uintL index = test_index();
    # Element ablegen:
    TheSvector(STACK_1)->data[index] = element;
    value1 = element; mv_count=1;
    skipSTACK(2);
  }}

LISPFUNN(psvstore,3) # (SYS::%SVSTORE element simple-vector index)
                     # = (SETF (SVREF simple-vector index) element)
  { # simple-vector �berpr�fen:
    if (!simple_vector_p(STACK_1)) fehler_svector();
   {# index �berpr�fen:
    var uintL index = test_index();
    # Element ablegen:
    value1 = TheSvector(STACK_1)->data[index] = STACK_2; mv_count=1;
    skipSTACK(3);
  }}

LISPFUNN(row_major_aref,2)
# (ROW-MAJOR-AREF array index), CLtL2 S. 450
  { var object array = STACK_1;
    # Array �berpr�fen:
    test_array(array);
    # index �berpr�fen:
    if (!posfixnump(STACK_0)) fehler_index_type();
   {var uintL index = posfixnum_to_L(STACK_0);
    if (!(index < array_total_size(array))) # Index mu� kleiner als Gr��e sein
      fehler_index_range(array_total_size(array));
    if (!array_simplep(array))
      { array = notsimple_displace(array,&index); }
    value1 = datenvektor_aref(array,index); mv_count=1;
    skipSTACK(2);
  }}

LISPFUNN(row_major_store,3)
# (SYS::ROW-MAJOR-STORE array index element)
# = (SETF (ROW-MAJOR-AREF array index) element), CLtL2 S. 450
  { var object element = popSTACK();
    var object array = STACK_1;
    # Array �berpr�fen:
    test_array(array);
    # index �berpr�fen:
    if (!posfixnump(STACK_0)) fehler_index_type();
   {var uintL index = posfixnum_to_L(STACK_0);
    if (!(index < array_total_size(array))) # Index mu� kleiner als Gr��e sein
      fehler_index_range(array_total_size(array));
    if (!array_simplep(array))
      { array = notsimple_displace(array,&index); }
    datenvektor_store(array,index,element);
    value1 = element; mv_count=1;
    skipSTACK(2);
  }}

# UP, liefert den Element-Typ eines Arrays
# array_element_type(array)
# > array : ein Array (simple oder nicht)
# < ergebnis : Element-Typ, eines der Symbole T, BIT, STRING-CHAR, oder eine Liste
# kann GC ausl�sen
  global object array_element_type (object array);
  global object array_element_type(array)
    var object array;
    { switch (Array_type(array))
        { case Array_type_sstring:
          case Array_type_string: # String -> STRING-CHAR
            return S(string_char);
          case Array_type_sbvector: # Simple-Bit-Vector -> BIT
            return S(bit);
          case Array_type_svector:
          case Array_type_vector: # allg. Vector -> T
            return S(t);
          case Array_type_bvector: # Byte-Vector
          case Array_type_mdarray: # allgemeiner Array
            { var uintBWL atype = Iarray_flags(array) & arrayflags_atype_mask;
              switch (atype)
                { case Atype_T:           return S(t);           # T
                  case Atype_Bit:         return S(bit);         # BIT
                  case Atype_String_Char: return S(string_char); # STRING-CHAR
                  case Atype_2Bit:        # (UNSIGNED-BYTE 2)
                  case Atype_4Bit:        # (UNSIGNED-BYTE 4)
                  case Atype_8Bit:        # (UNSIGNED-BYTE 8)
                  case Atype_16Bit:       # (UNSIGNED-BYTE 16)
                  case Atype_32Bit:       # (UNSIGNED-BYTE 32)
                    pushSTACK(S(unsigned_byte));
                    pushSTACK(fixnum(bit(atype)));
                    return listof(2);
                  default: NOTREACHED
            }   }
          default: NOTREACHED
    }   }

LISPFUNN(array_element_type,1) # (ARRAY-ELEMENT-TYPE array), CLTL S. 291
  { var object array = popSTACK();
    test_array(array);
    value1 = array_element_type(array); mv_count=1;
  }

LISPFUNN(array_rank,1) # (ARRAY-RANK array), CLTL S. 292
  { var object array = popSTACK();
    test_array(array);
    value1 = arrayrank(array); mv_count=1;
  }

LISPFUNN(array_dimension,2) # (ARRAY-DIMENSION array axis-number), CLTL S. 292
  { var object axis_number = popSTACK();
    var object array = popSTACK();
    test_array(array);
    if (array_simplep(array))
      # simpler Vektor: axis-number mu� =0 sein, Wert ist dann die L�nge.
      { if (eq(axis_number,Fixnum_0))
          { value1 = fixnum(Sarray_length(array));
            mv_count=1; return;
          }
          else goto fehler_axis;
      }
      else
      # nicht-simpler Array
      { if (posfixnump(axis_number)) # axis-number mu� ein Fixnum >=0,
          { var uintL axis = posfixnum_to_L(axis_number);
            if (axis < (uintL)Iarray_rank(array)) # und <rank sein
              { var uintL* dimptr = &TheIarray(array)->dims[0]; # Zeiger auf Dimensionen
                if (Iarray_flags(array) & bit(arrayflags_dispoffset_bit))
                  dimptr++; # evtl. Displaced-Offset �berspringen
                value1 = fixnum(dimptr[axis]);
                mv_count=1; return;
              }
              else goto fehler_axis;
          }
          else goto fehler_axis;
      }
    fehler_axis:
      pushSTACK(array);
      pushSTACK(axis_number); # Wert f�r Slot DATUM von TYPE-ERROR
      { var object tmp;
        pushSTACK(S(integer)); pushSTACK(Fixnum_0); pushSTACK(arrayrank(array));
        tmp = listof(1); pushSTACK(tmp); tmp = listof(3); pushSTACK(tmp); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      }
      pushSTACK(STACK_2); # array
      pushSTACK(STACK_2); # axis_number
      pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist nicht >= 0 und < dem Rang von ~" :
             ENGLISH ? "~: ~ is not an nonnegative integer less than the rank of ~" :
             FRANCAIS ? "~: ~ n'est pas un entier >= 0 et strictement inf�rieur au rang de ~." :
             ""
            );
  }

# UP, bildet Liste der Dimensionen eines Arrays
# array_dimensions(array)
# > array: ein Array (simple oder nicht)
# < ergebnis: Liste seiner Dimensionen
# kann GC ausl�sen
  global object array_dimensions (object array);
  global object array_dimensions(array)
    var object array;
    { if (array_simplep(array))
        # simpler Vektor, bilde (LIST length)
        { var object len # L�nge als Fixnum (nicht GC-gef�hrdet)
            = fixnum(Sarray_length(array));
          var object new_cons = allocate_cons();
          Car(new_cons) = len; Cdr(new_cons) = NIL;
          return new_cons;
        }
        else
        # nicht-simpler Array: alle Dimensionen als Fixnums auf den STACK,
        # dann eine Liste daraus machen.
        { var uintC rank = Iarray_rank(array);
          var uintL* dimptr = &TheIarray(array)->dims[0]; # Zeiger auf Dimensionen
          if (Iarray_flags(array) & bit(arrayflags_dispoffset_bit))
            dimptr++; # evtl. Displaced-Offset �berspringen
          get_space_on_STACK(sizeof(object)*(uintL)rank); # STACK �berpr�fen
          { var uintC count;
            dotimesC(count,rank,
              { # n�chste Dimension als Fixnum in den Stack:
                pushSTACK(fixnum(*dimptr++));
              });
          }
          return listof(rank); # Liste bilden
        }
    }

LISPFUNN(array_dimensions,1) # (ARRAY-DIMENSIONS array), CLTL S. 292
  { var object array = popSTACK();
    test_array(array);
    value1 = array_dimensions(array); mv_count=1;
  }

# UP, liefert Dimensionen eines Arrays und ihre Teilprodukte
# array_dims_sizes(array,&dims_sizes);
# > array: (echter) Array vom Rang r
# > struct { uintL dim; uintL dimprod; } dims_sizes[r]: Platz f�rs Ergebnis
# < f�r i=1,...r:  dims_sizes[r-i] = { Dim_i, Dim_i * ... * Dim_r }
  global void array_dims_sizes (object array, array_dim_size* dims_sizes);
  global void array_dims_sizes(array,dims_sizes)
    var object array;
    var array_dim_size* dims_sizes;
    { var uintC r = Iarray_rank(array); # Rang
      var const uintL* dimptr = &TheIarray(array)->dims[0]; # Zeiger auf Dimensionen
      if (Iarray_flags(array) & bit(arrayflags_dispoffset_bit))
        dimptr++; # evtl. Displaced-Offset �berspringen
      dimptr = &dimptr[(uintL)r]; # Zeiger hinter die Dimensionen
     {var uintL produkt = 1;
      dotimesC(r,r, # Schleife �ber die r Dimensionen von hinten
        { var uintL dim = *--dimptr; # n�chste Dimension
          produkt = mulu32_unchecked(produkt,dim); # aufs Produkt multiplizieren
          # Das gibt keinen �berlauf, weil dies
          # < Produkt der bisherigen Dimensionen
          # <= Produkt aller Dimensionen < arraysize_limit <= 2^32 ist.
          # (Ausnahme: Falls eine Dimension kleinerer Nummer =0 ist.
          # Aber dann ist das jetzige Produkt sowieso irrelevant, da
          # jede Schleife �ber diese Dimension eine Leerschleife ist.)
          dims_sizes->dim = dim; dims_sizes->dimprod = produkt;
          dims_sizes++;
        });
    }}

LISPFUNN(array_total_size,1) # (ARRAY-TOTAL-SIZE array), CLTL S. 292
  { var object array = popSTACK();
    test_array(array);
    value1 = fixnum(array_total_size(array));
    mv_count=1;
  }

LISPFUN(array_in_bounds_p,1,0,rest,nokey,0,NIL)
# (ARRAY-IN-BOUNDS-P array {subscript}), CLTL S. 292
  { var object* argptr = rest_args_pointer;
    var object array = BEFORE(rest_args_pointer); # Array holen
    test_array(array); # Array �berpr�fen
    if (array_simplep(array))
      # simpler Vektor, wird getrennt behandelt:
      { # Anzahl der Subscripts �berpr�fen:
        if (!(argcount == 1)) # sollte = 1 sein
          fehler_subscript_anz(array,argcount);
        # Subscript selbst �berpr�fen:
        { var object subscriptobj = STACK_0; # Subscript als Objekt
          if (!integerp(subscriptobj)) { fehler_index_type(); } # mu� Integer sein
          # Subscript mu� Fixnum>=0 sein,
          # Subscript als uintL mu� kleiner als L�nge sein:
          if (!( (posfixnump(subscriptobj))
                 && (posfixnum_to_L(subscriptobj) < Sarray_length(array)) ))
            goto no;
          goto yes;
      } }
      else
      # nicht-simpler Array
      { # Anzahl der Subscripts �berpr�fen:
        if (!(argcount == Iarray_rank(array))) # sollte = Rang sein
          fehler_subscript_anz(array,argcount);
        # Subscripts selbst �berpr�fen:
        {var uintL* dimptr = &TheIarray(array)->dims[0]; # Zeiger auf Dimensionen
         if (Iarray_flags(array) & bit(arrayflags_dispoffset_bit))
           dimptr++; # evtl. Displaced-Offset �berspringen
         { var uintC count;
           dotimesC(count,argcount,
             { var object subscriptobj = NEXT(argptr); # Subscript als Objekt
               if (!integerp(subscriptobj)) { fehler_subscript_type(argcount); } # mu� Integer sein
               # Subscript mu� Fixnum>=0 sein,
               # Subscript als uintL mu� kleiner als die entsprechende Dimension sein:
               if (!( (posfixnump(subscriptobj))
                      && (posfixnum_to_L(subscriptobj) < *dimptr++) ))
                 goto no;
             });
        }}
        goto yes;
      }
    yes: value1 = T; mv_count=1; set_args_end_pointer(rest_args_pointer); return;
    no: value1 = NIL; mv_count=1; set_args_end_pointer(rest_args_pointer); return;
  }

LISPFUN(array_row_major_index,1,0,rest,nokey,0,NIL)
# (ARRAY-ROW-MAJOR-INDEX array {subscript}), CLTL S. 293
  { var object array = Before(rest_args_pointer); # Array holen
    var uintL index;
    test_array(array); # Array �berpr�fen
    if (array_simplep(array))
      # simpler Vektor, wird getrennt behandelt:
      { # Anzahl der Subscripts �berpr�fen:
        if (!(argcount == 1)) # sollte = 1 sein
          fehler_subscript_anz(array,argcount);
        # Subscript selbst �berpr�fen:
        test_index();
        value1 = popSTACK(); mv_count=1; # Index = Row-Major-Index = Subscript
        skipSTACK(1);
      }
      else
      # nicht-simpler Array
      { # Subscripts �berpr�fen, Row-Major-Index errechnen, STACK aufr�umen:
        index = test_subscripts(array,rest_args_pointer,argcount);
        # Index als Fixnum zur�ck:
        value1 = fixnum(index); mv_count=1;
        skipSTACK(1);
      }
  }

LISPFUNN(adjustable_array_p,1) # (ADJUSTABLE-ARRAY-P array), CLTL S. 293
  { var object array = popSTACK(); # Argument holen
    test_array(array); # Array �berpr�fen
    if (array_simplep(array))
      goto no; # simpler Vektor, ist nicht adjustable
      else
      if (Iarray_flags(array) & bit(arrayflags_adjustable_bit))
        goto yes;
        else
        goto no;
    yes: value1 = T; mv_count=1; return;
    no:  value1 = NIL; mv_count=1; return;
  }

LISPFUNN(array_displacement,1) # (ARRAY-DISPLACEMENT array), CLHS
  { var object array = popSTACK(); # Argument holen
    test_array(array); # Array �berpr�fen
    if (!array_simplep(array)
        && (Iarray_flags(array) & bit(arrayflags_displaced_bit))
       )
      { value1 = TheIarray(array)->data; # n�chster Array
        value2 = fixnum(TheIarray(array)->dims[0]); # displaced-Offset
      }
    else
      { value1 = NIL; value2 = Fixnum_0; }
    mv_count=2;
  }

# Fehlermeldung
# fehler_bit_array()
# > STACK_0: Array, der kein Bit-Array ist
  nonreturning_function(local, fehler_bit_array, (void));
  local void fehler_bit_array()
    { pushSTACK(STACK_0); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(O(type_array_bit)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(STACK_(0+2));
      pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist kein Bit-Array." :
             ENGLISH ? "~: ~ is not an array of bits" :
             FRANCAIS ? "~: ~ n'est pas une matrice de bits." :
             ""
            );
    }

LISPFUN(bit,1,0,rest,nokey,0,NIL) # (BIT bit-array {subscript}), CLTL S. 293
  { var object array = Before(rest_args_pointer); # Array holen
    # Subscripts verarbeiten und Datenvektor und Index holen:
    var uintL index;
    var object datenvektor = subscripts_to_index(array,rest_args_pointer,argcount, &index);
    if (!(simple_bit_vector_p(datenvektor)))
      fehler_bit_array();
    # Datenvektor ist ein Simple-Bit-Vector. Element des Datenvektors holen:
    value1 = ( sbvector_btst(datenvektor,index) ? Fixnum_1 : Fixnum_0 ); mv_count=1;
    skipSTACK(1);
  }

LISPFUN(sbit,1,0,rest,nokey,0,NIL) # (SBIT bit-array {subscript}), CLTL S. 293
  { var object array = Before(rest_args_pointer); # Array holen
    # Subscripts verarbeiten und Datenvektor und Index holen:
    var uintL index;
    var object datenvektor = subscripts_to_index(array,rest_args_pointer,argcount, &index);
    if (!(simple_bit_vector_p(datenvektor)))
      fehler_bit_array();
    # Datenvektor ist ein Simple-Bit-Vector. Element des Datenvektors holen:
    value1 = ( sbvector_btst(datenvektor,index) ? Fixnum_1 : Fixnum_0 ); mv_count=1;
    skipSTACK(1);
  }

# F�r Unterprogramme f�r Bitvektoren:
  # Man arbeitet mit Bit-Bl�cken � bitpack Bits.
  # uint_bitpack ist ein unsigned Integer mit bitpack Bits.
  # uint_2bitpack ist ein unsigned Integer mit 2*bitpack Bits.
  # R_bitpack(x) liefert die rechte (untere) H�lfte eines uint_2bitpack.
  # L_bitpack(x) liefert die linke (obere) H�lfte eines uint_2bitpack.
  # LR_2bitpack(x,y) liefert zu x,y das aus der linken H�lfte x und der
  #                  rechten H�lfte y zusammengesetzte uint_2bitpack.
  # Verwende LR_0_bitpack(y) falls x=0, LR_bitpack_0(x) falls y=0.
  #if BIG_ENDIAN_P && (varobject_alignment%2 == 0)
    # Bei Big-Endian-Maschinen kann man gleich mit 16 Bit auf einmal arbeiten
    # (sofern varobject_alignment durch 2 Byte teilbar ist):
    #define bitpack  16
    #define uint_bitpack  uint16
    #define uint_2bitpack  uint32
    #define R_bitpack(x)  low16(x)
    #define L_bitpack(x)  high16(x)
    #define LR_2bitpack(x,y)  highlow32(x,y)
    #define LR_0_bitpack(y)  ((uint32)(uint16)(y))
    #define LR_bitpack_0(x)  highlow32_0(x)
  #else
    # Sonst kann man nur 8 Bit auf einmal nehmen:
    #define bitpack  8
    #define uint_bitpack  uint8
    #define uint_2bitpack  uint16
    #define R_bitpack(x)  ((uint_bitpack)(uint_2bitpack)(x))
    #define L_bitpack(x)  ((uint_bitpack)((uint_2bitpack)(x) >> bitpack))
    #define LR_2bitpack(x,y)  \
      (((uint_2bitpack)(uint_bitpack)(x) << bitpack)  \
       | (uint_2bitpack)(uint_bitpack)(y)             \
      )
    #define LR_0_bitpack(y)  LR_2bitpack(0,y)
    #define LR_bitpack_0(x)  LR_2bitpack(x,0)
  #endif

# Unterprogramm f�r Bitvektor-Vergleich:
# bit_compare(array1,index1,array2,index2,count)
# > array1: erster Bit-Array,
# > index1: absoluter Index in array1
# > array2: zweiter Bit-Array,
# > index2: absoluter Index in array2
# > count: Anzahl der zu vergleichenden Bits
# < ergebnis: TRUE, wenn die Ausschnitte bitweise gleich sind, FALSE sonst.
  global boolean bit_compare (object array1, uintL index1,
                              object array2, uintL index2,
                              uintL bitcount);
  global boolean bit_compare(array1,index1,array2,index2,bitcount)
    var object array1;
    var uintL index1;
    var object array2;
    var uintL index2;
    var uintL bitcount;
    { var uint_bitpack* ptr1 = &((uint_bitpack*)(&TheSbvector(array1)->data[0]))[index1/bitpack];
      var uint_bitpack* ptr2 = &((uint_bitpack*)(&TheSbvector(array2)->data[0]))[index2/bitpack];
      # ptr1 zeigt auf das erste teilnehmende Word des 1. Bit-Arrays.
      # ptr2 zeigt auf das erste teilnehmende Word des 2. Bit-Arrays.
      var uintL bitpackcount = bitcount / bitpack;
      # bitpackcount = Anzahl der ganzen Words
      var uintL bitcount_rest = bitcount % bitpack;
      # bitcount_rest = Anzahl der �brigbleibenden Bits
      index1 = index1 % bitpack; # Bit-Offset im 1. Bit-Array
      index2 = index2 % bitpack; # Bit-Offset im 2. Bit-Array
      if ((index1==0) && (index2==0))
        # einfache Schleife, da alle Bit-Offsets im Word =0 sind:
        { dotimesL(bitpackcount,bitpackcount,
            { if (!(*ptr1++ == *ptr2++)) { return FALSE; } }
            );
          # bitcount_rest = Anzahl der noch vergleichenden Bits
          if (!(bitcount_rest==0))
            # letztes Word vergleichen:
            { if (!(( (*ptr1 ^ *ptr2)
                      & # Bitmaske mit Bits bitpack-1..bitpack-bitcount_rest gesetzt
                        ~( (uint_bitpack)(bitm(bitpack)-1) >> bitcount_rest)
                    ) ==0
                 ) )
                { return FALSE; }
            }
          return TRUE;
        }
        else
        # kompliziertere Schleife:
        { var uint_2bitpack carry1 = LR_bitpack_0((*ptr1++) << index1);
          # carry1 hat in seinen oberen bitpack-index1 Bits (Bits 2*bitpack-1..bitpack+index1)
          # die betroffenen Bits des 1. Words des 1. Arrays, sonst Nullen.
          var uint_2bitpack carry2 = LR_bitpack_0((*ptr2++) << index2);
          # carry2 hat in seinen oberen bitpack-index2 Bits (Bits 2*bitpack-1..bitpack+index2)
          # die betroffenen Bits des 1. Words des 2. Arrays, sonst Nullen.
          dotimesL(bitpackcount,bitpackcount,
            { # Vergleichsschleife (jeweils wortweise):
              # Nach n>=0 Schleifendurchl�ufen ist
              # ptr1 und ptr2 um n+1 Words weiterger�ckt, also Pointer aufs
              # n�chste zu lesende Word des 1. bzw. 2. Arrays,
              # bitpackcount = Zahl zu verkn�pfender ganzer Words - n,
              # carry1 = �bertrag vom 1. Array
              #          (in den bitpack-index1 oberen Bits, sonst Null),
              # carry2 = �bertrag vom 2. Array
              #          (in den bitpack-index2 oberen Bits, sonst Null).
              if (!(
                    ( carry1 |=
                        LR_0_bitpack(*ptr1++) # n�chstes Word des 1. Arrays lesen
                        << index1, # zum carry1 dazunehmen
                      L_bitpack(carry1) # und davon das linke Word verwenden
                    )
                    ==
                    ( carry2 |=
                        LR_0_bitpack(*ptr2++) # n�chstes Word des 2. Arrays lesen
                        << index2, # zum carry2 dazunehmen
                      L_bitpack(carry2) # und davon das linke Word verwenden
                    )
                 ) )
                { return FALSE; }
              carry1 = LR_bitpack_0(R_bitpack(carry1)); # carry1 := rechtes Word von carry1
              carry2 = LR_bitpack_0(R_bitpack(carry2)); # carry2 := rechtes Word von carry2
            });
          # Noch bitcount_rest Bits zu vergleichen:
          if (!(bitcount_rest==0))
            # letztes Word vergleichen:
            { if (!(( (
                       ( carry1 |=
                           LR_0_bitpack(*ptr1++) # n�chstes Word des 1. Arrays lesen
                           << index1, # zum carry1 dazunehmen
                         L_bitpack(carry1) # und davon das linke Word verwenden
                       )
                       ^
                       ( carry2 |=
                           LR_0_bitpack(*ptr2++) # n�chstes Word des 2. Arrays lesen
                           << index2, # zum carry2 dazunehmen
                         L_bitpack(carry2) # und davon das linke Word verwenden
                       )
                      )
                      & # Bitmaske mit Bits bitpack-1..bitpack-bitcount_rest gesetzt
                        ~( (uint_bitpack)(bitm(bitpack)-1) >> bitcount_rest)
                    ) ==0
                 ) )
                { return FALSE; }
            }
          return TRUE;
        }
    }

# Unterprogramm f�r Bitvektor-Operationen:
# bit_op(array1,index1,array2,index2,array3,index3,op,count);
# > array1: erster Bit-Array,
# > index1: absoluter Index in array1
# > array2: zweiter Bit-Array,
# > index2: absoluter Index in array2
# > array3: dritter Bit-Array,
# > index3: absoluter Index in array3
# > op: Adresse der Operationsroutine
# > count: Anzahl der zu verkn�pfenden Bits
  # bit_op_fun ist eine Funktion, die zwei bitpack-Bit-W�rter verkn�pft:
  typedef uint_bitpack bit_op_fun (uint_bitpack x, uint_bitpack y);
  local void bit_op (object array1, uintL index1,
                     object array2, uintL index2,
                     object array3, uintL index3,
                     bit_op_fun* op, uintL bitcount);
  local void bit_op(array1,index1,array2,index2,array3,index3,op,bitcount)
    var object array1;
    var uintL index1;
    var object array2;
    var uintL index2;
    var object array3;
    var uintL index3;
    var bit_op_fun* op;
    var uintL bitcount;
    { var uint_bitpack* ptr1 = &((uint_bitpack*)(&TheSbvector(array1)->data[0]))[index1/bitpack];
      var uint_bitpack* ptr2 = &((uint_bitpack*)(&TheSbvector(array2)->data[0]))[index2/bitpack];
      var uint_bitpack* ptr3 = &((uint_bitpack*)(&TheSbvector(array3)->data[0]))[index3/bitpack];
      # ptr1 zeigt auf das erste teilnehmende Word des 1. Bit-Arrays.
      # ptr2 zeigt auf das erste teilnehmende Word des 2. Bit-Arrays.
      # ptr3 zeigt auf das erste teilnehmende Word des 3. Bit-Arrays.
      var uintL bitpackcount = bitcount / bitpack;
      # bitpackcount = Anzahl der ganzen Words
      var uintL bitcount_rest = bitcount % bitpack;
      # bitcount_rest = Anzahl der �brigbleibenden Bits
      index1 = index1 % bitpack; # Bit-Offset im 1. Bit-Array
      index2 = index2 % bitpack; # Bit-Offset im 2. Bit-Array
      index3 = index3 % bitpack; # Bit-Offset im 3. Bit-Array
      if ((index1==0) && (index2==0) && (index3==0))
        # einfache Schleife, da alle Bit-Offsets im Word =0 sind:
        { dotimesL(bitpackcount,bitpackcount,
            { *ptr3++ = (*op)(*ptr1++,*ptr2++); }
            );
          # bitcount_rest = Anzahl der noch abzulegenden Bits
          if (!(bitcount_rest==0))
            # letztes Word ablegen:
            { var uint_bitpack temp = (*op)(*ptr1,*ptr2);
              *ptr3 =
                ( ~
                    ( (uint_bitpack)(bitm(bitpack)-1) >> bitcount_rest)
                    # Bitmaske mit Bits bitpack-bitcount_rest-1..0 gesetzt
                  # Bitmaske mit Bits bitpack-1..bitpack-bitcount_rest gesetzt
                 &
                 (*ptr3 ^ temp)
                ) # zu �ndernde Bits
                ^ *ptr3
                ;
        }   }
        else
        # kompliziertere Schleife:
        { var uint_2bitpack carry1 = LR_bitpack_0((*ptr1++) << index1);
          # carry1 hat in seinen oberen bitpack-index1 Bits (Bits 2*bitpack-1..bitpack+index1)
          # die betroffenen Bits des 1. Words des 1. Arrays, sonst Nullen.
          var uint_2bitpack carry2 = LR_bitpack_0((*ptr2++) << index2);
          # carry2 hat in seinen oberen bitpack-index2 Bits (Bits 2*bitpack-1..bitpack+index2)
          # die betroffenen Bits des 1. Words des 2. Arrays, sonst Nullen.
          var uint_2bitpack carry3 =
            LR_bitpack_0(
                         (~
                            ( (uint_bitpack)(bitm(bitpack)-1) >> index3)
                            # Bitmaske mit Bits bitpack-index3-1..0 gesetzt
                         ) # Bitmaske mit Bits bitpack-1..bitpack-index3 gesetzt
                         & (*ptr3)
                        );
          # carry3 hat in seinen obersten index3 Bits (Bits 2*bitpack-1..2*bitpack-index3)
          # genau die Bits von *ptr3, die nicht ver�ndert werden d�rfen.
          loop
            { # Verkn�pfungsschleife (jeweils wortweise):
              # Nach n>=0 Schleifendurchl�ufen ist
              # ptr1 und ptr2 um n+1 Words weiterger�ckt, also Pointer aufs
              # n�chste zu lesende Word des 1. bzw. 2. Arrays,
              # ptr3 um n Words weiterger�ckt, also Pointer aufs
              # n�chste zu schreibende Word des 3. Arrays,
              # bitpackcount = Zahl zu verkn�pfender ganzer Words - n,
              # carry1 = �bertrag vom 1. Array
              #          (in den bitpack-index1 oberen Bits, sonst Null),
              # carry2 = �bertrag vom 2. Array
              #          (in den bitpack-index2 oberen Bits, sonst Null),
              # carry3 = �bertrag noch abzuspeichernder Bits
              #          (in den index3 oberen Bits, sonst Null).
              var uint_bitpack temp =
                (*op)(
                      ( carry1 |=
                          LR_0_bitpack(*ptr1++) # n�chstes Word des 1. Arrays lesen
                          << index1, # zum carry1 dazunehmen
                        L_bitpack(carry1) # und davon das linke Word verwenden
                      ),
                      ( carry2 |=
                          LR_0_bitpack(*ptr2++) # n�chstes Word des 2. Arrays lesen
                          << index2, # zum carry2 dazunehmen
                        L_bitpack(carry2) # und davon das linke Word verwenden
                      )
                     ) ; # beide durch *op verkn�pfen
              carry1 = LR_bitpack_0(R_bitpack(carry1)); # carry1 := rechtes Word von carry1
              carry2 = LR_bitpack_0(R_bitpack(carry2)); # carry2 := rechtes Word von carry2
              carry3 |= LR_bitpack_0(temp) >> index3;
              # Die oberen bitpack+index3 Bits von carry3 sind abzulegen.
              if (bitpackcount==0) break;
              *ptr3++ = L_bitpack(carry3); # bitpack Bits davon ablegen
              carry3 = LR_bitpack_0(R_bitpack(carry3)); # und index3 Bits f�r sp�ter behalten.
              bitpackcount--;
            }
          # letztes (halbes) Datenword speziell behandeln:
          # Vom letzten Word (nun in den Bits
          # 2*bitpack-index3-1..bitpack-index3 von carry3)
          # d�rfen nur bitcount_rest Bits im 3. Array abgelegt werden.
          { var uint_bitpack last_carry;
            bitcount_rest = index3+bitcount_rest;
            # Die oberen bitcount_rest Bits ablegen:
            if (bitcount_rest>=bitpack)
              { *ptr3++ = L_bitpack(carry3);
                last_carry = R_bitpack(carry3);
                bitcount_rest -= bitpack;
              }
              else
              { last_carry = L_bitpack(carry3); }
            # Die noch �brigen bitcount_rest Bits von last_carry ablegen:
            if (!(bitcount_rest==0))
              *ptr3 ^=
                (*ptr3 ^ last_carry)
                & (~( (uint_bitpack)(bitm(bitpack)-1) >> bitcount_rest ));
                  # Bitmaske, in der die oberen bitcount_rest Bits gesetzt sind
        } }
    }

# Unterprogramm f�r Bit-Verkn�pfung mit 2 Operanden
# bit_up(op)
# > STACK_2: bit-array1
# > STACK_1: bit-array2
# > STACK_0: result-bit-array oder #<UNBOUND>
# > op: Adresse der Verkn�pfungsroutine
# < value1/mv_count: Funktionswert
# Testet Argumente, r�umt STACK auf.
  local Values bit_up (bit_op_fun* op);
  local Values bit_up(op)
    var bit_op_fun* op;
    { # Hauptunterscheidung: Vektor / mehrdimensionaler Array
      var uintL len; # L�nge (des 1. Arrays), falls Vektoren
      var uintC rank; # Rang und
      var uintL* dimptr; # Pointer auf Dimensionen, falls mehrdimensional
      # Typ von bit-array1 untersuchen und danach verzweigen:
      #ifndef TYPECODES
      if (!orecordp(STACK_2)) goto fehler2;
      #endif
      switch (Array_type(STACK_2))
        { case Array_type_sbvector:
            len = Sbvector_length(STACK_2); goto vector;
          case Array_type_bvector:
            { var Iarray array1 = TheIarray(STACK_2);
              # bit-array1 mu� den Elementtyp BIT haben:
              if (!((iarray_flags(array1) & arrayflags_atype_mask) == Atype_Bit))
                goto fehler2;
              len = array1->totalsize;
              goto vector;
            }
          case Array_type_mdarray:
            { var Iarray array1 = TheIarray(STACK_2);
              # bit-array1 mu� den Elementtyp BIT haben:
              if (!((iarray_flags(array1) & arrayflags_atype_mask) == Atype_Bit))
                goto fehler2;
              # Rang merken:
              rank = iarray_rank(array1);
              # Dimensionen merken:
              dimptr = &array1->dims[0];
              if (iarray_flags(array1) & bit(arrayflags_dispoffset_bit))
                dimptr++;
              # die Anzahl der zu verkn�pfenden Bits ist die Totalsize:
              len = array1->totalsize;
              goto array;
            }
          default:
            goto fehler2;
        }
      vector: # Das erste Argument ist ein Bit-Vektor, mit L�nge len.
        # Teste, ob dies auch auf den/die anderen zutrifft:
        # bit-array2 �berpr�fen:
        #ifndef TYPECODES
        if (!orecordp(STACK_1)) goto fehler2;
        #endif
        switch (Array_type(STACK_1))
          { case Array_type_sbvector:
              if (!(len == Sbvector_length(STACK_1))) goto fehler2;
              break;
            case Array_type_bvector:
              { var Iarray array2 = TheIarray(STACK_1);
                # bit-array2 mu� den Elementtyp BIT haben:
                if (!((iarray_flags(array2) & arrayflags_atype_mask) == Atype_Bit))
                  goto fehler2;
                if (!(len == array2->totalsize)) goto fehler2;
              }
              break;
            default:
              goto fehler2;
          }
        # bit-array3 �berpr�fen:
        {var object array3 = STACK_0;
         if (eq(array3,unbound) || eq(array3,NIL)) # nicht angegeben oder NIL?
           # ja -> neuen Vektor erzeugen:
           { STACK_0 = allocate_bit_vector(len); }
           else
           if (eq(array3,T))
             { STACK_0 = STACK_2; } # statt T verwende bit-array1
             else
             {
               #ifndef TYPECODES
               if (!orecordp(STACK_0)) goto fehler3;
               #endif
               switch (Array_type(STACK_0))
                 { case Array_type_sbvector:
                     if (!(len == Sbvector_length(array3))) goto fehler3;
                     break;
                   case Array_type_bvector:
                     # bit-array3 mu� den Elementtyp BIT haben:
                     if (!((Iarray_flags(array3) & arrayflags_atype_mask) == Atype_Bit))
                       goto fehler3;
                     if (!(len == TheIarray(array3)->totalsize)) goto fehler3;
                     break;
                   default:
                     goto fehler3;
             }   }
        }
        goto weiter;
      array: # erstes Argument war ein mehrdimensionaler Bit-Array
        # mit Rang rank, Dimensionen ab dimptr und Totalsize len.
        # bit-array2 �berpr�fen:
        #ifndef TYPECODES
        if (!orecordp(STACK_1)) goto fehler2;
        #endif
        switch (Array_type(STACK_1))
          { case Array_type_mdarray:
              { var Iarray array2 = TheIarray(STACK_1);
                # bit-array2 mu� den Elementtyp BIT haben:
                if (!((iarray_flags(array2) & arrayflags_atype_mask) == Atype_Bit))
                  goto fehler2;
                # Rang vergleichen:
                if (!(rank == iarray_rank(array2))) goto fehler2;
                # Dimensionen vergleichen:
                { var uintC count;
                  var uintL* dimptr1 = dimptr;
                  var uintL* dimptr2;
                  dimptr2 = &array2->dims[0];
                  if (iarray_flags(array2) & bit(arrayflags_dispoffset_bit))
                    dimptr2++;
                  dotimesC(count,rank, { if (!(*dimptr1++==*dimptr2++)) goto fehler2; });
                }
                break;
              }
            default:
              goto fehler2;
          }
        # bit-array3 �berpr�fen:
        {var object array3 = STACK_0;
         if (eq(array3,unbound) || eq(array3,NIL)) # nicht angegeben oder NIL?
           # ja -> neuen Array erzeugen:
           { STACK_0 = allocate_bit_vector(len); # Bitvektor erzeugen
             array3 = allocate_iarray(bit(arrayflags_notbytep_bit)|Atype_Bit,rank,Array_type_mdarray); # Array erzeugen
             TheIarray(array3)->data = STACK_0; # Datenvektor eintragen
             # Dimensionen eintragen:
             { var uintC count;
               var uintL* dimptr1 = dimptr;
               var uintL* dimptr2 = &TheIarray(array3)->dims[0];
               dotimesC(count,rank, { *dimptr1++ = *dimptr2++; });
             }
             STACK_0 = array3; # neuen Array ablegen
           }
           else
           if (eq(array3,T))
             { STACK_0 = STACK_2; } # statt T verwende bit-array1
             else
             {
               #ifndef TYPECODES
               if (!orecordp(STACK_0)) goto fehler3;
               #endif
               switch (Array_type(STACK_0))
                 { case Array_type_mdarray:
                     { var Iarray array3 = TheIarray(STACK_0);
                       # bit-array3 mu� den Elementtyp BIT haben:
                       if (!((iarray_flags(array3) & arrayflags_atype_mask) == Atype_Bit))
                         goto fehler3;
                       # Rang vergleichen:
                       if (!(rank == iarray_rank(array3))) goto fehler3;
                       # Dimensionen vergleichen:
                       { var uintC count;
                         var uintL* dimptr1 = dimptr;
                         var uintL* dimptr2;
                         dimptr2 = &array3->dims[0];
                         if (iarray_flags(array3) & bit(arrayflags_dispoffset_bit))
                           dimptr2++;
                         dotimesC(count,rank, { if (!(*dimptr1++==*dimptr2++)) goto fehler3; });
                       }
                       break;
                     }
                   default:
                     goto fehler3;
             }   }
        }
      weiter: # Vorbereitungen sind abgeschlossen:
        # STACK_2 = bit-array1, STACK_1 = bit-array2, STACK_0 = bit-array3,
        # alle von denselben Dimensionen, mit je len Bits.
        { var uintL index1 = 0; # Index in Datenvektor von bit-array1
          var object array1 = # Datenvektor von bit-array1
                              (simple_bit_vector_p(STACK_2)
                                ? STACK_2
                                : iarray_displace_check(STACK_2,len,&index1)
                              );
          var uintL index2 = 0; # Index in Datenvektor von bit-array2
          var object array2 = # Datenvektor von bit-array2
                              (simple_bit_vector_p(STACK_1)
                                ? STACK_1
                                : iarray_displace_check(STACK_1,len,&index2)
                              );
          var uintL index3 = 0; # Index in Datenvektor von bit-array3
          var object array3 = # Datenvektor von bit-array3
                              (simple_bit_vector_p(STACK_0)
                                ? STACK_0
                                : iarray_displace_check(STACK_0,len,&index3)
                              );
          # Los geht's:
          bit_op(array1,index1,array2,index2,array3,index3,op,len);
        }
        # Fertig:
        value1 = popSTACK(); mv_count=1; # bit-array3 ist das Ergebnis
        skipSTACK(2);
        return;
      fehler2: # Fehlermeldung bei (mindestens) 2 Argumenten
        { var object array1 = STACK_2;
          var object array2 = STACK_1;
          pushSTACK(array2); pushSTACK(array1);
          pushSTACK(TheSubr(subr_self)->name);
          fehler(error,
                 DEUTSCH ? "~: Die Argumente ~ und ~ m�ssen Bit-Arrays gleicher Dimensionierung sein." :
                 ENGLISH ? "~: The arguments ~ and ~ should be arrays of bits with the same dimensions" :
                 FRANCAIS ? "~: Les arguments ~ et ~ doivent �tre des matrices de m�mes dimensions." :
                 ""
                );
        }
      fehler3: # Fehlermeldung bei 3 Argumenten
        { var object array1 = STACK_2;
          var object array2 = STACK_1;
          # array3 bereits in STACK_0
          pushSTACK(array2); pushSTACK(array1);
          pushSTACK(TheSubr(subr_self)->name);
          fehler(error,
                 DEUTSCH ? "~: Die Argumente ~, ~ und ~ m�ssen Bit-Arrays gleicher Dimensionierung sein." :
                 ENGLISH ? "~: The arguments ~, ~ and ~ should be arrays of bits with the same dimensions" :
                 FRANCAIS ? "~: Les arguments ~, ~ et ~ doivent �tre des matrices de m�mes dimensions." :
                 ""
                );
        }
    }

# Die einzelnen Operatoren f�r BIT-AND usw.:
  local uint_bitpack bitpack_and (uint_bitpack x, uint_bitpack y);
  local uint_bitpack bitpack_and(x,y) var uint_bitpack x; var uint_bitpack y;
    { return x&y; }
  local uint_bitpack bitpack_ior (uint_bitpack x, uint_bitpack y);
  local uint_bitpack bitpack_ior(x,y) var uint_bitpack x; var uint_bitpack y;
    { return x|y; }
  local uint_bitpack bitpack_xor (uint_bitpack x, uint_bitpack y);
  local uint_bitpack bitpack_xor(x,y) var uint_bitpack x; var uint_bitpack y;
    { return x^y; }
  local uint_bitpack bitpack_eqv (uint_bitpack x, uint_bitpack y);
  local uint_bitpack bitpack_eqv(x,y) var uint_bitpack x; var uint_bitpack y;
    { return ~(x^y); }
  local uint_bitpack bitpack_nand (uint_bitpack x, uint_bitpack y);
  local uint_bitpack bitpack_nand(x,y) var uint_bitpack x; var uint_bitpack y;
    { return ~(x&y); }
  local uint_bitpack bitpack_nor (uint_bitpack x, uint_bitpack y);
  local uint_bitpack bitpack_nor(x,y) var uint_bitpack x; var uint_bitpack y;
    { return ~(x|y); }
  local uint_bitpack bitpack_andc1 (uint_bitpack x, uint_bitpack y);
  local uint_bitpack bitpack_andc1(x,y) var uint_bitpack x; var uint_bitpack y;
    { return (~x)&y; }
  local uint_bitpack bitpack_andc2 (uint_bitpack x, uint_bitpack y);
  local uint_bitpack bitpack_andc2(x,y) var uint_bitpack x; var uint_bitpack y;
    { return x&(~y); }
  local uint_bitpack bitpack_orc1 (uint_bitpack x, uint_bitpack y);
  local uint_bitpack bitpack_orc1(x,y) var uint_bitpack x; var uint_bitpack y;
    { return (~x)|y; }
  local uint_bitpack bitpack_orc2 (uint_bitpack x, uint_bitpack y);
  local uint_bitpack bitpack_orc2(x,y) var uint_bitpack x; var uint_bitpack y;
    { return x|(~y); }
  local uint_bitpack bitpack_not (uint_bitpack x, uint_bitpack y);
  local uint_bitpack bitpack_not(x,y) var uint_bitpack x; var uint_bitpack y;
    { return ~x; }

LISPFUN(bit_and,2,1,norest,nokey,0,NIL)
# (BIT-AND bit-array1 bit-array2 [result-bit-array]), CLTL S. 294
  { return_Values bit_up(&bitpack_and); }

LISPFUN(bit_ior,2,1,norest,nokey,0,NIL)
# (BIT-IOR bit-array1 bit-array2 [result-bit-array]), CLTL S. 294
  { return_Values bit_up(&bitpack_ior); }

LISPFUN(bit_xor,2,1,norest,nokey,0,NIL)
# (BIT-XOR bit-array1 bit-array2 [result-bit-array]), CLTL S. 294
  { return_Values bit_up(&bitpack_xor); }

LISPFUN(bit_eqv,2,1,norest,nokey,0,NIL)
# (BIT-EQV bit-array1 bit-array2 [result-bit-array]), CLTL S. 294
  { return_Values bit_up(&bitpack_eqv); }

LISPFUN(bit_nand,2,1,norest,nokey,0,NIL)
# (BIT-NAND bit-array1 bit-array2 [result-bit-array]), CLTL S. 294
  { return_Values bit_up(&bitpack_nand); }

LISPFUN(bit_nor,2,1,norest,nokey,0,NIL)
# (BIT-NOR bit-array1 bit-array2 [result-bit-array]), CLTL S. 294
  { return_Values bit_up(&bitpack_nor); }

LISPFUN(bit_andc1,2,1,norest,nokey,0,NIL)
# (BIT-ANDC1 bit-array1 bit-array2 [result-bit-array]), CLTL S. 294
  { return_Values bit_up(&bitpack_andc1); }

LISPFUN(bit_andc2,2,1,norest,nokey,0,NIL)
# (BIT-ANDC2 bit-array1 bit-array2 [result-bit-array]), CLTL S. 294
  { return_Values bit_up(&bitpack_andc2); }

LISPFUN(bit_orc1,2,1,norest,nokey,0,NIL)
# (BIT-ORC1 bit-array1 bit-array2 [result-bit-array]), CLTL S. 294
  { return_Values bit_up(&bitpack_orc1); }

LISPFUN(bit_orc2,2,1,norest,nokey,0,NIL)
# (BIT-ORC2 bit-array1 bit-array2 [result-bit-array]), CLTL S. 294
  { return_Values bit_up(&bitpack_orc2); }

LISPFUN(bit_not,1,1,norest,nokey,0,NIL)
# (BIT-NOT bit-array [result-bit-array]), CLTL S. 295
  { # erstes Argument verdoppeln (wird bei der Operation ignoriert):
    {var object array3 = STACK_0; pushSTACK(array3); }
    STACK_1 = STACK_2;
    return_Values bit_up(&bitpack_not);
  }

# UP: Testet, ob ein Array einen Fill-Pointer hat.
# array_has_fill_pointer_p(array)
# > array: ein Array
# < TRUE, falls ja; FALSE falls nein.
  global boolean array_has_fill_pointer_p (object array);
  global boolean array_has_fill_pointer_p(array)
    var object array;
    { if (simplep(array))
        { return FALSE; }
        else
        { if (Iarray_flags(array) & bit(arrayflags_fillp_bit))
            return TRUE;
            else
            return FALSE;
        }
    }

LISPFUNN(array_has_fill_pointer_p,1) # (ARRAY-HAS-FILL-POINTER-P array), CLTL S. 296
  { var object array = popSTACK();
    test_array(array);
    value1 = (array_has_fill_pointer_p(array) ? T : NIL); mv_count=1;
  }

# �berpr�ft, ob ein Objekt ein Vektor mit Fill-Pointer ist, und liefert
# die Adresse des Fill-Pointers.
# *get_fill_pointer(obj) ist dann der Fill-Pointer selbst.
# get_fill_pointer(obj)[-1] ist dann die L�nge (Dimension 0) des Vektors.
# > subr_self: Aufrufer (ein SUBR)
  local uintL* get_fill_pointer (object obj);
  local uintL* get_fill_pointer(obj)
    var object obj;
    { # obj mu� ein Vektor sein:
      if (!vectorp(obj)) { fehler_vector(obj); }
      # darf nicht simple sein:
      if (simplep(obj)) { goto fehler_fillp; }
      # mu� einen Fill-Pointer enthalten:
      if (!(Iarray_flags(obj) & bit(arrayflags_fillp_bit))) { goto fehler_fillp; }
      # Wo steht der Fill-Pointer?
      return ((Iarray_flags(obj) & bit(arrayflags_dispoffset_bit))
              ? &TheIarray(obj)->dims[2] # nach Displaced-Offset und Dimension 0
              : &TheIarray(obj)->dims[1] # nach der Dimension 0
             );
      # Fehlermeldung:
      fehler_fillp:
        pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
        pushSTACK(O(type_vector_with_fill_pointer)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
        pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
        fehler(type_error,
               DEUTSCH ? "~: Vektor ~ hat keinen Fill-Pointer." :
               ENGLISH ? "~: vector ~ has no fill pointer" :
               FRANCAIS ? "~: Le vecteur ~ n'a pas de pointeur de remplissage." :
               ""
              );
    }

LISPFUNN(fill_pointer,1) # (FILL-POINTER vector), CLTL S. 296
  { var object obj = popSTACK();
    value1 = fixnum(* get_fill_pointer(obj)); # Fill-Pointer holen, als Fixnum
    mv_count=1;
  }

LISPFUNN(set_fill_pointer,2) # (SYS::SET-FILL-POINTER vector index)
                             # = (SETF (FILL-POINTER vector) index), CLTL S. 296
  { var uintL* fillp = get_fill_pointer(STACK_1); # Fillpointer-Adresse
    if (!posfixnump(STACK_0)) # neuer Fill-Pointer mu� Fixnum>=0 sein.
      fehler_index_type();
   {var uintL newfillp = posfixnum_to_L(STACK_0); # als uintL
    if (!(newfillp <= fillp[-1])) # mu� kleinergleich der L�nge sein
      fehler_index_range(fillp[-1]+1);
    *fillp = newfillp; # neuen Fill-Pointer eintragen
    value1 = STACK_0; mv_count=1; # neuen Fillpointer zur�ck
    skipSTACK(2);
  }}

LISPFUNN(vector_push,2) # (VECTOR-PUSH new-element vector), CLTL S. 296
  { var uintL* fillp = get_fill_pointer(STACK_0); # Fillpointer-Adresse
    var uintL oldfillp = *fillp; # alter Wert des Fillpointers
    if (oldfillp >= fillp[-1]) # Fill-Pointer am Ende?
      { value1 = NIL; mv_count=1; } # NIL zur�ck
      else
      { var uintL index = oldfillp;
        var object datenvektor = notsimple_displace(STACK_0,&index);
        datenvektor_store(datenvektor,index,STACK_1); # new-element eintragen
        (*fillp)++; # Fill-Pointer erh�hen
        value1 = fixnum(oldfillp); mv_count=1;
        # alter Fill-Pointer als Wert
      }
    skipSTACK(2);
  }

LISPFUNN(vector_pop,1) # (VECTOR-POP vector), CLTL S. 296
  { var object array = popSTACK();
    var uintL* fillp = get_fill_pointer(array);
    if (*fillp==0)
      { # Fill-Pointer war =0 -> Fehlermeldung
        pushSTACK(array); pushSTACK(TheSubr(subr_self)->name);
        fehler(error,
               DEUTSCH ? "~: ~ hat keine aktiven Elemente." :
               ENGLISH ? "~: ~ has length zero" :
               FRANCAIS ? "~: ~ ne contient pas d'�l�ments actifs (la longueur est nulle)." :
               ""
              );
      }
      else
      { var uintL index = --(*fillp); # Fill-Pointer erniedrigen
        var object datenvektor = notsimple_displace(array,&index);
        value1 = datenvektor_aref(datenvektor,index); mv_count=1; # Element zur�ck
      }
  }

LISPFUN(vector_push_extend,2,1,norest,nokey,0,NIL)
# (VECTOR-PUSH-EXTEND new-element vector [extension]), CLTL S. 296
  { var object extension = popSTACK(); # Extension (ungepr�ft)
    var uintL* fillp = get_fill_pointer(STACK_0); # Fillpointer-Adresse
    var uintL oldfillp = *fillp; # alter Wert des Fillpointers
    if (oldfillp < fillp[-1]) # Fill-Pointer noch nicht am Ende?
      { var uintL index = oldfillp;
        var object datenvektor = notsimple_displace(STACK_0,&index);
        datenvektor_store(datenvektor,index,STACK_1); # new-element eintragen
        (*fillp)++; # Fill-Pointer erh�hen
      }
      else
      { # Fill-Pointer am Ende -> Versuche, den Vektor zu verl�ngern:
        var object array = STACK_0;
        if (!(Iarray_flags(array) & bit(arrayflags_adjustable_bit)))
          { # Vektor nicht adjustable -> Fehlermeldung:
            # array noch in STACK_0
            pushSTACK(TheSubr(subr_self)->name);
            fehler(error,
                   DEUTSCH ? "~ funktioniert nur auf adjustierbaren Arrays, nicht auf ~" :
                   ENGLISH ? "~ works only on adjustable arrays, not on ~" :
                   FRANCAIS ? "~ ne fonctionne qu'avec des matrices ajustables et non avec ~." :
                   ""
                  );
          }
        { var uintB atype = Iarray_flags(array) & arrayflags_atype_mask;
          var uintL len = fillp[-1]; # bisherige L�nge (Dimension 0)
          var uintL inc; # gew�nschter Increment der L�nge
          if (!eq(extension,unbound))
            { # extension sollte ein Fixnum >0, <arraysize_limit sein:
              if ( (!(posfixnump(extension)))
                   || ((inc = posfixnum_to_L(extension)) == 0)
                   #ifndef UNIX_DEC_ULTRIX_GCCBUG
                   || (inc > arraysize_limit_1)
                   #endif
                 )
                { pushSTACK(extension); # Wert f�r Slot DATUM von TYPE-ERROR
                  pushSTACK(O(type_posfixnum1)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
                  pushSTACK(extension); pushSTACK(TheSubr(subr_self)->name);
                  fehler(type_error,
                         DEUTSCH ? "~: Extension ~ sollte ein Fixnum > 0 sein." :
                         ENGLISH ? "~: extension ~ should be a positive fixnum" :
                         FRANCAIS ? "~: L'extension ~ doit �tre de type FIXNUM strictement positif." :
                         ""
                        );
            }   }
            else
            { # Default-Verl�ngerung:
              switch (atype)
                { case Atype_T:           inc =  16; break; # bei general-Vektoren: 16 Objekte
                  case Atype_String_Char: inc =  64; break; # bei Strings: 64 Zeichen
                  case Atype_Bit:         inc = 128; break; # bei Bit-Vektoren: 128 Bits
                  case Atype_2Bit: case Atype_4Bit: case Atype_8Bit:
                  case Atype_16Bit: case Atype_32Bit: # bei Byte-Vektoren: entsprechend
                                          inc = bit(floor(14-atype,2)); break;
                  default: NOTREACHED
                }
              # mindestens jedoch die bisherige L�nge:
              if (inc<len) { inc = len; }
            }
          { var uintL newlen = len + inc; # neue L�nge
            #ifndef UNIX_DEC_ULTRIX_GCCBUG
            if (newlen > arraysize_limit_1)
              { # Vektor w�rde zu lang -> Fehlermeldung
                pushSTACK(extension); pushSTACK(TheSubr(subr_self)->name);
                fehler(error,
                       DEUTSCH ? "~: Durch die angegebene Extension von ~ wird der Vektor zu lang." :
                       ENGLISH ? "~: extending the vector by ~ elements makes it too long" :
                       FRANCAIS ? "~: �tendre le vecteur de ~ le rend trop long." :
                       ""
                      );
              }
            #endif
            { # Neuen Datenvektor holen. Dazu Fallunterscheidung je nach Typ:
              var object neuer_datenvektor;
              switch (atype)
                { case Atype_T: # array ist ein General-Vector
                    neuer_datenvektor = allocate_vector(newlen);
                    array = STACK_0; # array wieder holen
                    { var object* ptr2 = &TheSvector(neuer_datenvektor)->data[0];
                      # alten in neuen Datenvektor kopieren:
                      if (len>0)
                        { var uintL index = 0;
                          var object datenvektor = iarray_displace_check(array,len,&index);
                          var object* ptr1 = &TheSvector(datenvektor)->data[index];
                          var uintL count;
                          dotimespL(count,len, { *ptr2++ = *ptr1++; } );
                        }
                      # dann new_element anf�gen:
                      *ptr2 = STACK_1;
                    }
                    break;
                  case Atype_String_Char: # array ist ein String
                    neuer_datenvektor = allocate_string(newlen);
                    array = STACK_0; # array wieder holen
                    { var uintB* ptr2 = &TheSstring(neuer_datenvektor)->data[0];
                      # alten in neuen Datenvektor kopieren:
                      if (len>0)
                        { var uintL index = 0;
                          var object datenvektor = iarray_displace_check(array,len,&index);
                          var uintB* ptr1 = &TheSstring(datenvektor)->data[index];
                          var uintL count;
                          dotimespL(count,len, { *ptr2++ = *ptr1++; } );
                        }
                      # dann new_element anf�gen:
                      if (!(string_char_p(STACK_1))) goto fehler_type;
                      *ptr2 = char_code(STACK_1);
                    }
                    break;
                  case Atype_Bit: # array ist ein Bit-Vektor
                  case Atype_2Bit: case Atype_4Bit: case Atype_8Bit:
                  case Atype_16Bit: case Atype_32Bit: # array ist ein Byte-Vektor
                    neuer_datenvektor = (atype==Atype_Bit
                                         ? allocate_bit_vector(newlen)
                                         : allocate_byte_vector(atype,newlen)
                                        );
                    array = STACK_0; # array wieder holen
                    # alten in neuen Datenvektor kopieren:
                    if (len>0)
                      { var uintL index = 0;
                        var object datenvektor = iarray_displace_check(array,len,&index);
                        index = index << atype;
                       {var uint_bitpack* ptr1 = &((uint_bitpack*)(&TheSbvector(atype==Atype_Bit ? datenvektor : TheIarray(datenvektor)->data)->data[0]))[index/bitpack];
                        var uint_bitpack* ptr2 = (uint_bitpack*)(&TheSbvector(atype==Atype_Bit ? neuer_datenvektor : TheIarray(neuer_datenvektor)->data)->data[0]);
                        var uintL bitpackcount = ceiling(len<<atype,bitpack); # Anzahl der zu schreibenden Worte
                        # kopiere bitpackcount Words, von ptr1 ab (dabei um
                        # (index mod bitpack) Bits nach links schieben), mit
                        # Ziel ab ptr2. (Eventuell schie�t man �ber den Source-
                        # Datenvektor hinweg, aber das macht nichts.)
                        var uintL shift = index % bitpack;
                        if (shift==0)
                          { # keine Verschiebung n�tig
                            var uintL count;
                            dotimespL(count,bitpackcount, { *ptr2++ = *ptr1++; } );
                          }
                          else
                          { # beim Kopieren um shift Bits links schieben.
                            ptr1 += bitpackcount; ptr2 += bitpackcount; # von hinten anfangen
                           {var uint_2bitpack carry = L_bitpack(LR_0_bitpack(*ptr1)<<shift);
                            var uintL count;
                            dotimespL(count,bitpackcount,
                                      # Hier enthalten die rechten shift Bits von carry
                                      # den �bertrag von rechts, sonst Null.
                                      { carry |= LR_0_bitpack(*--ptr1)<<shift;
                                        *--ptr2 = R_bitpack(carry);
                                        carry = L_bitpack(carry);
                                      });
                      }}  }}
                    # new-element eintragen:
                    datenvektor_store(neuer_datenvektor,len,STACK_1);
                    break;
                  default: NOTREACHED
                  fehler_type:
                    { # Stackaufbau: new-element, vector.
                      pushSTACK(STACK_1); # Wert f�r Slot DATUM von TYPE-ERROR
                      pushSTACK(array_element_type(STACK_(0+1))); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
                      pushSTACK(STACK_(0+2)); pushSTACK(STACK_(1+3));
                      pushSTACK(TheSubr(subr_self)->name);
                      fehler(type_error,
                             DEUTSCH ? "~: Das Objekt ~ kann nicht in den Array ~ geschoben werden, weil vom falschen Typ." :
                             ENGLISH ? "~: cannot push ~ into array ~ (bad type)" :
                             FRANCAIS ? "~: L'objet ~ ne peut pas �tre pouss� dans la matrice ~ car il est de mauvais type." :
                             ""
                            );
                    }
                }
              set_break_sem_1(); # Unterbrechungen verbieten
              TheIarray(array)->data = neuer_datenvektor; # neuen Vektor als Datenvektor eintragen
              iarray_flags_clr(TheIarray(array),bit(arrayflags_displaced_bit)); # Displaced-Bit l�schen
              TheIarray(array)->dims[2] += 1; # Fillpointer um 1 erh�hen
              TheIarray(array)->dims[1] = newlen; # neue L�nge eintragen
              TheIarray(array)->totalsize = newlen; # ist auch neue totalsize
              clr_break_sem_1(); # Unterbrechungen wieder zulassen
          } }
      } }
    value1 = fixnum(oldfillp); mv_count=1;
    # alter Fill-Pointer als Wert
    skipSTACK(2);
  }

# UP: erzeugt einen mit Nullen gef�llten Bitvektor
# allocate_bit_vector_0(len)
# > uintL len: L�nge des Bitvektors (in Bits)
# < ergebnis: neuer Bitvektor, mit Nullen gef�llt
# kann GC ausl�sen
  global object allocate_bit_vector_0 (uintL len);
  global object allocate_bit_vector_0(len)
    var uintL len;
    { var object newvec = allocate_bit_vector(len); # neuer Bit-Vektor
      var uintL count = ceiling(len,bitpack); # ceiling(len/bitpack) Worte mit Nullen f�llen
      if (!(count==0))
        { var uint_bitpack* ptr = (uint_bitpack*)(&TheSbvector(newvec)->data[0]);
          dotimespL(count,count, { *ptr++ = 0; } );
        }
      return newvec;
    }

#if 0 # nur als Reserve, f�r den Fall, da� wir wieder auf ein GCC-Bug sto�en

# UP: l�scht ein Bit in einem Simple-Bit-Vector
# sbvector_bclr(sbvector,index);
# > sbvector: ein Simple-Bit-Vector
# > index: Index (Variable, sollte < (length sbvector) sein)
  global void sbvector_bclr (object sbvector, uintL index);
  global void sbvector_bclr(sbvector,index)
    var object sbvector;
    var uintL index;
    { # im Byte (index div 8) das Bit 7 - (index mod 8) l�schen:
      TheSbvector(sbvector)->data[index/8] &= ~bit((~index) % 8);
    }

# UP: setzt ein Bit in einem Simple-Bit-Vector
# sbvector_bset(sbvector,index);
# > sbvector: ein Simple-Bit-Vector
# > index: Index (Variable, sollte < (length sbvector) sein)
  global void sbvector_bset (object sbvector, uintL index);
  global void sbvector_bset(sbvector,index)
    var object sbvector;
    var uintL index;
    { # im Byte (index div 8) das Bit 7 - (index mod 8) setzen:
      TheSbvector(sbvector)->data[index/8] |= bit((~index) % 8);
    }

#endif

# Folgende beide Funktionen arbeiten auf "Semi-Simple String"s.
# Das sind STRING-CHAR-Arrays mit FILL-POINTER, die aber nicht adjustierbar
# und nicht displaced sind und deren Datenvektor ein Simple-String ist.
# Beim �berschreiten der L�nge wird ihre L�nge verdoppelt
# (so da� der Aufwand f�rs Erweitern nicht sehr ins Gewicht f�llt).

# UP: Liefert einen Semi-Simple String gegebener L�nge, Fill-Pointer =0.
# make_ssstring(len)
# > uintL len: L�nge >0
# < ergebnis: neuer Semi-Simple String dieser L�nge
# kann GC ausl�sen
  global object make_ssstring (uintL len);
  global object make_ssstring(len)
    var uintL len;
    { {var object new_string = allocate_string(len);
       # neuer Simple-String dieser L�nge
       pushSTACK(new_string); # retten
      }
      {var object new_array =
         allocate_iarray(bit(arrayflags_fillp_bit)|bit(arrayflags_notbytep_bit)|Atype_String_Char,1,Array_type_string);
         # Flags: nur FILL_POINTER_BIT, Elementtyp STRING-CHAR, Rang=1
       TheIarray(new_array)->dims[1] = 0; # Fill-Pointer := 0
       TheIarray(new_array)->totalsize =
         TheIarray(new_array)->dims[0] = len; # L�nge und Total-Size eintragen
       TheIarray(new_array)->data = popSTACK(); # Datenvektor eintragen
       return new_array;
    } }

# UP: Schiebt ein String-Char in einen Semi-Simple String und erweitert ihn
# dabei eventuell.
# ssstring_push_extend(ssstring,ch)
# > ssstring: Semi-Simple String
# > ch: Character
# < ergebnis: derselbe Semi-Simple String
# kann GC ausl�sen
  global object ssstring_push_extend (object ssstring, uintB ch);
  global object ssstring_push_extend(ssstring,ch)
    var object ssstring;
    var uintB ch;
    { var object sstring = TheIarray(ssstring)->data; # Datenvektor (ein Simple-String)
      if (TheIarray(ssstring)->dims[1] # Fill-Pointer
          >= Sstring_length(sstring) ) # >= L�nge ?
        { # ja -> String wird um den Faktor 2 l�nger gemacht
          pushSTACK(ssstring); # ssstring retten
          pushSTACK(sstring); # Datenvektor ebenfalls retten
         {var object neuer_sstring = allocate_string(2 * Sstring_length(sstring));
          # neuer Simple-String der doppelten L�nge
          sstring = popSTACK(); # sstring zur�ck
          # Stringinhalt von String sstring nach String neuer_sstring kopieren:
          { var uintB* ptr1 = &TheSstring(sstring)->data[0];
            var uintB* ptr2 = &TheSstring(neuer_sstring)->data[0];
            var uintL count;
            dotimespL(count,Sstring_length(sstring), { *ptr2++ = *ptr1++; } );
          }
          ssstring = popSTACK(); # ssstring zur�ck
          set_break_sem_1(); # Unterbrechungen verbieten
          TheIarray(ssstring)->data = neuer_sstring; # neuen String als Datenvektor abspeichern
          TheIarray(ssstring)->totalsize =
            TheIarray(ssstring)->dims[0] = Sstring_length(neuer_sstring); # neue L�nge eintragen
          clr_break_sem_1(); # Unterbrechungen wieder zulassen
          sstring = neuer_sstring;
        }}
      # Nun ist wieder sstring der Datenvektor, und es gilt
      # Fill-Pointer < L�nge(Datenvektor).
      # Character hineinschieben und Fill-Pointer erh�hen:
      TheSstring(sstring)->data[ TheIarray(ssstring)->dims[1]++ ] = ch;
      return ssstring;
    }

#ifdef STRM_WR_SS
# UP: Stellt sicher, da� ein Semi-Simple String eine bestimmte L�nge hat
# und erweitert ihn dazu eventuell.
# ssstring_extend(ssstring,size)
# > ssstring: Semi-Simple String
# > size: gew�nschte Mindestgr��e
# < ergebnis: derselbe Semi-Simple String
# kann GC ausl�sen
  global object ssstring_extend (object ssstring, uintL needed_len);
  global object ssstring_extend(ssstring,needed_len)
    var object ssstring;
    var uintL needed_len;
    { var object sstring = TheIarray(ssstring)->data; # Datenvektor (ein Simple-String)
      var uintL now_len = Sstring_length(sstring); # jetzige Maximal-L�nge
      if (needed_len > now_len)
        { # ja -> String wird l�nger gemacht, mindestens um den Faktor 2:
          pushSTACK(ssstring); # ssstring retten
          pushSTACK(sstring); # Datenvektor ebenfalls retten
          now_len = now_len * 2;
          if (needed_len > now_len) { now_len = needed_len; } # now_len vergr��ern
         {var object neuer_sstring = allocate_string(now_len);
          # neuer Simple-String mindestens der gew�nschten und der doppelten L�nge
          sstring = popSTACK(); # sstring zur�ck
          # Stringinhalt von String sstring nach String neuer_sstring kopieren:
          { var uintB* ptr1 = &TheSstring(sstring)->data[0];
            var uintB* ptr2 = &TheSstring(neuer_sstring)->data[0];
            var uintL count;
            dotimespL(count,Sstring_length(sstring), { *ptr2++ = *ptr1++; } );
          }
          ssstring = popSTACK(); # ssstring zur�ck
          set_break_sem_1(); # Unterbrechungen verbieten
          TheIarray(ssstring)->data = neuer_sstring; # neuen String als Datenvektor abspeichern
          TheIarray(ssstring)->totalsize =
            TheIarray(ssstring)->dims[0] = now_len; # neue L�nge eintragen
          clr_break_sem_1(); # Unterbrechungen wieder zulassen
        }}
      return ssstring;
    }
#endif


# Stackaufbau bei MAKE-ARRAY :
#   dims, adjustable, element-type, initial-element, initial-contents,
#   fill-pointer, displaced-to, displaced-index-offset.
# Stackaufbau bei ADJUST-ARRAY :
#   dims, array, element-type, initial-element, initial-contents,
#   fill-pointer, displaced-to, displaced-index-offset.

# Fehlermeldung
# > dim: fehlerhafte Dimension
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(local, fehler_dim_type, (object dim));
  local void fehler_dim_type(dim)
    var object dim;
    { pushSTACK(dim); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(O(type_array_index)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(dim);
      pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: Dimension ~ ist nicht vom Typ `(INTEGER 0 (,ARRAY-DIMENSION-LIMIT))." :
             ENGLISH ? "~: dimension ~ is not of type `(INTEGER 0 (,ARRAY-DIMENSION-LIMIT))" :
             FRANCAIS ? "~: La dimension ~ n'est pas de type  `(INTEGER 0 (,ARRAY-DIMENSION-LIMIT))." :
             ""
            );
    }

# Hilfsroutine f�r MAKE-ARRAY und ADJUST-ARRAY:
# �berpr�ft die Dimensionen und liefert den Rang und die Gesamtgr��e.
# test_dims(&totalsize)
# > STACK_7: Dimension oder Dimensionenliste
# > subr_self: Aufrufer (ein SUBR)
# < totalsize: Gesamtgr��e = Produkt der Dimensionen
# < ergebnis: Rang = Anzahl der Dimensionen
  local uintL test_dims (uintL* totalsize_);
  local uintL test_dims(totalsize_)
    var uintL* totalsize_;
    { var object dims = STACK_7;
      if (listp(dims))
        { var uintL rank = 0; # bisherige Anzahl der Dimensionen
          var uintL totalsize = 1; # bisheriges Produkt der Dimensionen,
                                   # bleibt < arraysize_limit
          while (consp(dims))
            { var object dim = Car(dims); # n�chste Dimension
              # if (!integerp(dim)) { fehler_dim_type(dim); } # mu� Integer sein
              if (!posfixnump(dim)) { fehler_dim_type(dim); } # mu� Fixnum >=0 sein
              # totalsize * dim bilden:
             {var uintL produkt_hi;
              var uintL produkt_lo;
              #if (oint_data_len<=24)
              mulu24(totalsize,posfixnum_to_L(dim), produkt_hi=,produkt_lo=);
              #else
              mulu32(totalsize,posfixnum_to_L(dim), produkt_hi=,produkt_lo=);
              #endif
              #ifndef UNIX_DEC_ULTRIX_GCCBUG
              if (!((produkt_hi==0) && (produkt_lo<=arraysize_limit_1))) # Produkt < 2^24 ?
              #else
              if (!(produkt_hi==0))
              #endif
                { # nein -> (sofern nicht noch eine Dimension=0 kommt)
                  # Total-Size zu gro�
                  pushSTACK(STACK_7); # dims
                  pushSTACK(TheSubr(subr_self)->name);
                  fehler(error,
                         DEUTSCH ? "~: Dimensionen ~ ergeben zu gro�e Gesamtgr��e." :
                         ENGLISH ? "~: dimensions ~ produce too large total-size" :
                         FRANCAIS ? "~: Les dimensions ~ donnent une taille totale trop grande." :
                         ""
                        );
                }
              totalsize = produkt_lo;
              rank++;
              dims = Cdr(dims);
            }}
          *totalsize_ = totalsize;
          return rank;
        }
      # dims ist keine Liste. Sollte eine einzelne Dimension sein:
      # if (!integerp(dims)) { fehler_dim_type(dims); } # mu� Integer sein
      if (!posfixnump(dims)) { fehler_dim_type(dims); } # mu� Fixnum >=0 sein
      *totalsize_ = posfixnum_to_L(dims); # Totalsize = einzige Dimension
      return 1; # Rang = 1
    }

# Hilfsroutine f�r MAKE-ARRAY und ADJUST-ARRAY:
# �berpr�ft einige der Keywords.
  local void test_otherkeys (void);
  local void test_otherkeys()
    { # fill-pointer hat Defaultwert NIL:
      if (eq(STACK_2,unbound)) { STACK_2 = NIL; }
      # displaced-to hat Defaultwert NIL:
      if (eq(STACK_1,unbound)) { STACK_1 = NIL; }
      # Testen, ob mehr als eine Initialisierung
      # (:initial-element, :initial-contents, :displaced-to) angegeben wurde:
      { var uintB initcount = 0; # Z�hler
        if (!(eq(STACK_4,unbound))) { initcount++; } # initial-element angegeben?
        if (!(eq(STACK_3,unbound))) { initcount++; } # initial-contents angegeben?
        if (!nullp(STACK_1)) { initcount++; } # displaced-to angegeben?
        if (initcount > 1) # Mehr als eine Initialisierung?
          { pushSTACK(TheSubr(subr_self)->name);
            fehler(error,
                   DEUTSCH ? "~: Mehr als eine Initialisierung angegeben." :
                   ENGLISH ? "~: ambiguous, more than one initialisation specified" :
                   FRANCAIS ? "~: Il fut indiqu� plus d'une initialisation, c'est ambigu." :
                   ""
                  );
      }   }
      # Testen, ob :displaced-index-offset ohne :displaced-to verwendet wurde:
      if ((!eq(STACK_0,unbound)) # displaced-index-offset angegeben?
          && (nullp(STACK_1)) # und displaced-to nicht angegeben?
         )
        { pushSTACK(S(Kdisplaced_to));
          pushSTACK(S(Kdisplaced_index_offset));
          pushSTACK(TheSubr(subr_self)->name);
          fehler(error,
                 DEUTSCH ? "~: ~ darf nur zusammen mit ~ verwendet werden." :
                 ENGLISH ? "~: ~ must not be specified without ~" :
                 FRANCAIS ? "~: ~ ne peut �tre utilis� qu'avec ~." :
                 ""
                );
        }
    }

# Hilfsroutine f�r MAKE-ARRAY und ADJUST-ARRAY:
# erzeugt einen Datenvektor gegebener L�nge
# und f�llt ihn mit initial-element, falls angegeben.
# make_datenvektor(len,eltype)
# > len: L�nge
# > eltype: Elementtyp-Code
# > subr_self: Aufrufer (ein SUBR)
# < ergebnis: einfacher Vektor des gegebenen Typs, evtl. gef�llt.
# kann GC ausl�sen
  local object make_datenvektor (uintL len, uintB eltype);
  local object make_datenvektor(len,eltype)
    var uintL len;
    var uintB eltype;
    { switch (eltype)
        { case Atype_T: # Simple-Vector erzeugen
            { var object vektor = allocate_vector(len);
              if (!(eq(STACK_4,unbound))) # initial-element angegeben?
                if (!(len==0)) # und L�nge > 0 ?
                  { # ja -> Vektor mit initial-element f�llen:
                    var object* ptr = &TheSvector(vektor)->data[0];
                    var object initial_element = STACK_4;
                    dotimespL(len,len, { *ptr++ = initial_element; });
                  }
              return vektor;
            }
          case Atype_Bit: # Simple-Bit-Vector erzeugen
            { var object vektor = allocate_bit_vector(len);
              if (!(eq(STACK_4,unbound))) # initial-element angegeben?
                { # ja -> �berpr�fen:
                  var uint_bitpack initial_bitpack;
                  if (eq(STACK_4,Fixnum_0)) { initial_bitpack = (uint_bitpack)0UL; } # 0 -> mit Nullword f�llen
                  elif (eq(STACK_4,Fixnum_1)) { initial_bitpack = (uint_bitpack)~0UL; } # 1 -> mit Einsenword f�llen
                  else goto fehler_init;
                  if (!(len==0)) # und L�nge > 0 ?
                    { # ja -> Vektor mit initial-element f�llen:
                      var uint_bitpack* ptr = (uint_bitpack*)(&TheSbvector(vektor)->data[0]);
                      dotimespL(len,ceiling(len,bitpack), { *ptr++ = initial_bitpack; });
                }   }
              return vektor;
            }
          case Atype_String_Char: # Simple-String erzeugen
            { var object vektor = allocate_string(len);
              if (!(eq(STACK_4,unbound))) # initial-element angegeben?
                { # ja -> �berpr�fen, mu� String-Char sein:
                  if (!(string_char_p(STACK_4))) goto fehler_init;
                 {var uintB initial_char = char_code(STACK_4);
                  if (!(len==0)) # und L�nge > 0 ?
                    { # ja -> Vektor mit initial-element f�llen:
                      var uintB* ptr = &TheSstring(vektor)->data[0];
                      dotimespL(len,len, { *ptr++ = initial_char; });
                }}  }
              return vektor;
            }
          case Atype_2Bit:
          case Atype_4Bit:
          case Atype_8Bit:
          case Atype_16Bit:
          case Atype_32Bit: # semi-simplen Byte-Vektor erzeugen
            { var object vektor = allocate_byte_vector(eltype,len);
              if (!(eq(STACK_4,unbound))) # initial-element angegeben?
                { # ja -> �berpr�fen, mu� passender Integer sein:
                  var uintL wert;
                  if (eltype==Atype_32Bit)
                    { wert = I_to_UL(STACK_4); }
                    else
                    { if (!(posfixnump(STACK_4) && ((wert = posfixnum_to_L(STACK_4)) < bit(bit(eltype)))))
                        goto fehler_init;
                    }
                  if (!(len==0))
                    switch (eltype)
                      { case Atype_2Bit:
                          len = ceiling(len,2); wert |= wert<<2;
                        case Atype_4Bit:
                          len = ceiling(len,2); wert |= wert<<4;
                        case Atype_8Bit:
                          #if !(varobject_alignment%2 == 0)
                          { var uintB* ptr = &TheSbvector(TheIarray(vektor)->data)->data[0];
                            dotimespL(len,len, { *ptr++ = wert; });
                          }
                          break;
                          #else
                          # Kann mit 16-Bit-Bl�cken arbeiten
                          len = ceiling(len,2); wert |= wert<<8;
                          #endif
                        case Atype_16Bit:
                          #if !(varobject_alignment%4 == 0)
                          { var uint16* ptr = (uint16*)(&TheSbvector(TheIarray(vektor)->data)->data[0]);
                            dotimespL(len,len, { *ptr++ = wert; });
                          }
                          break;
                          #else
                          # Kann mit 32-Bit-Bl�cken arbeiten
                          len = ceiling(len,2); wert |= wert<<16;
                          #endif
                        case Atype_32Bit:
                          { var uint32* ptr = (uint32*)(&TheSbvector(TheIarray(vektor)->data)->data[0]);
                            dotimespL(len,len, { *ptr++ = wert; });
                          }
                          break;
                }     }
              return vektor;
            }
          default: NOTREACHED
          fehler_init:
            pushSTACK(STACK_4); # Wert f�r Slot DATUM von TYPE-ERROR
            pushSTACK(STACK_(5+1)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
            pushSTACK(STACK_(5+2)); # element-type
            pushSTACK(STACK_(4+3)); # initial-element
            pushSTACK(TheSubr(subr_self)->name);
            fehler(type_error,
                   DEUTSCH ? "~: Das Initialisierungselement ~ ist nicht vom Typ ~." :
                   ENGLISH ? "~: the initial-element ~ is not of type ~" :
                   FRANCAIS ? "~: L'�l�ment initial ~ n'est pas de type ~." :
                   ""
                  );
    }   }

# Hilfsroutine f�r MAKE-ARRAY und ADJUST-ARRAY:
# F�llt einen Vektor lexikographisch mit dem Inhalt einer verschachtelten
# Sequence-Struktur, wie sie als Argument zum Keyword :initial-contents
# bei MAKE-ARRAY und ADJUST-ARRAY anzugeben ist.
# initial_contents(datenvektor,dims,rank,contents)
# > datenvektor: ein simpler Vektor
# > dims: Dimension oder Dimensionenliste, alle Dimensionen Fixnums,
#         L�nge(datenvektor) = Produkt der Dimensionen
# > rank: Anzahl der Dimensionen
# > contents: verschachtelte Sequence-Struktur
# < ergebnis: derselbe Datenvektor
# Nicht reentrant!
# kann GC ausl�sen
  local object initial_contents (object datenvektor, object dims, uintL rank, object contents);
  typedef struct { object* localptr; # Pointer auf Datenvektor und Dimensionen
                   uintL index; # Index in den Datenvektor
                   uintL depth; # Rekursionstiefe
                 }
          initial_contents_locals;
  local map_sequence_function initial_contents_aux;
  local object initial_contents(datenvektor,dims,rank,contents)
    var object datenvektor;
    var object dims;
    var uintL rank;
    var object contents;
    { # alle Dimensionen auf den Stack:
      get_space_on_STACK(rank*sizeof(object));
      if (listp(dims))
        { while (consp(dims)) { pushSTACK(Car(dims)); dims = Cdr(dims); } }
        else
        { pushSTACK(dims); }
     {var initial_contents_locals locals;
      locals.localptr = &STACK_0; # aktuellen STACK-Wert merken
      locals.index = 0; # Index := 0
      locals.depth = rank; # depth := rank
      pushSTACK(datenvektor); # Datenvektor in den Stack
      pushSTACK(subr_self); # aktuelles SUBR retten
      initial_contents_aux(&locals,contents); # initial_contents_aux aufrufen
      subr_self = popSTACK(); # aktuelles SUBR zur�ck
      datenvektor = popSTACK(); # Datenvektor zur�ck
      skipSTACK(rank); # STACK aufr�umen
      return datenvektor;
    }}

# Hilfsfunktion f�r initial_contents:
# Arbeitet die Sequence-Struktur rekursiv ab.
local void initial_contents_aux (void* arg, object obj);
local void initial_contents_aux(arg,obj)
  var void* arg;
  var object obj;
  { var initial_contents_locals* locals = (initial_contents_locals*)arg;
    # �bergeben wird:
    # locals->depth = Rekursionstiefe,
    # locals->index = Index in den Datenvektor,
    # locals->localptr = Pointer auf die Dimensionen,
    #   bei Tiefe depth>0 ist ma�geblich
    #   Dimension (rank-depth) = *(localptr+depth-1),
    #   Datenvektor = *(localptr-1), Aufrufer = *(localptr-2).
    var object* localptr = locals->localptr;
    if (locals->depth==0)
      # Tiefe 0 -> Element obj in den Datenvektor eintragen:
      { var object datenvektor = *(localptr STACKop -1);
        subr_self = *(localptr STACKop -2);
        pushSTACK(obj);
        pushSTACK(datenvektor);
        datenvektor_store(datenvektor,locals->index,STACK_1);
        locals->index++;
        skipSTACK(2); # Stack aufr�umen
      }
      else
      # Tiefe >0 -> rekursiv aufrufen:
      { locals->depth--;
        pushSTACK(obj);
        # obj = STACK_0 mu� eine Sequence korrekter L�nge sein:
        pushSTACK(STACK_0); funcall(L(length),1); # L�nge bestimmen
        # mu� EQL (also EQ) zur Dimension *(localptr+depth) sein:
        if (!(eq(value1,*(localptr STACKop locals->depth))))
          { # fehlerhafte Sequence seq noch in STACK_0.
            pushSTACK(TheSubr(*(localptr STACKop -2))->name);
            fehler(error,
                   DEUTSCH ? "~: ~ hat nicht die richtige L�nge." :
                   ENGLISH ? "~: ~ is of incorrect length" :
                   FRANCAIS ? "~: ~ n'est pas de longueur convenable." :
                   ""
                  );
          }
        # L�nge stimmt, nun (MAP NIL #'INITIAL-CONTENTS-AUX seq) ausf�hren:
        map_sequence(STACK_0,&initial_contents_aux,locals);
        locals->depth++;
        skipSTACK(1); # Stack aufr�umen
      }
  }

# Hilfsroutine f�r MAKE-ARRAY und ADJUST-ARRAY:
# �berpr�fe ein displaced-to-Argument und den dazugeh�rigen Offset.
# test_displaced(eltype,totalsize)
# > eltype: Elementtyp-Code des zu erzeugenden Arrays
# > totalsize: Gesamtgr��e des zu erzeugenden Arrays
# > subr_self: Aufrufer (ein SUBR)
# < ergebnis: Wert des displaced-index-offset
  local uintL test_displaced (uintB eltype, uintL totalsize);
  local uintL test_displaced(eltype,totalsize)
    var uintB eltype;
    var uintL totalsize;
    { # displaced-to �berpr�fen, mu� ein Array sein:
      var object displaced_to = STACK_1;
      if (!arrayp(displaced_to))
        { pushSTACK(displaced_to); # Wert f�r Slot DATUM von TYPE-ERROR
          pushSTACK(S(array)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
          pushSTACK(displaced_to);
          pushSTACK(S(Kdisplaced_to));
          pushSTACK(TheSubr(subr_self)->name);
          fehler(type_error,
                 DEUTSCH ? "~: ~-Argument ~ ist kein Array." :
                 ENGLISH ? "~: ~-argument ~ is not an array" :
                 FRANCAIS ? "~: Le ~ argument ~ n'est pas une matrice." :
                 ""
                );
        }
      {# Elementtyp von displaced_to bestimmen:
       var uintB displaced_eltype;
       switch (Array_type(STACK_1))
         { case Array_type_mdarray: case Array_type_bvector: # allgemeiner Array -> Arrayflags anschauen
             displaced_eltype = Iarray_flags(displaced_to) & arrayflags_atype_mask;
             break;
           # Zuordnung  Vektor-Typinfo -> ATYPE-Byte :
           case Array_type_sbvector: displaced_eltype = Atype_Bit; break;
           case Array_type_string:
           case Array_type_sstring: displaced_eltype = Atype_String_Char; break;
           case Array_type_vector:
           case Array_type_svector: displaced_eltype = Atype_T; break;
           default: NOTREACHED
         }
       # displaced_eltype ist der ATYPE des :displaced-to-Arguments.
       # Gegebenen Elementtyp damit vergleichen:
       if (!(eltype == displaced_eltype))
         { pushSTACK(displaced_to); # Wert f�r Slot DATUM von TYPE-ERROR
           pushSTACK(S(array)); pushSTACK(STACK_(5+2)); pushSTACK(listof(2)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
           pushSTACK(STACK_(5+2)); # element-type
           pushSTACK(STACK_2); # displaced_to
           pushSTACK(S(Kdisplaced_to));
           pushSTACK(TheSubr(subr_self)->name);
           fehler(type_error,
                  DEUTSCH ? "~: ~-Argument ~ hat nicht den Elementtyp ~." :
                  ENGLISH ? "~: ~-argument ~ does not have element type ~" :
                  FRANCAIS ? "~: Le ~ argument ~ n'a pas ~ comme type d'�l�ment." :
                  ""
                 );
         }
      }
      {# Displaced-Index-Offset �berpr�fen:
       var uintL displaced_index_offset;
       if (eq(STACK_0,unbound)) { displaced_index_offset = 0; } # Default ist 0
       elif (posfixnump(STACK_0)) { displaced_index_offset = posfixnum_to_L(STACK_0); }
       else
         { pushSTACK(STACK_0); # Wert f�r Slot DATUM von TYPE-ERROR
           pushSTACK(O(type_array_index)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
           pushSTACK(STACK_(0+2));
           pushSTACK(S(Kdisplaced_index_offset));
           pushSTACK(TheSubr(subr_self)->name);
           fehler(type_error,
                  DEUTSCH ? "~: ~-Argument ~ ist nicht vom Typ `(INTEGER 0 (,ARRAY-TOTAL-SIZE-LIMIT))." :
                  ENGLISH ? "~: ~-argument ~ is not of type `(INTEGER 0 (,ARRAY-TOTAL-SIZE-LIMIT))" :
                  FRANCAIS ? "~: Le ~ argument ~ n'est pas de type `(INTEGER 0 (,ARRAY-TOTAL-SIZE-LIMIT))." :
                  ""
                 );
         }
       {# �berpr�fen, ob angesprochenes Teilst�ck ganz in displaced-to pa�t:
        var uintL displaced_totalsize = array_total_size(displaced_to);
        if (!(displaced_index_offset+totalsize <= displaced_totalsize))
          { pushSTACK(S(Kdisplaced_to));
            pushSTACK(fixnum(displaced_totalsize));
            pushSTACK(fixnum(displaced_index_offset));
            pushSTACK(TheSubr(subr_self)->name);
            fehler(error,
                   DEUTSCH ? "~: Array-Gesamtgr��e mit Displaced-Offset (~) > Gesamtgr��e ~ des ~-Arguments" :
                   ENGLISH ? "~: array-total-size + displaced-offset (= ~) exceeds total size ~ of ~-argument" :
                   FRANCAIS ? "~: La taille totale de la matrice avec �displaced-offset� (~) est sup�rieure � la taille totale ~ du ~ argument." :
                   ""
                  );
       }  }
       return displaced_index_offset;
    } }

# Hilfsroutine f�r MAKE-ARRAY und ADJUST-ARRAY:
# �berpr�fe ein fill-pointer-Argument /=NIL.
# test_fillpointer(len)
# > totalsize: Maximalwert von fill-pointer
# > subr_self: Aufrufer (ein SUBR)
# < ergebnis: Wert des fill-pointer
  local uintL test_fillpointer (uintL totalsize);
  local uintL test_fillpointer(totalsize)
    var uintL totalsize;
    { # fill-pointer war angegeben und /=NIL
      if (eq(STACK_2,S(t))) # T angegeben ->
        { return totalsize; } # Fill-Pointer := L�nge = Gesamtgr��e
      elif (!posfixnump(STACK_2)) # kein Fixnum >=0 -> Fehler
        { pushSTACK(STACK_2); # Wert f�r Slot DATUM von TYPE-ERROR
          pushSTACK(O(type_posfixnum)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
          pushSTACK(STACK_(2+2));
          pushSTACK(TheSubr(subr_self)->name);
          fehler(type_error,
                 DEUTSCH ? "~: Gew�nschter Fill-Pointer ~ sollte ein Fixnum >=0 sein." :
                 ENGLISH ? "~: fill-pointer ~ should be a nonnegative fixnum" :
                 FRANCAIS ? "~: Le pointeur de remplissage ~ devrait �tre de type FIXNUM positif ou z�ro." :
                 ""
                );
        }
      else
        { var uintL fillpointer = posfixnum_to_L(STACK_2);
          if (!(fillpointer <= totalsize)) # mit L�nge vergleichen
            { pushSTACK(fixnum(totalsize));
              pushSTACK(STACK_(2+1));
              pushSTACK(TheSubr(subr_self)->name);
              fehler(error,
                     DEUTSCH ? "~: Gew�nschter Fill-Pointer ~ ist gr��er als die L�nge ~" :
                     ENGLISH ? "~: fill-pointer argument ~ is larger than the length ~" :
                     FRANCAIS ? "~: L'argument ~ pour le pointeur de remplissage est plus grand que la longueur ~." :
                     ""
                    );
            }
          return fillpointer;
    }   }

LISPFUN(make_array,1,0,norest,key,7,\
        (kw(adjustable),kw(element_type),kw(initial_element),\
         kw(initial_contents),kw(fill_pointer),\
         kw(displaced_to),kw(displaced_index_offset)) )
# (MAKE-ARRAY dimensions :adjustable :element-type :initial-element
#   :initial-contents :fill-pointer :displaced-to :displaced-index-offset),
#   CLTL S. 286
  # Stackaufbau:
  #   dims, adjustable, element-type, initial-element, initial-contents,
  #   fill-pointer, displaced-to, displaced-index-offset.
  { # Dimensionen �berpr�fen und Rang und Total-Size berechnen:
    var uintL totalsize;
    var uintL rank = test_dims(&totalsize);
    # adjustable hat Defaultwert NIL:
    if (eq(STACK_6,unbound)) { STACK_6 = NIL; }
   {# element-type in einen Code umwandeln:
    var uintB eltype;
    if (!(eq(STACK_5,unbound)))
      { eltype = eltype_code(STACK_5); }
      else
      { # Defaultwert ist T.
        STACK_5 = S(t); eltype = Atype_T;
      }
    test_otherkeys(); # einiges �berpr�fen
    { var uintB flags = eltype;
      var uintL displaced_index_offset;
      var uintL fillpointer;
      if (!((eltype<=Atype_32Bit) && !(eltype==Atype_Bit))) # au�er bei Byte-Vektoren
        flags |= bit(arrayflags_notbytep_bit); # notbytep-Bit setzen
      # Falls nicht displaced, Datenvektor bilden und evtl. f�llen:
      if (nullp(STACK_1)) # displaced-to nicht angegeben?
        { # Datenvektor bilden:
          var object datenvektor = make_datenvektor(totalsize,eltype);
          if (!eq(STACK_3,unbound)) # und falls initial-contents angegeben:
            { datenvektor = initial_contents(datenvektor,STACK_7,rank,STACK_3); } # f�llen
          # Falls displaced-to nicht angegeben ist
          # und fill-pointer nicht angegeben ist
          # und adjustable nicht angegeben ist
          # und rank=1 ist,
          # ist ein (semi-)simpler Vektor zu liefern:
          if ((rank==1) && (nullp(STACK_6)) && (nullp(STACK_2)))
            { value1 = datenvektor; mv_count=1; # Datenvektor als Ergebnis
              skipSTACK(8); return;
            }
          # Es ist ein allgemeiner Array zu liefern.
          STACK_1 = datenvektor; # datenvektor als "displaced-to" ablegen
          displaced_index_offset = 0; # mit Displacement 0
          # und ohne Displacement-Bit in den Flags
        }
        else
        { # displaced-to angegeben -> Es ist ein allgemeiner Array zu liefern.
          displaced_index_offset = test_displaced(eltype,totalsize);
          # Flags enthalten das Displacement-Bit:
          flags |= bit(arrayflags_displaced_bit)|bit(arrayflags_dispoffset_bit);
        }
      # Erzeuge einen allgemeinen Array.
      # Rang �berpr�fen:
      #ifndef UNIX_DEC_ULTRIX_GCCBUG
      if (rank > arrayrank_limit_1)
        { pushSTACK(fixnum(rank)); # Wert f�r Slot DATUM von TYPE-ERROR
          pushSTACK(O(type_array_rank)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
          pushSTACK(fixnum(rank));
          pushSTACK(TheSubr(subr_self)->name);
          fehler(type_error,
                 DEUTSCH ? "~: Der gew�nschte Rang ~ ist zu gro�." :
                 ENGLISH ? "~: attempted rank ~ is too large" :
                 FRANCAIS ? "~: Le rang souhait� est trop grand." :
                 ""
                );
        }
      #endif
      # Flags f�r allocate_iarray zusammensetzen:
      # flags enth�lt schon eltype und evtl. Displacement-Bit.
      if (!nullp(STACK_6)) # adjustable angegeben?
        { flags |= bit(arrayflags_adjustable_bit)|bit(arrayflags_dispoffset_bit); }
      if (!nullp(STACK_2)) # fill-pointer angegeben?
        { if (!(rank==1)) # Rang mu� 1 sein
            { pushSTACK(fixnum(rank));
              pushSTACK(S(Kfill_pointer));
              pushSTACK(TheSubr(subr_self)->name);
              fehler(error,
                     DEUTSCH ? "~: ~ darf bei einem Array vom Rang ~ nicht angegeben werden." :
                     ENGLISH ? "~: ~ may not be specified for an array of rank ~" :
                     FRANCAIS ? "~: ~ ne peut pas �tre sp�cifi� avec une matrice de rang ~." :
                     ""
                    );
            }
          flags |= bit(arrayflags_fillp_bit);
          fillpointer = test_fillpointer(totalsize); # Fill-Pointer-Wert
        }
      # Typinfo f�r das zu erzeugende Objekt bestimmen:
     {var tint type;
      if (rank==1)
        { # Vektor: Typinfo aus Tabelle bestimmen
          local const tint type_table[8] =
            { # Tabelle f�r Zuordnung  ATYPE-Byte -> Vektor-Typinfo
              Array_type_bvector,  # Atype_Bit         -> Array_type_bvector
              Array_type_bvector,  # Atype_2Bit        -> Array_type_bvector
              Array_type_bvector,  # Atype_4Bit        -> Array_type_bvector
              Array_type_bvector,  # Atype_8Bit        -> Array_type_bvector
              Array_type_bvector,  # Atype_16Bit       -> Array_type_bvector
              Array_type_bvector,  # Atype_32Bit       -> Array_type_bvector
              Array_type_vector,   # Atype_T           -> Array_type_vector
              Array_type_string,   # Atype_String_Char -> Array_type_string
                                   # restliche ATYPEs unbenutzt
            };
          type = type_table[eltype];
        }
        else
        { # allgemeiner Array
          type = Array_type_mdarray;
        }
      # Array allozieren:
      { var object array = allocate_iarray(flags,rank,type);
        TheIarray(array)->totalsize = totalsize; # Total-Size eintragen
        {var uintL* dimptr = &TheIarray(array)->dims[0];
         if (flags & bit(arrayflags_dispoffset_bit))
           { *dimptr++ = displaced_index_offset; } # Displaced-Index-Offset eintragen
         # Dimensionen eintragen:
         { var object dims = STACK_7;
           if (listp(dims))
             { while (consp(dims))
                 { *dimptr++ = posfixnum_to_L(Car(dims)); dims = Cdr(dims); }
             }
             else
             { *dimptr++ = posfixnum_to_L(dims); }
         }
         # evtl. Fill-Pointer eintragen:
         if (flags & bit(arrayflags_fillp_bit))
           { # fill-pointer war angegeben und /=NIL
             *dimptr++ = fillpointer;
           }
        }
        # Datenvektor eintragen:
        TheIarray(array)->data = STACK_1; # displaced-to-Argument oder neuer Datenvektor
        # array als Wert:
        value1 = array; mv_count=1; skipSTACK(8);
  }}}}}

# Hilfsfunktion f�r die Umf�llaufgabe bei ADJUST-ARRAY:
# F�llt den Datenvektor eines Arrays teilweise mit dem Inhalt eines anderen
# Datenvektors, und zwar so, da� die Elemente zu Indextupeln, die f�r beide
# Arrays g�ltig sind, �bereinstimmen.
# reshape(newvec,newdims,oldvec,olddims,offset,rank,eltype);
# > newvec: (semi-)simpler Vektor, in den zu f�llen ist.
# > newdims: Dimension(en) des Arrays,
#            in dem newvec Datenvektor ist (mit Offset 0).
# > oldvec: (semi-)simpler Vektor, aus dem zu f�llen ist.
# > olddims: Pointer auf die Dimensionen des Arrays,
#            in dem oldvec Datenvektor ist (mit Offset offset).
# > rank: Dimensionszahl von newdims = Dimensionenzahl von olddims.
# > eltype: Elementtyp von newvec = Elementtyp von oldvec.
  local void reshape (object newvec, object newdims, object oldvec, const uintL* olddims, uintL offset, uintL rank, uintB eltype);
  # Methode: pseudo-rekursiv, mit Pseudo-Stack, der unterhalb von STACK liegt.
  typedef struct { uintL olddim; # Dimension aus olddims
                   uintL newdim; # Dimension aus newdims
                   uintL mindim; # minimale dieser Dimensionen
                   uintL subscript; # Subscript, l�uft von 0 bis mindim-1
                   uintL oldindex; # Row-Major-Index in oldvec
                   uintL newindex; # Row-Major-Index in newvec
                   uintL olddelta; # Increment von oldindex bei subscript++
                   uintL newdelta; # Increment von newindex bei subscript++
                 }
          reshape_data;
  local void reshape(newvec,newdims,oldvec,olddims,offset,rank,eltype)
    var object newvec;
    var object newdims;
    var object oldvec;
    var const uintL* olddims;
    var uintL offset;
    var uintL rank;
    var uintB eltype;
    { # Platz f�r den Pseudo-Stack reservieren:
      get_space_on_STACK(rank*sizeof(reshape_data));
      # Startpunkt:
     {var reshape_data* reshape_stack = &STACKblock_(reshape_data,-1);
      # Pseudo-Stack f�llen:
      if (!(rank==0))
        { var reshape_data* ptr;
          var uintC count;
          # jeweils newdim einf�llen:
          ptr = reshape_stack;
          if (consp(newdims))
            { dotimespC(count,rank,
                { ptr->newdim = posfixnum_to_L(Car(newdims)); newdims = Cdr(newdims);
                  ptr = ptr STACKop -1;
                });
            }
            else
            { ptr->newdim = posfixnum_to_L(newdims); }
          # jeweils olddim und mindim einf�llen:
          ptr = reshape_stack;
          dotimespC(count,rank,
            { var uintL olddim;
              var uintL newdim;
              olddim = ptr->olddim = *olddims++;
              newdim = ptr->newdim;
              ptr->mindim = (olddim<newdim ? olddim : newdim);
              ptr = ptr STACKop -1;
            });
          # jeweils olddelta und newdelta einf�llen:
          { var uintL olddelta = 1;
            var uintL newdelta = 1;
            dotimespC(count,rank,
              { ptr = ptr STACKop 1;
                ptr->olddelta = olddelta;
                olddelta = mulu32_unchecked(olddelta,ptr->olddim);
                ptr->newdelta = newdelta;
                newdelta = mulu32_unchecked(newdelta,ptr->newdim);
              });
          }
        }
      # Los geht's mit der Pseudo-Rekursion:
      { var reshape_data* ptr = reshape_stack;
        var uintL oldindex = offset; # Row-Major-Index in oldvec
        var uintL newindex = 0; # Row-Major-Index in newvec
        var uintL depth = rank;
        entry: # Rekursionseinstieg
          if (depth==0)
            { # Element kopieren:
              # (setf (aref newvec newindex) (aref oldvec oldindex))
              # so kopieren, da� keine GC ausgel�st werden kann:
              if (eltype == Atype_32Bit)
                { ((uint32*)&TheSbvector(TheIarray(newvec)->data)->data[0])[newindex]
                    = ((uint32*)&TheSbvector(TheIarray(oldvec)->data)->data[0])[oldindex];
                }
                else
                { datenvektor_store(newvec,newindex,datenvektor_aref(oldvec,oldindex)); }
            }
            else
            { # Schleife �ber alle gemeinsamen Indizes:
              ptr->oldindex = oldindex; ptr->newindex = newindex;
              depth--;
              dotimesL(ptr->subscript,ptr->mindim,
                { oldindex = ptr->oldindex; newindex = ptr->newindex;
                  ptr = ptr STACKop -1;
                  goto entry;
                  reentry:
                  ptr = ptr STACKop 1;
                  ptr->oldindex += ptr->olddelta;
                  ptr->newindex += ptr->newdelta;
                });
              depth++;
            }
          # Rekursionsaustritt:
          if (depth<rank) goto reentry;
    }}}

LISPFUN(adjust_array,2,0,norest,key,6,\
        (kw(element_type),kw(initial_element),\
         kw(initial_contents),kw(fill_pointer),\
         kw(displaced_to),kw(displaced_index_offset)) )
# (ADJUST-ARRAY array dimensions :element-type :initial-element
#   :initial-contents :fill-pointer :displaced-to :displaced-index-offset),
#   CLTL S. 297
  { # array �berpr�fen:
    { var object array = STACK_7;
      if (!arrayp(array)) { fehler_array(array); }
      if (array_simplep(array)
          || ((Iarray_flags(array) & bit(arrayflags_adjustable_bit)) == 0)
         )
        { # nicht adjustierbarer Array
          #ifndef X3J13_003
          pushSTACK(array);
          pushSTACK(TheSubr(subr_self)->name);
          fehler(error,
                 DEUTSCH ? "~: Array ~ ist nicht adjustierbar." :
                 ENGLISH ? "~: array ~ is not adjustable" :
                 FRANCAIS ? "~: La matrice ~ n'est pas ajustable." :
                 ""
                );
          #else
          ??
          #endif
        }
      STACK_7 = STACK_6; STACK_6 = array; # Stack etwas umordnen
    }
   # Stackaufbau:
   #   dims, array, element-type, initial-element, initial-contents,
   #   fill-pointer, displaced-to, displaced-index-offset.
   {# Dimensionen �berpr�fen und Rang und Total-Size berechnen:
    var uintL totalsize;
    var uintL rank = test_dims(&totalsize);
    # Rang �berpr�fen, mu� = (array-rank array) sein:
    {var uintL oldrank = (uintL)Iarray_rank(STACK_6);
     if (!(rank==oldrank))
       { pushSTACK(STACK_7); # dims
         pushSTACK(STACK_(6+1)); # array
         pushSTACK(fixnum(oldrank));
         pushSTACK(TheSubr(subr_self)->name);
         fehler(error,
                DEUTSCH ? "~: Dimensionszahl ~ des Arrays ~ kann nicht ge�ndert werden: ~" :
                ENGLISH ? "~: rank ~ of array ~ cannot be altered: ~" :
                FRANCAIS ? "~: Le rang ~ de la matrice ~ ne peut pas �tre modifi�." :
                ""
               );
    }  }
    {# element-type in einen Code umwandeln und �berpr�fen:
     var uintB eltype;
     if (!(eq(STACK_5,unbound)))
       { eltype = eltype_code(STACK_5);
         # mit dem Elementtyp des Array-Arguments vergleichen:
         if (!(eltype == (Iarray_flags(STACK_6) & arrayflags_atype_mask)))
           { pushSTACK(STACK_6); # Wert f�r Slot DATUM von TYPE-ERROR
             pushSTACK(S(array)); pushSTACK(STACK_(5+2)); pushSTACK(listof(2)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
             pushSTACK(STACK_(5+2)); # element-type
             pushSTACK(STACK_(6+3)); # array
             pushSTACK(TheSubr(subr_self)->name);
             fehler(type_error,
                    DEUTSCH ? "~: Array ~ hat nicht Elementtyp ~" :
                    ENGLISH ? "~: array ~ does not have element-type ~" :
                    FRANCAIS ? "~: La matrice ~ n'as pas ~ comme type d'�l�ment." :
                    ""
                   );
       }   }
       else
       { # Defaultwert ist der Elementtyp des Array-Arguments.
         eltype = (Iarray_flags(STACK_6) & arrayflags_atype_mask);
         STACK_5 = array_element_type(STACK_6);
       }
     test_otherkeys(); # einiges �berpr�fen
     { var uintB flags = Iarray_flags(STACK_6);
       # Die Flags enthalten genau eltype als Atype (mit evtl.
       # arrayflags_notbytep_bit) und arrayflags_adjustable_bit und daher auch
       # arrayflags_dispoffset_bit und vielleicht auch arrayflags_fillp_bit
       # (diese werden nicht ver�ndert) und vielleicht auch
       # arrayflags_displaced_bit (dieses kann ge�ndert werden).
       var uintL displaced_index_offset;
       var uintL fillpointer;
       # Falls nicht displaced, Datenvektor bilden und evtl. f�llen:
       if (nullp(STACK_1)) # displaced-to nicht angegeben?
         { # Datenvektor bilden:
           var object datenvektor = make_datenvektor(totalsize,eltype);
           if (!eq(STACK_3,unbound)) # und falls initial-contents angegeben:
             { # mit dem initial-contents-Argument f�llen:
               datenvektor = initial_contents(datenvektor,STACK_7,rank,STACK_3);
             }
             else
             { # mit dem urspr�nglichen Inhalt von array f�llen:
               var object oldarray = STACK_6; # array
               var uintL oldoffset = 0;
               var object oldvec = iarray_displace_check(oldarray,TheIarray(oldarray)->totalsize,&oldoffset);
               # oldvec ist der Datenvektor, mit Displaced-Offset oldoffset.
               var uintL* olddimptr = &TheIarray(oldarray)->dims[1];
               # Ab olddimptr kommen die alten Dimensionen von array
               # (beachte: Da arrayflags_adjustable_bit gesetzt ist, ist auch
               # arrayflags_dispoffset_bit gesetzt, also ist
               # TheIarray(array)->data[0] f�r den Displaced-Offset reserviert.)
               reshape(datenvektor,STACK_7,oldvec,olddimptr,oldoffset,rank,eltype);
             }
           STACK_1 = datenvektor; # datenvektor als "displaced-to" ablegen
           displaced_index_offset = 0; # mit Displacement 0
           flags &= ~bit(arrayflags_displaced_bit); # und ohne Displacement-Bit in den Flags
         }
         else
         { # displaced-to angegeben.
           displaced_index_offset = test_displaced(eltype,totalsize);
           # Test auf entstehenden Zyklus:
           { var object array = STACK_6; # Array, der displaced werden soll
             var object to_array = STACK_1; # Array, auf den displaced werden soll
             # Teste, ob array in der Datenvektorenkette von to_array vorkommt:
             loop
               { # Falls array = to_array, ist ein Zyklus da.
                 if (eq(array,to_array))
                   { pushSTACK(array);
                     pushSTACK(TheSubr(subr_self)->name);
                     fehler(error,
                            DEUTSCH ? "~: Array ~ kann nicht auf sich selbst displaced werden." :
                            ENGLISH ? "~: cannot displace array ~ to itself" :
                            FRANCAIS ? "~: La matrice ~ ne peut pas �tre d�plac�e (�displaced�) vers elle-m�me." :
                            ""
                           );
                   }
                 # Falls to_array simple ist (also nicht displaced),
                 # liegt kein Zyklus vor.
                 if (simplep(to_array)) break;
                 # Displaced-Kette von to_array weiterverfolgen:
                 to_array = TheIarray(to_array)->data;
           }   }
           # Flags enthalten das Displacement-Bit:
           flags |= bit(arrayflags_displaced_bit);
         }
       # Flags sind nun korrekt.
       # Modifiziere den gegebenen Array.
       if (!nullp(STACK_2)) # fill-pointer angegeben?
         { # array mu� Fill-Pointer haben:
           if (!(Iarray_flags(STACK_6) & bit(arrayflags_fillp_bit)))
             { pushSTACK(STACK_6); # Wert f�r Slot DATUM von TYPE-ERROR
               pushSTACK(O(type_vector_with_fill_pointer)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
               pushSTACK(STACK_(6+2));
               pushSTACK(TheSubr(subr_self)->name);
               fehler(type_error,
                      DEUTSCH ? "~: Array ~ hat keinen Fill-Pointer." :
                      ENGLISH ? "~: array ~ has no fill-pointer" :
                      FRANCAIS ? "~: La matrice ~ n'a pas de pointeur de remplissage." :
                      ""
                     );
             }
           fillpointer = test_fillpointer(totalsize); # Fill-Pointer-Wert
         }
         else
         { # Hat array einen Fill-Pointer, so mu� er <= neue Total-Size sein:
           var object array = STACK_6;
           if (Iarray_flags(array) & bit(arrayflags_fillp_bit))
             if (!(TheIarray(array)->dims[2] <= totalsize))
               # dims[0] = displaced-offset, dims[1] = L�nge, dims[2] = Fill-Pointer
               { pushSTACK(fixnum(totalsize));
                 pushSTACK(fixnum(TheIarray(array)->dims[2]));
                 pushSTACK(array);
                 pushSTACK(TheSubr(subr_self)->name);
                 fehler(error,
                        DEUTSCH ? "~: Array ~ hat einen Fill-Pointer ~ > gew�nschte L�nge ~." :
                        ENGLISH ? "~: the fill-pointer of array ~ is ~, greater than ~" :
                        FRANCAIS ? "~: La matrice ~ poss�de un pointeur de remplissage ~ sup�rieur � la longueur souhait�e ~." :
                        ""
                       );
         }     }
       # Array modifizieren:
       { var object array = STACK_6;
         set_break_sem_1(); # Unterbrechungen verbieten
         iarray_flags_replace(TheIarray(array),flags); # neue Flags eintragen
         TheIarray(array)->totalsize = totalsize; # neue Total-Size eintragen
         {var uintL* dimptr = &TheIarray(array)->dims[0];
          *dimptr++ = displaced_index_offset; # Displaced-Index-Offset eintragen
          # neue Dimensionen eintragen:
          { var object dims = STACK_7;
            if (listp(dims))
              { while (consp(dims))
                  { *dimptr++ = posfixnum_to_L(Car(dims)); dims = Cdr(dims); }
              }
              else
              { *dimptr++ = posfixnum_to_L(dims); }
          }
          # evtl. Fill-Pointer eintragen bzw. korrigieren:
          if (flags & bit(arrayflags_fillp_bit)) # Array mit Fill-Pointer?
            if (!nullp(STACK_2)) # und fill-pointer angegeben?
              { # fill-pointer war angegeben und /=NIL
                *dimptr = fillpointer;
              }
         }
         # Datenvektor eintragen:
         TheIarray(array)->data = STACK_1; # displaced-to-Argument oder neuer Datenvektor
         clr_break_sem_1(); # Unterbrechungen wieder zulassen
         # array als Wert:
         value1 = array; mv_count=1; skipSTACK(8);
  }}}} }


# Funktionen, die Vektoren zu Sequences machen:

LISPFUNN(vector_init,1)
# #'(lambda (seq) 0)
  { skipSTACK(1);
    value1 = Fixnum_0; mv_count=1; # 0 als Wert
  }

LISPFUNN(vector_upd,2)
# #'(lambda (seq pointer) (1+ pointer))
  { if (posfixnump(STACK_0))
      { var object newpointer = fixnum_inc(STACK_0,1); # Fixnum >=0 um 1 erh�hen
        if (posfixnump(newpointer))
          { # ist ein Fixnum >=0 geblieben
            skipSTACK(2);
            value1 = newpointer; mv_count=1; # newpointer als Wert
            return;
      }   }
    # Pointer ist vor oder nach dem Erh�hen kein Fixnum >=0
    funcall(L(einsplus),1); # (1+ pointer) als Wert
    skipSTACK(1);
  }

LISPFUNN(vector_endtest,2)
# #'(lambda (seq pointer) (= pointer (vector-length seq)))
  { var object seq = STACK_1;
    if (!vectorp(seq)) { fehler_vector(seq); }
    if (eq(fixnum(vector_length(seq)),STACK_0))
      { value1 = T; mv_count=1; skipSTACK(2); } # 1 Wert T
      else
      { value1 = NIL; mv_count=1; skipSTACK(2); } # 1 Wert NIL
  }

LISPFUNN(vector_fe_init,1)
# #'(lambda (seq) (1- (vector-length seq)))
  { var object seq = popSTACK();
    if (!vectorp(seq)) { fehler_vector(seq); }
   {var uintL len = vector_length(seq);
    # len = (vector-length seq).
    # Als Fixnum, und um 1 erniedrigen:
    value1 = (len==0 ? Fixnum_minus1 : fixnum(len-1));
    mv_count=1;
  }}

LISPFUNN(vector_fe_upd,2)
# #'(lambda (seq pointer) (1- pointer))
  { if (posfixnump(STACK_0))
      { var object pointer = popSTACK();
        value1 = (eq(pointer,Fixnum_0)
                  ? Fixnum_minus1
                  : fixnum_inc(pointer,-1) # Fixnum >0 um 1 erniedrigen
                 );
        mv_count=1;
      }
      else
      { # Pointer ist vor oder nach dem Erniedrigen kein Fixnum >=0
        funcall(L(einsminus),1); # (1- pointer) als Wert
      }
    skipSTACK(1);
  }

LISPFUNN(vector_fe_endtest,2)
# #'(lambda (seq pointer) (minusp pointer))
  { value1 = (positivep(STACK_0) ? NIL : T); # Vorzeichen von pointer abfragen
    mv_count=1;
    skipSTACK(2);
  }

LISPFUNN(vector_length,1)
  { var object seq = popSTACK();
    if (!vectorp(seq)) { fehler_vector(seq); }
    value1 = fixnum(vector_length(seq)); mv_count=1;
  }

LISPFUNN(vector_init_start,2)
# #'(lambda (seq index)
#     (if (<= 0 index (vector-length seq))
#       index
#       (error "Unzul�ssiger :START - Index : ~S" index)
#   ) )
  { var object seq = STACK_1;
    if (!vectorp(seq)) { fehler_vector(seq); }
   {var uintL len = vector_length(seq);
    # index sollte ein Fixnum zwischen 0 und len (inclusive) sein:
    if (posfixnump(STACK_0) && (posfixnum_to_L(STACK_0)<=len))
      { value1 = STACK_0; mv_count=1; skipSTACK(2); } # index als Wert
      else
      { # Stackaufbau: seq, index.
        pushSTACK(STACK_0); # Wert f�r Slot DATUM von TYPE-ERROR
        { var object tmp;
          pushSTACK(S(integer)); pushSTACK(Fixnum_0); pushSTACK(UL_to_I(len));
          tmp = listof(3); pushSTACK(tmp); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
        }
        pushSTACK(STACK_3); # seq
        pushSTACK(STACK_3); # index
        fehler(type_error,
               DEUTSCH ? "Unzul�ssiger START - Index ~ f�r ~" :
               ENGLISH ? "Illegal START index ~ for ~" :
               FRANCAIS ? "Index START ~ invalide pour ~." :
               ""
              );
      }
  }}

LISPFUNN(vector_fe_init_end,2)
# #'(lambda (seq index)
#     (if (<= 0 index (vector-length seq))
#       (1- index)
#       (error "Unzul�ssiger :END - Index : ~S" index)
#   ) )
  { var object seq = STACK_1;
    if (!vectorp(seq)) { fehler_vector(seq); }
   {var uintL len = vector_length(seq);
    # index sollte ein Fixnum zwischen 0 und len (inclusive) sein:
    if (posfixnump(STACK_0) && (posfixnum_to_L(STACK_0)<=len))
      { var object index = STACK_0;
        skipSTACK(2);
        value1 = (eq(index,Fixnum_0)
                  ? Fixnum_minus1
                  : fixnum_inc(index,-1) # Fixnum >0 um 1 erniedrigen
                 );
        mv_count=1;
      }
      else
      { # Stackaufbau: seq, index.
        pushSTACK(STACK_0); # Wert f�r Slot DATUM von TYPE-ERROR
        { var object tmp;
          pushSTACK(S(integer)); pushSTACK(Fixnum_0); pushSTACK(UL_to_I(len));
          tmp = listof(3); pushSTACK(tmp); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
        }
        pushSTACK(STACK_3); # seq
        pushSTACK(STACK_3); # index
        fehler(type_error,
               DEUTSCH ? "Unzul�ssiger END - Index ~ f�r ~" :
               ENGLISH ? "Illegal END index ~ for ~" :
               FRANCAIS ? "Index END ~ invalide pour ~." :
               ""
              );
      }
  }}

LISPFUNN(make_bit_vector,1)
# (SYS::MAKE-BIT-VECTOR size) liefert einen Bit-Vector mit size Bits.
  { if (!posfixnump(STACK_0))
      { # STACK_0 = size, Wert f�r Slot DATUM von TYPE-ERROR
        pushSTACK(O(type_posfixnum)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
        pushSTACK(STACK_1); # size
        pushSTACK(TheSubr(subr_self)->name);
        fehler(type_error,
               DEUTSCH ? "~: Als Bit-Vektoren-L�nge ist ~ ungeeignet." :
               ENGLISH ? "~: invalid bit-vector length ~" :
               FRANCAIS ? "~: ~ n'est pas convenable comme longeur de vecteur bit." :
               ""
              );
      }
   {var uintL size = posfixnum_to_L(popSTACK()); # L�nge
    value1 = allocate_bit_vector(size); # euen Bit-Vektor beschaffen
    mv_count=1;
  }}

