# Funktionen f�r Records und Structures von CLISP
# Bruno Haible 20.8.1996

#include "lispbibl.c"


# ==============================================================================
# Records allgemein:

# (SYS::%RECORD-REF record index) liefert den Eintrag index in einem record.
# (SYS::%RECORD-STORE record index value) speichert value als Eintrag index
#   in record ab und liefert value.
# (SYS::%RECORD-LENGTH record) liefert die L�nge eines record.

# Fehlermeldung
# > STACK_1: Record
# > STACK_0: (fehlerhafter) Index
# > limit: exklusive Obergrenze f�r den Index
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(local, fehler_index, (uintL limit));
  local void fehler_index(limit)
    var uintL limit;
    { pushSTACK(STACK_0); # Wert f�r Slot DATUM von TYPE-ERROR
      { var object tmp;
        pushSTACK(S(integer)); pushSTACK(Fixnum_0); pushSTACK(UL_to_I(limit));
        tmp = listof(1); pushSTACK(tmp); tmp = listof(3);
        pushSTACK(tmp); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      }
      pushSTACK(STACK_(1+2)); # Record
      pushSTACK(STACK_(0+3)); # Index
      pushSTACK(TheSubr(subr_self)->name); # Funktionsname
      fehler(type_error,
             DEUTSCH ? "~: ~ ist kein erlaubter Index f�r ~." :
             ENGLISH ? "~: ~ is not a valid index into ~" :
             FRANCAIS ? "~ : ~ n'est pas un index valide pour ~." :
             ""
            );
    }

# Fehlermeldung
# > STACK_0: (fehlerhafter) Record
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(local, fehler_record, (void));
  local void fehler_record()
    { pushSTACK(TheSubr(subr_self)->name); # Funktionsname
      fehler(error, # type_error ??
             DEUTSCH ? "~: ~ ist kein Record." :
             ENGLISH ? "~: ~ is not a record" :
             FRANCAIS ? "~ : ~ n'est pas un �record�." :
             ""
            );
    }

# Unterprogramm f�r Record-Zugriffsfunktionen:
# > STACK_1: record-Argument
# > STACK_0: index-Argument
# > subr_self: Aufrufer (ein SUBR)
# < STACK: aufger�umt
# < ergebnis: Adresse des angesprochenen Record-Elements
  local object* record_up (void);
  local object* record_up ()
    { # record muss vom Typ Closure/Structure/Stream/OtherRecord sein:
      if_recordp(STACK_1, ; , { skipSTACK(1); fehler_record(); } );
     {var object record = STACK_1;
      var uintL length = Record_length(record);
      var uintL index;
      if (!(posfixnump(STACK_0) && ((index = posfixnum_to_L(STACK_0)) < length))) # Index holen und pr�fen
        { fehler_index(length); }
      skipSTACK(2); # Stack aufr�umen
      return &TheRecord(record)->recdata[index]; # Record-Element adressieren
    }}

LISPFUNN(record_ref,2)
# (SYS::%RECORD-REF record index) liefert den Eintrag index in einem record.
  { value1 = *(record_up()); mv_count=1; } # Record-Element als Wert

LISPFUNN(record_store,3)
# (SYS::%RECORD-STORE record index value) speichert value als Eintrag index
#   in record ab und liefert value.
  { var object value = popSTACK();
    value1 = *(record_up()) = value; mv_count=1; # Record-Element eintragen
  }

LISPFUNN(record_length,1)
# (SYS::%RECORD-LENGTH record) liefert die L�nge eines record.
  { # record muss vom Typ Closure/Structure/Stream/OtherRecord sein:
    if_recordp(STACK_0, ; , { fehler_record(); } );
   {var object record = popSTACK();
    var uintL length = Record_length(record);
    value1 = fixnum(length); mv_count=1; # L�nge als Fixnum
  }}

# �berpr�fung einer L�nge auf Typ (INTEGER (0) (65536))
# > STACK_0: gew�nschte L�nge
# > subr_self: Aufrufer (ein SUBR)
# < uintL length: L�nge, �berpr�ft
  #define test_record_length(length)  \
    if (!(posfixnump(STACK_0)                                                  \
          && ((length = posfixnum_to_L(STACK_0)) <= (uintL)(bitm(intWsize)-1)) \
          && (length>0)                                                        \
       ) )                                                                     \
      fehler_record_length();
  nonreturning_function(local, fehler_record_length, (void));
  local void fehler_record_length()
    { # STACK_0 = length, Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(O(type_posint16)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(STACK_1); # length
      pushSTACK(TheSubr(subr_self)->name); # Funktionsname
      fehler(type_error,
             DEUTSCH ? "~: ~ ist nicht als L�nge zugelassen, da nicht vom Typ (INTEGER (0) (65536))." :
             ENGLISH ? "~: length ~ is illegal, should be of type (INTEGER (0) (65536))" :
             FRANCAIS ? "~ : ~ n'est pas permis comme longueur parce qu'il faut le type (INTEGER (0) (65536))." :
             ""
            );
    }

# ==============================================================================
# Structures:

# (SYS::%STRUCTURE-REF type structure index) liefert zu einer Structure vom
#   gegebenen Typ type (ein Symbol) den Eintrag index>=1.
# (SYS::%STRUCTURE-STORE type structure index object) speichert object als
#   Eintrag index in einer Structure vom gegebenen Typ type und liefert object.
# (SYS::%MAKE-STRUCTURE type length) erzeugt eine Structure mit length>=1
#   Elementen, vom Typ type.
# (COPY-STRUCTURE structure) liefert eine Kopie der Structure structure,
#   vom selben Typ.
# (SYS::%STRUCTURE-TYPE-P type object) �berpr�ft, ob object eine
#   Structure ist, die vom Typ type ist, was daran erkennbar ist, dass in
#   der Komponente 0 ein Objekt (name_1 ... name_i-1 name_i) steht, wobei
#   einer der Namen EQ zu type ist.

# Unterprogramm f�r Structure-Zugriffsfunktionen:
# > STACK_2: type-Argument
# > STACK_1: structure-Argument
# > STACK_0: index-Argument
# > subr_self: Aufrufer (ein SUBR)
# < ergebnis: Adresse des angesprochenen Structure-Elements
  local object* structure_up (void);
  local object* structure_up ()
    { # structure muss vom Typ Structure sein:
      if (!structurep(STACK_1))
        { fehler_bad_structure: # STACK_2 = type, STACK_1 = structure
          pushSTACK(STACK_1); # Wert f�r Slot DATUM von TYPE-ERROR
          pushSTACK(STACK_(2+1)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
          pushSTACK(STACK_(2+2));
          pushSTACK(STACK_(1+3));
          pushSTACK(TheSubr(subr_self)->name); # Funktionsname
          fehler(type_error,
                 DEUTSCH ? "~: ~ ist keine Structure vom Typ ~." :
                 ENGLISH ? "~: ~ is not a structure of type ~" :
                 FRANCAIS ? "~ : ~ n'est pas une structure de type ~." :
                 ""
                );
        }
     {var object structure = STACK_1;
      var object namelist = TheStructure(structure)->structure_types; # erste Komponente
      var object type = STACK_2; # type-Argument
      # Teste, ob in namelist = (name_1 ... name_i-1 name_i) type vorkommt:
      while (consp(namelist))
        { if (eq(Car(namelist),type)) goto yes;
          namelist = Cdr(namelist);
        }
      # type kam nicht vor -> Error:
      goto fehler_bad_structure;
      # type kam vor:
      yes:
      {var uintL length = (uintL)Structure_length(structure);
       var uintL index;
       if (!(posfixnump(STACK_0) && ((index = posfixnum_to_L(STACK_0)) < length))) # Index holen und pr�fen
         { fehler_index(length); }
       return &TheStructure(structure)->recdata[index]; # Structure-Komponente adressieren
    }}}

LISPFUNN(pstructure_ref,3)
# (SYS::%%STRUCTURE-REF type structure index) liefert zu einer Structure vom
#   gegebenen Typ type (ein Symbol) den Eintrag index>=1.
# #<UNBOUND> ist m�glich.
  { value1 = *(structure_up()); mv_count=1; # Structure-Element als Wert
    skipSTACK(3); # Stack aufr�umen
  }

LISPFUNN(structure_ref,3)
# (SYS::%STRUCTURE-REF type structure index) liefert zu einer Structure vom
#   gegebenen Typ type (ein Symbol) den Eintrag index>=1.
  { value1 = *(structure_up()); # Structure-Element als Wert
    if (eq(value1,unbound)) # K�nnte = #<UNBOUND> sein, nach Gebrauch von SLOT-MAKUNBOUND oder nach unvollst�ndigem INITIALIZE-INSTANCE
      { dynamic_bind(S(print_length),Fixnum_0); # *PRINT-LENGTH* an 0 binden
        pushSTACK(STACK_(1+3)); # Wert f�r Slot INSTANCE von UNBOUND-SLOT
        # (clos::slotdef-name (find index (clos::class-slots (find-class type)) :key #'clos::slotdef-location))
        pushSTACK(STACK_(2+3+1)); funcall(L(find_class),1);
        pushSTACK(value1); funcall(S(class_slots),1);
        pushSTACK(STACK_(0+3+1)); pushSTACK(value1); pushSTACK(S(Kkey)); pushSTACK(Symbol_function(S(slotdef_location))); funcall(L(find),4);
        pushSTACK(value1); funcall(S(slotdef_name),1);
        pushSTACK(value1); # Wert f�r Slot NAME von UNBOUND-SLOT
        pushSTACK(STACK_(1+3+2));
        pushSTACK(value1);
        pushSTACK(S(structure_ref));
        fehler(unbound_slot,
               DEUTSCH ? "~: Slot ~ von ~ hat keinen Wert." :
               ENGLISH ? "~: Slot ~ of ~ has no value" :
               FRANCAIS ? "~ : Composant ~ de ~ n'a pas de valeur." :
               ""
              );
      }
    mv_count=1;
    skipSTACK(3); # Stack aufr�umen
  }

LISPFUNN(structure_store,4)
# (SYS::%STRUCTURE-STORE type structure index object) speichert object als
#   Eintrag index in einer Structure vom gegebenen Typ type und liefert object.
  { var object value = popSTACK();
    value1 = *(structure_up()) = value; mv_count=1; # Structure-Element eintragen
    skipSTACK(3); # Stack aufr�umen
  }

LISPFUNN(make_structure,2)
# (SYS::%MAKE-STRUCTURE type length) erzeugt eine Structure mit length>=1
#   Elementen, vom Typ type.
  { # L�nge �berpr�fen, sollte ein Fixnum /=0 sein, das in ein uintW passt:
    var uintL length;
    test_record_length(length);
    skipSTACK(1);
   {var object structure = allocate_structure(length);
    # neue Structure, mit NILs gef�llt
    TheStructure(structure)->structure_types = popSTACK(); # Typ-Komponente eintragen
    value1 = structure; mv_count=1; # structure als Wert
  }}

LISPFUNN(copy_structure,1)
# (COPY-STRUCTURE structure) liefert eine Kopie der Structure structure,
#   vom selben Typ.
  { if (!structurep(STACK_0))
      { # STACK_0 = Wert f�r Slot DATUM von TYPE-ERROR
        pushSTACK(S(structure_object)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
        pushSTACK(STACK_1); # structure
        pushSTACK(TheSubr(subr_self)->name); # Funktionsname
        fehler(type_error,
               DEUTSCH ? "~: ~ ist keine Structure." :
               ENGLISH ? "~: ~ is not a structure" :
               FRANCAIS ? "~ : ~ n'est pas une structure." :
               ""
              );
      }
   {var uintC length = Structure_length(STACK_0);
    var object new_structure = allocate_structure(length); # neue Structure
    # und f�llen:
    {var object* old_ptr = &TheStructure(popSTACK())->structure_types;
     var object* new_ptr = &TheStructure(new_structure)->structure_types;
     dotimespC(length,length, { *new_ptr++ = *old_ptr++; });
    }
    # und als Wert zur�ck:
    value1 = new_structure; mv_count=1;
  }}

LISPFUNN(structure_type_p,2)
# (SYS::%STRUCTURE-TYPE-P type object) �berpr�ft, ob object eine
#   Structure ist, die vom Typ type ist, was daran erkennbar ist, dass in
#   der Komponente 0 ein Objekt (name_1 ... name_i-1 name_i) steht, wobei
#   einer der Namen EQ zu type ist.
  { # object auf Structure testen:
    if (!structurep(STACK_0)) { skipSTACK(2); goto no; }
    { var object namelist = TheStructure(popSTACK())->structure_types;
      var object type = popSTACK();
      # Teste, ob in namelist = (name_1 ... name_i-1 name_i) type vorkommt:
      while (consp(namelist))
        { if (eq(Car(namelist),type)) goto yes;
          namelist = Cdr(namelist);
    }   }
    # type kam nicht vor:
    no: value1 = NIL; mv_count=1; return; # 1 Wert NIL
    # type kam vor:
    yes: value1 = T; mv_count=1; return; # 1 Wert T
  }

# ==============================================================================
# Closures:

# (SYS::CLOSURE-NAME closure) liefert den Namen einer Closure.
# (SYS::CLOSURE-CODEVEC closure) liefert den Code-Vektor einer compilierten
#   Closure, als Liste von Fixnums >=0, <256.
# (SYS::CLOSURE-CONSTS closure) liefert eine Liste aller Konstanten einer
#   compilierten Closure.
# (SYS::MAKE-CODE-VECTOR list) liefert zu einer Liste von Fixnums >=0, <256
#   einen Simple-Bit-Vector der 8-fachen L�nge, der diese Zahlen als Bytes
#   enth�lt.
# (SYS::%MAKE-CLOSURE name codevec consts) liefert eine Closure mit gegebenem
#   Namen (einem Symbol), gegebenem Code-Vektor (einem Simple-Bit-Vector) und
#   gegebenen weiteren Konstanten.
# (SYS::GENERIC-FUNCTION-EFFECTIVE-METHOD-FUNCTION generic-function)
#   liefert eine Funktion, die die effektiven Methoden liefert, d.h. so dass
#   (APPLY generic-function arguments)
#   == (APPLY (APPLY ergebnis arguments) arguments)  w�re.

LISPFUNN(closure_name,1)
# (SYS::CLOSURE-NAME closure) liefert den Namen einer Closure.
  { var object closure = popSTACK();
    if (!(closurep(closure)))
      { pushSTACK(closure);
        pushSTACK(TheSubr(subr_self)->name); # Funktionsname
        fehler(error, # type_error ??
               DEUTSCH ? "~: ~ ist keine Closure." :
               ENGLISH ? "~: ~ is not a closure" :
               FRANCAIS ? "~ : ~ n'est pas une fermeture." :
               ""
              );
      }
    value1 = TheClosure(closure)->clos_name; mv_count=1;
  }

# Fehler, wenn Argument keine compilierte Closure
  nonreturning_function(local, fehler_cclosure, (object obj));
  local void fehler_cclosure(obj)
    var object obj;
    { pushSTACK(obj);
      pushSTACK(TheSubr(subr_self)->name); # Funktionsname
      fehler(error, # type_error ??
             DEUTSCH ? "~: Das ist keine compilierte Closure: ~" :
             ENGLISH ? "~: This is not a compiled closure: ~" :
             FRANCAIS ? "~ : Ceci n'est pas un fermeture compil�e : ~" :
             ""
            );
    }

LISPFUNN(closure_codevec,1)
# (SYS::CLOSURE-CODEVEC closure) liefert den Code-Vektor einer compilierten
#   Closure, als Liste von Fixnums >=0, <256.
  { var object closure = popSTACK();
    if (!(cclosurep(closure))) fehler_cclosure(closure);
   {var object codevec = TheCclosure(closure)->clos_codevec;
    var uintL index = Sbvector_length(codevec)/8; # index := L�nge in Bytes
    # Codevektor codevec von hinten durchgehen und Bytes auf eine Liste pushen:
    pushSTACK(codevec); # Codevektor
    pushSTACK(NIL); # Liste := ()
    until (index==0)
      { index--; # Index decrementieren
        # neues Cons vor die Liste setzen:
       {var object new_cons = allocate_cons();
        Cdr(new_cons) = popSTACK();
        Car(new_cons) = fixnum((uintL)(TheSbvector(STACK_0)->data[index])); # Byte herausholen
        pushSTACK(new_cons);
      }}
    value1 = STACK_0; mv_count=1; skipSTACK(2); # Liste als Wert
  }}

LISPFUNN(closure_consts,1)
# (SYS::CLOSURE-CONSTS closure) liefert eine Liste aller Konstanten einer
#   compilierten Closure.
  { var object closure = popSTACK();
    if (!(cclosurep(closure))) fehler_cclosure(closure);
    # Elemente 2,3,... zu einer Liste zusammenfassen:
   {var uintC index = Cclosure_length(closure)-2; # index := L�nge
    # Closure von hinten durchgehen und Konstanten auf eine Liste pushen:
    pushSTACK(closure); # Closure
    pushSTACK(NIL); # Liste := ()
    until (index==0)
      { index--; # Index decrementieren
        # neues Cons vor die Liste setzen:
       {var object new_cons = allocate_cons();
        Cdr(new_cons) = popSTACK();
        Car(new_cons) = TheCclosure(STACK_0)->clos_consts[(uintP)index]; # Konstante herausholen
        pushSTACK(new_cons);
      }}
    value1 = STACK_0; mv_count=1; skipSTACK(2); # Liste als Wert
  }}

LISPFUNN(make_code_vector,1)
# (SYS::MAKE-CODE-VECTOR list) liefert zu einer Liste von Fixnums >=0, <256
#   einen Simple-Bit-Vector der 8-fachen L�nge, der diese Zahlen als Bytes
#   enth�lt.
  { var object bv = allocate_bit_vector(8*llength(STACK_0)); # Simple-Bit-Vektor
    # f�llen:
    var object listr = popSTACK(); # Liste
    var uintB* ptr = &TheSbvector(bv)->data[0]; # l�uft durch den Bit-Vektor
    while (consp(listr))
      { var uintL byte;
        # Listenelement muss ein Fixnum >=0, <256 sein:
        if (!(posfixnump(Car(listr))
              && ((byte = posfixnum_to_L(Car(listr))) < (1<<intBsize))
           ) )
          goto bad_byte;
        # in den Bit-Vektor stecken:
        *ptr++ = (uintB)byte;
        listr = Cdr(listr);
      }
    value1 = bv; mv_count=1; return; # bv als Wert
    bad_byte:
      pushSTACK(Car(listr)); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(O(type_uint8)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(STACK_1);
      fehler(type_error,
             DEUTSCH ? "~ ist als Byte in einem Code-Vektor ungeeignet." :
             ENGLISH ? "~ is not a valid code-vector byte" :
             FRANCAIS ? "~ est inutilisable comme octet dans un �code-vector�." :
             ""
            );
  }

LISPFUNN(make_closure,3)
# (SYS::%MAKE-CLOSURE name codevec consts) liefert eine Closure mit gegebenem
#   Namen (einem Symbol), gegebenem Code-Vektor (einem Simple-Bit-Vector) und
#   gegebenen weiteren Konstanten.
  { # codevec muss ein Simple-Bit-Vector sein:
    if (!simple_bit_vector_p(STACK_1))
      { # STACK_1 = codevec
        pushSTACK(STACK_1); # Wert f�r Slot DATUM von TYPE-ERROR
        pushSTACK(S(simple_bit_vector)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
        pushSTACK(STACK_(1+2));
        pushSTACK(TheSubr(subr_self)->name);
        fehler(type_error,
               DEUTSCH ? "~: Als Code-Vektor einer Funktion ist ~ ungeeignet." :
               ENGLISH ? "~: invalid code-vector ~" :
               FRANCAIS ? "~ : ~ n'est pas utilisable comme �code-vector� d'une fonction." :
               ""
              );
      }
   {# neue Closure der L�nge (+ 2 (length consts)) erzeugen:
    var uintL length = 2+llength(STACK_0);
    if (!(length <= (uintL)(bitm(intWsize)-1))) # sollte in ein uintW passen
      { # STACK_0 = consts
        pushSTACK(STACK_2); # name
        pushSTACK(TheSubr(subr_self)->name);
        fehler(error,
               DEUTSCH ? "~: Funktion ~ ist zu gro�: ~" :
               ENGLISH ? "~: function ~ is too big: ~" :
               FRANCAIS ? "~ : La function ~ est trop grosse: ~" :
               ""
              );
      }
    {var object closure = allocate_closure(length);
     TheCclosure(closure)->clos_name = STACK_2; # Namen einf�llen
     TheCclosure(closure)->clos_codevec = STACK_1; # Codevektor einf�llen
     # Konstanten einf�llen:
     {var object constsr = popSTACK();
      var object* ptr = &TheCclosure(closure)->clos_consts[0];
      while (consp(constsr))
        { *ptr++ = Car(constsr); constsr = Cdr(constsr); }
     }
     value1 = closure; mv_count=1; skipSTACK(2);
  }}}

LISPFUNN(generic_function_effective_method_function,1)
# (SYS::GENERIC-FUNCTION-EFFECTIVE-METHOD-FUNCTION generic-function)
#   liefert eine Funktion, die die effektiven Methoden liefert, d.h. so dass
#   (APPLY generic-function arguments)
#   == (APPLY (APPLY ergebnis arguments) arguments)  w�re.
#   Verwendet f�r CALL-NEXT-METHOD; kann deswegen voraussetzen, dass die
#   generic-function schon aufgerufen wurde, d.h. dass der Dispatch schon
#   installiert ist.
  { var object oldclos = STACK_0;
    var object newclos;
    if (!genericfunctionp(oldclos))
      { pushSTACK(oldclos); # Wert f�r Slot DATUM von TYPE-ERROR
        pushSTACK(S(standard_generic_function)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
        pushSTACK(oldclos);
        pushSTACK(TheSubr(subr_self)->name); # Funktionsname
        fehler(type_error,
               DEUTSCH ? "~: Das ist keine generische Funktion: ~" :
               ENGLISH ? "~: This is not a generic function: ~" :
               FRANCAIS ? "~ : Ceci n'est pas une fonction g�n�rique : ~" :
               ""
              );
      }
    # Closure gleicher L�nge allozieren:
    newclos = allocate_cclosure_copy(oldclos);
    oldclos = STACK_0;
    do_cclosure_copy(newclos,oldclos);
    STACK_0 = newclos;
    # Code-Vektor ebenfalls kopieren:
   {var object newcodevec = copy_sbvector(TheClosure(newclos)->clos_codevec);
    # und darin das Bit setzen, das von der RETGF-Instruktion abgefragt wird:
    TheCodevec(newcodevec)->ccv_flags |= bit(3);
    newclos = popSTACK();
    TheClosure(newclos)->clos_codevec = newcodevec;
    value1 = newclos; mv_count=1;
  }}

# ==============================================================================
# Load-Time-Eval:

# (SYS::MAKE-LOAD-TIME-EVAL form) liefert ein Load-Time-Eval-Objekt, das
#   - wenn ausgegeben und wieder eingelesen - form auswertet.

LISPFUNN(make_load_time_eval,1)
# (SYS::MAKE-LOAD-TIME-EVAL form) liefert ein Load-Time-Eval-Objekt, das
#   - wenn ausgegeben und wieder eingelesen - form auswertet.
  { var object lte = allocate_loadtimeeval();
    TheLoadtimeeval(lte)->loadtimeeval_form = popSTACK();
    value1 = lte; mv_count=1;
  }

# ==============================================================================
# Symbol-Macro:

# (SYS::MAKE-SYMBOL-MACRO expansion) liefert ein Symbol-Macro-Objekt,
#   das die gegebene Expansion repr�sentiert.
# (SYS::SYMBOL-MACRO-P object) testet auf Symbol-Macro.

# Wegen ihrer besonderen Bedeutung im Interpreter sind Symbol-Macro-Objekte
# - genauso wie #<UNBOUND> und #<SPECDECL> - keine Objekte erster Klasse.
# Sie k�nnen nur als Werte durchgereicht, nicht aber an Variablen zugewiesen
# werden.

# (SYMBOL-MACRO-EXPAND symbol) testet, ob ein Symbol ein Symbol-Macro
# repr�sentiert, und liefert T und die Expansion wenn ja, NIL wenn nein.

LISPFUNN(make_symbol_macro,1)
# (SYS::MAKE-SYMBOL-MACRO expansion) liefert ein Symbol-Macro-Objekt,
#   das die gegebene Expansion repr�sentiert.
  { var object sm = allocate_symbolmacro();
    TheSymbolmacro(sm)->symbolmacro_expansion = popSTACK();
    value1 = sm; mv_count=1;
  }

LISPFUNN(symbol_macro_p,1)
# (SYS::SYMBOL-MACRO-P object) testet auf Symbol-Macro.
  { var object obj = popSTACK();
    value1 = (symbolmacrop(obj) ? T : NIL); mv_count=1;
  }

LISPFUNN(symbol_macro_expand,1)
# (SYMBOL-MACRO-EXPAND symbol) testet, ob ein Symbol ein Symbol-Macro
# repr�sentiert, und liefert T und die Expansion wenn ja, NIL wenn nein.
# (defun symbol-macro-expand (v)
#   (unless (symbolp v) (error ...))
#   (and (boundp v) (symbol-macro-p (%symbol-value v))
#        (values t (sys::%record-ref (%symbol-value v) 0))
# ) )
  { var object obj = popSTACK();
    if (!symbolp(obj)) { fehler_symbol(obj); }
    obj = Symbol_value(obj);
    if (!symbolmacrop(obj))
      { value1 = NIL; mv_count=1; return; }
    value1 = T; value2 = TheSymbolmacro(obj)->symbolmacro_expansion; mv_count=2;
  }

# ==============================================================================
# Weak-Pointer:

LISPFUNN(make_weak_pointer,1)
# (MAKE-WEAK-POINTER value) returns a fresh weak pointer referring to value.
  { var object wp = allocate_weakpointer();
    var object obj = popSTACK();
    TheWeakpointer(wp)->wp_value = obj;
    if (gcinvariant_object_p(obj))
      { TheWeakpointer(wp)->wp_cdr = Fixnum_0; } # a GC-invariant dummy
      else
      { TheWeakpointer(wp)->wp_cdr = O(all_weakpointers);
        O(all_weakpointers) = wp;
      }
    value1 = wp; mv_count=1;
  }

LISPFUNN(weak_pointer_p,1)
# (WEAK-POINTER-P object) returns true if the object is of type WEAK-POINTER.
  { var object obj = popSTACK();
    value1 = (weakpointerp(obj) ? T : NIL); mv_count=1;
  }

LISPFUNN(weak_pointer_value,1)
# (WEAK-POINTER-VALUE weak-pointer) returns two values: The original value and
# T, if the value has not yet been garbage collected, else NIL and NIL.
  { var object wp = popSTACK();
    if (!weakpointerp(wp))
      { pushSTACK(wp); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
        pushSTACK(S(weak_pointer)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
        pushSTACK(wp);
        pushSTACK(TheSubr(subr_self)->name); # Funktionsname
        fehler(type_error,
               DEUTSCH ? "~: ~ ist kein Weak-Pointer." :
               ENGLISH ? "~: ~ is not a weak pointer" :
               FRANCAIS ? "~ : ~ n'est pas de type WEAK-POINTER." :
               ""
              );
      }
    if (eq(TheWeakpointer(wp)->wp_cdr,unbound))
      { value1 = NIL; value2 = NIL; }
      else
      { value1 = TheWeakpointer(wp)->wp_value; value2 = T; }
    mv_count=2;
  }

# ==============================================================================
# Finalisierer:

LISPFUN(finalize,2,1,norest,nokey,0,NIL)
# (FINALIZE object function &optional alive)
# registiert, dass, wenn object durch GC stirbt, function aufgerufen wird, mit
# object und evtl. alive als Argument. Wenn alive stirbt, bevor object stirbt,
# wird gar nichts getan.
  { if (!gcinvariant_object_p(STACK_2))
      { var object f = allocate_finalizer();
        TheFinalizer(f)->fin_trigger = STACK_2;
        TheFinalizer(f)->fin_function = STACK_1;
        TheFinalizer(f)->fin_alive = STACK_0; # Der Default #<UNBOUND> lebt ewig.
        TheFinalizer(f)->fin_cdr = O(all_finalizers);
        O(all_finalizers) = f;
      }
    skipSTACK(3); value1 = NIL; mv_count=1;
  }

# ==============================================================================
# CLOS-Objekte:

LISPFUNN(structure_object_p,1)
# (CLOS::STRUCTURE-OBJECT-P object) �berpr�ft, ob object eine Structure ist.
  { var object obj = popSTACK();
    value1 = (structurep(obj) ? T : NIL); mv_count=1;
  }

LISPFUNN(std_instance_p,1)
# (CLOS::STD-INSTANCE-P object) testet, ob ein Objekt ein CLOS-Objekt ist.
  { var object obj = popSTACK();
    value1 = (instancep(obj) ? T : NIL); mv_count=1;
  }

# Liefert (CLOS:CLASS-OF object), aber besonders effizient f�r CLOS-Objekte.
  #define class_of(obj)  \
    (instancep(obj) ? TheInstance(obj)->inst_class           \
                    : (pushSTACK(obj), C_class_of(), value1) \
    )

# Fehlermeldung, wenn ein Objekt keine Klasse ist.
# fehler_keine_klasse(caller,obj);
# > subr_self: Aufrufer
# > obj: Nicht-Klasse
  nonreturning_function(local, fehler_keine_klasse, (object obj));
  local void fehler_keine_klasse(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(S(class)); # CLOS:CLASS, Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj);
      pushSTACK(TheSubr(subr_self)->name); # Funktionsname
      fehler(type_error,
             DEUTSCH ? "~: ~ ist keine Klasse." :
             ENGLISH ? "~: ~ is not a class" :
             FRANCAIS ? "~ : ~ n'est pas une classe." :
             ""
            );
    }

LISPFUNN(allocate_std_instance,2)
# (CLOS::ALLOCATE-STD-INSTANCE class n) liefert eine CLOS-Instanz der L�nge n,
# mit Klasse class und n-1 zus�tzlichen Slots.
  { # L�nge �berpr�fen, sollte ein Fixnum >0 sein, das in ein uintW passt:
    var uintL length;
    test_record_length(length);
    skipSTACK(1);
   {var object instance = allocate_srecord(0,Rectype_Instance,length,instance_type);
    var object clas = popSTACK();
    if_classp(clas, ; , fehler_keine_klasse(clas); );
    TheInstance(instance)->inst_class = clas;
    # Slots der Instanz mit #<UNBOUND> f�llen:
    {var object* ptr = &TheInstance(instance)->other[0];
     dotimesL(length,length-1, { *ptr++ = unbound; } );
    }
    value1 = instance; mv_count=1; # instance als Wert
  }}

LISPFUNN(allocate_instance,1)
# (CLOS::%ALLOCATE-INSTANCE class) returns an instance of the class.
# class must be a <standard-class> or <structure-class>.
  { var object clas = popSTACK();
    if_classp(clas, ; , fehler_keine_klasse(clas); );
    # F�r allocate-instance zwischen <standard-class> und <structure-class>
    # unterscheiden: (class-shared-slots class) ein Vektor oder NIL, oder
    # (class-names class) ein Cons?
    if (matomp(TheClass(clas)->shared_slots))
      { # class ist eine <standard-class>.
        # (CLOS::ALLOCATE-STD-INSTANCE class (class-instance-size class))
        pushSTACK(clas); pushSTACK(TheClass(clas)->instance_size);
        C_allocate_std_instance();
      }
    else
      { # class ist eine <structure-class>.
        # (SYS::%MAKE-STRUCTURE (class-names class) (class-instance-size class))
        pushSTACK(TheClass(clas)->shared_slots); pushSTACK(TheClass(clas)->instance_size);
        C_make_structure();
        # Slots der Structure mit #<UNBOUND> f�llen, damit nachher
        # INITIALIZE-INSTANCE die Default-Werte eintr�gt:
        {var object* ptr = &TheStructure(value1)->recdata[1];
         var uintL count;
         dotimesL(count,Structure_length(value1)-1, { *ptr++ = unbound; } );
      } }
  }

# (CLOS:SLOT-VALUE instance slot-name)
# (CLOS::SET-SLOT-VALUE instance slot-name new-value)
# (CLOS:SLOT-BOUNDP instance slot-name)
# (CLOS:SLOT-MAKUNBOUND instance slot-name)
# (CLOS:SLOT-EXISTS-P instance slot-name)
# CLtL2 S. 855,857

# Liefert aus einer Slot-Location-Info die Adresse eines existierenden Slots
# in einer Instanz einer Standard- oder Structure-Klasse.
  #define ptr_to_slot(instance,slotinfo)  \
    (atomp(slotinfo)                                            \
     # local slot, slotinfo ist Index                           \
     ? &TheSrecord(instance)->recdata[posfixnum_to_L(slotinfo)] \
     # shared slot, slotinfo ist (class . index)                \
     : &TheSvector(TheClass(Car(slotinfo))->shared_slots)       \
                  ->data[posfixnum_to_L(Cdr(slotinfo))]         \
    )

# UP: Sucht einen Slot auf.
# slot_up()
# > STACK_1: instance
# > STACK_0: slot-name
# < ergebnis: Pointer auf den Slot (dann ist value1 = (class-of instance)),
#             oder NULL (dann wurde SLOT-MISSING aufgerufen).
  local object* slot_up (void);
  #ifdef RISCOS_CCBUG
    #pragma -z0
  #endif
  local object* slot_up()
    { pushSTACK(STACK_1); C_class_of(); # (CLASS-OF instance) bestimmen
     {var object slotinfo = # (GETHASH slot-name (class-slot-location-table class))
        gethash(STACK_0,TheClass(value1)->slot_location_table);
      if (!eq(slotinfo,nullobj)) # gefunden?
        { return ptr_to_slot(STACK_1,slotinfo); }
        else
        # missing slot -> (SLOT-MISSING class instance slot-name caller)
        { pushSTACK(value1); pushSTACK(STACK_(1+1)); pushSTACK(STACK_(0+2));
          pushSTACK(TheSubr(subr_self)->name);
          funcall(S(slot_missing),4);
          return NULL;
        }
    }}
  #ifdef RISCOS_CCBUG
    #pragma -z1
  #endif

LISPFUNN(slot_value,2)
{ var object* slot = slot_up();
  if (slot)
    { var object value = *slot;
      if (!eq(value,unbound))
        { value1 = value; }
        else
        # (SLOT-UNBOUND class instance slot-name)
        { pushSTACK(value1); pushSTACK(STACK_(1+1)); pushSTACK(STACK_(0+2));
          funcall(S(slot_unbound),3);
    }   }
  mv_count=1;
  skipSTACK(2);
}

#ifdef RISCOS_CCBUG
  #pragma -z0
#endif
LISPFUNN(set_slot_value,3)
{ # Stackaufbau: instance, slot-name, new-value.
  pushSTACK(STACK_2); C_class_of(); # (CLASS-OF instance) bestimmen
 {var object slotinfo = # (GETHASH slot-name (class-slot-location-table class))
    gethash(STACK_1,TheClass(value1)->slot_location_table);
  if (!eq(slotinfo,nullobj)) # gefunden?
    { value1 = *ptr_to_slot(STACK_2,slotinfo) = STACK_0; }
    else
    # missing slot -> (SLOT-MISSING class instance slot-name 'setf new-value)
    { pushSTACK(value1); pushSTACK(STACK_(2+1)); pushSTACK(STACK_(1+2));
      pushSTACK(S(setf)); pushSTACK(STACK_(0+4));
      funcall(S(slot_missing),5);
      value1 = STACK_0;
    }
  mv_count=1;
  skipSTACK(3);
}}
#ifdef RISCOS_CCBUG
  #pragma -z1
#endif

LISPFUNN(slot_boundp,2)
{ var object* slot = slot_up();
  if (slot)
    { value1 = (eq(*slot,unbound) ? NIL : T); }
  mv_count=1;
  skipSTACK(2);
}

LISPFUNN(slot_makunbound,2)
{ var object* slot = slot_up();
  if (slot)
    { *slot = unbound; }
  value1 = STACK_1; mv_count=1; # instance als Wert
  skipSTACK(2);
}

#ifdef RISCOS_CCBUG
  #pragma -z0
#endif
LISPFUNN(slot_exists_p,2)
{ pushSTACK(STACK_1); C_class_of(); # (CLASS-OF instance) bestimmen
 {var object slotinfo = # (GETHASH slot-name (class-slot-location-table class))
    gethash(STACK_0,TheClass(value1)->slot_location_table);
  value1 = (eq(slotinfo,nullobj) ? NIL : T); mv_count=1; skipSTACK(2);
}}
#ifdef RISCOS_CCBUG
  #pragma -z1
#endif

# UP: Keywords �berpr�fen, vgl. SYSTEM::KEYWORD-TEST
# keyword_test(caller,rest_args_pointer,argcount,valid_keywords);
# > caller: Aufrufer (ein Symbol)
# > rest_args_pointer: Pointer �ber die Argumente
# > argcount: Anzahl der Argumente / 2
# > valid_keywords: Liste der g�ltigen Keywords, oder T wenn alle g�ltig sind
  local void keyword_test (object caller, object* rest_args_pointer, uintC argcount, object valid_keywords);
  local void keyword_test(caller,rest_args_pointer,argcount,valid_keywords)
    var object caller;
    var object* rest_args_pointer;
    var uintC argcount;
    var object valid_keywords;
    { if (argcount==0) return;
      if (eq(valid_keywords,T)) return;
      # Suche, ob :ALLOW-OTHER-KEYS kommt:
      { var object* ptr = rest_args_pointer;
        var uintC count;
        dotimespC(count,argcount,
          { if (eq(NEXT(ptr),S(Kallow_other_keys)))
              if (!nullp(Next(ptr)))
                return;
            NEXT(ptr);
          });
      }
      # Suche, ob alle angegebenen Keywords in valid_keywords vorkommen:
      { var object* ptr = rest_args_pointer;
        var uintC count;
        dotimespC(count,argcount,
          { var object key = NEXT(ptr);
            var object kwlistr = valid_keywords;
            while (consp(kwlistr))
              { if (eq(Car(kwlistr),key)) goto kw_found;
                kwlistr = Cdr(kwlistr);
              }
            # nicht gefunden
            pushSTACK(key); # Wert f�r Slot DATUM von KEYWORD-ERROR
            pushSTACK(valid_keywords);
            pushSTACK(valid_keywords);
            pushSTACK(Next(ptr));
            pushSTACK(key);
            pushSTACK(caller);
            {var object type = allocate_cons();
             Car(type) = S(member); Cdr(type) = STACK_4;
             STACK_4 = type; # `(MEMBER ,@valid_keywords) = Wert f�r Slot EXPECTED-TYPE von KEYWORD-ERROR
            }
            fehler(keyword_error,
                   DEUTSCH ? "~: Unzul�ssiges Keyword/Wert-Paar ~, ~ in der Argumentliste." NLstring "Die erlaubten Keywords sind ~" :
                   ENGLISH ? "~: illegal keyword/value pair ~, ~ in argument list." NLstring "The allowed keywords are ~" :
                   FRANCAIS ? "~ : Paire mot-cl� - valeur ~, ~ illicite dans la liste d'arguments." NLstring "Les mots-cl� permis sont ~" :
                   ""
                  );
            kw_found: # gefunden. Weiter:
            NEXT(ptr);
          });
    } }

LISPFUN(shared_initialize,2,0,rest,nokey,0,NIL)
# (CLOS::%SHARED-INITIALIZE instance slot-names &rest initargs)
# instance ist eine Instanz von <standard-object> oder <structure-object>,
# initargs eine paarige Liste.
# Das ist die prim�re Methode von CLOS:SHARED-INITIALIZE.
# vgl. clos.lsp
# (defmethod shared-initialize ((instance standard-object) slot-names &rest initargs)
#   (dolist (slot (class-slots (class-of instance)))
#     (let ((slotname (slotdef-name slot)))
#       (multiple-value-bind (init-key init-value foundp)
#           (get-properties initargs (slotdef-initargs slot))
#         (declare (ignore init-key))
#         (if foundp
#           (setf (slot-value instance slotname) init-value)
#           (unless (slot-boundp instance slotname)
#             (let ((init (slotdef-initer slot)))
#               (when init
#                 (when (or (eq slot-names 'T) (member slotname slot-names :test #'eq))
#                   (setf (slot-value instance slotname)
#                         (if (car init) (funcall (car init)) (cdr init))
#   ) ) ) ) ) ) ) ) )
#   instance
# )
{ if (!((argcount%2) == 0))
    { var object arglist = listof(argcount);
      pushSTACK(arglist);
      fehler(program_error,
             DEUTSCH ? "SHARED-INITIALIZE: Keyword-Argumentliste ~ hat ungerade L�nge." :
             ENGLISH ? "SHARED-INITIALIZE: keyword argument list ~ has an odd length" :
             FRANCAIS ? "SHARED-INITIALIZE : La liste de mots cl� ~ est de longueur impaire." :
             ""
            );
    }
  argcount = argcount/2; # Anzahl der Initarg/Wert-Paare
  # Stackaufbau: instance, slot-names, argcount Initarg/Wert-Paare.
  { var object instance = Before(rest_args_pointer STACKop 1);
    var object clas = class_of(instance); # Instanz der <standard-class> oder <structure-class>
    var object slots = TheClass(clas)->slots; # Liste aller Slots (als Slot-Definitionen)
    while (consp(slots))
      { var object slot = Car(slots);
        slots = Cdr(slots);
        # Suche ob der Slot durch die Initargs initialisiert wird:
        { var object l = TheSvector(slot)->data[1]; # (slotdef-initargs slot)
          var object* ptr = rest_args_pointer;
          var uintC count;
          dotimesC(count,argcount,
            { var object initarg = NEXT(ptr);
              # Suche initarg in l
              var object lr = l;
              while (consp(lr))
                { if (eq(initarg,Car(lr))) goto initarg_found;
                  lr = Cdr(lr);
                }
              NEXT(ptr);
            });
          goto initarg_not_found;
          initarg_found:
          value1 = NEXT(ptr);
          goto fill_slot;
        }
        initarg_not_found:
        # Nicht gefunden -> erst auf (slot-boundp instance slotname) testen:
        { var object slotinfo = TheSvector(slot)->data[2]; # (slotdef-location slot)
          if (!eq(*ptr_to_slot(Before(rest_args_pointer STACKop 1),slotinfo),unbound))
            goto slot_done;
        }
        # Slot hat noch keinen Wert. Evtl. die Initform auswerten:
        { var object init = TheSvector(slot)->data[3]; # (slotdef-initer slot)
          if (atomp(init)) goto slot_done;
          # Slot in slot-names suchen:
          { var object slotnames = Before(rest_args_pointer);
            if (eq(slotnames,T)) goto eval_init;
           {var object slotname = TheSvector(slot)->data[0]; # (slotdef-name slot)
            while (consp(slotnames))
              { if (eq(Car(slotnames),slotname)) goto eval_init;
                slotnames = Cdr(slotnames);
              }
            goto slot_done;
          }}
          eval_init:
          # Die Initform auswerten:
          if (!nullp(Car(init)))
            { pushSTACK(slots); pushSTACK(slot);
              funcall(Car(init),0);
              slot = popSTACK(); slots = popSTACK();
            }
            else
            { value1 = Cdr(init); }
        }
        fill_slot:
        # Slot mit value1 initialisieren:
        { var object slotinfo = TheSvector(slot)->data[2]; # (slotdef-location slot)
          *ptr_to_slot(Before(rest_args_pointer STACKop 1),slotinfo) = value1;
        }
        slot_done: ;
  }   }
  value1 = Before(rest_args_pointer STACKop 1); mv_count=1; # Instanz als Wert
  set_args_end_pointer(rest_args_pointer STACKop 2); # STACK aufr�umen
}

LISPFUN(reinitialize_instance,1,0,rest,nokey,0,NIL)
# (CLOS::%REINITIALIZE-INSTANCE instance &rest initargs)
# instance ist eine Instanz von <standard-object> oder <structure-object>,
# initargs eine paarige Liste.
# Das ist die prim�re Methode von CLOS:REINITIALIZE-INSTANCE.
# vgl. clos.lsp
# (defmethod reinitialize-instance ((instance standard-object) &rest initargs)
#   (let ((h (gethash (class-of instance) *reinitialize-instance-table*)))
#     (if h
#       (progn
#         ; 28.1.9.2. validity of initialization arguments
#         (let ((valid-keywords (car h)))
#           (sys::keyword-test initargs valid-keywords)
#         )
#         (if (not (eq (cdr h) #'clos::%shared-initialize))
#           ; effektive Methode von shared-initialize anwenden:
#           (apply (cdr h) instance 'NIL initargs)
#           ; clos::%shared-initialize mit slot-names=NIL l�sst sich vereinfachen:
#           (progn
#             (dolist (slot (class-slots (class-of instance)))
#               (let ((slotname (slotdef-name slot)))
#                 (multiple-value-bind (init-key init-value foundp)
#                     (get-properties initargs (slotdef-initargs slot))
#                   (declare (ignore init-key))
#                   (if foundp
#                     (setf (slot-value instance slotname) init-value)
#             ) ) ) )
#             instance
#       ) ) )
#       (apply #'initial-reinitialize-instance instance initargs)
# ) ) )
{ var object instance = Before(rest_args_pointer);
  var object clas = class_of(instance); # Instanz der <standard-class> oder <structure-class>
  # (GETHASH class *REINITIALIZE-INSTANCE-TABLE*) suchen:
  { var object info = gethash(clas,Symbol_value(S(reinitialize_instance_table)));
    if (eq(info,nullobj))
      # Hash-Tabellen-Eintrag neu berechnen. Siehe clos.lsp.
      { funcall(S(initial_reinitialize_instance),argcount+1); return; }
    # Keywords �berpr�fen:
    if (!((argcount%2) == 0))
      { var object arglist = listof(argcount);
        pushSTACK(arglist);
        fehler(program_error,
               DEUTSCH ? "REINITIALIZE-INSTANCE: Keyword-Argumentliste ~ hat ungerade L�nge." :
               ENGLISH ? "REINITIALIZE-INSTANCE: keyword argument list ~ has an odd length" :
               FRANCAIS ? "REINITIALIZE-INSTANCE : La liste de mots cl� ~ est de longueur impaire." :
               ""
              );
      }
    argcount = argcount/2; # Anzahl der Initarg/Wert-Paare
    keyword_test(S(reinitialize_instance),rest_args_pointer,argcount,Car(info));
  # Stackaufbau: instance, slot-names, argcount Initarg/Wert-Paare.
   {var object fun = Cdr(info);
    if (!eq(fun,L(shared_initialize)))
      { # initargs im Stack um 1 nach unten schieben, dann fun aufrufen:
        var object* ptr = rest_args_pointer;
        var object last = NIL;
        var uintC count;
        dotimesC(count,argcount,
          { var object next = Next(ptr); NEXT(ptr) = last;
            last = Next(ptr); NEXT(ptr) = next;
          });
        pushSTACK(last);
        funcall(fun,2*argcount+2);
        return;
      }
  }}
  # CLOS::%SHARED-INITIALIZE mit slot-names=NIL l�sst sich vereinfachen:
  { var object slots = TheClass(clas)->slots; # Liste aller Slots (als Slot-Definitionen)
    while (consp(slots))
      { var object slot = Car(slots);
        slots = Cdr(slots);
        # Suche ob der Slot durch die Initargs initialisiert wird:
        { var object l = TheSvector(slot)->data[1]; # (slotdef-initargs slot)
          var object* ptr = rest_args_pointer;
          var uintC count;
          dotimesC(count,argcount,
            { var object initarg = NEXT(ptr);
              # Suche initarg in l
              var object lr = l;
              while (consp(lr))
                { if (eq(initarg,Car(lr))) goto initarg_found;
                  lr = Cdr(lr);
                }
              NEXT(ptr);
            });
          goto slot_done;
          initarg_found:
         {var object value = NEXT(ptr);
          # Slot mit value initialisieren:
          {var object slotinfo = TheSvector(slot)->data[2]; # (slotdef-location slot)
           *ptr_to_slot(Before(rest_args_pointer STACKop 1),slotinfo) = value;
        }}}
        slot_done: ;
  }   }
  value1 = Before(rest_args_pointer); mv_count=1; # Instanz als Wert
  set_args_end_pointer(rest_args_pointer STACKop 1); # STACK aufr�umen
}

# (CLOS::%INITIALIZE-INSTANCE instance &rest initargs)
# instance ist eine Instanz von <standard-object> oder <structure-object>,
# initargs eine paarige Liste.
# Das ist die prim�re Methode von CLOS:INITIALIZE-INSTANCE.
# vgl. clos.lsp
# (defmethod initialize-instance ((instance standard-object) &rest initargs)
#   (let ((h (gethash class *make-instance-table*)))
#     (if h
#       (if (not (eq (cddr h) #'clos::%shared-initialize))
#         ; effektive Methode von shared-initialize anwenden:
#         (apply (cddr h) instance 'T initargs)
#         ; clos::%shared-initialize mit slot-names=T l�sst sich vereinfachen:
#         (progn
#           (dolist (slot (class-slots (class-of instance)))
#             (let ((slotname (slotdef-name slot)))
#               (multiple-value-bind (init-key init-value foundp)
#                   (get-properties initargs (slotdef-initargs slot))
#                 (declare (ignore init-key))
#                 (if foundp
#                   (setf (slot-value instance slotname) init-value)
#                   (unless (slot-boundp instance slotname)
#                     (let ((init (slotdef-initer slot)))
#                       (when init
#                         (setf (slot-value instance slotname)
#                               (if (car init) (funcall (car init)) (cdr init))
#           ) ) ) ) ) ) ) )
#           instance
#       ) )
#       (apply #'initial-initialize-instance instance initargs)
# ) ) )
local Values do_initialize_instance (object info, object* rest_args_pointer, uintC argcount);
LISPFUN(initialize_instance,1,0,rest,nokey,0,NIL)
{ var object instance = Before(rest_args_pointer);
  var object clas = class_of(instance); # Instanz der <standard-class> oder <structure-class>
  # (GETHASH class *MAKE-INSTANCE-TABLE*) suchen:
  { var object info = gethash(clas,Symbol_value(S(make_instance_table)));
    if (eq(info,nullobj))
      # Hash-Tabellen-Eintrag neu berechnen. Siehe clos.lsp.
      { funcall(S(initial_initialize_instance),argcount+1); return; }
    if (!((argcount%2) == 0))
      { var object arglist = listof(argcount);
        pushSTACK(arglist);
        fehler(program_error,
               DEUTSCH ? "INITIALIZE-INSTANCE: Keyword-Argumentliste ~ hat ungerade L�nge." :
               ENGLISH ? "INITIALIZE-INSTANCE: keyword argument list ~ has an odd length" :
               FRANCAIS ? "INITIALIZE-INSTANCE : La liste de mots cl� ~ est de longueur impaire." :
               ""
              );
      }
    argcount = argcount/2; # Anzahl der Initarg/Wert-Paare
    return_Values do_initialize_instance(info,rest_args_pointer,argcount);
} }
local Values do_initialize_instance(info,rest_args_pointer,argcount)
  var object info;
  var object* rest_args_pointer;
  var uintC argcount;
  { # Stackaufbau: instance, argcount Initarg/Wert-Paare.
    { var object fun = Cdr(Cdr(info));
      if (!eq(fun,L(shared_initialize)))
        { # initargs im Stack um 1 nach unten schieben, dann fun aufrufen:
          var object* ptr = rest_args_pointer;
          var object last = T;
          var uintC count;
          dotimesC(count,argcount,
            { var object next = Next(ptr); NEXT(ptr) = last;
              last = Next(ptr); NEXT(ptr) = next;
            });
          pushSTACK(last);
          funcall(fun,2*argcount+2);
          return;
        }
    }
    # CLOS::%SHARED-INITIALIZE mit slot-names=T l�sst sich vereinfachen:
    { var object instance = Before(rest_args_pointer);
      var object clas = class_of(instance); # Instanz der <standard-class> oder <structure-class>
      var object slots = TheClass(clas)->slots; # Liste aller Slots (als Slot-Definitionen)
      while (consp(slots))
        { var object slot = Car(slots);
          slots = Cdr(slots);
          # Suche ob der Slot durch die Initargs initialisiert wird:
          { var object l = TheSvector(slot)->data[1]; # (slotdef-initargs slot)
            var object* ptr = rest_args_pointer;
            var uintC count;
            dotimesC(count,argcount,
              { var object initarg = NEXT(ptr);
                # Suche initarg in l
                var object lr = l;
                while (consp(lr))
                  { if (eq(initarg,Car(lr))) goto initarg_found;
                    lr = Cdr(lr);
                  }
                NEXT(ptr);
              });
            goto initarg_not_found;
            initarg_found:
            value1 = NEXT(ptr);
            goto fill_slot;
          }
          initarg_not_found:
          # Nicht gefunden -> erst auf (slot-boundp instance slotname) testen:
          { var object slotinfo = TheSvector(slot)->data[2]; # (slotdef-location slot)
            if (!eq(*ptr_to_slot(Before(rest_args_pointer),slotinfo),unbound))
              goto slot_done;
          }
          # Slot hat noch keinen Wert. Die Initform auswerten:
          { var object init = TheSvector(slot)->data[3]; # (slotdef-initer slot)
            if (atomp(init)) goto slot_done;
            if (!nullp(Car(init)))
              { pushSTACK(slots); pushSTACK(slot);
                funcall(Car(init),0);
                slot = popSTACK(); slots = popSTACK();
              }
              else
              { value1 = Cdr(init); }
          }
          fill_slot:
          # Slot mit value1 initialisieren:
          { var object slotinfo = TheSvector(slot)->data[2]; # (slotdef-location slot)
            *ptr_to_slot(Before(rest_args_pointer),slotinfo) = value1;
          }
          slot_done: ;
    }   }
    value1 = Before(rest_args_pointer); mv_count=1; # Instanz als Wert
    set_args_end_pointer(rest_args_pointer STACKop 1); # STACK aufr�umen
  }

#ifdef RISCOS_CCBUG
  #pragma -z0
#endif
LISPFUN(make_instance,1,0,rest,nokey,0,NIL)
# (CLOS::%MAKE-INSTANCE class &rest initargs)
# class ist eine Instanz der <standard-class> oder <structure-class>,
# initargs eine (hoffentlich paarige) Liste.
# vgl. clos.lsp
# (defun %make-instance (class &rest initargs)
#   ; 28.1.9.3., 28.1.9.4. default-initargs zur Kenntnis nehmen:
#   (dolist (default-initarg (class-default-initargs class))
#     (let ((nothing default-initarg))
#       (when (eq (getf initargs (car default-initarg) nothing) nothing)
#         (setq initargs
#               (append initargs
#                 (list (car default-initarg)
#                       (let ((init (cdr default-initarg)))
#                         (if (car init) (funcall (car init)) (cdr init))
#   ) ) ) )     ) )     )
#   (let ((h (gethash class *make-instance-table*)))
#     (if h
#       (progn
#         ; 28.1.9.2. validity of initialization arguments
#         (let ((valid-keywords (car h)))
#           (sys::keyword-test initargs valid-keywords)
#         )
#         (let ((instance (allocate-instance class)))
#           (if (not (eq (cadr h) #'clos::%initialize-instance))
#             ; effektive Methode von initialize-instance anwenden:
#             (apply (cadr h) instance initargs)
#             ; clos::%initialize-instance l�sst sich vereinfachen (man braucht
#             ; nicht nochmal in *make-instance-table* nachzusehen):
#             (if (not (eq (cddr h) #'clos::%shared-initialize))
#               ; effektive Methode von shared-initialize anwenden:
#               (apply (cddr h) instance 'T initargs)
#               ...
#             )
#       ) ) )
#       (apply #'initial-make-instance class initargs)
# ) ) )
{ if (!((argcount%2) == 0))
    { var object arglist = listof(argcount);
      pushSTACK(arglist);
      fehler(program_error,
             DEUTSCH ? "MAKE-INSTANCE: Keyword-Argumentliste ~ hat ungerade L�nge." :
             ENGLISH ? "MAKE-INSTANCE: keyword argument list ~ has an odd length" :
             FRANCAIS ? "MAKE-INSTANCE : La liste de mots cl� ~ est de longueur impaire." :
             ""
            );
    }
  argcount = argcount/2; # Anzahl der Initarg/Wert-Paare
  # Stackaufbau: class, argcount Initarg/Wert-Paare.
  # Default-Initargs anf�gen:
  { var object clas = Before(rest_args_pointer);
    var object l = TheClass(clas)->default_initargs;
    while (consp(l))
      { var object default_initarg = Car(l);
        l = Cdr(l);
       {var object key = Car(default_initarg);
        # Suche key unter den bisherigen Initargs:
        { var object* ptr = rest_args_pointer;
          var uintC count;
          dotimesC(count,argcount,
            { if (eq(NEXT(ptr),key)) goto key_found;
              NEXT(ptr);
            });
        }
        # Nicht gefunden
        pushSTACK(key); # Initarg in den Stack
        { var object init = Cdr(default_initarg);
          if (!nullp(Car(init)))
            { pushSTACK(l);
              funcall(Car(init),0); # Default auswerten
              l = STACK_0;
              STACK_0 = value1; # Wert in den Stack
            }
            else
            { pushSTACK(Cdr(init)); } # Default in den Stack
        }
        argcount++;
        key_found: ;
      }}
  }
  # (GETHASH class *MAKE-INSTANCE-TABLE*) suchen:
  { var object clas = Before(rest_args_pointer);
    var object info = gethash(clas,Symbol_value(S(make_instance_table)));
    if (eq(info,nullobj))
      # Hash-Tabellen-Eintrag neu berechnen. Siehe clos.lsp.
      { return_Values funcall(S(initial_make_instance),2*argcount+1); }
      else
      { # Keywords �berpr�fen:
        keyword_test(S(make_instance),rest_args_pointer,argcount,Car(info));
        pushSTACK(info);
        # F�r allocate-instance zwischen <standard-class> und <structure-class>
        # unterscheiden: (class-shared-slots class) ein Vektor oder NIL, oder
        # (class-names class) ein Cons?
        if (matomp(TheClass(clas)->shared_slots))
          { # class ist eine <standard-class>.
            # (CLOS::ALLOCATE-STD-INSTANCE class (class-instance-size class))
            pushSTACK(clas); pushSTACK(TheClass(clas)->instance_size);
            C_allocate_std_instance();
          }
        else
          { # class ist eine <structure-class>.
            # (SYS::%MAKE-STRUCTURE (class-names class) (class-instance-size class))
            pushSTACK(TheClass(clas)->shared_slots); pushSTACK(TheClass(clas)->instance_size);
            C_make_structure();
            # Slots der Structure mit #<UNBOUND> f�llen, damit nachher
            # INITIALIZE-INSTANCE die Default-Werte eintr�gt:
            {var object* ptr = &TheStructure(value1)->recdata[1];
             var uintL count;
             dotimesL(count,Structure_length(value1)-1, { *ptr++ = unbound; } );
          } }
        info = popSTACK();
        # Effektive Methode von INITIALIZE-INSTANCE anwenden:
        Before(rest_args_pointer) = value1; # instance als 1. Argument statt class
       {var object fun = Car(Cdr(info));
        if (!eq(fun,L(initialize_instance)))
          { return_Values funcall(fun,2*argcount+1); }
          else
          # CLOS::%INITIALIZE-INSTANCE l�sst sich vereinfachen (man braucht
          # nicht nochmal in *make-instance-table* nachzusehen):
          { return_Values do_initialize_instance(info,rest_args_pointer,argcount); }
        # Deren Wert ist die Instanz.
      }}
} }
#ifdef RISCOS_CCBUG
  #pragma -z1
#endif

# ==============================================================================

