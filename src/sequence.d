# Sequences f�r CLISP
# Bruno Haible 28.3.1997

#include "lispbibl.c"


# O(seq_types) enth�lt eine Liste von Typdescriptoren f�r Sequences.
# Das sind Simple-Vektoren der L�nge 16, mit folgendem Inhalt:
#  SEQ-TYPE        ; der Typ der Sequence, meist ein Symbol
#  Zugriffsfunktionen:
#  SEQ-INIT
#  SEQ-UPD
#  SEQ-ENDTEST
#  SEQ-FE-INIT
#  SEQ-FE-UPD
#  SEQ-FE-ENDTEST
#  SEQ-ACCESS
#  SEQ-ACCESS-SET
#  SEQ-COPY
#  SEQ-LENGTH
#  SEQ-MAKE
#  SEQ-ELT
#  SEQ-SET-ELT
#  SEQ-INIT-START
#  SEQ-FE-INIT-END

/*

 Erkl�rung der Einzelfunktionen SEQ-XXX:

Ein "Pointer" ist etwas, was durch die Sequence durchlaufen kann.
Es gibt Pointer, die von links nach rechts laufen;
  sie werden mit INIT oder INIT-START kreiert, mit COPY kopiert,
             mit UPD um eine Stelle weiterger�ckt,
             mit ENDTEST getestet, ob sie am Ende der Sequence angelangt sind,
             mit ACCESS wird das Element, worauf der Pointer zeigt, geholt,
             mit ACCESS-SET wird das Element, worauf der Pointer zeigt, gesetzt.
Es gibt auch Pointer, die von rechts nach links laufen;
  sie werden mit FE-INIT oder FE-INIT-END kreiert, mit COPY kopiert,
             mit FE-UPD um eine Stelle nach links weiterger�ckt,
             mit FE-ENDTEST getestet, ob sie am Ende der Sequence angelangt sind,
             mit ACCESS wird das Element, worauf der Pointer zeigt, geholt.
  F�r sie funktioniert ACCESS-SET nicht.

Durchlaufe-Operationen:
INIT          (lambda (seq) ...) -> pointer
              liefert den Pointer zu SEQ, der ganz links steht.
UPD           (lambda (seq pointer) ...) -> pointer
              liefert zu einem Pointer den Pointer eins weiter rechts.
              SEQ-UPD kann voraussetzen, dass dabei der rechte Rand von
              SEQ nicht �berschritten wird.
ENDTEST       (lambda (seq pointer) ...) -> boolean
              testet, ob dieser Pointer am rechten Rand von SEQ steht.
Dasselbe "FROM END" :
FE-INIT       (lambda (seq) ...) -> pointer
              liefert den Pointer zu SEQ, der ganz rechts steht.
FE-UPD        (lambda (seq pointer) ...) -> pointer
              liefert zu einem Pointer den Pointer eins weiter links.
              SEQ-FE-UPD kann voraussetzen, dass dabei der linke Rand von
              SEQ nicht �berschritten wird.
FE-ENDTEST    (lambda (seq pointer) ...) -> boolean
              testet, ob dieser Pointer am linken Rand von SEQ steht.
Zugriff mit Pointer:
ACCESS        (lambda (seq pointer) ...) -> value
              liefert zu einem Pointer in SEQ das entsprechende Element an
              dieser Stelle.
ACCESS-SET    (lambda (seq pointer value) ...) ->
              setzt das Element in SEQ, auf das der Pointer zeigt, auf den
              gegebenen Wert. Nur bei von links nach rechts laufenden Pointern!
COPY          (lambda (pointer) ...) -> pointer
              liefert eine Kopie des Pointers zu SEQ (denn UPD und FE-UPD
              k�nnen destruktiv auf den Pointern arbeiten)
Gesamtl�nge:
LENGTH        (lambda (seq) ...) -> size
              liefert die (aktive) L�nge der Sequence SEQ.
MAKE          (lambda (size) ...) -> sequence
              liefert eine neu allozierte, leere Sequence, die vom Typ
              SEQ-TYPE ist und die angegebene L�nge hat.
Zugriff �ber Index (meist ineffizienter als �ber Pointer):
ELT           (lambda (seq index) ...) -> value
              liefert (ELT SEQ index)
SET-ELT       (lambda (seq index value) ...) ->
              setzt (ELT SEQ index) auf value.
INIT-START    (lambda (seq index) ...) -> pointer
              liefert einen nach rechts laufenden Pointer in SEQ
              ab Position index. Muss den Range-test selbst durchf�hren.
FE-INIT-END   (lambda (seq index) ...) -> pointer
              liefert einen nach links laufenden Pointer in SEQ
              an Position index. Muss den Range-test selbst durchf�hren.

*/

#define seq_type(seqdesc)         (TheSvector(seqdesc)->data[0])
#define seq_init(seqdesc)         (TheSvector(seqdesc)->data[1])
#define seq_upd(seqdesc)          (TheSvector(seqdesc)->data[2])
#define seq_endtest(seqdesc)      (TheSvector(seqdesc)->data[3])
#define seq_fe_init(seqdesc)      (TheSvector(seqdesc)->data[4])
#define seq_fe_upd(seqdesc)       (TheSvector(seqdesc)->data[5])
#define seq_fe_endtest(seqdesc)   (TheSvector(seqdesc)->data[6])
#define seq_access(seqdesc)       (TheSvector(seqdesc)->data[7])
#define seq_access_set(seqdesc)   (TheSvector(seqdesc)->data[8])
#define seq_copy(seqdesc)         (TheSvector(seqdesc)->data[9])
#define seq_length(seqdesc)       (TheSvector(seqdesc)->data[10])
#define seq_make(seqdesc)         (TheSvector(seqdesc)->data[11])
#define seq_elt(seqdesc)          (TheSvector(seqdesc)->data[12])
#define seq_set_elt(seqdesc)      (TheSvector(seqdesc)->data[13])
#define seq_init_start(seqdesc)   (TheSvector(seqdesc)->data[14])
#define seq_fe_init_end(seqdesc)  (TheSvector(seqdesc)->data[15])

# UP: �berpr�ft, ob name ein g�ltiger Sequence-Typ-Bezeichner ist
# (sonst Error) und liefert den dazugeh�rigen Typdescriptor.
# valid_type(name)
# > name: Sequence-Typ-Bezeichner
# < ergebnis: dazugeh�riger Typdescriptor
# < -(STACK): durch den Typ erzwungene L�nge, oder unbound.
# kann GC ausl�sen
  local object valid_type (object name);
  local object valid_type(name)
    var object name;
    { # Unsere elementaren Sequence-Typen sind LIST, VECTOR, STRING, BIT-VECTOR.
      # Wir erkennen aber auch gewisse Alias-Namen:
      # - DEFTYPE-defininierte Typen werden expandiert.
      # - ([SIMPLE-]ARRAY [eltype [1 | (dim)]]), (VECTOR [eltype [size]]) ergeben
      #   STRING falls eltype = CHARACTER,
      #   BIT-VECTOR falls eltype = BIT,
      #   n [steht f�r (VECTOR (UNSIGNED-BYTE n))] falls eltype = n BIT,
      #   VECTOR sonst.
      # - (SIMPLE-VECTOR [size]), VECTOR, SIMPLE-VECTOR ergeben VECTOR.
      # - ([SIMPLE-]STRING [size]), [SIMPLE-]STRING ergeben STRING.
      # - ([SIMPLE-]BIT-VECTOR [size]), [SIMPLE-]BIT-VECTOR ergeben BIT-VECTOR.
      # - Zus�tzlich (nicht sehr sch�n): [SIMPLE-]ARRAY ergibt VECTOR.
      reexpand:
      if (symbolp(name))
        { if (eq(name,S(list))) { goto expanded_unconstrained; }
          if (eq(name,S(vector))) { goto expanded_unconstrained; }
          if (eq(name,S(simple_vector))) { name = S(vector); goto expanded_unconstrained; }
          if (eq(name,S(string))) { goto expanded_unconstrained; }
          if (eq(name,S(simple_string))) { name = S(string); goto expanded_unconstrained; }
          if (eq(name,S(bit_vector))) { goto expanded_unconstrained; }
          if (eq(name,S(simple_bit_vector))) { name = S(bit_vector); goto expanded_unconstrained; }
          if (eq(name,S(array)) || eq(name,S(simple_array))) { name = S(vector); goto expanded_unconstrained; }
          # evtl. (get name 'DEFTYPE-EXPANDER) mit Argument (list name) aufrufen:
          {var object expander = get(name,S(deftype_expander));
           if (!eq(expander,unbound))
             { pushSTACK(expander);
               pushSTACK(name); name = allocate_cons(); Car(name) = popSTACK(); # (list name)
               expander = STACK_0; STACK_0 = name;
               funcall(expander,1); # Expander aufrufen
               name = value1; goto reexpand; # Ergebnis weiterverwenden
          } }
          goto expanded_unconstrained; # sonstige Symbole k�nnen DEFSTRUCT-Typen sein
        }
      elif (consp(name))
        { var object name1 = Car(name);
          if (symbolp(name1))
            { var object name2 = Cdr(name);
              if (nullp(name2) || (consp(name2) && nullp(Cdr(name2))))
                { if (eq(name1,S(simple_vector)))
                    { name = S(vector); goto expanded_maybe_constrained; }
                  if (eq(name1,S(string)) || eq(name1,S(simple_string)))
                    { name = S(string); goto expanded_maybe_constrained; }
                  if (eq(name1,S(bit_vector)) || eq(name1,S(simple_bit_vector)))
                    { name = S(bit_vector); goto expanded_maybe_constrained; }
                  if (FALSE)
                    { expanded_maybe_constrained:
                      if (consp(name2) && integerp(Car(name2)))
                        { pushSTACK(Car(name2)); goto expanded; }
                        else
                        { goto expanded_unconstrained; }
                    }
                }
             {var object name3;
              if (nullp(name2)) { name2 = S(mal); name3 = S(mal); goto try_vector; }
              if (consp(name2))
                { name3=Cdr(name2); name2 = Car(name2);
                  if (nullp(name3)) { name3 = S(mal); goto try_vector; }
                  if (consp(name3) && nullp(Cdr(name3)))
                    { name3 = Car(name3); goto try_vector; }
                }
              if (FALSE)
                { try_vector: # Hier ist name2 = (second name), name3 = (third name), Defaults: *
                  if (eq(name1,S(vector))
                      || (   (eq(name1,S(array)) || eq(name1,S(simple_array)))
                          && (eq(name3,S(mal)) || eq(name3,Fixnum_1) || (consp(name3) && nullp(Cdr(name3))))
                     )   )
                    { if (eq(name1,S(vector)))
                        { if (integerp(name3)) { pushSTACK(name3); } else { pushSTACK(unbound); } }
                      else
                        { if (consp(name3) && integerp(Car(name3))) { pushSTACK(Car(name3)); } else { pushSTACK(unbound); } }
                     {var uintB atype = eltype_code(name2);
                      if (atype==Atype_T) { name = S(vector); goto expanded; } # (VECTOR T)
                      elif (atype==Atype_Char) { name = S(string); goto expanded; } # (VECTOR CHARACTER)
                      elif (atype==Atype_Bit) { name = S(bit_vector); goto expanded; } # (VECTOR BIT)
                      else { name = fixnum(bit(atype)); goto expanded; } # (VECTOR (UNSIGNED-BYTE n))
             }  }   }}
              # evtl. (get name1 'DEFTYPE-EXPANDER) mit Argument name aufrufen:
             {var object expander = get(name1,S(deftype_expander));
              if (!eq(expander,unbound))
                { pushSTACK(name); funcall(expander,1); # Expander aufrufen
                  name = value1; goto reexpand; # Ergebnis weiterverwenden
        }   }} }
      goto bad_name;
    expanded_unconstrained:
      pushSTACK(unbound); # no length constraint
    expanded:
      # SEQ-TYPES-Liste durchgehen:
      { var object list = O(seq_types);
        while (consp(list))
          { var object typdescr = Car(list);
            if (eq(name,seq_type(typdescr))) { return typdescr; }
            list = Cdr(list);
      }   }
    bad_name:
      pushSTACK(name); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(O(type_recognizable_sequence_type)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(name);
      fehler(type_error,
             DEUTSCH ? "Es gibt keine Sequences vom Typ ~." :
             ENGLISH ? "There are no sequences of type ~" :
             FRANCAIS ? "Il n'existe pas de s�quences de type ~." :
             ""
            );
    }

# UP: liefert den Typdescriptor einer Sequence
# get_seq_type(seq)
# > seq: eine Sequence
# < ergebnis: Typdescriptor oder NIL
  local object get_seq_type (object seq);
  local object get_seq_type(seq)
    var object seq;
    { var object name;
      if (listp(seq)) { name = S(list); } # Typ LIST
      elif (stringp(seq)) { name = S(string); } # Typ STRING
      elif (bit_vector_p(seq)) { name = S(bit_vector); } # Typ BIT-VECTOR
      elif (general_byte_vector_p(seq)) # Typ n, bedeutet (VECTOR (UNSIGNED-BYTE n))
        { name = fixnum(bit(Iarray_flags(seq) & arrayflags_atype_mask)); }
      elif (vectorp(seq)) { name = S(vector); } # Typ [GENERAL-]VECTOR
      elif (structurep(seq))
        { name = TheStructure(seq)->structure_types; # Structure-Typen-List*e
          while (consp(name)) { name = Cdr(name); } # davon den letzten Typ nehmen
        }
      else return NIL;
      # SEQ-TYPES-Liste durchgehen:
      { var object list = O(seq_types);
        while (consp(list))
          { var object typdescr = Car(list);
            if (eq(name,seq_type(typdescr))) { return typdescr; }
            list = Cdr(list);
          }
        return NIL;
    } }

# UP: liefert den Typdescriptor einer Sequence, evtl. Fehlermeldung
# get_valid_seq_type(seq)
# > seq: eine Sequence
# < ergebnis: Typdescriptor
  local object get_valid_seq_type (object seq);
  local object get_valid_seq_type(seq)
    var object seq;
    { var object typdescr = get_seq_type(seq); # Typdescriptor bestimmen
      if (!(nullp(typdescr))) { return typdescr; } # gefunden -> OK
      # sonst Fehler melden:
      pushSTACK(seq); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(S(sequence)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(seq);
      fehler(type_error,
             DEUTSCH ? "Das ist keine Sequence: ~" :
             ENGLISH ? "~ is not a sequence" :
             FRANCAIS ? "~ n'est pas une s�quence." :
             ""
            );
    }

# Fehler, wenn der Sequence-Typ eine andere L�nge vorgibt als die, die
# herauskommt.
  nonreturning_function(local, fehler_seqtype_length, (object seqtype_length, object computed_length));
  local void fehler_seqtype_length(seqtype_length,computed_length)
    var object seqtype_length;
    var object computed_length;
    { pushSTACK(computed_length); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(NIL);
      pushSTACK(computed_length);
      pushSTACK(seqtype_length);
      pushSTACK(S(eql)); pushSTACK(seqtype_length);
      { var object type = listof(2); STACK_2 = type; } # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      fehler(type_error,
             DEUTSCH ? "Sequence-Typ gibt L�nge ~ vor, Ergebnis hat aber die L�nge ~." :
             ENGLISH ? "sequence type forces length ~, but result has length ~" :
             FRANCAIS ? "Le type de s�quence implique une longueur ~, mais le r�sultat est de longueur ~." :
             ""
            );
    }

# Fehler, wenn Argument kein Integer >=0
  nonreturning_function(local, fehler_posint, (object fun, object kw, object obj));
  local void fehler_posint(fun,kw,obj)
    var object fun;
    var object kw;
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(O(type_posinteger)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj);
      pushSTACK(kw);
      pushSTACK(fun);
      fehler(type_error,
             DEUTSCH ? "~: ~ muss ein Integer >=0 sein, nicht ~" :
             ENGLISH ? "~: ~ should be an integer >=0, not ~" :
             FRANCAIS ? "~ : ~ doit �tre un entier positif ou z�ro et non ~" :
             ""
            );
    }

# Macro: Tr�gt NIL als Defaultwert eines Parameters in den Stack ein:
# default_NIL(par);
  #define default_NIL(par)  \
    if (eq(par,unbound)) { par = NIL; }

# Macro: Tr�gt 0 als Defaultwert von START in den Stack ein:
# start_default_0(start);
  #define start_default_0(start)  \
    if (eq(start,unbound)) { start = Fixnum_0; }

# Macro: Tr�gt (SEQ-LENGTH sequence) als Defaultwert von END in den Stack ein:
# end_default_len(end,seq,typdescr);
# kann GC ausl�sen
  #define end_default_len(end,seq,typdescr)  \
    if (eq(end,unbound) || eq(end,NIL))              \
      { var object old_subr_self = subr_self; # aktuelles SUBR, nicht GC-gef�hrdet! \
        var object lengthfun = seq_length(typdescr); \
        pushSTACK(seq); funcall(lengthfun,1);        \
        end = value1;                                \
        subr_self = old_subr_self;                   \
      }

# UP: �berpr�ft START- und END- Argumente
# > subr_self: Aufrufer (ein SUBR)
# > kwptr: kwptr[0] = START-Keyword,
#          kwptr[1] = END-Keyword
# > argptr: *(argptr STACKop 1) = START-Argument,
#           *(argptr STACKop 0) = END-Argument
  local void test_start_end (const object* kwptr, const object* argptr);
  local void test_start_end(kwptr,argptr)
    var const object* kwptr;
    var const object* argptr;
    { # START-Argument muss ein Integer >= 0 sein:
      var object start = *(argptr STACKop 1);
      if (!(integerp(start) && positivep(start)))
        { fehler_posint(TheSubr(subr_self)->name,kwptr[0],start); }
      # END-Argument muss ein Integer >= 0 sein:
     {var object end = *(argptr STACKop 0);
      if (!(integerp(end) && positivep(end)))
        { fehler_posint(TheSubr(subr_self)->name,kwptr[1],end); }
      # Argumente vergleichen:
      if (!(I_I_comp(end,start)>=0)) # end >= start ?
        { # nein -> Fehler melden:
          pushSTACK(end); pushSTACK(kwptr[1]);
          pushSTACK(start); pushSTACK(kwptr[0]);
          pushSTACK(TheSubr(subr_self)->name);
          fehler(error,
                 DEUTSCH ? "~: ~ = ~ darf ~ = ~ nicht �bersteigen." :
                 ENGLISH ? "~: ~ = ~ should not be greater than ~ = ~" :
                 FRANCAIS ? "~ : ~ = ~ ne doit pas exc�der ~ = ~." :
                 ""
                );
        }
    }}

# UP: �berpr�ft START- und END- Argumente (END-Argument evtl. NIL)
# > subr_self: Aufrufer (ein SUBR)
# > kwptr: kwptr[0] = START-Keyword,
#          kwptr[1] = END-Keyword
# > argptr: *(argptr STACKop 1) = START-Argument,
#           *(argptr STACKop 0) = END-Argument
  local void test_start_end_1 (const object* kwptr, const object* argptr);
  local void test_start_end_1(kwptr,argptr)
    var const object* kwptr;
    var const object* argptr;
    { # START-Argument muss ein Integer >= 0 sein:
      var object start = *(argptr STACKop 1);
      if (!(integerp(start) && positivep(start)))
        { fehler_posint(TheSubr(subr_self)->name,kwptr[0],start); }
      # END-Argument muss NIL oder ein Integer >= 0 sein:
     {var object end = *(argptr STACKop 0);
      if (nullp(end)) { return; } # end=NIL -> OK, fertig
      if (!(integerp(end) && positivep(end)))
        { fehler_posint(TheSubr(subr_self)->name,kwptr[1],end); }
      # Argumente vergleichen:
      if (!(I_I_comp(end,start)>=0)) # end >= start ?
        { # nein -> Fehler melden:
          pushSTACK(end); pushSTACK(kwptr[1]);
          pushSTACK(start); pushSTACK(kwptr[0]);
          pushSTACK(TheSubr(subr_self)->name);
          fehler(error,
                 DEUTSCH ? "~: ~ = ~ darf ~ = ~ nicht �bersteigen." :
                 ENGLISH ? "~: ~ = ~ should not be greater than ~ = ~" :
                 FRANCAIS ? "~ : ~ = ~ ne doit pas exc�der ~ = ~." :
                 ""
                );
        }
    }}

# Macro: Incrementiert eine Integer-Variable (im Stack).
# increment(var)
# > var: alter Wert
# < var: neuer Wert
# < ergebnis: neuer Wert
# kann GC ausl�sen
  #define increment(var)  (var = I_1_plus_I(var)) # var := (1+ var)

# Macro: Decrementiert eine Integer-Variable (im Stack).
# decrement(var)
# > var: alter Wert
# < var: neuer Wert
# < ergebnis: neuer Wert
# kann GC ausl�sen
  #define decrement(var)  (var = I_minus1_plus_I(var)) # var := (1- var)

# Macro: R�ckt einen Vorw�rts-Pointer (im Stack) weiter.
# pointer_update(pointer,sequence,typdescr);
# pointer muss von der Form STACK_i sein!
# kann GC ausl�sen
  #define pointer_update(pointer,sequence,typdescr)  \
    { var object updatefun = seq_upd(typdescr);          \
      pushSTACK(sequence); # sequence                    \
      pushSTACK(*(&(pointer) STACKop 1)); # pointer      \
      funcall(updatefun,2); # (SEQ-UPD sequence pointer) \
      pointer = value1; # =: pointer                     \
    }

# Macro: R�ckt einen R�ckw�rts-Pointer (im Stack) weiter.
# pointer_fe_update(pointer,sequence,typdescr);
# pointer muss von der Form STACK_i sein!
# kann GC ausl�sen
  #define pointer_fe_update(pointer,sequence,typdescr)  \
    { var object updatefun = seq_fe_upd(typdescr);          \
      pushSTACK(sequence); # sequence                       \
      pushSTACK(*(&(pointer) STACKop 1)); # pointer         \
      funcall(updatefun,2); # (SEQ-FE-UPD sequence pointer) \
      pointer = value1; # =: pointer                        \
    }

# UP: kopiert einen Teil einer Sequence in eine andere Sequence.
# > STACK_6: sequence1
# > STACK_5: typdescr1
# > STACK_4: sequence2
# > STACK_3: typdescr2
# > STACK_2: count (ein Integer >=0)
# > STACK_1: pointer1
# > STACK_0: pointer2
# kopiert count Elemente von sequence1 nach sequence2 und r�ckt dabei
# pointer1 und pointer2 um count Stellen weiter (mit SEQ-UPD), setzt count:=0.
# kann GC ausl�sen
  local void copy_seqpart_into (void);
  local void copy_seqpart_into()
    { # Methode etwa so:
      # (loop
      #   (when (zerop count) (return))
      #   (SEQ2-ACCESS-SET sequence2 pointer2 (SEQ1-ACCESS sequence1 pointer1))
      #   (setq pointer1 (SEQ1-UPD pointer1))
      #   (setq pointer2 (SEQ2-UPD pointer2))
      #   (decf count)
      # )
      until (eq(STACK_2,Fixnum_0)) # count (ein Integer) = 0 -> Ende
        { # (SEQ1-ACCESS seq1 pointer1) bilden:
          pushSTACK(STACK_(6+0)); # seq1
          pushSTACK(STACK_(1+1)); # pointer1
          funcall(seq_access(STACK_(5+2)),2);
          # (SEQ2-ACCESS-SET seq2 pointer2 ...) ausf�hren:
          pushSTACK(STACK_(4+0)); # seq2
          pushSTACK(STACK_(0+1)); # pointer2
          pushSTACK(value1);
          funcall(seq_access_set(STACK_(3+3)),3);
          # pointer1 := (SEQ1-UPD seq1 pointer1) :
          pointer_update(STACK_1,STACK_6,STACK_5);
          # pointer2 := (SEQ2-UPD seq2 pointer2) :
          pointer_update(STACK_0,STACK_4,STACK_3);
          # count := (1- count) :
          decrement(STACK_2);
        }
    }

LISPFUNN(sequencep,1)
# (SYS::SEQUENCEP object) testet, ob object eine Sequence ist.
  { var object typdescr = get_seq_type(popSTACK()); # Typdescriptor oder NIL
    value1 = (!(nullp(typdescr)) ? T : NIL); mv_count=1;
  }

LISPFUNN(defseq,1)
# (SYSTEM::%DEFSEQ typdescr) erweitert die Liste der Sequencetypen um
# typdescr (muss ein Simple-Vector der L�nge 16 sein).
  { # (list typdescr) bilden:
    var object new_cons = allocate_cons();
    Car(new_cons) = STACK_0;
    # (nconc SEQ_TYPES (list typdescr)) bilden:
    Cdr(new_cons) = nreverse(O(seq_types)); # (nreverse SEQ_TYPES)
    O(seq_types) = nreverse(new_cons);
    # Typ (als Symbol) zur�ck:
    value1 = seq_type(popSTACK()); mv_count=1;
  }

LISPFUNN(elt,2) # (ELT sequence index), CLTL S. 248
  { # sequence �berpr�fen:
    var object typdescr = get_valid_seq_type(STACK_1);
    # index �berpr�fen:
    if (!(posfixnump(STACK_0)))
      { pushSTACK(STACK_0); # Wert f�r Slot DATUM von TYPE-ERROR
        pushSTACK(O(type_posfixnum)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
        pushSTACK(STACK_(0+2)); pushSTACK(S(elt));
        fehler(type_error,
               DEUTSCH ? "~: Der Index muss ein Fixnum >=0 sein, nicht ~" :
               ENGLISH ? "~: the index should be a fixnum >=0, not ~" :
               FRANCAIS ? "~ : L'index doit �tre de type FIXNUM positif ou z�ro et non ~" :
               ""
              );
      }
    # SEQ-ELT aufrufen:
    funcall(seq_elt(typdescr),2); # (SEQ-ELT sequence index)
    # value1 als Wert
  }

LISPFUNN(setelt,3) # (SYSTEM::%SETELT sequence index value), vgl. CLTL S. 248
  { # sequence �berpr�fen:
    var object typdescr = get_valid_seq_type(STACK_2);
    # index �berpr�fen:
    if (!(posfixnump(STACK_1)))
      { pushSTACK(STACK_1); # Wert f�r Slot DATUM von TYPE-ERROR
        pushSTACK(O(type_posfixnum)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
        pushSTACK(STACK_(1+2)); pushSTACK(S(elt)); pushSTACK(S(setf));
        fehler(type_error,
               DEUTSCH ? "~ ~: Der Index muss ein Fixnum >=0 sein, nicht ~" :
               ENGLISH ? "~ ~: the index should be a fixnum >=0, not ~" :
               FRANCAIS ? "~ ~ : L'index doit �tre de type FIXNUM positif ou z�ro et non ~" :
               ""
              );
      }
    # SEQ-SET-ELT aufrufen:
    pushSTACK(STACK_(2+0)); # sequence
    pushSTACK(STACK_(1+1)); # index
    pushSTACK(STACK_(0+2)); # value
    funcall(seq_set_elt(typdescr),3); # (SEQ-SET-ELT sequence index value)
    value1 = popSTACK(); mv_count=1; # value als Wert
    skipSTACK(2);
  }

# UP: Kopiert ein sequence1 - Teilst�ck in sequence2 hinein
# und liefert sequence2 als Wert.
# copy_seqpart_onto()
# > Stackaufbau: seq1, typdescr1, seq2, typdescr2, count, pointer1
# < STACK: aufger�umt
# < Wert: gef�llte seq2
  local Values copy_seqpart_onto (void);
  local Values copy_seqpart_onto()
    { # Stackaufbau: seq1, typdescr1, seq2, typdescr2, count, pointer1.
      pushSTACK(STACK_3); funcall(seq_init(STACK_(2+1)),1); # (SEQ2-INIT seq2)
      pushSTACK(value1);
      # Stackaufbau: seq1, typdescr1, seq2, typdescr2, count, pointer1, pointer2.
      copy_seqpart_into(); # Teilst�ck von seq1 nach seq2 kopieren
      value1 = STACK_4; mv_count=1; # seq2 als Wert
      skipSTACK(7);
    }

# UP: Liefert ein neu alloziertes sequence-Teilst�ck als Wert.
# subseq()
# > Stackaufbau: sequence, start, end, typdescr,
#   mit �berpr�ften Argumenten (start,end Integers >=0, start<=end)
# < STACK: aufger�umt
# < Wert: Kopie des angegebenen Teilst�cks von sequence
  local Values subseq (void);
  local Values subseq()
    { STACK_1 = I_I_minus_I(STACK_1,STACK_2); # count := (- end start)
      # Stackaufbau: sequence, start, count, typdescr.
      pushSTACK(STACK_1); funcall(seq_make(STACK_(0+1)),1); # (SEQ-MAKE count)
     {var object start = STACK_2;
      var object typdescr = STACK_0;
      STACK_2 = typdescr;
      pushSTACK(STACK_1);
      STACK_2 = value1;
      # Stackaufbau: sequence, typdescr, seq2, typdescr, count.
      pushSTACK(STACK_4); pushSTACK(start); funcall(seq_init_start(typdescr),2);
      pushSTACK(value1); # (SEQ-INIT-START sequence start)
      # Stackaufbau; seq1, typdescr, seq2, typdescr, count, pointer1.
      return_Values copy_seqpart_onto(); # kopieren, seq2 als Wert
    }}

LISPFUN(subseq,2,1,norest,nokey,0,NIL)
# (SUBSEQ sequence start &optional end), CLTL S. 248
  { # Stackaufbau: sequence, start, end.
    # sequence �berpr�fen:
    var object typdescr = get_valid_seq_type(STACK_2);
    pushSTACK(typdescr);
    # Stackaufbau: sequence, start, end, typdescr.
    # Defaultwert f�r end ist (length sequence):
    if (eq(STACK_1,unbound)
        #ifdef X3J13_149
        || nullp(STACK_1)
        #endif
       )
      { var object old_subr_self = subr_self; # aktuelles SUBR, nicht GC-gef�hrdet!
        # end nicht angegeben -> muss end:=(length sequence) setzen:
        pushSTACK(STACK_3); funcall(seq_length(typdescr),1); # (SEQ-LENGTH sequence)
        STACK_1 = value1;
        subr_self = old_subr_self;
      }
    # Stackaufbau: sequence, start, end, typdescr.
    # Start- und End-Argumente �berpr�fen:
    test_start_end(&O(kwpair_start),&STACK_1);
    # Teilst�ck bilden:
    return_Values subseq();
  }

# UP: Kopiert sequence1 in sequence2 hinein und liefert sequence2 als Wert.
# copy_seq_onto()
# > Stackaufbau: seq1, typdescr1, seq2, typdescr2, len
# < STACK: aufger�umt
# < Wert: gef�llte seq2
  local Values copy_seq_onto (void);
  local Values copy_seq_onto()
    { # Stackaufbau: seq1, typdescr1, seq2, typdescr2, len.
      pushSTACK(STACK_4); funcall(seq_init(STACK_(3+1)),1); # (SEQ1-INIT seq1)
      pushSTACK(value1);
      # Stackaufbau: seq1, typdescr1, seq2, typdescr2, len, pointer1.
      return_Values copy_seqpart_onto();
    }

LISPFUNN(copy_seq,1) # (COPY-SEQ sequence), CLTL S. 248
  { # Stackaufbau: sequence.
    # sequence �berpr�fen:
    var object typdescr = get_valid_seq_type(STACK_0);
    pushSTACK(typdescr);
    # Stackaufbau: sequence, typdescr.
    pushSTACK(STACK_1); funcall(seq_length(typdescr),1);
    pushSTACK(value1); # (SEQ-LENGTH sequence)
    # Stackaufbau: sequence, typdescr, len.
    pushSTACK(STACK_0); funcall(seq_make(STACK_(1+1)),1); # (SEQ-MAKE len)
    pushSTACK(STACK_1); pushSTACK(STACK_(0+1)); STACK_2 = value1;
    # Stackaufbau: seq1, typdescr, seq2, typdescr, len.
    return_Values copy_seq_onto();
  }

LISPFUNN(length,1) # (LENGTH sequence), CLTL S. 248
  { var object arg = popSTACK();
    if (consp(arg))
      { # arg ist ein Cons
        value1 = fixnum(llength(arg)); # Listenl�nge als Fixnum
        mv_count=1;
        return;
      }
    elif (symbolp(arg))
      { # arg ist ein Symbol
        if (nullp(arg))
          { value1 = Fixnum_0; mv_count=1; # NIL hat als Liste die L�nge 0
            return;
      }   } # sonstige Symbole sind keine Sequences
    elif (vectorp(arg))
      { # arg ist ein Vektor
        value1 = fixnum(vector_length(arg)); # Vektorl�nge als Fixnum
        mv_count=1;
        return;
      }
    else
      { # arg ist weder eine Liste noch ein Vektor
        var object typdescr = get_valid_seq_type(arg); # hier evtl. Fehlermeldung
        # sonstige Sequences:
        pushSTACK(arg); funcall(seq_length(typdescr),1); # (SEQ-LENGTH arg) aufrufen
        return;
      }
    # arg ist keine Sequence
    pushSTACK(arg); # Wert f�r Slot DATUM von TYPE-ERROR
    pushSTACK(S(sequence)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
    pushSTACK(arg); pushSTACK(S(length));
    fehler(type_error,
           DEUTSCH ? "~: ~ ist keine Sequence." :
           ENGLISH ? "~: ~ is not a sequence" :
           FRANCAIS ? "~ : ~ n'est pas une s�quence." :
           ""
          );
  }

LISPFUNN(reverse,1) # (REVERSE sequence), CLTL S. 248
  { var object arg = STACK_0;
    if (listp(arg))
      { # arg ist eine Liste
        value1 = reverse(arg); mv_count=1; skipSTACK(1);
      }
      else
      { var object typdescr = get_valid_seq_type(arg);
        # arg ist eine sonstige Sequence
        pushSTACK(typdescr);
        # Stackaufbau: seq1, typdescr.
        pushSTACK(arg); funcall(seq_length(typdescr),1); # (SEQ-LENGTH seq1)
        pushSTACK(value1);
        # Stackaufbau: seq1, typdescr, len.
        pushSTACK(STACK_0); funcall(seq_make(STACK_(1+1)),1); # (SEQ-MAKE len)
        pushSTACK(value1);
        # Stackaufbau: seq1, typdescr, count, seq2.
        pushSTACK(STACK_3); funcall(seq_fe_init(STACK_(2+1)),1); # (SEQ-FE-INIT seq1)
        pushSTACK(value1);
        # Stackaufbau: seq1, typdescr, count, seq2, pointer1.
        pushSTACK(STACK_1); funcall(seq_init(STACK_(3+1)),1); # (SEQ-INIT seq2)
        pushSTACK(value1);
        # Stackaufbau: seq1, typdescr, count, seq2, pointer1, pointer2.
        until (eq(STACK_3,Fixnum_0)) # count (ein Integer) = 0 -> Ende
          { # (SEQ-ACCESS seq1 pointer1) bilden:
            pushSTACK(STACK_5); pushSTACK(STACK_(1+1));
            funcall(seq_access(STACK_(4+2)),2); # (SEQ-ACCESS seq1 pointer1)
            # (SEQ-ACCESS-SET seq2 pointer2 ...) ausf�hren:
            pushSTACK(STACK_2); pushSTACK(STACK_(0+1)); pushSTACK(value1);
            funcall(seq_access_set(STACK_(4+3)),3); # (SEQ-ACCESS-SET seq2 pointer2 ...)
            # pointer1 := (SEQ-FE-UPD seq1 pointer1) :
            pointer_fe_update(STACK_1,STACK_5,STACK_4);
            # pointer2 := (SEQ-UPD seq2 pointer2) :
            pointer_update(STACK_0,STACK_2,STACK_4);
            # count := (1- count) :
            decrement(STACK_3);
          }
        value1 = STACK_2; mv_count=1; # seq2 als Wert
        skipSTACK(6);
  }   }

LISPFUNN(nreverse,1) # (NREVERSE sequence), CLTL S. 248
  { var object seq = STACK_0;
    if (listp(seq))
      { # seq ist eine Liste
        value1 = nreverse(seq); mv_count=1;
        skipSTACK(1);
      }
    elif (vectorp(seq))
      { # seq ist ein Vektor
        var object typdescr = get_valid_seq_type(seq);
        pushSTACK(typdescr);
        # Stackaufbau: seq, typdescr.
        pushSTACK(seq); funcall(seq_length(typdescr),1); # (SEQ-LENGTH seq)
        { var object len = value1;
          var object len2 = I_I_ash_I(len,Fixnum_minus1);
          pushSTACK(len2); # (ASH len -1) = (FLOOR len 2)
        }
        # Stackaufbau: seq, typdescr, count.
        pushSTACK(STACK_2); funcall(seq_init(STACK_(1+1)),1); # (SEQ-INIT seq)
        pushSTACK(value1);
        # Stackaufbau: seq, typdescr, count, pointer1.
        pushSTACK(STACK_3); funcall(seq_fe_init(STACK_(2+1)),1); # (SEQ-FE-INIT seq)
        pushSTACK(value1);
        # Stackaufbau: seq, typdescr, count, pointer1, pointer2.
        until (eq(STACK_2,Fixnum_0)) # count (ein Integer) = 0 -> Ende
          { # (SEQ-ACCESS seq pointer1) bilden:
            pushSTACK(STACK_4); pushSTACK(STACK_(1+1));
            funcall(seq_access(STACK_(3+2)),2); # (SEQ-ACCESS seq pointer1)
            pushSTACK(value1); # und retten
            # (SEQ-ACCESS seq pointer2) bilden:
            pushSTACK(STACK_(4+1)); pushSTACK(STACK_(0+1+1));
            funcall(seq_access(STACK_(3+1+2)),2); # (SEQ-ACCESS seq pointer2)
            # (SEQ-ACCESS-SET seq pointer1 ...) ausf�hren:
            pushSTACK(STACK_(4+1)); pushSTACK(STACK_(1+1+1)); pushSTACK(value1);
            funcall(seq_access_set(STACK_(3+1+3)),3); # (SEQ-ACCESS-SET seq pointer1 ...)
            # (SEQ-ACCESS-SET seq pointer2 ...) ausf�hren:
           {var object element1 = popSTACK(); # gerettetes ELement
            pushSTACK(STACK_4); pushSTACK(STACK_(0+1)); pushSTACK(element1); }
            funcall(seq_access_set(STACK_(3+3)),3); # (SEQ-ACCESS-SET seq pointer2 ...)
            # pointer1 := (SEQ-UPD seq pointer1) :
            pointer_update(STACK_1,STACK_4,STACK_3);
            # pointer2 := (SEQ-FE-UPD seq pointer2) :
            pointer_fe_update(STACK_0,STACK_4,STACK_3);
            # count := (1- count) :
            decrement(STACK_2);
          }
        skipSTACK(4);
        value1 = popSTACK(); mv_count=1; # modifizierte seq als Wert
      }
    else
      { var object typdescr = get_valid_seq_type(seq);
        # seq ist eine allgemeine Sequence
        pushSTACK(typdescr);
        # Stackaufbau: seq, typdescr.
        pushSTACK(seq); funcall(seq_length(typdescr),1); # (SEQ-LENGTH seq)
        if (!(posfixnump(value1))) # sollte ein Fixnum >=0 sein
          { pushSTACK(value1); pushSTACK(S(nreverse));
            fehler(error,
                   DEUTSCH ? "~: Fehlerhafte L�nge aufgetreten: ~" :
                   ENGLISH ? "~: bad length ~" :
                   FRANCAIS ? "~ : occurence d'une mauvaise longueur: ~" :
                   ""
                  );
          }
        {var uintL len = posfixnum_to_L(value1); # len
         # Grundidee: Um eine Sequence mit len Elementen umzudrehen, m�ssen
         # der linke und der rechte Block mit je floor(len/2) Elementen
         # vertauscht und dann einzeln umgedreht werden (rekursiv!); das
         # mittlere Element (bei ungeradem len) bleibt unver�ndert.
         # Entrekursivierter Algorithmus:
         # F�r j=0,1,2,... sind 2^j mal zwei (fast) adjazente Bl�cke
         # der L�nge k2=floor(len/2^(j+1)) zu vertauschen.
         var uintL j = 0; # j := 0
         var uintL k = len; # k = floor(len/2^j) := len
         var uintL k2; # k2 = floor(k/2)
         var uintL k1; # k1 = ceiling(k/2)
         until ((k2 = floor(k,2)) == 0) # k halbiert =0 -> Schleifenende
           { k1 = k - k2; # k1 = (altes k) - (neues k) = ceiling((altes k)/2)
            {var uintL pstack = 0; # ein Pseudo-Stack
             # Stackaufbau: seq, typdescr.
             pushSTACK(STACK_1); funcall(seq_init(STACK_(0+1)),1); # (SEQ-INIT seq)
             pushSTACK(value1);
             # Stackaufbau: seq, typdescr, pointer1.
             pushSTACK(STACK_2); pushSTACK(fixnum(k1));
             funcall(seq_init_start(STACK_(1+2)),2); # (SEQ-INIT-START seq k1)
             pushSTACK(value1);
             # Stackaufbau: seq, typdescr, pointer1, pointer2.
             # pointer1 und pointer2 laufen gemeinsam durch seq, dabei hat
             # pointer2 einen Vorsprung von k1.
             loop
               { # Zwei Bl�cke der L�nge k2 = floor(len/2^(j+1)) vertauschen:
                 {var uintL i = k2; # i:=k2 >0
                  do { # (SEQ-ACCESS seq pointer1) bilden:
                       pushSTACK(STACK_3); pushSTACK(STACK_(1+1));
                       funcall(seq_access(STACK_(2+2)),2); # (SEQ-ACCESS seq pointer1)
                       pushSTACK(value1); # und retten
                       # (SEQ-ACCESS seq pointer2) bilden:
                       pushSTACK(STACK_(3+1)); pushSTACK(STACK_(0+1+1));
                       funcall(seq_access(STACK_(2+1+2)),2); # (SEQ-ACCESS seq pointer2)
                       # (SEQ-ACCESS-SET seq pointer1 ...) ausf�hren:
                       pushSTACK(STACK_(3+1)); pushSTACK(STACK_(1+1+1)); pushSTACK(value1);
                       funcall(seq_access_set(STACK_(2+1+3)),3); # (SEQ-ACCESS-SET seq pointer1 ...)
                       # (SEQ-ACCESS-SET seq pointer2 ...) ausf�hren:
                      {var object element1 = popSTACK(); # gerettetes ELement
                       pushSTACK(STACK_3); pushSTACK(STACK_(0+1)); pushSTACK(element1); }
                       funcall(seq_access_set(STACK_(2+3)),3); # (SEQ-ACCESS-SET seq pointer2 ...)
                       # pointer1 := (SEQ-UPD seq pointer1) :
                       pointer_update(STACK_1,STACK_3,STACK_2);
                       # pointer2 := (SEQ-FE-UPD seq pointer2) :
                       pointer_fe_update(STACK_0,STACK_3,STACK_2);
                       --i; # i:=i-1
                     }
                     until (i==0); # bei i=0 Schleifenende
                 }
                 pstack = pstack+1; # stack:=stack+1
                 if (pstack == (1UL<<j)) break; # stack=2^j geworden -> Schleifenabbruch
                 # pointer1 und pointer2 um k1+(0 oder 1) Stellen weiterr�cken:
                 { var uintL skipcount = k1;
                   { var uintL r1 = 1;
                     # r := Anzahl der Nullbits am Ende der Dualdarstellung von stack:
                     { var uintL pstackr = pstack;
                       while ((pstackr & bit(0))==0) { pstackr = pstackr>>1; r1=r1+1; }
                     }
                     # r1 = r+1
                     if (len & bit(j-r1)) # Bit j-r-1 in len gesetzt?
                       { skipcount++; } # falls ja: skipcount=k1+1, sonst skipcount=k1
                   }
                   # skipcount >= k1 >= k2 > 0
                   do { # pointer1 := (SEQ-UPD seq pointer1) :
                        pointer_update(STACK_1,STACK_3,STACK_2);
                        # pointer2 := (SEQ-FE-UPD seq pointer2) :
                        pointer_fe_update(STACK_0,STACK_3,STACK_2);
                        --skipcount;
                      }
                      until (skipcount==0);
               } }
             skipSTACK(2); # pointer1 und pointer2 vergessen
            }
            j=j+1; k=k2; # j:=j+1, k halbieren
        }  }
        skipSTACK(1); # typdescr vergessen
        value1 = popSTACK(); mv_count=1; # modifizierte seq als Wert
      }
  }

LISPFUN(make_sequence,2,0,norest,key,2,\
        (kw(initial_element),kw(update)) )
# (MAKE-SEQUENCE type size [:initial-element] [:update]), CLTL S. 249
# mit zus�tzlichem Argument :update, z.B.
# (make-sequence 'vector 5 :initial-element 3 :update #'1+) ==> #(3 4 5 6 7)
  { # Stackaufbau: type, size, initial-element, updatefun.
    # type �berpr�fen:
    var object typdescr = valid_type(STACK_3);
    # Stackaufbau: type, size, initial-element, updatefun, type-len.
    STACK_4 = typdescr;
    # size �berpr�fen, muss Integer >=0 sein:
   {var object size = STACK_3;
    if (!(integerp(size) && positivep(size)))
      { pushSTACK(size); # Wert f�r Slot DATUM von TYPE-ERROR
        pushSTACK(O(type_posinteger)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
        pushSTACK(size); pushSTACK(S(make_sequence));
        fehler(type_error,
               DEUTSCH ? "~: SIZE muss ein Integer >=0 sein, nicht ~" :
               ENGLISH ? "~: size should be an integer >=0, not ~" :
               FRANCAIS ? "~ : SIZE doit �tre un entier positif ou z�ro et non ~" :
               ""
              );
      }
    # initial-element bei Strings defaultm��ig erg�nzen:
    if (eq(STACK_2,unbound)) # :initial-element nicht angegeben?
      { if (!eq(STACK_1,unbound)) # :update ohne :initial-element -> Error
          { pushSTACK(S(make_sequence));
            fehler(error,
                   DEUTSCH ? "~: :UPDATE darf nur mit :INITIAL-ELEMENT angegeben werden." :
                   ENGLISH ? "~: :update must not be specified without :initial-element" :
                   FRANCAIS ? "~ : :UPDATE ne peut �tre sp�cifi� qu'avec :INITIAL-ELEMENT." :
                   ""
                  );
          }
        if (eq(seq_type(typdescr),S(string))) # Typname = STRING ?
          { STACK_2 = code_char(' '); } # initial-element := ' '
        elif (posfixnump(seq_type(typdescr))) # Typname Integer? (bedeutet Byte-Vektoren)
          { STACK_2 = Fixnum_0; } # initial-element := 0
      }
    if (!(eq(STACK_0,unbound) || eql(STACK_0,size)))
      { fehler_seqtype_length(STACK_0,size); }
    STACK_0 = size; funcall(seq_make(typdescr),1); # (SEQ-MAKE size)
    # Stackaufbau: typdescr, size, initial-element, updatefun.
   }
    if (!(eq(STACK_1,unbound))) # :initial-element angegeben?
      if (!(eq(STACK_2,Fixnum_0))) # size (ein Integer) = 0 -> nichts zu tun
        { pushSTACK(value1);
          # Stackaufbau: typdescr, count, element, updatefun, seq.
          pushSTACK(STACK_0); funcall(seq_init(STACK_(4+1)),1); # (SEQ-INIT seq)
          pushSTACK(value1);
          # Stackaufbau: typdescr, count, element, updatefun, seq, pointer.
          loop
            { pushSTACK(STACK_(1+0)); pushSTACK(STACK_(0+1)); pushSTACK(STACK_(3+2));
              funcall(seq_access_set(STACK_(5+3)),3); # (SEQ-ACCESS-SET seq pointer element)
              # pointer := (SEQ-UPD seq pointer) :
              pointer_update(STACK_0,STACK_1,STACK_5);
              # count := (1- count) :
              decrement(STACK_4);
              if (eq(STACK_4,Fixnum_0)) break; # count (ein Integer) = 0 -> Schleifenende
              {var object updatefun = STACK_2;
               if (!(eq(updatefun,unbound))) # falls angegeben,
                 { pushSTACK(STACK_3); funcall(updatefun,1); # (FUNCALL updatefun element)
                   STACK_3 = value1; # =: element
            } }  }
          skipSTACK(1); # pointer vergessen
          value1 = popSTACK(); # seq
        }
    mv_count=1; # seq als Wert
    skipSTACK(4);
  }

# UP: Wandelt ein Objekt in eine Sequence gegebenen Typs um.
# coerce_sequence(obj,result_type)
# > obj: Objekt, sollte eine Sequence sein
# > result_type: Bezeichner (Symbol) des Sequence-Typs
# < Wert: Sequence vom Typ result_type
# kann GC ausl�sen
  global Values coerce_sequence (object sequence, object result_type);
  global Values coerce_sequence(sequence,result_type)
    var object sequence;
    var object result_type;
    { pushSTACK(sequence);
      pushSTACK(result_type);
      { # result-type �berpr�fen:
        var object typdescr2 = valid_type(result_type);
        pushSTACK(typdescr2);
        # Stackaufbau: seq1, result-type, typdescr2-len, typdescr2.
       {var object typdescr1 = get_valid_seq_type(STACK_3); # Typ von seq1
        if (eq(seq_type(typdescr1),seq_type(typdescr2)))
          { # beide Typen dieselben -> nichts zu tun
            if (!eq(STACK_1,unbound))
              { pushSTACK(STACK_3); funcall(seq_length(typdescr1),1); # (SEQ1-LENGTH seq1)
                if (!eql(value1,STACK_1))
                  { fehler_seqtype_length(STACK_1,value1); }
              }
            skipSTACK(3); value1 = popSTACK(); mv_count=1; # seq1 als Wert
          }
          else
          { STACK_2 = typdescr1;
            # Stackaufbau: seq1, typdescr1, typdescr2-len, typdescr2.
            pushSTACK(STACK_3); funcall(seq_length(typdescr1),1); # (SEQ1-LENGTH seq1)
            if (!(eq(STACK_1,unbound) || eql(value1,STACK_1)))
              { fehler_seqtype_length(STACK_1,value1); }
            pushSTACK(value1);
            # Stackaufbau: seq1, typdescr1, typdescr2-len, typdescr2, len.
            pushSTACK(STACK_0); funcall(seq_make(STACK_(1+1)),1); # (SEQ2-MAKE len)
            STACK_2 = value1;
            # Stackaufbau: seq1, typdescr1, seq2, typdescr2, len.
            return_Values copy_seq_onto();
          }
    } }}

LISPFUN(concatenate,1,0,rest,nokey,0,NIL)
# (CONCATENATE result-type {sequence}), CLTL S. 249
  { var object* args_pointer = rest_args_pointer;
    # result-type in Typdescriptor umwandeln:
    { var object type = Before(args_pointer);
      type = valid_type(type);
      BEFORE(args_pointer) = type;
    }
    # args_pointer = Pointer �ber die Argumente,
    # rest_args_pointer = Pointer �ber die argcount Sequence-Argumente.
    # Stackaufbau: [args_pointer] typdescr2,
    #              [rest_args_pointer] {sequence}, result-type-len, [STACK].
    # Brauche 2*argcount STACK-Eintr�ge:
    get_space_on_STACK(sizeof(object) * 2*(uintL)argcount);
   {var object* behind_args_pointer = args_end_pointer; # Pointer unter die Argumente
    # Stackaufbau: [args_pointer] typdescr2,
    #              [rest_args_pointer] {sequence}, result-type-len, [behind_args_pointer].
    # Typdescriptoren und L�ngen bestimmen und im STACK ablegen:
    { var object* ptr = rest_args_pointer;
      var uintC count;
      dotimesC(count,argcount,
        { var object seq = NEXT(ptr); # n�chste Sequence
          var object typdescr = get_valid_seq_type(seq);
          pushSTACK(typdescr); # Typdescriptor in den Stack
          pushSTACK(seq); funcall(seq_length(typdescr),1); # (SEQ-LENGTH seq)
          pushSTACK(value1); # L�nge in den Stack
        });
    }
    # Stackaufbau: [args_pointer] typdescr2,
    #              [rest_args_pointer] {sequence}, result-type-len,
    #              [behind_args_pointer] {typdescr, len}, [STACK].
    # L�ngen addieren:
    { var object total_length = Fixnum_0;
      {var object* ptr = behind_args_pointer;
       var uintC count;
       dotimesC(count,argcount,
         { NEXT(ptr); # typdescr �berspringen
          {var object len = NEXT(ptr); # n�chste L�nge
           if (!(posfixnump(len)))
             { pushSTACK(len); pushSTACK(S(concatenate));
               fehler(error,
                      DEUTSCH ? "~: Fehlerhafte L�nge aufgetreten: ~" :
                      ENGLISH ? "~: bad length ~" :
                      FRANCAIS ? "~ : occurence d'une mauvaise longueur: ~" :
                      ""
                     );
             }
           total_length = I_I_plus_I(total_length,len); # total_length = total_length + len
         }});
      }
      { var object result_type_len = Before(behind_args_pointer);
        if (!(eq(result_type_len,unbound) || eql(total_length,result_type_len)))
          { fehler_seqtype_length(result_type_len,total_length); }
      }
      pushSTACK(NIL); pushSTACK(NIL); pushSTACK(NIL); # Dummies
      # neue Sequence allozieren:
      {var object* ptr = args_pointer;
       var object typdescr2 = NEXT(ptr);
       pushSTACK(typdescr2);
       pushSTACK(total_length); funcall(seq_make(typdescr2),1); # (SEQ2-MAKE total_length)
       STACK_1 = value1; # =: seq2
    } }
    # Stackaufbau: [args_pointer] typdescr2,
    #              [rest_args_pointer] {sequence}, result-type-len,
    #              [behind_args_pointer] {typdescr, len},
    #              NIL, NIL, seq2, typdescr2, [STACK].
    pushSTACK(NIL); pushSTACK(NIL); # Dummies
    # Stackaufbau: [args_pointer] typdescr2,
    #              [rest_args_pointer] {sequence}, result-type-len,
    #              [behind_args_pointer] {typdescr, len},
    #              NIL, NIL, seq2, typdescr2, NIL, NIL, [STACK].
    pushSTACK(STACK_(3)); funcall(seq_init(STACK_(2+1)),1); # (SEQ-INIT seq2)
    pushSTACK(value1);
    # Stackaufbau: [args_pointer] typdescr2,
    #              [rest_args_pointer] {sequence}, result-type-len,
    #              [behind_args_pointer] {typdescr, len},
    #              NIL, NIL, seq2, typdescr2, NIL, NIL, pointer2, [STACK].
    # Schleife �ber die argcount Sequences: in seq2 hineinkopieren
    dotimesC(argcount,argcount,
      { STACK_6 = NEXT(rest_args_pointer); # seq1 = n�chste Sequence
        STACK_5 = NEXT(behind_args_pointer); # deren typdescr1
        STACK_2 = NEXT(behind_args_pointer); # deren L�nge
        pushSTACK(STACK_6); funcall(seq_init(STACK_(5+1)),1); # (SEQ1-INIT seq1)
        STACK_1 = value1; # =: pointer1
        # Stackaufbau: [args_pointer] typdescr2,
        #              [rest_args_pointer] {sequence}, result-type-len,
        #              [behind_args_pointer] {typdescr, len},
        #              seq1, typdescr1, seq2, typdescr2, count,
        #              pointer1, pointer2, [STACK].
        copy_seqpart_into(); # ganze seq1 in die seq2 hineinkopieren
      });
    value1 = STACK_4; mv_count=1; # seq2 als Wert
    set_args_end_pointer(args_pointer); # STACK aufr�umen
  }}

# UP: L�uft durch eine Sequence durch und ruft f�r jedes Element eine Funktion
# auf.
# map_sequence(obj,fun,arg);
# > obj: Objekt, sollte eine Sequence sein
# > fun: Funktion, fun(arg,element) darf GC ausl�sen
# > arg: beliebiges vorgegebenes Argument
# kann GC ausl�sen
  global void map_sequence (object obj, map_sequence_function* fun, void* arg);
  global void map_sequence(obj,fun,arg)
    var object obj;
    var map_sequence_function* fun;
    var void* arg;
    { var object typdescr = get_valid_seq_type(obj);
      pushSTACK(typdescr);
      pushSTACK(obj);
      pushSTACK(obj); funcall(seq_init(typdescr),1); # (SEQ-INIT obj)
      pushSTACK(value1);
      # Stackaufbau: typdescr, sequence, pointer.
      loop
        { # (SEQ-ENDTEST sequence pointer) :
          pushSTACK(STACK_1); pushSTACK(STACK_1); funcall(seq_endtest(STACK_4),2);
          if (!nullp(value1)) break;
          # (SEQ-ACCESS sequence pointer) :
          pushSTACK(STACK_1); pushSTACK(STACK_1); funcall(seq_access(STACK_4),2);
          # Funktion aufrufen:
          (*fun)(arg,value1);
          # pointer := (SEQ-UPD sequence pointer) :
          pushSTACK(STACK_1); pushSTACK(STACK_1); funcall(seq_upd(STACK_4),2);
          STACK_0 = value1;
        }
      skipSTACK(3);
    }

# UP: f�hrt eine Boolesche Operation mit Pr�dikat wie SOME oder EVERY aus.
# > Stackaufbau: [args_pointer] ... predicate sequence,
#                [rest_args_pointer] {sequence} [STACK].
# > fun: Routine, die das predicate-Ergebnis abtestet und
#        TRUE liefert (und in value1 ihr Ergebnis hinterl�sst),
#        falls vorzeitig herausgesprungen werden soll.
# > argcount: Anzahl der Sequence-Argumente - 1
# > default: Defaultwert am Schluss
# < 1 Wert: wie von fun beim Hinausspringen vorgegeben, oder default.
# < STACK: aufger�umt (= args_pointer beim Einsprung)
# kann GC ausl�sen
  typedef boolean seq_boolop_fun (object pred_ergebnis);
  local Values seq_boolop (seq_boolop_fun* boolop_fun,
                           object* args_pointer,
                           object* rest_args_pointer,
                           uintC argcount,
                           object defolt);
  local Values seq_boolop(boolop_fun,args_pointer,rest_args_pointer,argcount,defolt)
    var seq_boolop_fun* boolop_fun;
    var object* args_pointer;
    var object* rest_args_pointer;
    var uintC argcount;
    var object defolt;
    { BEFORE(rest_args_pointer);
      { var object predicate = Before(rest_args_pointer);
        if (!(symbolp(predicate)
              || subrp(predicate) || closurep(predicate) || ffunctionp(predicate)
           ) )
          { pushSTACK(predicate); # Wert f�r Slot DATUM von TYPE-ERROR
            pushSTACK(S(function)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
            pushSTACK(predicate);
            pushSTACK(TheSubr(subr_self)->name);
            fehler(type_error,
                   DEUTSCH ? "~: ~ ist keine Funktion." :
                   ENGLISH ? "~: ~ is not a function" :
                   FRANCAIS ? "~: ~ n'est pas une fonction." :
                   ""
                  );
      }   }
      # rest_args_pointer zeigt jetzt �ber alle argcount+1 Sequence-Argumente
      pushSTACK(defolt); # Defaultwert retten
      # 3*(argcount+1) Pl�tze auf dem STACK beanspruchen:
      # (2mal f�r Typdescriptoren und Pointer, 1mal f�r Funktionsaufruf)
      get_space_on_STACK(sizeof(object)*3*(uintL)(argcount+1));
     {var object* typdescr_pointer = args_end_pointer; # Pointer �ber die Typdescriptoren
      # Typdescriptoren und je einen Pointer zu jeder der argcount+1
      # Sequences bestimmen und im STACK ablegen:
      { var object* ptr = rest_args_pointer;
        var uintC count;
        dotimespC(count,argcount+1,
          { var object seq = NEXT(ptr); # n�chste Sequence
            var object typdescr = get_valid_seq_type(seq);
            pushSTACK(typdescr); # Typdescriptor im STACK ablegen
            pushSTACK(seq); funcall(seq_init(typdescr),1); # (SEQ-INIT sequence)
            pushSTACK(value1); # Pointer im STACK ablegen
          });
      }
      # Stackaufbau:
      #         [args_pointer] ... predicate,
      #         [rest_args_pointer] {sequence}, default,
      #         [typdescr_pointer] {typdescr, pointer}, [STACK].
      # Schleife: die Funktion aufrufen:
      loop
        { var object* ptr1 = rest_args_pointer;
          var object* ptr2 = typdescr_pointer;
          # ptr1 l�uft von oben durch die Sequences durch,
          # ptr2 l�uft von oben durch die Typdescr/Pointer durch.
          var uintC count;
          dotimespC(count,argcount+1,
            { var object* sequence_ = &NEXT(ptr1);
              var object* typdescr_ = &NEXT(ptr2);
              var object* pointer_ = &NEXT(ptr2);
              # (SEQ-ENDTEST sequence pointer) :
              pushSTACK(*sequence_); pushSTACK(*pointer_); funcall(seq_endtest(*typdescr_),2);
              # eine der Sequences zu Ende -> gro�e Schleife beenden:
              if (!(nullp(value1))) goto end_with_default;
              # (SEQ-ACCESS sequence pointer) :
              pushSTACK(*sequence_); pushSTACK(*pointer_); funcall(seq_access(*typdescr_),2);
              # als Argument auf den STACK legen:
              pushSTACK(value1);
              # pointer := (SEQ-UPD sequence pointer) :
              pushSTACK(*sequence_); pushSTACK(*pointer_); funcall(seq_upd(*typdescr_),2);
              *pointer_ = value1;
            });
          # Alle Sequences abgearbeitet.
          # (FUNCALL predicate (SEQ-ACCESS sequence pointer) ...) aufrufen:
          { var object* ptr = rest_args_pointer;
            var object predicate = BEFORE(ptr);
            funcall(predicate,argcount+1);
          }
          # Abtestroutine drauf anwenden:
          if ((*boolop_fun)(value1)) goto end_with_value1;
        }
      end_with_default:
        { var object* ptr = typdescr_pointer;
          value1 = BEFORE(ptr); # default als Wert
        }
      end_with_value1:
        mv_count=1; # 1 Wert
        set_args_end_pointer(args_pointer); # STACK aufr�umen
    }}

# Hilfsfunktion f�r MAP:
  local boolean boolop_nothing (object pred_ergebnis);
  local boolean boolop_nothing(pred_ergebnis)
    var object pred_ergebnis;
    { return FALSE; } # nie vorzeitig zur�ckkehren

LISPFUN(map,3,0,rest,nokey,0,NIL)
# (MAP result-type function sequence {sequence}), CLTL S. 249
  { var object* args_pointer = rest_args_pointer STACKop 3;
    # args_pointer = Pointer �ber die Argumente,
    # rest_args_pointer = Pointer �ber die argcount weiteren Sequence-Argumente.
    var object* result_type_ = &Next(args_pointer);
    # result_type_ zeigt in den STACK, auf result-type.
    if (!(nullp(*result_type_)))
      # allgemeines result-type
      { BEFORE(rest_args_pointer);
        # rest_args_pointer zeigt jetzt �ber alle argcount+1 Sequence-Argumente
        # 4*(argcount+1) Pl�tze auf dem STACK beanspruchen:
        # (3mal f�r Typdescriptoren und Pointer, 1mal f�r Funktionsaufruf)
        get_space_on_STACK(sizeof(object)*4*(uintL)(argcount+1));
        # result-type �berpr�fen:
        *result_type_ = valid_type(*result_type_);
       {var object* typdescr_pointer = args_end_pointer; # Pointer �ber die Typdescriptoren
        # Typdescriptoren und je zwei Pointer zu jeder der argcount+1
        # Sequences bestimmen und im STACK ablegen:
        { var object* ptr = rest_args_pointer;
          var uintC count;
          dotimespC(count,argcount+1,
            { var object* sequence_ = &NEXT(ptr);
              var object seq = *sequence_; # n�chste Sequence
              var object typdescr = get_valid_seq_type(seq);
              pushSTACK(typdescr); # Typdescriptor im STACK ablegen
              pushSTACK(seq); funcall(seq_init(typdescr),1); # (SEQ-INIT sequence)
              pushSTACK(value1); # Pointer im STACK ablegen
              pushSTACK(*sequence_); funcall(seq_init(STACK_(1+1)),1); # (SEQ-INIT sequence)
              pushSTACK(value1); # Pointer im STACK ablegen
            });
        }
        # Stackaufbau:
        #         [args_pointer] *result_type_ = typdescr2, function,
        #         [rest_args_pointer] {sequence}, result-type-len,
        #         [typdescr_pointer] {typdescr, pointer, pointer}, [STACK].
        # Minimale L�nge aller Sequences bestimmen, indem jeweils mit dem
        # zweiten Pointer durchgelaufen wird:
        pushSTACK(Fixnum_0); # minlength:=0
        loop
          { var object* ptr1 = rest_args_pointer;
            var object* ptr2 = typdescr_pointer;
            # ptr1 l�uft von oben durch die Sequences durch,
            # ptr2 l�uft von oben durch die Typdescr/Pointer durch.
            var uintC count;
            dotimespC(count,argcount+1,
              { var object* sequence_ = &NEXT(ptr1);
                var object* typdescr_ = &NEXT(ptr2);
                NEXT(ptr2);
               {var object* pointer_ = &NEXT(ptr2);
                # (SEQ-ENDTEST sequence pointer) :
                pushSTACK(*sequence_); pushSTACK(*pointer_); funcall(seq_endtest(*typdescr_),2);
                # eine der Sequences zu Ende -> gro�e Schleife beenden:
                if (!(nullp(value1))) goto end_found;
                # pointer := (SEQ-UPD sequence pointer) :
                pushSTACK(*sequence_); pushSTACK(*pointer_); funcall(seq_upd(*typdescr_),2);
                *pointer_ = value1;
              }});
            # Keine der Sequences war zu Ende.
            STACK_0 = fixnum_inc(STACK_0,1); # minlength := minlength+1
          }
        end_found:
        # STACK_0 = minimale L�nge der Sequences
        # Stackaufbau:
        #         [args_pointer] *result_type_ = typdescr2, function,
        #         [rest_args_pointer] {sequence}, result-type-len,
        #         [typdescr_pointer] {typdescr, pointer, pointer},
        #         size [STACK].
        { var object result_type_len = Before(typdescr_pointer);
          if (!(eq(result_type_len,unbound) || eql(STACK_0,result_type_len)))
            { fehler_seqtype_length(result_type_len,STACK_0); }
        }
        # Neue Sequence der L�nge size allozieren:
        pushSTACK(STACK_0); funcall(seq_make(*result_type_),1); # (SEQ2-MAKE size)
        pushSTACK(value1); # seq2 im STACK ablegen
        pushSTACK(STACK_0); funcall(seq_init(*result_type_),1); # (SEQ2-INIT seq2)
        pushSTACK(value1); # pointer2 im STACK ablegen
        # Stackaufbau:
        #         [args_pointer] *result_type_ = typdescr2, function,
        #         [rest_args_pointer] {sequence}, result-type-len,
        #         [typdescr_pointer] {typdescr, pointer, pointer},
        #         size, seq2, pointer2 [STACK].
        # size mal die Funktion aufrufen, Ergebnis in seq2 eintragen:
        until (eq(STACK_2,Fixnum_0)) # count (ein Integer) = 0 -> fertig
          { var object* ptr1 = rest_args_pointer;
            var object* ptr2 = typdescr_pointer;
            # ptr1 l�uft von oben durch die Sequences durch,
            # ptr2 l�uft von oben durch die Typdescr/Pointer durch.
            var uintC count;
            dotimespC(count,argcount+1,
              { var object* sequence_ = &NEXT(ptr1);
                var object* typdescr_ = &NEXT(ptr2);
                var object* pointer_ = &NEXT(ptr2);
                NEXT(ptr2);
                # (SEQ-ACCESS sequence pointer) :
                pushSTACK(*sequence_); pushSTACK(*pointer_); funcall(seq_access(*typdescr_),2);
                # als Argument auf den STACK legen:
                pushSTACK(value1);
                # pointer := (SEQ-UPD sequence pointer) :
                pushSTACK(*sequence_); pushSTACK(*pointer_); funcall(seq_upd(*typdescr_),2);
                *pointer_ = value1;
              });
            # Alle Sequences abgearbeitet.
            # (FUNCALL function (SEQ-ACCESS sequence pointer) ...) aufrufen:
            funcall(*(result_type_ STACKop -1),argcount+1);
            # (SEQ2-ACCESS-SET seq2 pointer2 ...) ausf�hren:
            pushSTACK(STACK_(1+0)); pushSTACK(STACK_(0+1)); pushSTACK(value1);
            funcall(seq_access_set(*result_type_),3);
            # pointer2 := (SEQ2-UPD seq2 pointer2) :
            pointer_update(STACK_0,STACK_1,*result_type_);
            # size := (1- size) :
            STACK_2 = fixnum_inc(STACK_2,-1);
          }
        value1 = STACK_1; mv_count=1; # seq2 als Wert
        set_args_end_pointer(args_pointer); # STACK aufr�umen
      }}
      else
      # result-type = NIL -> viel einfacher:
      # seq_boolop mit boolop_nothing als Funktion und NIL als (Default-)Wert.
      # Dadurch wird function auf alle Elemente der Sequences angewandt.
      return_Values seq_boolop(&boolop_nothing,args_pointer,rest_args_pointer,argcount,NIL);
  }

LISPFUN(map_into,2,0,rest,nokey,0,NIL)
# (MAP-INTO result-sequence function {sequence}), CLtL2 S. 395
  { var object* args_pointer = rest_args_pointer STACKop 2;
    # args_pointer = Pointer �ber die Argumente,
    # rest_args_pointer = Pointer �ber die argcount Sequence-Argumente.
    # 3*argcount Pl�tze auf dem STACK beanspruchen:
    # (2mal f�r Typdescriptoren und Pointer, 1mal f�r Funktionsaufruf)
    get_space_on_STACK(sizeof(object)*3*(uintL)argcount);
    # result-sequence der Einfachheit halber nochmal in den STACK:
    pushSTACK(Next(args_pointer));
   {var object* typdescr_pointer = args_end_pointer; # Pointer �ber die Typdescriptoren
    # Typdescriptoren und je einen Pointer zu jeder der argcount+1
    # Sequences bestimmen und im STACK ablegen:
    { var object* ptr = rest_args_pointer;
      var uintC count;
      dotimespC(count,argcount+1,
        { var object seq = NEXT(ptr);
          var object typdescr = get_valid_seq_type(seq);
          pushSTACK(typdescr); # Typdescriptor im STACK ablegen
          pushSTACK(seq); funcall(seq_init(typdescr),1); # (SEQ-INIT sequence)
          pushSTACK(value1); # Pointer im STACK ablegen
        });
    }
    # Stackaufbau:
    #         [args_pointer] result-sequence, function,
    #         [rest_args_pointer] {sequence}, result-sequence,
    #         [typdescr_pointer] {typdescr, pointer},
    #         result-typdescr, result-pointer, [STACK].
    # Sooft wie n�tig, die Funktion aufrufen, Ergebnis in result-sequence eintragen:
    loop
      { # Test, ob eine weitere Iteration n�tig:
        { var object* ptr1 = rest_args_pointer;
          var object* ptr2 = typdescr_pointer;
          # ptr1 l�uft von oben durch die Sequences durch,
          # ptr2 l�uft von oben durch die Typdescr/Pointer durch.
          var uintC count;
          dotimesC(count,argcount,
            { var object sequence = NEXT(ptr1);
              var object typdescr = NEXT(ptr2);
              var object pointer = NEXT(ptr2);
              # (SEQ-ENDTEST sequence pointer) :
              pushSTACK(sequence); pushSTACK(pointer); funcall(seq_endtest(typdescr),2);
              # eine der Sequences zu Ende -> gro�e Schleife beenden:
              if (!nullp(value1)) goto end_reached;
            });
          # result-sequence zu Ende -> gro�e Schleife beenden:
          { var object sequence = NEXT(ptr1);
            var object typdescr = NEXT(ptr2);
            var object pointer = NEXT(ptr2);
            if (vectorp(sequence))
              { # Bei der result-sequence wird der Fill-Pointer ignoriert.
                # pointer ist der Index als Fixnum.
                if (posfixnum_to_L(pointer) >= array_total_size(sequence))
                  goto end_reached;
              }
              else
              { # (SEQ-ENDTEST sequence pointer) :
                pushSTACK(sequence); pushSTACK(pointer); funcall(seq_endtest(typdescr),2);
                if (!nullp(value1)) goto end_reached;
          }   }
        }
        # Jetzt die Funktion aufrufen:
        { var object* ptr1 = rest_args_pointer;
          var object* ptr2 = typdescr_pointer;
          # ptr1 l�uft von oben durch die Sequences durch,
          # ptr2 l�uft von oben durch die Typdescr/Pointer durch.
          var uintC count;
          dotimesC(count,argcount,
            { var object* sequence_ = &NEXT(ptr1);
              var object* typdescr_ = &NEXT(ptr2);
              var object* pointer_ = &NEXT(ptr2);
              # (SEQ-ACCESS sequence pointer) :
              pushSTACK(*sequence_); pushSTACK(*pointer_); funcall(seq_access(*typdescr_),2);
              # als Argument auf den STACK legen:
              pushSTACK(value1);
              # pointer := (SEQ-UPD sequence pointer) :
              pushSTACK(*sequence_); pushSTACK(*pointer_); funcall(seq_upd(*typdescr_),2);
              *pointer_ = value1;
            });
          # Alle Sequences abgearbeitet.
          # (FUNCALL function (SEQ-ACCESS sequence pointer) ...) aufrufen:
          funcall(Before(rest_args_pointer),argcount);
          # (SEQ-ACCESS-SET result-sequence result-pointer ...) ausf�hren:
          { var object* sequence_ = &NEXT(ptr1);
            var object* typdescr_ = &NEXT(ptr2);
            var object* pointer_ = &NEXT(ptr2);
            pushSTACK(*sequence_); pushSTACK(*pointer_); pushSTACK(value1);
            funcall(seq_access_set(*typdescr_),3);
            # pointer := (SEQ-UPD sequence pointer) :
            pushSTACK(*sequence_); pushSTACK(*pointer_); funcall(seq_upd(*typdescr_),2);
            *pointer_ = value1;
        } }
      }
    end_reached:
    { var object result = Next(args_pointer);
      if (vectorp(result) && array_has_fill_pointer_p(result))
        { # (SYS::SET-FILL-POINTER result-sequence result-pointer)
          pushSTACK(result); pushSTACK(STACK_(0+1)); funcall(L(set_fill_pointer),2);
    }   }
    value1 = Next(args_pointer); # result-sequence als Wert
    set_args_end_pointer(args_pointer); # STACK aufr�umen
  }}

# Hilfsfunktion f�r SOME:
  local boolean boolop_some (object pred_ergebnis);
  local boolean boolop_some(pred_ergebnis)
    var object pred_ergebnis;
    { if (nullp(pred_ergebnis)) # Funktionsergebnis abtesten
        { return FALSE; } # =NIL -> weitersuchen
        else
        { value1 = pred_ergebnis; # /=NIL -> dies als Wert
          return TRUE;
    }   }

LISPFUN(some,2,0,rest,nokey,0,NIL)
# (SOME predicate sequence {sequence}), CLTL S. 250
  { return_Values seq_boolop(&boolop_some,rest_args_pointer STACKop 2,rest_args_pointer,argcount,NIL); }

# Hilfsfunktion f�r EVERY:
  local boolean boolop_every (object pred_ergebnis);
  local boolean boolop_every(pred_ergebnis)
    var object pred_ergebnis;
    { if (!(nullp(pred_ergebnis))) # Funktionsergebnis abtesten
        { return FALSE; } # /=NIL -> weitersuchen
        else
        { value1 = pred_ergebnis; # =NIL -> dies (= NIL) als Wert
          return TRUE;
    }   }

LISPFUN(every,2,0,rest,nokey,0,NIL)
# (EVERY predicate sequence {sequence}), CLTL S. 250
  { return_Values seq_boolop(&boolop_every,rest_args_pointer STACKop 2,rest_args_pointer,argcount,T); }

# Hilfsfunktion f�r NOTANY:
  local boolean boolop_notany (object pred_ergebnis);
  local boolean boolop_notany(pred_ergebnis)
    var object pred_ergebnis;
    { if (nullp(pred_ergebnis)) # Funktionsergebnis abtesten
        { return FALSE; } # =NIL -> weitersuchen
        else
        { value1 = NIL; # /=NIL -> NIL als Wert
          return TRUE;
    }   }

LISPFUN(notany,2,0,rest,nokey,0,NIL)
# (NOTANY predicate sequence {sequence}), CLTL S. 250
  { return_Values seq_boolop(&boolop_notany,rest_args_pointer STACKop 2,rest_args_pointer,argcount,T); }

# Hilfsfunktion f�r NOTEVERY:
  local boolean boolop_notevery (object pred_ergebnis);
  local boolean boolop_notevery(pred_ergebnis)
    var object pred_ergebnis;
    { if (!(nullp(pred_ergebnis))) # Funktionsergebnis abtesten
        { return FALSE; } # /=NIL -> weitersuchen
        else
        { value1 = T; # =NIL -> T als Wert
          return TRUE;
    }   }

LISPFUN(notevery,2,0,rest,nokey,0,NIL)
# (NOTEVERY predicate sequence {sequence}), CLTL S. 250
  { return_Values seq_boolop(&boolop_notevery,rest_args_pointer STACKop 2,rest_args_pointer,argcount,NIL); }

# UP: �berpr�ft das :KEY-Argument
# test_key_arg(stackptr)
# > *(stackptr-4): optionales Argument
# < *(stackptr-4): korrekte KEY-Funktion
  local void test_key_arg (object* stackptr);
  local void test_key_arg(stackptr)
    var object* stackptr;
    { var object key_arg = *(stackptr STACKop -4);
      if (eq(key_arg,unbound) || nullp(key_arg))
        *(stackptr STACKop -4) = L(identity); # #'IDENTITY als Default f�r :KEY
    }

# Anwenden eines :KEY-Arguments
# funcall_key(key);
# > key: Wert des :KEY-Arguments
# > value1: Element einer Sequence
# < value1: (FUNCALL key value1)
# kann GC ausl�sen
  #define funcall_key(key)  \
    { var object _key = (key);                                                \
      if (!eq(_key,L(identity))) # :KEY #'IDENTITY ist sehr h�ufig, Abk�rzung \
        { pushSTACK(value1); funcall(_key,1); }                               \
    }

LISPFUN(reduce,2,0,norest,key,5,\
        (kw(from_end),kw(start),kw(end),kw(key),kw(initial_value)) )
# (REDUCE function sequence [:from-end] [:start] [:end] [:key] [:initial-value]),
# CLTL S. 251, CLTL2 S. 397
  { # Stackaufbau: function, sequence, from-end, start, end, key, initial-value.
    # sequence �berpr�fen:
    pushSTACK(get_valid_seq_type(STACK_5));
    # Stackaufbau: function, sequence, from-end, start, end, key, initial-value,
    #              typdescr.
    # key �berpr�fen:
    test_key_arg(&STACK_(5+1));
    # Defaultwert f�r start ist 0:
    start_default_0(STACK_(3+1));
    # Defaultwert f�r end ist die L�nge der Sequence:
    end_default_len(STACK_(2+1),STACK_(5+1),STACK_0);
    # start- und end-Argumente �berpr�fen:
    test_start_end(&O(kwpair_start),&STACK_(2+1));
    # start- und end-Argumente subtrahieren und vergleichen:
    { var object count = I_I_minus_I(STACK_(2+1),STACK_(3+1));
      # count = (- end start), ein Integer >=0.
      if (eq(count,Fixnum_0)) # count = 0 ?
        # start und end sind gleich
        { if (eq(STACK_(0+1),unbound)) # initial-value angegeben?
            { # nein -> function mit 0 Argumenten aufrufen:
              funcall(STACK_(6+1),0);
            }
            else
            { # ja -> initial-value als Wert:
              value1 = STACK_(0+1); mv_count=1;
            }
          skipSTACK(7+1);
          return;
        }
      # allgemeiner Fall: start < end, count > 0
      pushSTACK(count);
    }
    # Stackaufbau: function, sequence, from-end, start, end, key, initial-value,
    #              typdescr, count.
    # from-end abfragen:
    if (!(eq(STACK_(4+2),unbound)) && !(nullp(STACK_(4+2))))
      # from-end ist angegeben und /=NIL
      { # Durchlauf-Pointer bestimmen:
        pushSTACK(STACK_(5+2)); pushSTACK(STACK_(2+2+1));
        funcall(seq_fe_init_end(STACK_(1+2)),2); # (SEQ-FE-INIT-END seq end)
        pushSTACK(value1); # =: pointer
        # Stackaufbau: function, sequence, from-end, start, end, key, initial-value,
        #              typdescr, count, pointer.
        # Startwert bestimmen:
        if (eq(STACK_(0+3),unbound))
          # initial-value ist nicht angegeben
          { pushSTACK(STACK_(5+3)); pushSTACK(STACK_(0+1));
            funcall(seq_access(STACK_(2+2)),2); # (SEQ-ACCESS seq pointer)
            funcall_key(STACK_(1+3)); # (FUNCALL key (SEQ-ACCESS seq pointer))
            pushSTACK(value1); # =: value
            goto into_fromend_loop;
          }
          else
          # initial-value ist angegeben
          { pushSTACK(STACK_(0+3)); } # value := initial-value
        # Stackaufbau: function, seq, from-end, start, end, key, initial-value,
        #              typdescr, count, pointer, value.
        do { # n�chstes value berechnen:
             pushSTACK(STACK_(5+4)); pushSTACK(STACK_(1+1));
             funcall(seq_access(STACK_(3+2)),2); # (SEQ-ACCESS seq pointer)
             funcall_key(STACK_(1+4)); # (FUNCALL key (SEQ-ACCESS seq pointer))
             pushSTACK(value1); pushSTACK(STACK_(0+1));
             funcall(STACK_(6+4+2),2); # (FUNCALL fun (FUNCALL key (SEQ-ACCESS seq pointer)) value)
             STACK_0 = value1; # =: value
             into_fromend_loop:
             # pointer weiterr�cken:
             pointer_fe_update(STACK_1,STACK_(5+4),STACK_3);
             # count := (1- count) :
             decrement(STACK_2);
           }
           until (eq(STACK_2,Fixnum_0)); # count (ein Integer) = 0 ?
        value1 = popSTACK(); mv_count=1; # value als Wert
        skipSTACK(7+3);
      }
      else
      # from-end ist nicht angegeben
      { # Durchlauf-Pointer bestimmen:
        pushSTACK(STACK_(5+2)); pushSTACK(STACK_(3+2+1));
        funcall(seq_init_start(STACK_(1+2)),2); # (SEQ-INIT-START seq start)
        pushSTACK(value1); # =: pointer
        # Stackaufbau: function, sequence, from-end, start, end, key, initial-value,
        #              typdescr, count, pointer.
        # Startwert bestimmen:
        if (eq(STACK_(0+3),unbound))
          # initial-value ist nicht angegeben
          { pushSTACK(STACK_(5+3)); pushSTACK(STACK_(0+1));
            funcall(seq_access(STACK_(2+2)),2); # (SEQ-ACCESS seq pointer)
            funcall_key(STACK_(1+3)); # (FUNCALL key (SEQ-ACCESS seq pointer))
            pushSTACK(value1); # =: value
            goto into_fromstart_loop;
          }
          else
          # initial-value ist angegeben
          { pushSTACK(STACK_(0+3)); } # value := initial-value
        # Stackaufbau: function, seq, from-end, start, end, key, initial-value,
        #              typdescr, count, pointer, value.
        do { # n�chstes value berechnen:
             pushSTACK(STACK_(5+4)); pushSTACK(STACK_(1+1));
             funcall(seq_access(STACK_(3+2)),2); # (SEQ-ACCESS seq pointer)
             funcall_key(STACK_(1+4)); # (FUNCALL key (SEQ-ACCESS seq pointer))
             pushSTACK(STACK_0); pushSTACK(value1);
             funcall(STACK_(6+4+2),2); # (FUNCALL fun value (FUNCALL key (SEQ-ACCESS seq pointer)))
             STACK_0 = value1; # =: value
             into_fromstart_loop:
             # pointer weiterr�cken:
             pointer_update(STACK_1,STACK_(5+4),STACK_3);
             # count := (1- count) :
             decrement(STACK_2);
           }
           until (eq(STACK_2,Fixnum_0)); # count (ein Integer) = 0 ?
        value1 = popSTACK(); mv_count=1; # value als Wert
        skipSTACK(7+3);
      }
  }

LISPFUN(fill,2,0,norest,key,2, (kw(start),kw(end)) )
# (FILL sequence item [:start] [:end]), CLTL S. 252
  { # Stackaufbau: sequence, item, start, end.
    # sequence �berpr�fen:
    pushSTACK(get_valid_seq_type(STACK_3));
    # Stackaufbau: sequence, item, start, end, typdescr.
    # Defaultwert f�r start ist 0:
    start_default_0(STACK_2);
    # Defaultwert f�r end ist die L�nge der Sequence:
    end_default_len(STACK_1,STACK_4,STACK_0);
    # start- und end-Argumente �berpr�fen:
    test_start_end(&O(kwpair_start),&STACK_1);
    # start- und end-Argumente subtrahieren:
    STACK_1 = I_I_minus_I(STACK_1,STACK_2); # (- end start), ein Integer >=0
    # Stackaufbau: sequence, item, start, count, typdescr.
    # Durchlauf-Pointer bestimmen:
    pushSTACK(STACK_4); pushSTACK(STACK_(2+1));
    funcall(seq_init_start(STACK_(0+2)),2); # (SEQ-INIT-START sequence start)
    STACK_2 = value1; # =: pointer
    # Stackaufbau: sequence, item, pointer, count, typdescr.
    until (eq(STACK_1,Fixnum_0)) # count (ein Integer) = 0 -> fertig
      { pushSTACK(STACK_4); pushSTACK(STACK_(2+1)); pushSTACK(STACK_(3+2));
        funcall(seq_access_set(STACK_(0+3)),3); # (SEQ-ACCESS-SET sequence pointer item)
        # pointer := (SEQ-UPD sequence pointer) :
        pointer_update(STACK_2,STACK_4,STACK_0);
        # count := (1- count) :
        decrement(STACK_1);
      }
    skipSTACK(4);
    value1 = popSTACK(); mv_count=1; # sequence als Wert
  }

LISPFUN(replace,2,0,norest,key,4,\
        (kw(start1),kw(end1),kw(start2),kw(end2)) )
# (REPLACE sequence1 sequence2 [:start1] [:end1] [:start2] [:end2]),
# CLTL S. 252
  { # Methode (schematisch):
    # Argumente �berpr�fen.
    # Anzahl der zu kopierenden Elemente bestimmen:
    #   count1 := (- end1 start1), count2 := (- end2 start2).
    #   count1 < count2  ->  count := count1, end2 := (+ start2 count).
    #   count1 > count2  ->  count := count2, #| end1 := (+ start1 count) |# .
    # Nun ist (= count #|(- end1 start1)|# (- end2 start2)).
    # Falls sequence1 und sequence2 EQ sind, die Indexbereiche sich
    # �berschneiden (also nicht (or (>= start2 end1) (>= start1 end2)) gilt)
    # und nach oben kopiert werden soll (also (< start2 start1) gilt):
    #   Das Source-St�ck aus sequence2 herauskopieren:
    #   (unless (or #|(>= start2 end1)|# (>= start1 end2) (>= start2 start1))
    #     (psetq sequence2 (subseq sequence2 start2 end2)
    #            start2    0
    #         #| end2      count |#
    #   ) )
    # Dann elementweise kopieren: f�r i=0,1,...
    #   (setf (elt sequence1 (+ start1 i)) (elt sequence2 (+ start2 i))).
    # Stackaufbau: sequence1, sequence2, start1, end1, start2, end2.
    # sequence1 �berpr�fen:
    pushSTACK(get_valid_seq_type(STACK_5));
    # sequence1 �berpr�fen:
    pushSTACK(get_valid_seq_type(STACK_(4+1)));
    # Stackaufbau: sequence1, sequence2, start1, end1, start2, end2,
    #              typdescr1, typdescr2.
    # Defaultwert f�r start1 ist 0:
    start_default_0(STACK_(3+2));
    # Defaultwert f�r end1 ist die L�nge von sequence1:
    end_default_len(STACK_(2+2),STACK_(5+2),STACK_1);
    # Defaultwert f�r start2 ist 0:
    start_default_0(STACK_(1+2));
    # Defaultwert f�r end2 ist die L�nge von sequence2:
    end_default_len(STACK_(0+2),STACK_(4+2),STACK_0);
    # start- und end-Argumente �berpr�fen:
    test_start_end(&O(kwpair_start1),&STACK_(2+2));
    test_start_end(&O(kwpair_start2),&STACK_(0+2));
    # count1 bestimmen:
    STACK_(2+2) = I_I_minus_I(STACK_(2+2),STACK_(3+2)); # (- end1 start1) = count1
    # Stackaufbau: sequence1, sequence2, start1, count1, start2, end2,
    #              typdescr1, typdescr2.
    # count2 bestimmen:
   {var object count2 = I_I_minus_I(STACK_(0+2),STACK_(1+2)); # (- end2 start2)
    # count bestimmen und evtl. end2 herabsetzen:
    if (I_I_comp(STACK_(2+2),count2)<0) # count1 < count2 ?
      { # ja -> count1 ist das Minimum
        STACK_(0+2) = I_I_plus_I(STACK_(1+2),STACK_(2+2)); # end2 := (+ start2 count1)
      }
      else
      { # nein -> count2 ist das Minimum
        STACK_(2+2) = count2; # count := count2
   }  }
    # Stackaufbau: sequence1, sequence2, start1, count, start2, end2,
    #              typdescr1, typdescr2.
    # Falls beide Sequences dieselben sind und die Bereiche sich
    # �berschneiden, muss die Source erst herauskopiert werden:
    if (eq(STACK_(5+2),STACK_(4+2)) # (eq sequence1 sequence2)
        && (I_I_comp(STACK_(1+2),STACK_(3+2))<0) # (< start2 start1)
        && (I_I_comp(STACK_(3+2),STACK_(0+2))<0) # (< start1 end2)
       )
      { # St�ck aus sequence2 herauskopieren:
        pushSTACK(STACK_(4+2)); pushSTACK(STACK_(1+2+1)); pushSTACK(STACK_(0+2+2));
        pushSTACK(STACK_(0+3)); subseq(); # (SUBSEQ sequence2 start2 end2)
        STACK_(4+2) = value1; # =: sequence2
        # Indizes adjustieren:
        STACK_(1+2) = Fixnum_0; # start2 := 0
      }
    # Stackaufbau: sequence1, sequence2, start1, count, start2, dummy,
    #              typdescr1, typdescr2.
    # Argumente f�r copy_seqpart_into auf den Stack legen:
    pushSTACK(STACK_(4+2+0)); pushSTACK(STACK_(0+1));
    pushSTACK(STACK_(5+2+2)); pushSTACK(STACK_(1+3));
    pushSTACK(STACK_(2+2+4));
    # Stackaufbau: sequence1, sequence2, start1, count, start2, dummy,
    #              typdescr1, typdescr2,
    #              sequence2, typdescr2, sequence1, typdescr1, count.
    pushSTACK(STACK_4); pushSTACK(STACK_(1+2+5+1));
    funcall(seq_init_start(STACK_(3+2)),2); # (SEQ-INIT-START sequence2 start2)
    pushSTACK(value1); # =: pointer2
    pushSTACK(STACK_(2+1)); pushSTACK(STACK_(3+2+5+1+1));
    funcall(seq_init_start(STACK_(1+1+2)),2); # (SEQ-INIT-START sequence1 start1)
    pushSTACK(value1); # =: pointer1
    # Stackaufbau: sequence1, sequence2, start1, count, start2, dummy,
    #              typdescr1, typdescr2,
    #              sequence2, typdescr2, sequence1, typdescr1, count,
    #              pointer2, pointer1.
    copy_seqpart_into(); # kopiere von sequence2 nach sequence1
    skipSTACK(5+2+5+2);
    value1 = popSTACK(); mv_count=1; # sequence1 als Wert
  }

# Unterprogramm zum Ausf�hren des Tests :TEST
# up_test(stackptr,x)
# > *(stackptr-5): die Testfunktion
# > *(stackptr+1): das zu vergleichende Item
# > x: Argument
# < ergebnis: TRUE falls der Test erf�llt ist, FALSE sonst
# kann GC ausl�sen
  local boolean up_test (const object* stackptr, object x);
  local boolean up_test(stackptr,x)
    var const object* stackptr;
    var object x;
    { # nach CLTL S. 247 ein (funcall testfun item x) ausf�hren:
      pushSTACK(*(stackptr STACKop 1)); # item
      pushSTACK(x); # x
      funcall(*(stackptr STACKop -5),2);
      if (nullp(value1)) return FALSE; else return TRUE;
    }

# Unterprogramm zum Ausf�hren des Tests :TEST-NOT
# up_test_not(stackptr,x)
# > *(stackptr-6): die Testfunktion
# > *(stackptr+1): das zu vergleichende Item
# > x: Argument
# < ergebnis: TRUE falls der Test erf�llt ist, FALSE sonst
# kann GC ausl�sen
  local boolean up_test_not (const object* stackptr, object x);
  local boolean up_test_not(stackptr,x)
    var const object* stackptr;
    var object x;
    { # nach CLTL S. 247 ein (not (funcall testfun item x)) ausf�hren:
      pushSTACK(*(stackptr STACKop 1)); # item
      pushSTACK(x); # x
      funcall(*(stackptr STACKop -6),2);
      if (nullp(value1)) return TRUE; else return FALSE;
    }

# Unterprogramm zum Ausf�hren des Tests -IF
# up_if(stackptr,x)
# > *(stackptr+1): das Testpr�dikat
# > x: Argument
# < ergebnis: TRUE falls der Test erf�llt ist, FALSE sonst
# kann GC ausl�sen
  local boolean up_if (const object* stackptr, object x);
  local boolean up_if(stackptr,x)
    var const object* stackptr;
    var object x;
    { # nach CLTL S. 247 ein (funcall predicate x) ausf�hren:
      pushSTACK(x); funcall(*(stackptr STACKop 1),1);
      if (nullp(value1)) return FALSE; else return TRUE;
    }

# Unterprogramm zum Ausf�hren des Tests -IF-NOT
# up_if_not(stackptr,x)
# > *(stackptr+1): das Testpr�dikat
# > x: Argument
# < ergebnis: TRUE falls der Test erf�llt ist, FALSE sonst
# kann GC ausl�sen
  local boolean up_if_not (const object* stackptr, object x);
  local boolean up_if_not(stackptr,x)
    var const object* stackptr;
    var object x;
    { # nach CLTL S. 247 ein (not (funcall predicate x)) ausf�hren:
      pushSTACK(x); funcall(*(stackptr STACKop 1),1);
      if (nullp(value1)) return TRUE; else return FALSE;
    }

# UP: �berpr�ft das :COUNT-Argument
# > STACK_1: optionales Argument
# > subr_self: Aufrufer (ein SUBR)
# < STACK_1: korrekter COUNT-Wert: NIL oder ein Integer >=0
  local void test_count_arg (void);
  local void test_count_arg()
    { var object count = STACK_1;
      if (eq(count,unbound))
        { STACK_1 = NIL; } # Defaultwert NIL
        else
        # COUNT-Argument muss NIL oder ein Integer >= 0 sein:
        if (!(nullp(count) || (integerp(count) && positivep(count))))
          { fehler_posint(TheSubr(subr_self)->name,S(Kcount),count); }
    }

# Fehler, wenn beide :TEST, :TEST-NOT - Argumente angegeben wurden.
# fehler_both_tests();
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_both_tests, (void));
  global void fehler_both_tests()
    { pushSTACK(TheSubr(subr_self)->name);
      fehler(error,
             DEUTSCH ? "~: Argumente zu :TEST und :TEST-NOT d�rfen nicht beide angegeben werden." :
             ENGLISH ? "~: Must not specify both arguments to :TEST and :TEST-NOT" :
             FRANCAIS ? "~ : Les arguments pour :TEST et :TEST-NOT ne peuvent �tre sp�cifi�s en m�me temps." :
             ""
            );
    }

# UP: �berpr�ft die :TEST, :TEST-NOT - Argumente
# test_test_args(stackptr)
# > stackptr: Pointer in den STACK
# > *(stackptr-5): :TEST-Argument
# > *(stackptr-6): :TEST-NOT-Argument
# > subr_self: Aufrufer (ein SUBR)
# < *(stackptr-5): verarbeitetes :TEST-Argument
# < *(stackptr-6): verarbeitetes :TEST-NOT-Argument
# < up_fun: Adresse einer Testfunktion, die wie folgt spezifiziert ist:
#       > stackptr: derselbe Pointer in den Stack, *(stackptr+1) = item,
#         *(stackptr-5) = :test-Argument, *(stackptr-6) = :test-not-Argument,
#       > x: Argument
#       < TRUE, falls der Test erf�llt ist, FALSE sonst.
  # up_function sei der Typ der Adresse einer solchen Testfunktion:
  typedef boolean (*up_function) (const object* stackptr, object x);
  local up_function test_test_args (object* stackptr);
  local up_function test_test_args(stackptr)
    var object* stackptr;
    { var object test_arg = *(stackptr STACKop -5);
      if (eq(test_arg,unbound)) { test_arg=NIL; }
      # test_arg ist das :TEST-Argument
     {var object test_not_arg = *(stackptr STACKop -6);
      if (eq(test_not_arg,unbound)) { test_not_arg=NIL; }
      # test_not_arg ist das :TEST-NOT-Argument
      if (nullp(test_not_arg))
        # :TEST-NOT wurde nicht angegeben
        { if (nullp(test_arg))
            *(stackptr STACKop -5) = L(eql); # #'EQL als Default f�r :TEST
          return(&up_test);
        }
        # :TEST-NOT wurde angegeben
        { if (nullp(test_arg))
            return(&up_test_not);
          else
            fehler_both_tests();
    }}  }

# UP: bereitet eine Sequence-Operation mit Test vor.
# > Stackaufbau:
#     ... sequence [stackptr] from-end start end key ... [STACK]
#   genauer:
#     ... item sequence [stackptr] from-end start end key test test-not ... [STACK]
#     oder
#     ... test sequence [stackptr] from-end start end key ... [STACK]
#     oder
#     ... test-not sequence [stackptr] from-end start end key ... [STACK]
# > stackptr: Pointer in den Stack
# > subr_self: Aufrufer (ein SUBR)
# < STACK: wird um 1 erniedrigt
# < STACK_0: typdescr zu sequence
  local void seq_prepare_testop (object* stackptr);
  local void seq_prepare_testop(stackptr)
    var object* stackptr;
    { # sequence �berpr�fen, typdescr auf den Stack:
      pushSTACK(get_valid_seq_type(*(stackptr STACKop 0)));
      # key �berpr�fen:
      test_key_arg(stackptr);
      # Defaultwert f�r from-end ist NIL:
      default_NIL(*(stackptr STACKop -1));
      # Defaultwert f�r start ist 0:
      start_default_0(*(stackptr STACKop -2));
      # Defaultwert f�r end ist NIL:
      default_NIL(*(stackptr STACKop -3));
      # start und end �berpr�fen:
      test_start_end_1(&O(kwpair_start),&*(stackptr STACKop -3));
    }

# UP: f�hrt eine Sequence-Filter-Operation aus.
# Eine Sequence wird durchlaufen und dabei in einem Bit-Vektor abgespeichert,
# welche Elemente dem Test gen�gen. Dann wird eine Routine aufgerufen, die
# den Rest erledigt.
# > Stackaufbau:
#     ... sequence [stackptr] from-end start end key ... count typdescr [STACK]
# > stackptr: Pointer in den Stack
# > up_fun: Adresse einer Testfunktion, die wie folgt spezifiziert ist:
#           > stackptr: derselbe Pointer in den Stack,
#           > x: Argument
#           < TRUE, falls der Test erf�llt ist, FALSE sonst.
# > help_fun: Adresse einer Hilfsroutine, die den Rest erledigt.
#   Spezifiziert durch:
#       > stackptr: Pointer in den Stack,
#         *(stackptr+0)=sequence, *(stackptr-2)=start, *(stackptr-3)=end,
#       > STACK_2: typdescr,
#       > STACK_1: L�nge l der Sequence,
#       > STACK_0: Bit-Vektor bv,
#       > bvl: L�nge des Bit-Vektors (= end - start),
#       > dl: Anzahl der im Bit-Vektor gesetzten Bits,
#       < ergebnis: Ergebnis
# > subr_self: Aufrufer (ein SUBR)
# < mv_space/mv_count: Werte
# kann GC ausl�sen
  # help_function sei der Typ der Adresse einer solchen Hilfsfunktion:
  typedef object (*help_function) (object* stackptr, uintL bvl, uintL dl);
  local Values seq_filterop (object* stackptr, up_function up_fun, help_function help_fun);
  local Values seq_filterop(stackptr,up_fun,help_fun)
    var object* stackptr;
    var up_function up_fun;
    var help_function help_fun;
    { # COUNT-Argument muss NIL oder ein Integer >= 0 sein:
      test_count_arg();
     {var object old_subr_self = subr_self; # aktuelles SUBR, nicht GC-gef�hrdet!
      # l = (SEQ-LENGTH sequence) bestimmen:
      pushSTACK(*(stackptr STACKop 0)); # sequence
      funcall(seq_length(STACK_(0+1)),1); # (SEQ-LENGTH sequence)
      pushSTACK(value1); # l in den Stack
      subr_self = old_subr_self;
     }
      # Defaultwert f�r END ist l:
      if (nullp(*(stackptr STACKop -3))) # end=NIL ?
        { *(stackptr STACKop -3) = STACK_0; # ja -> end:=l
          # Dann nochmals start und end �berpr�fen:
          test_start_end(&O(kwpair_start),&*(stackptr STACKop -3));
        }
      # Nun sind alle Argumente �berpr�ft.
      pushSTACK(*(stackptr STACKop 0)); # sequence
      pushSTACK(*(stackptr STACKop -4)); # key
      # (- end start) bestimmen und neuen Bitvektor allozieren:
     {var uintL bvl; # Bitvektor-L�nge
      var uintL dl = 0; # Anzahl der im Bitvektor gesetzten Bits
      { var object bvsize = I_I_minus_I(*(stackptr STACKop -3),*(stackptr STACKop -2));
        # bvsize = (- end start), ein Integer >=0
        if (!(posfixnump(bvsize))) # Fixnum?
          { pushSTACK(*(stackptr STACKop 0)); # sequence
            pushSTACK(TheSubr(subr_self)->name);
            fehler(error,
                   DEUTSCH ? "~: Zu lange Sequence: ~" :
                   ENGLISH ? "~: sequence ~ is too long" :
                   FRANCAIS ? "~ : S�quence trop longue: ~" :
                   ""
                  );
          }
        bvl = posfixnum_to_L(bvsize); # L�nge des Bitvektors als Longword
      }
      pushSTACK(allocate_bit_vector_0(bvl)); # neuer Bitvektor bv
      # Stackaufbau: ... count, typdescr,
      #              l, sequence, key, bv [STACK].
      if (!(nullp(*(stackptr STACKop -1)))) # from-end abfragen
        # from-end ist angegeben
        { pushSTACK(STACK_2); # sequence
          pushSTACK(*(stackptr STACKop -3)); # end
          funcall(seq_fe_init_end(STACK_(0+4+2)),2); # (SEQ-FE-INIT-END sequence end)
          pushSTACK(value1); # =: pointer
          pushSTACK(STACK_(1+4+1)); # countdown := count
          # Stackaufbau: ... count, typdescr,
          #              l, sequence, key, bv,
          #              pointer, countdown [STACK].
         {var uintL bvi = bvl; # Schleife bvl mal durchlaufen
          until (bvi==0)
            { bvi--;
              if (!(nullp(STACK_(1+4+2))) && eq(STACK_0,Fixnum_0))
                # count/=NIL und countdown=0 -> Schleife kann abgebrochen werden
                break;
              # n�chstes Element abtesten:
              pushSTACK(STACK_(2+2)); # sequence
              pushSTACK(STACK_(1+1)); # pointer
              funcall(seq_access(STACK_(0+4+2+2)),2); # (SEQ-ACCESS sequence pointer)
              funcall_key(STACK_(1+2)); # (FUNCALL key ...)
              if ((*up_fun)(stackptr,value1)) # Testroutine aufrufen
                # Test erf�llt
                { sbvector_bset(STACK_(0+2),bvi); # (setf (sbit bv bvi) 1)
                  dl++; # dl := dl+1, ein gesetztes Bit mehr
                  if (!(nullp(STACK_(1+4+2)))) # falls count/=NIL:
                    { decrement(STACK_0); } # (decf countdown)
                }
              # pointer weiterr�cken:
              pointer_fe_update(STACK_1,STACK_(2+2),STACK_(0+4+2));
        }}  }
        else
        # from-end ist nicht angegeben
        { pushSTACK(STACK_2); # sequence
          pushSTACK(*(stackptr STACKop -2)); # start
          funcall(seq_init_start(STACK_(0+4+2)),2); # (SEQ-INIT-START sequence start)
          pushSTACK(value1); # =: pointer
          pushSTACK(STACK_(1+4+1)); # countdown := count
          # Stackaufbau: ... count, typdescr,
          #              l, sequence, key, bv,
          #              pointer, countdown [STACK].
         {var uintL bvi = 0; # Schleife bvl mal durchlaufen
          until (bvi==bvl)
            { if (!(nullp(STACK_(1+4+2))) && eq(STACK_0,Fixnum_0))
                # count/=NIL und countdown=0 -> Schleife kann abgebrochen werden
                break;
              # n�chstes Element abtesten:
              pushSTACK(STACK_(2+2)); # sequence
              pushSTACK(STACK_(1+1)); # pointer
              funcall(seq_access(STACK_(0+4+2+2)),2); # (SEQ-ACCESS sequence pointer)
              funcall_key(STACK_(1+2)); # (FUNCALL key ...)
              if ((*up_fun)(stackptr,value1)) # Testroutine aufrufen
                # Test erf�llt
                { sbvector_bset(STACK_(0+2),bvi); # (setf (sbit bv bvi) 1)
                  dl++; # dl := dl+1, ein gesetztes Bit mehr
                  if (!(nullp(STACK_(1+4+2)))) # falls count/=NIL:
                    { decrement(STACK_0); } # (decf countdown)
                }
              # pointer weiterr�cken:
              pointer_update(STACK_1,STACK_(2+2),STACK_(0+4+2));
              bvi++;
        }}  }
      skipSTACK(2); # pointer und countdown vergessen
      # Stackaufbau: ... count, typdescr,
      #              l, sequence, key, bv [STACK].
      STACK_2 = STACK_0; skipSTACK(2); # bv hochschieben
      # Stackaufbau: ... count, typdescr, l, bv [STACK].
      value1 = (*help_fun)(stackptr,bvl,dl); # Rest durchf�hren
      mv_count=1; # Ergebnis als Wert
      skipSTACK(2); # l und bv vergessen
    }}

# UP: Hilfsroutine f�r REMOVE-Funktionen.
# Bildet zu einer Sequence eine neue Sequence, in der genau die Elemente
# fehlen, die in einem Bitvektor markiert sind.
# > stackptr: Pointer in den Stack,
#   *(stackptr+0)=sequence, *(stackptr-2)=start, *(stackptr-3)=end,
# > STACK_2: typdescr,
# > STACK_1: L�nge l der Sequence,
# > STACK_0: Bit-Vektor bv,
# > bvl: L�nge des Bit-Vektors (= end - start),
# > dl: Anzahl der im Bit-Vektor gesetzten Bits,
# < ergebnis: Ergebnis
# kann GC ausl�sen
  local object remove_help (object* stackptr, uintL bvl, uintL dl);
  local object remove_help(stackptr,bvl,dl)
    var object* stackptr;
    var uintL bvl;
    var uintL dl;
    { # dl=0 -> sequence unver�ndert zur�ckgeben:
      if (dl==0) { return *(stackptr STACKop 0); }
      # neue Sequence allozieren:
      pushSTACK(I_I_minus_I(STACK_1,fixnum(dl))); # (- l dl)
      funcall(seq_make(STACK_(2+1)),1); # (SEQ-MAKE (- l dl))
      pushSTACK(value1);
      # Stackaufbau: typdescr, l, bv, sequence2.
      pushSTACK(*(stackptr STACKop 0)); # sequence
      pushSTACK(STACK_(3+1)); # typdescr
      pushSTACK(STACK_(0+2)); # sequence2
      pushSTACK(STACK_(3+3)); # typdescr
      pushSTACK(*(stackptr STACKop -2)); # start
      # Stackaufbau: typdescr, l, bv, sequence2,
      #              seq1, typdescr1, seq2, typdescr2, start.
      pushSTACK(STACK_4); funcall(seq_init(STACK_(3+1)),1); # (SEQ-INIT sequence)
      pushSTACK(value1); # =: pointer1
      pushSTACK(STACK_(2+1)); funcall(seq_init(STACK_(1+1+1)),1); # (SEQ-INIT sequence2)
      pushSTACK(value1); # =: pointer2
      # Stackaufbau: typdescr, l, bv, sequence2,
      #              seq1, typdescr1, seq2, typdescr2, start,
      #              pointer1, pointer2.
      { # Vorderes Teilst�ck:
        # Elemente mit Index <start von sequence1 nach sequence2
        # unver�ndert �bertragen:
        copy_seqpart_into();
      }
      { # Mittleres Teilst�ck: sieben.
        var uintL bvi = 0;
        until (bvi==bvl)
          { if (!(sbvector_btst(STACK_(1+5+2),bvi))) # (sbit bv bvi) abfragen
              # Bit ist nicht gesetzt, also Element �bernehmen
              { pushSTACK(STACK_(4+2)); pushSTACK(STACK_(1+1));
                funcall(seq_access(STACK_(3+2+2)),2); # (SEQ-ACCESS seq1 pointer1)
                pushSTACK(STACK_(2+2)); pushSTACK(STACK_(0+1)); pushSTACK(value1);
                funcall(seq_access_set(STACK_(1+2+3)),3); # (SEQ-ACCESS-SET seq2 pointer2 ...)
                # pointer2 := (SEQ-UPD seq2 pointer2) :
                pointer_update(STACK_0,STACK_(2+2),STACK_(1+2));
              }
            # pointer1 := (SEQ-UPD seq1 pointer1) :
            pointer_update(STACK_1,STACK_(4+2),STACK_(3+2));
            bvi++;
      }   }
      { # Hinteres Teilst�ck:
        # Elemente mit Index >=end von sequence1 nach sequence2
        # unver�ndert �bertragen:
        STACK_(0+2) = I_I_minus_I(STACK_(2+5+2),*(stackptr STACKop -3)); # (- l end)
        copy_seqpart_into();
      }
      skipSTACK(5+2);
      return popSTACK(); # sequence2 als Ergebnis
    }

# UP: Hilfsroutine f�r DELETE-Funktionen.
# Entfernt aus einer Sequence genau die Elemente, die in einem Bitvektor
# markiert sind.
# > stackptr: Pointer in den Stack,
#   *(stackptr+0)=sequence, *(stackptr-2)=start, *(stackptr-3)=end,
# > STACK_2: typdescr,
# > STACK_1: L�nge l der Sequence,
# > STACK_0: Bit-Vektor bv,
# > bvl: L�nge des Bit-Vektors (= end - start),
# > dl: Anzahl der im Bit-Vektor gesetzten Bits,
# < ergebnis: Ergebnis
# kann GC ausl�sen
  local object delete_help (object* stackptr, uintL bvl, uintL dl);
  local object delete_help(stackptr,bvl,dl)
    var object* stackptr;
    var uintL bvl;
    var uintL dl;
    { # dl=0 -> sequence unver�ndert zur�ckgeben:
      if (dl==0) { return *(stackptr STACKop 0); }
     {var object type = seq_type(STACK_2);
      if (eq(type,S(list))) # Typ LIST ?
        { # Noch �berpr�fen, ob sequence wirklich eine Liste ist.
          # Wegen l >= dl > 0 ist zu testen, ob sequence ein Cons ist.
          if (mconsp(*(stackptr STACKop 0)))
            { # Listen speziell behandeln:
              var object whole_list = *(stackptr STACKop 0); # ganze Liste
              var object* list_ = &whole_list;
              var object list = *list_;
              # Stets list = *list_.
              # Vorderes Teilst�ck:
              # start mal mit list:=Cdr(list) weiterr�cken:
              { var uintL count;
                dotimesL(count,posfixnum_to_L(*(stackptr STACKop -2)),
                  { list_ = &Cdr(list); list = *list_; });
              }
              # Mittleres Teilst�ck:
              # bvl mal ein Bit abfragen und evtl. ein Cons streichen:
              { var uintL bvi = 0;
                until (bvi==bvl)
                  { if (sbvector_btst(STACK_0,bvi)) # (sbit bv bvi) abfragen
                      # Bit ist =1 -> Cons bei list herausnehmen:
                      { *list_ = list = Cdr(list); }
                      else
                      # Bit ist =0 -> nur weiterr�cken:
                      { list_ = &Cdr(list); list = *list_; }
                    bvi++;
              }   }
              return whole_list; # modifizierte Liste als Ergebnis
            }
            else
            goto other;
        }
      elif (eq(type,S(vector)) || eq(type,S(string)) || eq(type,S(bit_vector)) || posfixnump(type))
        # Typ [GENERAL-]VECTOR, STRING, BIT-VECTOR, Byte-VECTOR
        { # Noch �berpr�fen, ob sequence wirklich ein Vektor ist.
          var object sequence = *(stackptr STACKop 0);
          if (!(vectorp(sequence))) { goto other; }
          # Bei Arrays ohne Fill-Pointer kann man nichts Spezielles machen:
          if (!(array_has_fill_pointer_p(sequence))) { goto other; }
          # sequence ist ein Vektor mit Fill-Pointer.
          # Elemente zusammenschieben und dann Fill-Pointer herabsetzen:
          pushSTACK(sequence); # sequence
          pushSTACK(*(stackptr STACKop -2)); # i := start
          pushSTACK(STACK_0); # j := i
          # Stackaufbau: typdescr, l, bv, sequence, i, j.
          # j = Source-Index, i = Destination-Index, start <= i <= j .
          # Mittleres Teilst�ck:
          { var uintL bvi = 0;
            until (bvi==bvl)
              { if (!(sbvector_btst(STACK_3,bvi))) # (sbit bv bvi) abfragen
                  # Bit gel�scht -> Element �bertragen:
                  { # (setf (aref sequence i) (aref sequence j)) :
                    pushSTACK(STACK_2); pushSTACK(STACK_(0+1));
                    funcall(L(aref),2); # (AREF sequence j)
                    pushSTACK(STACK_2); pushSTACK(STACK_(1+1)); pushSTACK(value1);
                    funcall(L(store),3); # (SYS::STORE sequence i ...)
                    # i:=i+1 :
                    STACK_1 = fixnum_inc(STACK_1,1);
                  }
                # j:=j+1 :
                STACK_0 = fixnum_inc(STACK_0,1);
                bvi++;
          }   }
          # Hinteres Teilst�ck:
          { until (eq(STACK_0,STACK_4)) # solange bis j = l (beides Fixnums)
              # Element �bertragen:
              { # (setf (aref sequence i) (aref sequence j)) :
                pushSTACK(STACK_2); pushSTACK(STACK_(0+1));
                funcall(L(aref),2); # (AREF sequence j)
                pushSTACK(STACK_2); pushSTACK(STACK_(1+1)); pushSTACK(value1);
                funcall(L(store),3); # (SYS::STORE sequence i ...)
                # i:=i+1 :
                STACK_1 = fixnum_inc(STACK_1,1);
                # j:=j+1 :
                STACK_0 = fixnum_inc(STACK_0,1);
          }   }
          skipSTACK(1);
          # Stackaufbau: typdescr, l, bv, sequence, i.
          # (setf (fill-pointer sequence) i) :
          funcall(L(set_fill_pointer),2); # (SYS::SET-FILL-POINTER sequence i)
          # Stackaufbau: typdescr, l, bv.
          return *(stackptr STACKop 0); # sequence mit modifiziertem Fill-Pointer
        }
      other: # sonstige Sequences
        return remove_help(stackptr,bvl,dl); # DELETE wie REMOVE behandeln
    }}

LISPFUN(remove,2,0,norest,key,7,\
        (kw(from_end),kw(start),kw(end),kw(key),kw(test),kw(test_not),kw(count)) )
# (REMOVE item sequence [:from-end] [:start] [:end] [:key] [:test] [:test-not] [:count]),
# CLTL S. 253
  { var object* stackptr = &STACK_7;
    var up_function up_fun = test_test_args(stackptr); # Testfunktion
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    seq_filterop(stackptr,up_fun,&remove_help); # Filtern
    skipSTACK(2+7+1);
  }

LISPFUN(remove_if,2,0,norest,key,5,\
        (kw(from_end),kw(start),kw(end),kw(key),kw(count)) )
# (REMOVE-IF test sequence [:from-end] [:start] [:end] [:key] [:count]),
# CLTL S. 253
  { var object* stackptr = &STACK_5;
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    seq_filterop(stackptr,&up_if,&remove_help); # Filtern
    skipSTACK(2+5+1);
  }

LISPFUN(remove_if_not,2,0,norest,key,5,\
        (kw(from_end),kw(start),kw(end),kw(key),kw(count)) )
# (REMOVE-IF-NOT test sequence [:from-end] [:start] [:end] [:key] [:count]),
# CLTL S. 253
  { var object* stackptr = &STACK_5;
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    seq_filterop(stackptr,&up_if_not,&remove_help); # Filtern
    skipSTACK(2+5+1);
  }

LISPFUN(delete,2,0,norest,key,7,\
        (kw(from_end),kw(start),kw(end),kw(key),kw(test),kw(test_not),kw(count)) )
# (DELETE item sequence [:from-end] [:start] [:end] [:key] [:test] [:test-not] [:count]),
# CLTL S. 254
  { var object* stackptr = &STACK_7;
    var up_function up_fun = test_test_args(stackptr); # Testfunktion
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    seq_filterop(stackptr,up_fun,&delete_help); # Filtern
    skipSTACK(2+7+1);
  }

LISPFUN(delete_if,2,0,norest,key,5,\
        (kw(from_end),kw(start),kw(end),kw(key),kw(count)) )
# (DELETE-IF test sequence [:from-end] [:start] [:end] [:key] [:count]),
# CLTL S. 254
  { var object* stackptr = &STACK_5;
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    seq_filterop(stackptr,&up_if,&delete_help); # Filtern
    skipSTACK(2+5+1);
  }

LISPFUN(delete_if_not,2,0,norest,key,5,\
        (kw(from_end),kw(start),kw(end),kw(key),kw(count)) )
# (DELETE-IF-NOT test sequence [:from-end] [:start] [:end] [:key] [:count]),
# CLTL S. 254
  { var object* stackptr = &STACK_5;
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    seq_filterop(stackptr,&up_if_not,&delete_help); # Filtern
    skipSTACK(2+5+1);
  }

# Unterprogramm zum Ausf�hren des Tests :TEST
# up2_test(stackptr,x,y)
# > *(stackptr-5): die Testfunktion
# > x,y: Argumente
# < ergebnis: TRUE falls der Test erf�llt ist, FALSE sonst
# kann GC ausl�sen
  local boolean up2_test (const object* stackptr, object x, object y);
  local boolean up2_test(stackptr,x,y)
    var const object* stackptr;
    var object x;
    var object y;
    { # ein (funcall testfun x y) ausf�hren:
      pushSTACK(x); # x
      pushSTACK(y); # y
      funcall(*(stackptr STACKop -5),2);
      if (nullp(value1)) return FALSE; else return TRUE;
    }

# Unterprogramm zum Ausf�hren des Tests :TEST-NOT
# up2_test_not(stackptr,x,y)
# > *(stackptr-6): die Testfunktion
# > x,y: Argumente
# < ergebnis: TRUE falls der Test erf�llt ist, FALSE sonst
# kann GC ausl�sen
  local boolean up2_test_not (const object* stackptr, object x, object y);
  local boolean up2_test_not(stackptr,x,y)
    var const object* stackptr;
    var object x;
    var object y;
    { # ein (not (funcall testfun x y)) ausf�hren:
      pushSTACK(x); # x
      pushSTACK(y); # y
      funcall(*(stackptr STACKop -6),2);
      if (nullp(value1)) return TRUE; else return FALSE;
    }

# UP: �berpr�ft die :TEST, :TEST-NOT - Argumente
# test_test2_args(stackptr)
# > stackptr: Pointer in den STACK
# > *(stackptr-5): :TEST-Argument
# > *(stackptr-6): :TEST-NOT-Argument
# > subr_self: Aufrufer (ein SUBR)
# < *(stackptr-5): verarbeitetes :TEST-Argument
# < *(stackptr-6): verarbeitetes :TEST-NOT-Argument
# < up2_fun: Adresse einer Testfunktion, die wie folgt spezifiziert ist:
#       > stackptr: derselbe Pointer in den Stack,
#         *(stackptr-5) = :test-Argument, *(stackptr-6) = :test-not-Argument,
#       > x,y: Argumente
#       < TRUE, falls der Test erf�llt ist, FALSE sonst.
  # up2_function sei der Typ der Adresse einer solchen Testfunktion:
  typedef boolean (*up2_function) (const object* stackptr, object x, object y);
  local up2_function test_test2_args (object* stackptr);
  local up2_function test_test2_args(stackptr)
    var object* stackptr;
    { var object test_arg = *(stackptr STACKop -5);
      if (eq(test_arg,unbound)) { test_arg=NIL; }
      # test_arg ist das :TEST-Argument
     {var object test_not_arg = *(stackptr STACKop -6);
      if (eq(test_not_arg,unbound)) { test_not_arg=NIL; }
      # test_not_arg ist das :TEST-NOT-Argument
      if (nullp(test_not_arg))
        # :TEST-NOT wurde nicht angegeben
        { if (nullp(test_arg))
            *(stackptr STACKop -5) = L(eql); # #'EQL als Default f�r :TEST
          return(&up2_test);
        }
        # :TEST-NOT wurde angegeben
        { if (nullp(test_arg))
            return(&up2_test_not);
          else
            fehler_both_tests();
    }}  }

# UP: f�hrt eine Sequence-Duplicates-Operation aus.
# seq_duplicates(help_fun)
# Eine Sequence wird durchlaufen und dabei in einem Bit-Vektor abgespeichert,
# welche Elemente doppelt vorkommen. Dann wird eine Routine aufgerufen, die
# den Rest erledigt.
# > Stackaufbau:
#     sequence from-end start end key test test-not [STACK]
# > help_fun: Adresse einer Hilfsroutine, die den Rest erledigt.
#     Spezifiziert durch:
#       > stackptr: Pointer in den Stack,
#         *(stackptr+0)=sequence, *(stackptr-2)=start, *(stackptr-3)=end,
#       > STACK_2: typdescr,
#       > STACK_1: L�nge der Sequence,
#       > STACK_0: Bit-Vektor bv,
#       > bvl: L�nge des Bit-Vektors (= end - start),
#       > dl: Anzahl der im Bit-Vektor gesetzten Bits,
#       < ergebnis: Ergebnis
#       kann GC ausl�sen
# > subr_self: Aufrufer (ein SUBR)
# < mv_space/mv_count: Werte
# kann GC ausl�sen
  local Values seq_duplicates (help_function help_fun);
  local Values seq_duplicates(help_fun)
    var help_function help_fun;
    { var object* stackptr = &STACK_6;
      # Stackaufbau:
      #   sequence [stackptr], from-end, start, end, key, test, test-not.
      # sequence �berpr�fen:
      { var object sequence = *(stackptr STACKop 0);
        pushSTACK(get_valid_seq_type(sequence)); # typdescr auf den Stack
      }
      # Stackaufbau:
      #   sequence [stackptr], from-end, start, end, key, test, test-not,
      #   typdescr.
      # :test und :test-not �berpr�fen:
     {var up2_function up2_fun = test_test2_args(stackptr);
      # key �berpr�fen:
      test_key_arg(stackptr);
      # Defaultwert f�r from-end ist NIL:
      default_NIL(*(stackptr STACKop -1));
      # Defaultwert f�r start ist 0:
      start_default_0(*(stackptr STACKop -2));
      # Defaultwert f�r end ist nil:
      default_NIL(*(stackptr STACKop -3));
      # start und end �berpr�fen:
      test_start_end_1(&O(kwpair_start),&*(stackptr STACKop -3));
      # L�nge der Sequence bestimmen:
      { var object old_subr_self = subr_self; # aktuelles SUBR, nicht GC-gef�hrdet!
        pushSTACK(STACK_(6+1)); # sequence
        funcall(seq_length(STACK_(0+1)),1); # (SEQ-LENGTH sequence)
        pushSTACK(value1); # l
        subr_self = old_subr_self;
      }
      # Stackaufbau:
      #   sequence [stackptr], from-end, start, end, key, test, test-not,
      #   typdescr, l.
      # Defaultwert f�r end ist l = (length sequence):
      if (nullp(*(stackptr STACKop -3)))
        { *(stackptr STACKop -3) = STACK_0; # end := l
          # Dann nochmals start und end �berpr�fen:
          test_start_end(&O(kwpair_start),&*(stackptr STACKop -3));
        }
      # Nun sind alle Argumente �berpr�ft.
      { var uintL bvl; # Bitvektor-L�nge
        var uintL dl; # Anzahl der im Bitvektor gesetzten Bits
        # (- end start) bestimmen und neuen Bitvektor allozieren:
        { var object size = I_I_minus_I(STACK_(3+2),STACK_(4+2));
          # size = (- end start), ein Integer >=0
          if (!(posfixnump(size)))
            { pushSTACK(*(stackptr STACKop 0)); # sequence
              fehler(error,
                     DEUTSCH ? "Zu lange Sequence: ~" :
                     ENGLISH ? "too long sequence ~" :
                     FRANCAIS ? "S�quence trop longue : ~" :
                     ""
                    );
            }
          bvl = posfixnum_to_L(size);
        }
        pushSTACK(allocate_bit_vector_0(bvl));
        # Stackaufbau:
        #   sequence [stackptr], from-end, start, end, key, test, test-not,
        #   typdescr, l, bv.
        dl = 0; # dl := 0
        # Bei :test #'eq/eql/equal und gro�er L�nge verwende Hashtabelle:
        if (bvl < 10) goto standard;
        if (!(up2_fun == &up2_test)) goto standard;
        { var object test = STACK_(1+3);
          if (!(eq(test,L(eq)) || eq(test,L(eql)) || eq(test,L(equal))
                || eq(test,S(eq)) || eq(test,S(eql)) || eq(test,S(equal))
             ) )
            goto standard;
        }
        if (FALSE)
          standard: # Standardmethode
          { if (!(nullp(STACK_(5+3)))) # from-end abfragen
              # from-end ist angegeben
              {{pushSTACK(STACK_(6+3)); # sequence
                pushSTACK(STACK_(4+3+1)); # start
                funcall(seq_init_start(STACK_(2+2)),2); # (SEQ-INIT-START sequence start)
                pushSTACK(value1); # =: pointer1
               }
               # Stackaufbau:
               #   sequence [stackptr], from-end, start, end, key, test, test-not,
               #   typdescr, l, bv,
               #   pointer1.
               # pointer1 l�uft von links nach rechts (von start bis end).
               {var uintL bvi1 = 0; # Schleife bvl mal durchlaufen
                until (bvi1==bvl)
                  { if (!(sbvector_btst(STACK_(0+1),bvi1))) # (sbit bv bvi1) abfragen
                      # falls Bit=0: dieses Element ist noch nicht gestrichen ->
                      # teste, ob es weiter rechts vorkommt:
                      {{pushSTACK(STACK_(6+3+1)); # sequence
                        pushSTACK(STACK_(0+1)); # pointer1
                        funcall(seq_access(STACK_(2+1+2)),2); # (SEQ-ACCESS sequence pointer1)
                        funcall_key(STACK_(2+3+1)); # (FUNCALL key (SEQ-ACCESS sequence pointer1))
                        pushSTACK(value1); # =: item1
                       }
                        # Stackaufbau:
                        #   sequence [stackptr], from-end, start, end, key, test, test-not,
                        #   typdescr, l, bv,
                        #   pointer1, item1.
                        # pointer1 := (SEQ-UPD sequence pointer1) :
                        pointer_update(STACK_1,STACK_(6+3+2),STACK_(2+2));
                        # pointer2 := (SEQ-COPY pointer1) :
                       {pushSTACK(STACK_1); funcall(seq_copy(STACK_(2+2+1)),1); # (SEQ-COPY pointer1)
                        pushSTACK(value1); # =: pointer2
                       }
                        # Stackaufbau:
                        #   sequence [stackptr], from-end, start, end, key, test, test-not,
                        #   typdescr, l, bv,
                        #   pointer1, item1, pointer2.
                        # pointer2 l�uft von pointer1 nach rechts.
                       {var uintL bvi2 = bvi1+1; # bvi2 := bvi1+1
                        until (bvi2==bvl)
                          { if (!(sbvector_btst(STACK_(0+3),bvi2))) # (sbit bv bvi2) abfragen
                              # falls Bit=0: dieses Element ist auch noch nicht gestrichen.
                              # vergleiche beide Elemente:
                              { pushSTACK(STACK_(6+3+3)); # sequence
                                pushSTACK(STACK_(0+1)); # pointer2
                                funcall(seq_access(STACK_(2+3+2)),2); # (SEQ-ACCESS sequence pointer2)
                                funcall_key(STACK_(2+3+3)); # (FUNCALL key (SEQ-ACCESS sequence pointer2))
                                # value1 =: item2
                                # item1 und item2 vergleichen:
                                if ((*up2_fun)(stackptr,STACK_1,value1)) # Testroutine aufrufen
                                  # Test erf�llt -> vermerke, dass item2 zu streichen ist:
                                  { sbvector_bset(STACK_(0+3),bvi2); # (setf (sbit bv bvi2) 1)
                                    dl = dl+1; # dl:=dl+1
                                  }
                              }
                            # pointer2 := (SEQ-UPD sequence pointer2) :
                            pointer_update(STACK_0,STACK_(6+3+3),STACK_(2+3));
                            bvi2++; # bvi2 := bvi2+1
                       }  }
                        skipSTACK(2); # item1 und pointer2 vergessen
                      }
                      else
                      # falls Bit=1: dieses Element einfach �bergehen
                      { # pointer1 := (SEQ-UPD sequence pointer1) :
                        pointer_update(STACK_0,STACK_(6+3+1),STACK_(2+1));
                      }
                    bvi1++;
               }  }
                skipSTACK(1); # pointer1 vergessen
              }
              else
              # from-end ist nicht angegeben
              {{pushSTACK(STACK_(6+3)); # sequence
                pushSTACK(STACK_(4+3+1)); # start
                funcall(seq_init_start(STACK_(2+2)),2); # (SEQ-INIT-START sequence start)
                pushSTACK(value1); # =: pointer0
               }
               # Stackaufbau:
               #   sequence [stackptr], from-end, start, end, key, test, test-not,
               #   typdescr, l, bv,
               #   pointer0.
               # pointer0 steht links.
               {pushSTACK(STACK_0); funcall(seq_copy(STACK_(2+1+1)),1); # (SEQ-COPY pointer0)
                pushSTACK(value1); # =: pointer2
               }
               # Stackaufbau:
               #   sequence [stackptr], from-end, start, end, key, test, test-not,
               #   typdescr, l, bv,
               #   pointer0, pointer2.
               # pointer2 l�uft von links nach rechts (von start bis end).
               {var uintL bvi2 = 0; # Schleife bvl mal durchlaufen
                until (bvi2==bvl)
                  { if (!(sbvector_btst(STACK_(0+2),bvi2))) # (sbit bv bvi2) abfragen
                      # falls Bit=0: dieses Element ist noch nicht gestrichen ->
                      # teste, ob es weiter links vorkommt:
                      {{pushSTACK(STACK_(6+3+2)); # sequence
                        pushSTACK(STACK_(0+1)); # pointer2
                        funcall(seq_access(STACK_(2+2+2)),2); # (SEQ-ACCESS sequence pointer2)
                        funcall_key(STACK_(2+3+2)); # (FUNCALL key (SEQ-ACCESS sequence pointer1))
                        pushSTACK(value1); # =: item2
                       }
                        # Stackaufbau:
                        #   sequence [stackptr], from-end, start, end, key, test, test-not,
                        #   typdescr, l, bv,
                        #   pointer0, pointer2, item2.
                        # pointer1 := (SEQ-COPY pointer0) :
                       {pushSTACK(STACK_2); funcall(seq_copy(STACK_(2+3+1)),1); # (SEQ-COPY pointer0)
                        pushSTACK(value1); # =: pointer1
                       }
                        # Stackaufbau:
                        #   sequence [stackptr], from-end, start, end, key, test, test-not,
                        #   typdescr, l, bv,
                        #   pointer0, pointer2, item2, pointer1.
                        # pointer1 l�uft von links bis pointer2.
                       {var uintL bvi1 = 0; # bvi1 := 0
                        until (bvi1==bvi2)
                          { if (!(sbvector_btst(STACK_(0+4),bvi1))) # (sbit bv bvi1) abfragen
                              # falls Bit=0: dieses Element ist auch noch nicht gestrichen.
                              # vergleiche beide Elemente:
                              { pushSTACK(STACK_(6+3+4)); # sequence
                                pushSTACK(STACK_(0+1)); # pointer1
                                funcall(seq_access(STACK_(2+4+2)),2); # (SEQ-ACCESS sequence pointer1)
                                funcall_key(STACK_(2+3+4)); # (FUNCALL key (SEQ-ACCESS sequence pointer1))
                                # value1 =: item1
                                # item1 und item2 vergleichen:
                                if ((*up2_fun)(stackptr,value1,STACK_1)) # Testroutine aufrufen
                                  # Test erf�llt -> vermerke, dass item1 zu streichen ist:
                                  { sbvector_bset(STACK_(0+4),bvi1); # (setf (sbit bv bvi1) 1)
                                    dl = dl+1; # dl:=dl+1
                                  }
                              }
                            # pointer1 := (SEQ-UPD sequence pointer1) :
                            pointer_update(STACK_0,STACK_(6+3+4),STACK_(2+4));
                            bvi1++; # bvi1 := bvi1+1
                       }  }
                        skipSTACK(2); # item2 und pointer1 vergessen
                      }
                    # falls Bit=1: dieses Element einfach �bergehen
                    # pointer2 := (SEQ-UPD sequence pointer2) :
                    pointer_update(STACK_0,STACK_(6+3+2),STACK_(2+2));
                    bvi2++; # bvi2 := bvi2+1
               }  }
                skipSTACK(2); # pointer0 und pointer2 vergessen
              }
          }
          else
          # Methode mit Hash-Tabelle
          { # mit (MAKE-HASH-TABLE :test test) eine leere Hash-Tabelle bauen:
            pushSTACK(S(Ktest)); pushSTACK(STACK_(1+3+1)); funcall(L(make_hash_table),2);
            pushSTACK(value1); # ht retten
            {pushSTACK(STACK_(6+3+1)); # sequence
             pushSTACK(STACK_(4+3+2)); # start
             funcall(seq_init_start(STACK_(2+3)),2); # (SEQ-INIT-START sequence start)
             pushSTACK(value1); # =: pointer
            }
            # Stackaufbau:
            #   sequence [stackptr], from-end, start, end, key, test, test-not,
            #   typdescr, l, bv,
            #   ht, pointer.
            if (!(nullp(STACK_(5+3+2)))) # from-end abfragen
              # from-end ist angegeben
              { # pointer l�uft von links nach rechts (von start bis end).
                var uintL bvi = 0; # Schleife bvl mal durchlaufen
                until (bvi==bvl)
                  {{pushSTACK(STACK_(6+3+2)); # sequence
                    pushSTACK(STACK_(0+1)); # pointer
                    funcall(seq_access(STACK_(2+2+2)),2); # (SEQ-ACCESS sequence pointer)
                    funcall_key(STACK_(2+3+2)); # (FUNCALL key (SEQ-ACCESS sequence pointer))
                   }# item wird in die Tabelle gesteckt; war es schon
                    # drin, wird bei pointer gestrichen.
                   {var object old_value = shifthash(STACK_1,value1,T);
                    if (!nullp(old_value))
                      # item war schon in ht -> wird jetzt gestrichen
                      { sbvector_bset(STACK_(0+2),bvi); # (setf (sbit bv bvi) 1)
                        dl = dl+1; # dl:=dl+1
                   }  }
                    # pointer := (SEQ-UPD sequence pointer) :
                    pointer_update(STACK_0,STACK_(6+3+2),STACK_(2+2));
                    bvi++; # bvi := bvi+1
                  }
              }
              else
              # from-end ist nicht angegeben
              { # pointer l�uft von links nach rechts (von start bis end).
                var uintL bvi = 0; # Schleife bvl mal durchlaufen
                until (bvi==bvl)
                  {{pushSTACK(STACK_(6+3+2)); # sequence
                    pushSTACK(STACK_(0+1)); # pointer
                    funcall(seq_access(STACK_(2+2+2)),2); # (SEQ-ACCESS sequence pointer)
                    funcall_key(STACK_(2+3+2)); # (FUNCALL key (SEQ-ACCESS sequence pointer))
                   }# item wird in die Tabelle gesteckt; war es schon
                    # drin, wird an der vorigen Position gestrichen.
                   {var object old_value =
                      shifthash(STACK_1,value1,fixnum(bvi));
                    if (!nullp(old_value))
                      # item war schon in ht -> wird an der vorigen Position gestrichen
                      { var uintL i = posfixnum_to_L(old_value);
                        sbvector_bset(STACK_(0+2),i); # (setf (sbit bv i) 1)
                        dl = dl+1; # dl:=dl+1
                   }  }
                    # pointer := (SEQ-UPD sequence pointer) :
                    pointer_update(STACK_0,STACK_(6+3+2),STACK_(2+2));
                    bvi++; # bvi := bvi+1
                  }
              }
            skipSTACK(2); # ht und pointer vergessen
          }
        # Stackaufbau:
        #   sequence [stackptr], from-end, start, end, key, test, test-not,
        #   typdescr, l, bv.
        value1 = (*help_fun)(stackptr,bvl,dl); # Rest durchf�hren
        mv_count=1; # Ergebnis als Wert
        skipSTACK(7+3); # STACK aufr�umen
    }}}

LISPFUN(remove_duplicates,1,0,norest,key,6,\
        (kw(from_end),kw(start),kw(end),kw(key),kw(test),kw(test_not)) )
# (REMOVE-DUPLICATES sequence [:from-end] [:start] [:end] [:key] [:test] [:test-not]),
# CLTL S. 254
  { return_Values seq_duplicates(&remove_help); }

LISPFUN(delete_duplicates,1,0,norest,key,6,\
        (kw(from_end),kw(start),kw(end),kw(key),kw(test),kw(test_not)) )
# (DELETE-DUPLICATES sequence [:from-end] [:start] [:end] [:key] [:test] [:test-not]),
# CLTL S. 254
  { return_Values seq_duplicates(&delete_help); }

# UP: Hilfsroutine f�r SUBSTITUTE-Funktionen.
# Bildet zu einer Sequence eine neue Sequence, in der genau die Elemente
# ersetzt sind, die in einem Bitvektor markiert sind.
# > stackptr: Pointer in den Stack, *(stackptr+2)=newitem,
#   *(stackptr+0)=sequence, *(stackptr-2)=start, *(stackptr-3)=end,
# > STACK_2: typdescr,
# > STACK_1: L�nge l der Sequence,
# > STACK_0: Bit-Vektor bv,
# > bvl: L�nge des Bit-Vektors (= end - start),
# > dl: Anzahl der im Bit-Vektor gesetzten Bits,
# < ergebnis: Ergebnis
# kann GC ausl�sen
  local object substitute_help (object* stackptr, uintL bvl, uintL dl);
  local object substitute_help(stackptr,bvl,dl)
    var object* stackptr;
    var uintL bvl;
    var uintL dl;
    { # dl=0 -> sequence unver�ndert zur�ckgeben:
      if (dl==0) { return *(stackptr STACKop 0); }
      if (eq(seq_type(STACK_2),S(list))) # Typ LIST ?
        # Noch �berpr�fen, ob sequence wirklich eine Liste ist.
        # Wegen l >= dl > 0 ist zu testen, ob sequence ein Cons ist.
        if (mconsp(*(stackptr STACKop 0)))
          { # Listen speziell behandeln:
            pushSTACK(NIL); # L1 := nil
            pushSTACK(*(stackptr STACKop 0)); # L2 := sequence
            # Stackaufbau: ..., typdescr, l, bv,
            #              L1, L2.
            # Erste start Conses kopieren:
            { var uintL count = posfixnum_to_L(*(stackptr STACKop -2)); # 0 <= start <= l ==> start ist Fixnum
              dotimesL(count,count,
                { # Hier gilt (revappend L1 L2) = sequence
                  var object new_cons = allocate_cons();
                  var object L2 = STACK_0;
                  Car(new_cons) = Car(L2);
                  STACK_0 = Cdr(L2); # L2 := (cdr L2)
                  Cdr(new_cons) = STACK_1; STACK_1 = new_cons; # L1 := (cons ... L1)
                });
            }
            # bvl bis �ber die letzte Eins im Bit-Vector erniedrigen:
            # (Es gibt Einsen, da dl>0.)
            { var object bv = STACK_(0+2);
              loop { var uintL bvl_1 = bvl-1;
                     if (sbvector_btst(bv,bvl_1)) break; #  Bit bvl-1 abfragen
                     bvl = bvl_1; # Bit =0 -> bvl erniedrigen und weitersuchen
            }      }
            # Teilabschnitt kopieren bzw. mit newitem f�llen:
            { var uintL bvi = 0; # bvi := 0
              until (bvi==bvl) # Schleife bvl mal durchlaufen
                { if (sbvector_btst(STACK_(0+2),bvi)) # (sbit bv bvi) abfragen
                    { # Bit =1 -> newitem nehmen
                      pushSTACK(*(stackptr STACKop 2)); # newitem
                    }
                    else
                    { # Bit =0 -> (car L2) nehmen
                      pushSTACK(Car(STACK_0));
                    }
                  {var object new_cons = allocate_cons();
                   Car(new_cons) = popSTACK(); # mit Obigem als CAR
                   Cdr(new_cons) = STACK_1; STACK_1 = new_cons; # L1 := (cons ... L1)
                  }
                  STACK_0 = Cdr(STACK_0); # L2 := (cdr L2)
                  bvi++; # bvi:=bvi+1
            }   }
            # letzten Teilabschnitt unver�ndert dazunehmen:
            { var object L2 = popSTACK();
              var object L1 = popSTACK();
              return nreconc(L1,L2); # (nreconc L1 L2) als Ergebnis
          } }
      # neue Sequence allozieren:
      pushSTACK(STACK_1); # l
      funcall(seq_make(STACK_(2+1)),1); # (SEQ-MAKE l)
      pushSTACK(value1); # =: sequence2
      # Stackaufbau: ..., typdescr, l, bv, sequence2.
      pushSTACK(*(stackptr STACKop 0)); # sequence
      pushSTACK(STACK_(3+1)); # typdescr
      pushSTACK(STACK_(0+2)); # sequence2
      pushSTACK(STACK_(3+3)); # typdescr
      pushSTACK(*(stackptr STACKop -2)); # start
      # Stackaufbau: ..., typdescr, l, bv, sequence2,
      #              seq1, typdescr1, seq2, typdescr2, start.
      pushSTACK(STACK_4); funcall(seq_init(STACK_(3+1)),1); # (SEQ-INIT sequence)
      pushSTACK(value1); # =: pointer1
      pushSTACK(STACK_(2+1)); funcall(seq_init(STACK_(1+1+1)),1); # (SEQ-INIT sequence2)
      pushSTACK(value1); # =: pointer2
      # Stackaufbau: ..., typdescr, l, bv, sequence2,
      #              seq1, typdescr1, seq2, typdescr2, start,
      #              pointer1, pointer2.
      { # Vorderes Teilst�ck:
        # Elemente mit Index <start von sequence1 nach sequence2
        # unver�ndert �bertragen:
        copy_seqpart_into();
      }
      { # Mittleres Teilst�ck:
        var uintL bvi = 0;
        until (bvi==bvl)
          { var object item; # zu �bernehmendes Element
            if (sbvector_btst(STACK_(1+5+2),bvi)) # (sbit bv bvi) abfragen
              # Bit =1 -> newitem nehmen:
              { item = *(stackptr STACKop 2); }
              else
              # Bit =0 -> Element aus sequence �bernehmen:
              { pushSTACK(STACK_(4+2)); pushSTACK(STACK_(1+1));
                funcall(seq_access(STACK_(3+2+2)),2); # (SEQ-ACCESS seq1 pointer1)
                item = value1;
              }
            pushSTACK(STACK_(2+2)); pushSTACK(STACK_(0+1)); pushSTACK(item);
            funcall(seq_access_set(STACK_(1+2+3)),3); # (SEQ-ACCESS-SET seq2 pointer2 ...)
            # pointer1, pointer2, bvi weiterr�cken:
            # pointer1 := (SEQ-UPD seq1 pointer1) :
            pointer_update(STACK_1,STACK_(4+2),STACK_(3+2));
            # pointer2 := (SEQ-UPD seq2 pointer2) :
            pointer_update(STACK_0,STACK_(2+2),STACK_(1+2));
            bvi++;
      }   }
      { # Hinteres Teilst�ck:
        # Elemente mit Index >=end von sequence1 nach sequence2
        # unver�ndert �bertragen:
        STACK_(0+2) = I_I_minus_I(STACK_(2+5+2),*(stackptr STACKop -3)); # (- l end)
        copy_seqpart_into();
      }
      skipSTACK(5+2);
      return popSTACK(); # sequence2 als Ergebnis
    }

LISPFUN(substitute,3,0,norest,key,7,\
        (kw(from_end),kw(start),kw(end),kw(key),kw(test),kw(test_not),kw(count)) )
# (SUBSTITUTE newitem item sequence [:from-end] [:start] [:end] [:key] [:test] [:test-not] [:count]),
# CLTL S. 255
  { var object* stackptr = &STACK_7;
    var up_function up_fun = test_test_args(stackptr); # Testfunktion
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    seq_filterop(stackptr,up_fun,&substitute_help); # Filtern
    skipSTACK(3+7+1);
  }

LISPFUN(substitute_if,3,0,norest,key,5,\
        (kw(from_end),kw(start),kw(end),kw(key),kw(count)) )
# (SUBSTITUTE-IF newitem test sequence [:from-end] [:start] [:end] [:key] [:count]),
# CLTL S. 255
  { var object* stackptr = &STACK_5;
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    seq_filterop(stackptr,&up_if,&substitute_help); # Filtern
    skipSTACK(3+5+1);
  }

LISPFUN(substitute_if_not,3,0,norest,key,5,\
        (kw(from_end),kw(start),kw(end),kw(key),kw(count)) )
# (SUBSTITUTE-IF-NOT newitem test sequence [:from-end] [:start] [:end] [:key] [:count]),
# CLTL S. 255
  { var object* stackptr = &STACK_5;
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    seq_filterop(stackptr,&up_if_not,&substitute_help); # Filtern
    skipSTACK(3+5+1);
  }

# UP: Hilfsroutine f�r NSUBSTITUTE-Funktionen im Fall FROM-END.
# Ersetzt in einer Sequence genau die Elemente, die in einem Bitvektor
# markiert sind.
# > stackptr: Pointer in den Stack, *(stackptr+2)=newitem,
#   *(stackptr+0)=sequence, *(stackptr-2)=start, *(stackptr-3)=end,
# > STACK_2: typdescr,
# > STACK_1: L�nge l der Sequence,
# > STACK_0: Bit-Vektor bv,
# > bvl: L�nge des Bit-Vektors (= end - start),
# > dl: Anzahl der im Bit-Vektor gesetzten Bits,
# < ergebnis: Ergebnis
# kann GC ausl�sen
  local object nsubstitute_fe_help (object* stackptr, uintL bvl, uintL dl);
  local object nsubstitute_fe_help(stackptr,bvl,dl)
    var object* stackptr;
    var uintL bvl;
    var uintL dl;
    { {pushSTACK(*(stackptr STACKop 0)); # sequence
       pushSTACK(*(stackptr STACKop -2)); # start
       funcall(seq_init_start(STACK_(2+2)),2); # (SEQ-INIT-START sequence start)
       pushSTACK(value1); # =: pointer
      }
      # Stackaufbau: ..., typdescr, l, bv,
      #                   pointer.
      {var uintL bvi = 0; # bvi := 0
       until (bvi==bvl) # Schleife bvl mal durchlaufen
         { if (sbvector_btst(STACK_(0+1),bvi)) # (sbit bv bvi) abfragen
             # Bit =1 -> ersetze Element durch newitem:
             { pushSTACK(*(stackptr STACKop 0)); # sequence
               pushSTACK(STACK_(0+1)); # pointer
               pushSTACK(*(stackptr STACKop 2)); # newitem
               funcall(seq_access_set(STACK_(2+1+3)),3); # (SEQ-ACCESS-SET sequence pointer newitem)
             }
           # pointer := (SEQ-UPD sequence pointer) :
           pointer_update(STACK_0,*(stackptr STACKop 0),STACK_(2+1));
           bvi++; # bvi:=bvi+1
      }  }
      skipSTACK(1); # pointer vergessen
      return *(stackptr STACKop 0); # sequence als Ergebnis
    }

# Macro: endvar := (and end (- end start)) auf den STACK legen
# init_endvar(stackptr);
# > stackptr: Pointer in den Stack, *(stackptr+1)=start, *(stackptr+0)=end
  #define init_endvar(stackptr)  \
    {var object end = *(stackptr STACKop 0); # end                                        \
     if (!(nullp(end)))                                                                   \
       { end = I_I_minus_I(end,*(stackptr STACKop 1)); } # (- end start), ein Integer >=0 \
     pushSTACK(end);                                                                      \
    }

# Macro: endvar decrementieren falls endvar/=NIL
# decrement_endvar(endvar);
# > object endvar: entweder NIL oder ein Fixnum >0
# < object endvar: entweder immer noch NIL oder (decrementiert) ein Fixnum >=0
  #define decrement_endvar(endvar)  \
    { if (!(nullp(endvar))) # end angegeben ?                \
        { decrement(endvar); } # ja -> endvar := (1- endvar) \
    }

# UP: F�hrt eine NSUBSTITUTE-Operation durch.
# > Stackaufbau:
#     ... sequence [stackptr] from-end start end key ... count typdescr [STACK]
# > stackptr: Pointer in den Stack, *(stackptr+2)=newitem
# > up_fun: Adresse einer Testfunktion, die wie folgt spezifiziert ist:
#           > stackptr: derselbe Pointer in den Stack,
#           > x: Argument
#           < TRUE, falls der Test erf�llt ist, FALSE sonst.
# > subr_self: Aufrufer (ein SUBR)
# < mv_space/mv_count: Werte
# kann GC ausl�sen
  local Values nsubstitute_op (object* stackptr, up_function up_fun);
  local Values nsubstitute_op(stackptr,up_fun)
    var object* stackptr;
    var up_function up_fun;
    { if (!(nullp(*(stackptr STACKop -1)))) # from-end abfragen
        # from-end ist angegeben -> Bit-Vector erzeugen und dann ersetzen:
        { return_Values seq_filterop(stackptr,up_fun,&nsubstitute_fe_help); }
        else
        # from-end ist nicht angegeben
        { # COUNT-Argument muss NIL oder ein Integer >= 0 sein:
          test_count_arg();
          # Nun sind alle Argumente �berpr�ft.
          pushSTACK(*(stackptr STACKop 0)); # sequence
          pushSTACK(*(stackptr STACKop -4)); # key
          init_endvar(&*(stackptr STACKop -3)); # endvar := (and end (- end start)) auf den Stack
          pushSTACK(STACK_(1+3)); # countdown := count
          # Stackaufbau: ..., count, typdescr,
          #              sequence, key, endvar, countdown.
          {pushSTACK(STACK_3); # sequence
           pushSTACK(*(stackptr STACKop -2)); # start
           funcall(seq_init_start(STACK_(0+4+2)),2); # (SEQ-INIT-START sequence start)
           pushSTACK(value1); # =: pointer
          }
          # Stackaufbau: ..., count, typdescr,
          #              sequence, key, endvar, countdown, pointer.
          # endvar und countdown sind jeweils entweder =NIL oder ein Integer >=0.
          { until (eq(STACK_2,Fixnum_0)) # endvar = 0 ?
                # (also end angegeben und (- end start) Elemente durchlaufen ?)
                # ja -> fertig
              { pushSTACK(STACK_4); pushSTACK(STACK_(0+1));
                funcall(seq_endtest(STACK_(0+5+2)),2); # (SEQ-ENDTEST sequence pointer)
                if (!(nullp(value1))) break; # Pointer am Ende -> fertig
                if (eq(STACK_1,Fixnum_0)) # countdown=0 ?
                  # (also count angegeben und ersch�pft?)
                  break; # ja -> Schleife kann abgebrochen werden
                # item herausgreifen:
                pushSTACK(STACK_4); pushSTACK(STACK_(0+1));
                funcall(seq_access(STACK_(0+5+2)),2); # (SEQ-ACCESS sequence pointer)
                funcall_key(STACK_3); # (FUNCALL key (SEQ-ACCESS sequence pointer))
                # value1 =: item
                if ((*up_fun)(stackptr,value1)) # Testroutine aufrufen
                  # Test ist erf�llt
                  { pushSTACK(STACK_4); pushSTACK(STACK_(0+1));
                    pushSTACK(*(stackptr STACKop 2)); # newitem
                    funcall(seq_access_set(STACK_(0+5+3)),3); # (SEQ-ACCESS-SET sequence pointer newitem)
                    if (!(nullp(STACK_(1+5)))) # falls count/=NIL:
                      { decrement(STACK_1); } # (decf countdown)
                  }
                # pointer := (SEQ-UPD sequence pointer) :
                pointer_update(STACK_0,STACK_4,STACK_(0+5));
                # endvar eventuell decrementieren:
                decrement_endvar(STACK_2);
          }   }
          skipSTACK(4);
          value1 = popSTACK(); mv_count=1; # modifizierte Sequence als Wert
        }
    }

LISPFUN(nsubstitute,3,0,norest,key,7,\
        (kw(from_end),kw(start),kw(end),kw(key),kw(test),kw(test_not),kw(count)) )
# (NSUBSTITUTE newitem item sequence [:from-end] [:start] [:end] [:key] [:test] [:test-not] [:count]),
# CLTL S. 256
  { var object* stackptr = &STACK_7;
    var up_function up_fun = test_test_args(stackptr); # Testfunktion
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    nsubstitute_op(stackptr,up_fun); # gefiltert ersetzen
    skipSTACK(3+7+1);
  }

LISPFUN(nsubstitute_if,3,0,norest,key,5,\
        (kw(from_end),kw(start),kw(end),kw(key),kw(count)) )
# (NSUBSTITUTE-IF newitem test sequence [:from-end] [:start] [:end] [:key] [:count]),
# CLTL S. 256
  { var object* stackptr = &STACK_5;
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    nsubstitute_op(stackptr,&up_if); # gefiltert ersetzen
    skipSTACK(3+5+1);
  }

LISPFUN(nsubstitute_if_not,3,0,norest,key,5,\
        (kw(from_end),kw(start),kw(end),kw(key),kw(count)) )
# (NSUBSTITUTE-IF-NOT newitem test sequence [:from-end] [:start] [:end] [:key] [:count]),
# CLTL S. 256
  { var object* stackptr = &STACK_5;
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    nsubstitute_op(stackptr,&up_if_not); # gefiltert ersetzen
    skipSTACK(3+5+1);
  }

# UP: F�hrt eine FIND-Operation durch.
# > Stackaufbau:
#     ... sequence [stackptr] from-end start end key ... typdescr [STACK]
# > stackptr: Pointer in den Stack
# > up_fun: Adresse einer Testfunktion, die wie folgt spezifiziert ist:
#           > stackptr: derselbe Pointer in den Stack,
#           > x: Argument
#           < TRUE, falls der Test erf�llt ist, FALSE sonst.
# > subr_self: Aufrufer (ein SUBR)
# < mv_space/mv_count: Werte
# kann GC ausl�sen
  local Values find_op (object* stackptr, up_function up_fun);
  local Values find_op(stackptr,up_fun)
    var object* stackptr;
    var up_function up_fun;
    { pushSTACK(*(stackptr STACKop 0)); # sequence
      # Stackaufbau: ..., typdescr, sequence.
      if (!(nullp(*(stackptr STACKop -1)))) # from-end abfragen
        # from-end ist angegeben
        { # Defaultwert f�r end ist die L�nge der Sequence:
          if (nullp(*(stackptr STACKop -3)))
            { { var object old_subr_self = subr_self; # aktuelles SUBR, nicht GC-gef�hrdet!
                pushSTACK(STACK_0); funcall(seq_length(STACK_(1+1)),1); # (SEQ-LENGTH sequence)
                *(stackptr STACKop -3) = value1; # =: end
                subr_self = old_subr_self;
              }
              # Dann nochmals start und end �berpr�fen:
              test_start_end(&O(kwpair_start),&*(stackptr STACKop -3));
            }
          {pushSTACK(STACK_0); pushSTACK(*(stackptr STACKop -3));
           funcall(seq_fe_init_end(STACK_(1+2)),2); # (SEQ-FE-INIT-END sequence end)
           pushSTACK(value1); # =: pointer
          }
          { # count := (- end start), ein Integer >=0 :
            pushSTACK(I_I_minus_I(*(stackptr STACKop -3),*(stackptr STACKop -2)));
          }
          # Stackaufbau: ..., typdescr, sequence, pointer, count.
          { until (eq(STACK_0,Fixnum_0)) # count (ein Integer) = 0 -> fertig
              { # item herausgreifen:
                pushSTACK(STACK_2); pushSTACK(STACK_(1+1));
                funcall(seq_access(STACK_(3+2)),2); # (SEQ-ACCESS sequence pointer)
                pushSTACK(value1); # =: item
                funcall_key(*(stackptr STACKop -4)); # (FUNCALL key item)
                if ((*up_fun)(stackptr,value1)) # Testroutine aufrufen
                  goto found; # Test erf�llt -> gefunden
                # Test ist nicht erf�llt
                skipSTACK(1); # item vergessen
                # pointer weiterr�cken und count decrementieren:
                # pointer := (SEQ-FE-UPD sequence pointer) :
                pointer_fe_update(STACK_1,STACK_2,STACK_3);
                decrement(STACK_0); # count := (1- count)
        } }   }
        else
        # from-end ist nicht angegeben
        { init_endvar(&*(stackptr STACKop -3)); # endvar := (and end (- end start)) auf den Stack
          # Stackaufbau: ..., typdescr, sequence, endvar.
          {pushSTACK(STACK_1); pushSTACK(*(stackptr STACKop -2));
           funcall(seq_init_start(STACK_(2+2)),2); # (SEQ-INIT-START sequence start)
           pushSTACK(value1); # =: pointer
          }
          # Stackaufbau: ... typdescr, sequence, endvar, pointer
          { until (eq(STACK_1,Fixnum_0)) # endvar = 0 ?
                # (also end angegeben und (- end start) Elemente durchlaufen ?)
                # ja -> fertig
              { pushSTACK(STACK_2); pushSTACK(STACK_(0+1));
                funcall(seq_endtest(STACK_(3+2)),2); # (SEQ-ENDTEST sequence pointer)
                if (!(nullp(value1))) break; # Pointer am Ende -> fertig
                # item herausgreifen:
                pushSTACK(STACK_2); pushSTACK(STACK_(0+1));
                funcall(seq_access(STACK_(3+2)),2); # (SEQ-ACCESS sequence pointer)
                pushSTACK(value1); # =: item
                funcall_key(*(stackptr STACKop -4)); # (FUNCALL key item)
                if ((*up_fun)(stackptr,value1)) # Testroutine aufrufen
                  goto found; # Test erf�llt -> gefunden
                # Test ist nicht erf�llt
                skipSTACK(1); # item vergessen
                # pointer := (SEQ-UPD sequence pointer) :
                pointer_update(STACK_0,STACK_2,STACK_3);
                # endvar eventuell decrementieren:
                decrement_endvar(STACK_1);
        } }   }
      skipSTACK(3); # STACK aufr�umen
      value1 = NIL; mv_count=1; return; # NIL als Wert
      found: # item gefunden, das den Test erf�llt. STACK_0 = item.
      value1 = popSTACK(); mv_count=1; # item als Wert
      skipSTACK(3); # STACK aufr�umen
    }

LISPFUN(find,2,0,norest,key,6,\
        (kw(from_end),kw(start),kw(end),kw(key),kw(test),kw(test_not)) )
# (FIND item sequence [:from-end] [:start] [:end] [:key] [:test] [:test-not]),
# CLTL S. 257
  { var object* stackptr = &STACK_6;
    var up_function up_fun = test_test_args(stackptr); # Testfunktion
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    find_op(stackptr,up_fun); # suchen
    skipSTACK(2+6+1);
  }

LISPFUN(find_if,2,0,norest,key,4,\
        (kw(from_end),kw(start),kw(end),kw(key)) )
# (FIND-IF test sequence [:from-end] [:start] [:end] [:key]),
# CLTL S. 257
  { var object* stackptr = &STACK_4;
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    find_op(stackptr,&up_if); # suchen
    skipSTACK(2+4+1);
  }

LISPFUN(find_if_not,2,0,norest,key,4,\
        (kw(from_end),kw(start),kw(end),kw(key)) )
# (FIND-IF-NOT test sequence [:from-end] [:start] [:end] [:key]),
# CLTL S. 257
  { var object* stackptr = &STACK_4;
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    find_op(stackptr,&up_if_not); # suchen
    skipSTACK(2+4+1);
  }

# UP: F�hrt eine POSITION-Operation durch.
# > Stackaufbau:
#     ... sequence [stackptr] from-end start end key ... typdescr [STACK]
# > stackptr: Pointer in den Stack
# > up_fun: Adresse einer Testfunktion, die wie folgt spezifiziert ist:
#           > stackptr: derselbe Pointer in den Stack,
#           > x: Argument
#           < TRUE, falls der Test erf�llt ist, FALSE sonst.
# > subr_self: Aufrufer (ein SUBR)
# < mv_space/mv_count: Werte
# kann GC ausl�sen
  local Values position_op (object* stackptr, up_function up_fun);
  local Values position_op(stackptr,up_fun)
    var object* stackptr;
    var up_function up_fun;
    { pushSTACK(*(stackptr STACKop 0)); # sequence
      # Stackaufbau: ..., typdescr, sequence.
      if (!(nullp(*(stackptr STACKop -1)))) # from-end abfragen
        # from-end ist angegeben
        { # Defaultwert f�r end ist die L�nge der Sequence:
          if (nullp(*(stackptr STACKop -3)))
            { { var object old_subr_self = subr_self; # aktuelles SUBR, nicht GC-gef�hrdet!
                pushSTACK(STACK_0); funcall(seq_length(STACK_(1+1)),1); # (SEQ-LENGTH sequence)
                *(stackptr STACKop -3) = value1; # =: end
                subr_self = old_subr_self;
              }
              # Dann nochmals start und end �berpr�fen:
              test_start_end(&O(kwpair_start),&*(stackptr STACKop -3));
            }
          pushSTACK(*(stackptr STACKop -3)); # index := end
          {pushSTACK(STACK_(0+1)); pushSTACK(*(stackptr STACKop -3));
           funcall(seq_fe_init_end(STACK_(1+1+2)),2); # (SEQ-FE-INIT-END sequence end)
           pushSTACK(value1); # =: pointer
          }
          { # count := (- end start), ein Integer >=0 :
            pushSTACK(I_I_minus_I(*(stackptr STACKop -3),*(stackptr STACKop -2)));
          }
          # Stackaufbau: ..., typdescr, sequence, index, pointer, count.
          { until (eq(STACK_0,Fixnum_0)) # count (ein Integer) = 0 -> fertig
              { # index decrementieren:
                decrement(STACK_2);
                # item herausgreifen:
                pushSTACK(STACK_3); pushSTACK(STACK_(1+1));
                funcall(seq_access(STACK_(4+2)),2); # (SEQ-ACCESS sequence pointer)
                funcall_key(*(stackptr STACKop -4)); # (FUNCALL key (SEQ-ACCESS sequence pointer))
                if ((*up_fun)(stackptr,value1)) # Testroutine aufrufen
                  goto found; # Test erf�llt -> gefunden
                # Test ist nicht erf�llt
                # pointer weiterr�cken und count decrementieren:
                # pointer := (SEQ-FE-UPD sequence pointer) :
                pointer_fe_update(STACK_1,STACK_3,STACK_4);
                decrement(STACK_0); # count := (1- count)
        } }   }
        else
        # from-end ist nicht angegeben
        { pushSTACK(*(stackptr STACKop -2)); # index := start
          init_endvar(&*(stackptr STACKop -3)); # endvar := (and end (- end start)) auf den Stack
          # Stackaufbau: ..., typdescr, sequence, index, endvar.
          {pushSTACK(STACK_2); pushSTACK(*(stackptr STACKop -2));
           funcall(seq_init_start(STACK_(3+2)),2); # (SEQ-INIT-START sequence start)
           pushSTACK(value1); # =: pointer
          }
          # Stackaufbau: ... typdescr, sequence, index, endvar, pointer
          { until (eq(STACK_1,Fixnum_0)) # endvar = 0 ?
                # (also end angegeben und (- end start) Elemente durchlaufen ?)
                # ja -> fertig
              { pushSTACK(STACK_3); pushSTACK(STACK_(0+1));
                funcall(seq_endtest(STACK_(4+2)),2); # (SEQ-ENDTEST sequence pointer)
                if (!(nullp(value1))) break; # Pointer am Ende -> fertig
                # item herausgreifen:
                pushSTACK(STACK_3); pushSTACK(STACK_(0+1));
                funcall(seq_access(STACK_(4+2)),2); # (SEQ-ACCESS sequence pointer)
                funcall_key(*(stackptr STACKop -4)); # (FUNCALL key (SEQ-ACCESS sequence pointer))
                if ((*up_fun)(stackptr,value1)) # Testroutine aufrufen
                  goto found; # Test erf�llt -> gefunden
                # Test ist nicht erf�llt
                # pointer := (SEQ-UPD sequence pointer) :
                pointer_update(STACK_0,STACK_3,STACK_4);
                # endvar eventuell decrementieren:
                decrement_endvar(STACK_1);
                # index incrementieren:
                increment(STACK_2);
        } }   }
      skipSTACK(4); # STACK aufr�umen
      value1 = NIL; mv_count=1; return; # NIL als Wert
      found: # item gefunden, das den Test erf�llt. STACK_2 = index.
      value1 = STACK_2; mv_count=1; # index als Wert
      skipSTACK(4); # STACK aufr�umen
    }

LISPFUN(position,2,0,norest,key,6,\
        (kw(from_end),kw(start),kw(end),kw(key),kw(test),kw(test_not)) )
# (POSITION item sequence [:from-end] [:start] [:end] [:key] [:test] [:test-not]),
# CLTL S. 257
  { var object* stackptr = &STACK_6;
    var up_function up_fun = test_test_args(stackptr); # Testfunktion
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    position_op(stackptr,up_fun); # suchen
    skipSTACK(2+6+1);
  }

LISPFUN(position_if,2,0,norest,key,4,\
        (kw(from_end),kw(start),kw(end),kw(key)) )
# (POSITION-IF test sequence [:from-end] [:start] [:end] [:key]),
# CLTL S. 257
  { var object* stackptr = &STACK_4;
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    position_op(stackptr,&up_if); # suchen
    skipSTACK(2+4+1);
  }

LISPFUN(position_if_not,2,0,norest,key,4,\
        (kw(from_end),kw(start),kw(end),kw(key)) )
# (POSITION-IF-NOT test sequence [:from-end] [:start] [:end] [:key]),
# CLTL S. 257
  { var object* stackptr = &STACK_4;
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    position_op(stackptr,&up_if_not); # suchen
    skipSTACK(2+4+1);
  }

# UP: F�hrt eine COUNT-Operation durch.
# > Stackaufbau:
#     ... sequence [stackptr] from-end start end key ... typdescr [STACK]
# > stackptr: Pointer in den Stack
# > up_fun: Adresse einer Testfunktion, die wie folgt spezifiziert ist:
#           > stackptr: derselbe Pointer in den Stack,
#           > x: Argument
#           < TRUE, falls der Test erf�llt ist, FALSE sonst.
# > subr_self: Aufrufer (ein SUBR)
# < mv_space/mv_count: Werte
# kann GC ausl�sen
  local Values count_op (object* stackptr, up_function up_fun);
  local Values count_op(stackptr,up_fun)
    var object* stackptr;
    var up_function up_fun;
    { pushSTACK(*(stackptr STACKop 0)); # sequence
      pushSTACK(Fixnum_0); # total := 0
      # Stackaufbau: ..., typdescr, sequence, total.
      if (!(nullp(*(stackptr STACKop -1)))) # from-end abfragen
        # from-end ist angegeben
        { # Defaultwert f�r end ist die L�nge der Sequence:
          if (nullp(*(stackptr STACKop -3)))
            { { var object old_subr_self = subr_self; # aktuelles SUBR, nicht GC-gef�hrdet!
                pushSTACK(STACK_1); funcall(seq_length(STACK_(2+1)),1); # (SEQ-LENGTH sequence)
                *(stackptr STACKop -3) = value1; # =: end
                subr_self = old_subr_self;
              }
              # Dann nochmals start und end �berpr�fen:
              test_start_end(&O(kwpair_start),&*(stackptr STACKop -3));
            }
          {pushSTACK(STACK_1); pushSTACK(*(stackptr STACKop -3));
           funcall(seq_fe_init_end(STACK_(2+2)),2); # (SEQ-FE-INIT-END sequence end)
           pushSTACK(value1); # =: pointer
          }
          { # count := (- end start), ein Integer >=0 :
            pushSTACK(I_I_minus_I(*(stackptr STACKop -3),*(stackptr STACKop -2)));
          }
          # Stackaufbau: ..., typdescr, sequence, total, pointer, count.
          { until (eq(STACK_0,Fixnum_0)) # count (ein Integer) = 0 -> fertig
              { # item herausgreifen:
                pushSTACK(STACK_3); pushSTACK(STACK_(1+1));
                funcall(seq_access(STACK_(4+2)),2); # (SEQ-ACCESS sequence pointer)
                funcall_key(*(stackptr STACKop -4)); # (FUNCALL key (SEQ-ACCESS sequence pointer))
                if ((*up_fun)(stackptr,value1)) # Testroutine aufrufen
                  { # Test ist erf�llt -> total := total + 1 :
                    STACK_2 = fixnum_inc(STACK_2,1);
                  }
                # pointer weiterr�cken und count decrementieren:
                # pointer := (SEQ-FE-UPD sequence pointer) :
                pointer_fe_update(STACK_1,STACK_3,STACK_4);
                decrement(STACK_0); # count := (1- count)
        } }   }
        else
        # from-end ist nicht angegeben
        { init_endvar(&*(stackptr STACKop -3)); # endvar := (and end (- end start)) auf den Stack
          # Stackaufbau: ..., typdescr, sequence, total, endvar.
          {pushSTACK(STACK_2); pushSTACK(*(stackptr STACKop -2));
           funcall(seq_init_start(STACK_(3+2)),2); # (SEQ-INIT-START sequence start)
           pushSTACK(value1); # =: pointer
          }
          # Stackaufbau: ... typdescr, sequence, total, endvar, pointer
          { until (eq(STACK_1,Fixnum_0)) # endvar = 0 ?
                # (also end angegeben und (- end start) Elemente durchlaufen ?)
                # ja -> fertig
              { pushSTACK(STACK_3); pushSTACK(STACK_(0+1));
                funcall(seq_endtest(STACK_(4+2)),2); # (SEQ-ENDTEST sequence pointer)
                if (!(nullp(value1))) break; # Pointer am Ende -> fertig
                # item herausgreifen:
                pushSTACK(STACK_3); pushSTACK(STACK_(0+1));
                funcall(seq_access(STACK_(4+2)),2); # (SEQ-ACCESS sequence pointer)
                funcall_key(*(stackptr STACKop -4)); # (FUNCALL key (SEQ-ACCESS sequence pointer))
                if ((*up_fun)(stackptr,value1)) # Testroutine aufrufen
                  { # Test ist erf�llt -> total := total + 1 :
                    STACK_2 = fixnum_inc(STACK_2,1);
                  }
                # pointer := (SEQ-UPD sequence pointer) :
                pointer_update(STACK_0,STACK_3,STACK_4);
                # endvar eventuell decrementieren:
                decrement_endvar(STACK_1);
        } }   }
      value1 = STACK_2; mv_count=1; skipSTACK(4); # total als Wert
    }

LISPFUN(count,2,0,norest,key,6,\
        (kw(from_end),kw(start),kw(end),kw(key),kw(test),kw(test_not)) )
# (COUNT item sequence [:from-end] [:start] [:end] [:key] [:test] [:test-not]),
# CLTL S. 257
  { var object* stackptr = &STACK_6;
    var up_function up_fun = test_test_args(stackptr); # Testfunktion
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    count_op(stackptr,up_fun); # suchen
    skipSTACK(2+6+1);
  }

LISPFUN(count_if,2,0,norest,key,4,\
        (kw(from_end),kw(start),kw(end),kw(key)) )
# (COUNT-IF test sequence [:from-end] [:start] [:end] [:key]),
# CLTL S. 257
  { var object* stackptr = &STACK_4;
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    count_op(stackptr,&up_if); # suchen
    skipSTACK(2+4+1);
  }

LISPFUN(count_if_not,2,0,norest,key,4,\
        (kw(from_end),kw(start),kw(end),kw(key)) )
# (COUNT-IF-NOT test sequence [:from-end] [:start] [:end] [:key]),
# CLTL S. 257
  { var object* stackptr = &STACK_4;
    seq_prepare_testop(stackptr); # Argumente aufbereiten, typdescr
    count_op(stackptr,&up_if_not); # suchen
    skipSTACK(2+4+1);
  }

LISPFUN(mismatch,2,0,norest,key,8,\
        (kw(start1),kw(end1),kw(start2),kw(end2),kw(from_end),\
         kw(key),kw(test),kw(test_not)) )
# (MISMATCH sequence1 sequence2
#           [:start1] [:end1] [:start2] [:end2] [:from-end] [:key] [:test] [:test-not]),
# CLTL S. 257
  { # Stackaufbau: seq1, seq2, start1, end1, start2, end2, from-end,
    #              key, test, test-not.
    var object* stackptr = &STACK_6;
    # key �berpr�fen:
    test_key_arg(stackptr);
    # test, test-not �berpr�fen:
   {var up2_function up2_fun = test_test2_args(stackptr);
    # sequence1 �berpr�fen:
    pushSTACK(get_valid_seq_type(STACK_(6+3)));
    # sequence2 �berpr�fen:
    pushSTACK(get_valid_seq_type(STACK_(5+3+1)));
    # Stackaufbau: seq1, seq2, start1, end1, start2, end2, from-end,
    #              key, test, test-not, typdescr1, typdescr2.
    default_NIL(STACK_(0+5)); # Defaultwert f�r from-end ist NIL
    start_default_0(STACK_(4+5)); # Defaultwert f�r start1 ist 0
    default_NIL(STACK_(3+5)); # Defaultwert f�r end1 ist NIL
    start_default_0(STACK_(2+5)); # Defaultwert f�r start2 ist 0
    default_NIL(STACK_(1+5)); # Defaultwert f�r end2 ist NIL
    # from-end abfragen:
    if (!(nullp(STACK_(0+5))))
      # from-end ist angegeben
      { # Defaultwert von end1 ist (SEQ-LENGTH seq1):
        end_default_len(STACK_(3+5),STACK_(6+5),STACK_1);
        # Defaultwert von end2 ist (SEQ-LENGTH seq2):
        end_default_len(STACK_(1+5),STACK_(5+5),STACK_0);
        # start- und end-Argumente �berpr�fen:
        subr_self = L(mismatch);
        test_start_end(&O(kwpair_start1),&STACK_(3+5));
        test_start_end(&O(kwpair_start2),&STACK_(1+5));
        # pointer1 und pointer2 ans Ende der Sequences setzen:
        { pushSTACK(STACK_(6+5)); pushSTACK(STACK_(3+5+1));
          funcall(seq_fe_init_end(STACK_(1+2)),2); # (SEQ-FE-INIT-END seq1 end1)
          pushSTACK(value1); # =: pointer1
        }
        { pushSTACK(STACK_(5+5+1)); pushSTACK(STACK_(1+5+1+1));
          funcall(seq_fe_init_end(STACK_(0+1+2)),2); # (SEQ-FE-INIT-END seq2 end2)
          pushSTACK(value1); # =: pointer2
        }
        { pushSTACK(STACK_(3+5+2)); } # index := end1
        { var object len1 = I_I_minus_I(STACK_(3+5+3),STACK_(4+5+3)); # (- end1 start1)
          pushSTACK(len1); # =: len1, ein Integer >=0
        }
        { var object len2 = I_I_minus_I(STACK_(1+5+4),STACK_(2+5+4)); # (- end2 start2)
          pushSTACK(len2); # =: len2, ein Integer >=0
        }
        { var object count = (I_I_comp(STACK_1,STACK_0)<0 ? STACK_1 : STACK_0); # (min len1 len2)
          pushSTACK(count); # =: count, ein Integer >=0
        }
        # Stackaufbau: seq1, seq2, start1, end1, start2, end2, from-end,
        #              key, test, test-not, typdescr1, typdescr2,
        #              pointer1, pointer2, index, len1, len2, count.
        until (eq(STACK_0,Fixnum_0)) # count (ein Integer) = 0 ?
          { pushSTACK(STACK_(6+5+6)); pushSTACK(STACK_(5+1));
            funcall(seq_access(STACK_(1+6+2)),2); # (SEQ-ACCESS seq1 pointer1)
            funcall_key(STACK_(4+6)); # (FUNCALL key (SEQ-ACCESS seq1 pointer1))
            pushSTACK(value1); # =: item1, retten
            pushSTACK(STACK_(5+5+6+1)); pushSTACK(STACK_(4+1+1));
            funcall(seq_access(STACK_(0+6+1+2)),2); # (SEQ-ACCESS seq2 pointer2)
            funcall_key(STACK_(4+6+1)); # (FUNCALL key (SEQ-ACCESS seq2 pointer2))
            {var object item2 = value1;
             var object item1 = popSTACK();
             # beide vergleichen:
             if (!((*up2_fun)(&STACK_(8+6),item1,item2))) # Testroutine anwenden
               goto fe_found;
            }
            # Test erf�llt -> weitersuchen:
            # pointer1 := (SEQ-FE-UPD seq1 pointer1) :
            pointer_fe_update(STACK_5,STACK_(6+5+6),STACK_(1+6));
            # pointer2 := (SEQ-FE-UPD seq2 pointer2) :
            pointer_fe_update(STACK_4,STACK_(5+5+6),STACK_(0+6));
            # index decrementieren:
            decrement(STACK_3);
            # count decrementieren:
            decrement(STACK_0);
          }
        # Schleife erfolgreich.
        # Bei len1=len2 Ergebnis NIL, sonst index:
        if (I_I_comp(STACK_2,STACK_1)==0) # len1=len2 (Integers) ?
          # Beide Sequence-St�cke sind gleich -> NIL als Wert
          { value1 = NIL; mv_count=1; skipSTACK(7+5+6); return; }
        fe_found: # Es ist ein Unterschied gefunden -> index als Wert
        { value1 = STACK_3; mv_count=1; skipSTACK(7+5+6); return; }
      }
      else
      # from-end ist nicht angegeben
      { # start- und end-Argumente �berpr�fen:
        test_start_end_1(&O(kwpair_start1),&STACK_(3+5));
        test_start_end_1(&O(kwpair_start2),&STACK_(1+5));
        # pointer1 und pointer2 an den Anfang der Sequences setzen:
        { pushSTACK(STACK_(6+5)); pushSTACK(STACK_(4+5+1));
          funcall(seq_init_start(STACK_(1+2)),2); # (SEQ-INIT-START seq1 start1)
          pushSTACK(value1); # =: pointer1
        }
        { pushSTACK(STACK_(5+5+1)); pushSTACK(STACK_(2+5+1+1));
          funcall(seq_init_start(STACK_(0+1+2)),2); # (SEQ-INIT-START seq2 start2)
          pushSTACK(value1); # =: pointer2
        }
        { pushSTACK(STACK_(4+5+2)); } # index := start1
        init_endvar(&STACK_(3+5+3)); # endvar1 := (and end1 (- end1 start1))
        init_endvar(&STACK_(1+5+4)); # endvar2 := (and end2 (- end2 start2))
        # Stackaufbau: seq1, seq2, start1, end1, start2, end2, from-end,
        #              key, test, test-not, typdescr1, typdescr2,
        #              pointer1, pointer2, index, endvar1, endvar2.
        { var boolean seq1_ended; # Flag, ob seq1-Teilst�ck zu Ende
          var boolean seq2_ended; # Flag, ob seq2-Teilst�ck zu Ende
          loop
            { # Teste, ob seq1-Teilst�ck zu Ende:
              if (eq(STACK_1,Fixnum_0)) # endvar1 = 0 (und damit end1 /= nil) ?
                { seq1_ended = TRUE; }
                else
                { pushSTACK(STACK_(6+5+5)); pushSTACK(STACK_(4+1));
                  funcall(seq_endtest(STACK_(1+5+2)),2); # (SEQ-ENDTEST seq1 pointer1)
                  seq1_ended = !nullp(value1);
                }
              # Teste, ob seq2-Teilst�ck zu Ende:
              if (eq(STACK_0,Fixnum_0)) # endvar2 = 0 (und damit end2 /= nil) ?
                { seq2_ended = TRUE; }
                else
                { pushSTACK(STACK_(5+5+5)); pushSTACK(STACK_(3+1));
                  funcall(seq_endtest(STACK_(0+5+2)),2); # (SEQ-ENDTEST seq2 pointer2)
                  seq2_ended = !nullp(value1);
                }
              # Flags abtesten:
              if (seq1_ended || seq2_ended) break;
              # keines der beiden Flags ist gesetzt
              pushSTACK(STACK_(6+5+5)); pushSTACK(STACK_(4+1));
              funcall(seq_access(STACK_(1+5+2)),2); # (SEQ-ACCESS seq1 pointer1)
              funcall_key(STACK_(4+5)); # (FUNCALL key (SEQ-ACCESS seq1 pointer1))
              pushSTACK(value1); # =: item1, retten
              pushSTACK(STACK_(5+5+5+1)); pushSTACK(STACK_(3+1+1));
              funcall(seq_access(STACK_(0+5+1+2)),2); # (SEQ-ACCESS seq2 pointer2)
              funcall_key(STACK_(4+5+1)); # (FUNCALL key (SEQ-ACCESS seq2 pointer2))
              {var object item2 = value1;
               var object item1 = popSTACK();
               # beide vergleichen:
               if (!((*up2_fun)(&STACK_(8+5),item1,item2))) # Testroutine anwenden
                 goto fs_found;
              }
              # Test erf�llt -> weitersuchen:
              # pointer1 := (SEQ-UPD seq1 pointer1) :
              pointer_update(STACK_4,STACK_(6+5+5),STACK_(1+5));
              # pointer2 := (SEQ-UPD seq2 pointer2) :
              pointer_update(STACK_3,STACK_(5+5+5),STACK_(0+5));
              # index incrementieren:
              increment(STACK_2);
              # endvar1 eventuell decrementieren:
              decrement_endvar(STACK_1);
              # endvar2 eventuell decrementieren:
              decrement_endvar(STACK_0);
            }
          # Falls beide Flags gesetzt sind, Ergebnis NIL, sonst index:
          if (seq1_ended && seq2_ended)
            # Beide Sequence-St�cke sind gleich -> NIL als Wert
            { value1 = NIL; mv_count=1; skipSTACK(7+5+5); return; }
          fs_found: # Es ist ein Unterschied gefunden -> index als Wert
          { value1 = STACK_2; mv_count=1; skipSTACK(7+5+5); return; }
      } }
  }}

LISPFUN(search,2,0,norest,key,8,\
        (kw(start1),kw(end1),kw(start2),kw(end2),kw(from_end),\
         kw(key),kw(test),kw(test_not)) )
# (SEARCH sequence1 sequence2
#         [:start1] [:end1] [:start2] [:end2] [:from-end] [:key] [:test] [:test-not]),
# CLTL S. 258
  # Primitiv-Algorithmus:
  #   R�cke immer in sequence2 um 1 weiter und teste, ob dann sequence1 kommt.
  # Knuth-Algorithmus:
  #   [Donald Ervin Knuth, James H. Morris, Vaughan R. Pratt:
  #    Fast pattern matching in string.
  #    SIAM J. Comput. 6(1977), 323-350.]
  #   Kann hier nicht verwendet werden, weil er die Kommutativit�t der
  #   Testfunktion erfordert, die nach CLTL S. 247 nicht notwendig gegeben ist.
  { # Stackaufbau: seq1, seq2, start1, end1, start2, end2, from-end,
    #              key, test, test-not.
    var object* stackptr = &STACK_6;
    # key �berpr�fen:
    test_key_arg(stackptr);
    # test, test-not �berpr�fen:
   {var up2_function up2_fun = test_test2_args(stackptr);
    # sequence1 �berpr�fen:
    pushSTACK(get_valid_seq_type(STACK_(6+3)));
    # sequence2 �berpr�fen:
    pushSTACK(get_valid_seq_type(STACK_(5+3+1)));
    # Stackaufbau: seq1, seq2, start1, end1, start2, end2, from-end,
    #              key, test, test-not, typdescr1, typdescr2.
    default_NIL(STACK_(0+5)); # Defaultwert f�r from-end ist NIL
    # Sonderfall f�r Strings: schnellere Routine aufrufen
    if (eq(seq_type(STACK_1),S(string)) && eq(seq_type(STACK_0),S(string)) # beides STRINGs ?
        && nullp(STACK_(0+5)) # und kein from-end ?
        && eq(STACK_4,L(identity)) # und key = #'identity ?
        && (up2_fun == &up2_test) # und test-not nicht angegeben ?
       )
      { var object test = STACK_3;
        if (eq(test,L(eq)) || eq(test,L(eql)) || eq(test,L(equal)) || eq(test,L(char_gleich)))
          { skipSTACK(6);
            C_search_string_gleich(); # SUBR sys::search-string= mit denselben Argumenten
            return;
          }
        if (eq(test,L(equalp)) || eq(test,L(char_equal)))
          { skipSTACK(6);
            C_search_string_equal(); # SUBR sys::search-string-equal mit denselben Argumenten
            return;
      }   }
    start_default_0(STACK_(4+5)); # Defaultwert f�r start1 ist 0
    default_NIL(STACK_(3+5)); # Defaultwert f�r end1 ist NIL
    start_default_0(STACK_(2+5)); # Defaultwert f�r start2 ist 0
    default_NIL(STACK_(1+5)); # Defaultwert f�r end2 ist NIL
    # from-end abfragen:
    if (!(nullp(STACK_(0+5))))
      # from-end ist angegeben
      { # Defaultwert von end1 ist (SEQ-LENGTH seq1):
        end_default_len(STACK_(3+5),STACK_(6+5),STACK_1);
        # Defaultwert von end2 ist (SEQ-LENGTH seq2):
        end_default_len(STACK_(1+5),STACK_(5+5),STACK_0);
        # start- und end-Argumente �berpr�fen:
        subr_self = L(search);
        test_start_end(&O(kwpair_start1),&STACK_(3+5));
        test_start_end(&O(kwpair_start2),&STACK_(1+5));
        # pointer10 und pointer20 ans Ende der Sequences setzen:
        { pushSTACK(STACK_(6+5)); pushSTACK(STACK_(3+5+1));
          funcall(seq_fe_init_end(STACK_(1+2)),2); # (SEQ-FE-INIT-END seq1 end1)
          pushSTACK(value1); # =: pointer10
        }
        { pushSTACK(STACK_(5+5+1)); pushSTACK(STACK_(1+5+1+1));
          funcall(seq_fe_init_end(STACK_(0+1+2)),2); # (SEQ-FE-INIT-END seq2 end2)
          pushSTACK(value1); # =: pointer20
        }
        { var object len1 = I_I_minus_I(STACK_(3+5+2),STACK_(4+5+2)); # (- end1 start1)
          pushSTACK(len1); # =: len1, ein Integer >=0
        }
        { var object len2 = I_I_minus_I(STACK_(1+5+3),STACK_(2+5+3)); # (- end2 start2)
          pushSTACK(len2); # =: len2, ein Integer >=0
        }
        { var object index = I_I_minus_I(STACK_(1+5+4),STACK_1); # (- end2 len1)
          pushSTACK(index); # =: index, ein Integer
        }
        # Stackaufbau: seq1, seq2, start1, end1, start2, end2, from-end,
        #              key, test, test-not, typdescr1, typdescr2,
        #              pointer10, pointer20, len1, len2, index.
        loop
          { # pointer1 und pointer2 ab pointer10 bzw. pointer20 laufen lassen:
            { pushSTACK(STACK_4); funcall(seq_copy(STACK_(1+5+1)),1); # (SEQ-COPY pointer10)
              pushSTACK(value1); # =: pointer1
            }
            { pushSTACK(STACK_(3+1)); funcall(seq_copy(STACK_(0+5+1+1)),1); # (SEQ-COPY pointer20)
              pushSTACK(value1); # =: pointer2
            }
            pushSTACK(STACK_(2+2)); # count1 := len1
            pushSTACK(STACK_(1+3)); # count2 := len2
            # Stackaufbau: seq1, seq2, start1, end1, start2, end2, from-end,
            #              key, test, test-not, typdescr1, typdescr2,
            #              pointer10, pointer20, len1, len2, index,
            #              pointer1, pointer2, count1, count2.
            loop
              { if (eq(STACK_1,Fixnum_0)) # count1 (ein Integer) = 0 ?
                  goto found; # ja -> seq1 zu Ende, gefunden
                if (eq(STACK_0,Fixnum_0)) # count2 (ein Integer) = 0 ?
                  goto notfound; # ja -> seq2 zu Ende, nicht gefunden
                pushSTACK(STACK_(6+5+5+4)); pushSTACK(STACK_(3+1));
                funcall(seq_access(STACK_(1+5+4+2)),2); # (SEQ-ACCESS seq1 pointer1)
                funcall_key(STACK_(4+5+4)); # (FUNCALL key (SEQ-ACCESS seq1 pointer1))
                pushSTACK(value1); # =: item1, retten
                pushSTACK(STACK_(5+5+5+4+1)); pushSTACK(STACK_(2+1+1));
                funcall(seq_access(STACK_(0+5+4+1+2)),2); # (SEQ-ACCESS seq2 pointer2)
                funcall_key(STACK_(4+5+4+1)); # (FUNCALL key (SEQ-ACCESS seq2 pointer2))
                {var object item2 = value1;
                 var object item1 = popSTACK();
                 # beide vergleichen:
                 if (!((*up2_fun)(&STACK_(8+5+4),item1,item2))) # Testroutine anwenden
                   break;
                }
                # Test erf�llt -> weitervergleichen:
                # pointer1 := (SEQ-FE-UPD seq1 pointer1) :
                pointer_fe_update(STACK_3,STACK_(6+5+5+4),STACK_(1+5+4));
                # pointer2 := (SEQ-FE-UPD seq2 pointer2) :
                pointer_fe_update(STACK_2,STACK_(5+5+5+4),STACK_(0+5+4));
                # count1 decrementieren:
                decrement(STACK_1);
                # count2 decrementieren:
                decrement(STACK_0);
              }
            # Test nicht erf�llt -> weitersuchen
            skipSTACK(4); # pointer1, pointer2, count1, count2 vergessen
            # pointer20 weiterr�cken, len2 und index decrementieren:
            pointer_fe_update(STACK_3,STACK_(6+5+5),STACK_(0+5));
            decrement(STACK_1); # len2 := (1- len2)
            decrement(STACK_0); # index := (1- index)
      }   }
      else
      # from-end ist nicht angegeben
      { # start- und end-Argumente �berpr�fen:
        test_start_end_1(&O(kwpair_start1),&STACK_(3+5));
        test_start_end_1(&O(kwpair_start2),&STACK_(1+5));
        # pointer10 und pointer20 an den Anfang der Sequences setzen:
        { pushSTACK(STACK_(6+5)); pushSTACK(STACK_(4+5+1));
          funcall(seq_init_start(STACK_(1+2)),2); # (SEQ-INIT-START seq1 start1)
          pushSTACK(value1); # =: pointer10
        }
        { pushSTACK(STACK_(5+5+1)); pushSTACK(STACK_(2+5+1+1));
          funcall(seq_init_start(STACK_(0+1+2)),2); # (SEQ-INIT-START seq2 start2)
          pushSTACK(value1); # =: pointer20
        }
        init_endvar(&STACK_(3+5+2)); # endvar10 := (and end1 (- end1 start1))
        init_endvar(&STACK_(1+5+3)); # endvar20 := (and end2 (- end2 start2))
        pushSTACK(STACK_(2+5+4)); # index := start2
        # Stackaufbau: seq1, seq2, start1, end1, start2, end2, from-end,
        #              key, test, test-not, typdescr1, typdescr2,
        #              pointer10, pointer20, endvar10, endvar20, index.
        loop
          { # pointer1 und pointer2 ab pointer10 bzw. pointer20 laufen lassen:
            { pushSTACK(STACK_4); funcall(seq_copy(STACK_(1+5+1)),1); # (SEQ-COPY pointer10)
              pushSTACK(value1); # =: pointer1
            }
            { pushSTACK(STACK_(3+1)); funcall(seq_copy(STACK_(0+5+1+1)),1); # (SEQ-COPY pointer20)
              pushSTACK(value1); # =: pointer2
            }
            pushSTACK(STACK_(2+2)); # endvar1 := endvar10
            pushSTACK(STACK_(1+3)); # endvar2 := endvar20
            # Stackaufbau: seq1, seq2, from-end, start1, end1, start2, end2,
            #              key, test, test-not, typdescr1, typdescr2,
            #              pointer10, pointer20, endvar10, endvar20, index,
            #              pointer1, pointer2, endvar1, endvar2.
            loop
              { # Teste, ob seq1-Teilst�ck zu Ende. Wenn ja: gefunden.
                if (eq(STACK_1,Fixnum_0)) # endvar1 = 0 (und damit end1 /= nil) ?
                  { goto found; }
                  else
                  { pushSTACK(STACK_(6+5+5+4)); pushSTACK(STACK_(3+1));
                    funcall(seq_endtest(STACK_(1+5+4+2)),2); # (SEQ-ENDTEST seq1 pointer1)
                    if (!nullp(value1)) goto found;
                  }
                # seq1 ist noch nicht am Ende.
                # Teste, ob seq2-Teilst�ck zu Ende. Wenn ja: nicht gefunden.
                if (eq(STACK_0,Fixnum_0)) # endvar2 = 0 (und damit end2 /= nil) ?
                  { goto notfound; }
                  else
                  { pushSTACK(STACK_(5+5+5+4)); pushSTACK(STACK_(2+1));
                    funcall(seq_endtest(STACK_(0+5+4+2)),2); # (SEQ-ENDTEST seq2 pointer2)
                    if (!nullp(value1)) goto notfound;
                  }
                # seq2 ist noch nicht am Ende.
                pushSTACK(STACK_(6+5+5+4)); pushSTACK(STACK_(3+1));
                funcall(seq_access(STACK_(1+5+4+2)),2); # (SEQ-ACCESS seq1 pointer1)
                funcall_key(STACK_(4+5+4)); # (FUNCALL key (SEQ-ACCESS seq1 pointer1))
                pushSTACK(value1); # =: item1, retten
                pushSTACK(STACK_(5+5+5+4+1)); pushSTACK(STACK_(2+1+1));
                funcall(seq_access(STACK_(0+5+4+1+2)),2); # (SEQ-ACCESS seq2 pointer2)
                funcall_key(STACK_(4+5+4+1)); # (FUNCALL key (SEQ-ACCESS seq2 pointer2))
                {var object item2 = value1;
                 var object item1 = popSTACK();
                 # beide vergleichen:
                 if (!((*up2_fun)(&STACK_(8+5+4),item1,item2))) # Testroutine anwenden
                   break;
                }
                # Test erf�llt -> weitervergleichen:
                # pointer1 := (SEQ-UPD seq1 pointer1) :
                pointer_update(STACK_3,STACK_(6+5+5+4),STACK_(1+5+4));
                # pointer2 := (SEQ-UPD seq2 pointer2) :
                pointer_update(STACK_2,STACK_(5+5+5+4),STACK_(0+5+4));
                # endvar1 eventuell decrementieren:
                decrement_endvar(STACK_1);
                # endvar2 eventuell decrementieren:
                decrement_endvar(STACK_0);
              }
            # Test nicht erf�llt -> weitersuchen
            skipSTACK(4); # pointer1, pointer2, endvar1, endvar2 vergessen
            # pointer20 weiterr�cken:
            pointer_update(STACK_3,STACK_(6+5+5),STACK_(0+5));
            # endvar20 eventuell decrementieren:
            decrement_endvar(STACK_1);
            # index incrementieren:
            increment(STACK_0);
      }   }
    /*NOTREACHED*/
    found: # index als Wert
      { value1 = STACK_4; mv_count=1; skipSTACK(7+5+5+4); return; }
    notfound: # NIL als Wert
      { value1 = NIL; mv_count=1; skipSTACK(7+5+5+4); return; }
  }}

# UP f�r SORT, STABLE-SORT und MERGE:
# merge(stackptr);
# sortiert zwei sortierte Sequence-Teile in eine dritte Sequence zusammen.
# > STACK_10: sequence1
# > STACK_9: typdescr1
# > STACK_8: sequence2
# > STACK_7: typdescr2
# > STACK_6: sequence3
# > STACK_5: typdescr3
# > STACK_4: count1 (ein Integer >=0)
# > STACK_3: count2 (ein Integer >=0)
# > STACK_2: pointer1
# > STACK_1: pointer2
# > STACK_0: pointer3
# > stackptr: Pointer in den Stack,
#     *(stackptr+0) = predicate, *(stackptr-1) = key
# count1+count2 Elemente aus sequence1 oder sequence2 werden nach sequence3
# �bertragen (im Zweifelsfall die aus sequence1 zuerst).
# Dabei wird pointer1 genau  count1  mal weiterger�ckt (mit SEQ-UPD),
#            pointer2 genau  count2  mal weiterger�ckt (mit SEQ-UPD),
#            pointer3 genau  count1+count2  mal weiterger�ckt (mit SEQ-UPD).
# count1 und count2 werden auf 0 gesetzt.
# kann GC ausl�sen
  local void merge (object* stackptr);
  local void merge(stackptr)
    var object* stackptr;
    { loop
        { if (eq(STACK_4,Fixnum_0)) goto seq1_end; # count1 = 0 -> seq1 zu Ende
          if (eq(STACK_3,Fixnum_0)) goto seq2_end; # count1 = 0 -> seq2 zu Ende
          # item2 holen:
          { pushSTACK(STACK_8); pushSTACK(STACK_(1+1));
            funcall(seq_access(STACK_(7+2)),2); # (SEQ-ACCESS sequence2 pointer2)
            funcall_key(*(stackptr STACKop -1)); # (FUNCALL key (SEQ-ACCESS sequence2 pointer2))
            pushSTACK(value1); # =: item2
          }
          # item1 holen:
          { pushSTACK(STACK_(10+1)); pushSTACK(STACK_(2+1+1));
            funcall(seq_access(STACK_(9+1+2)),2); # (SEQ-ACCESS sequence1 pointer1)
            funcall_key(*(stackptr STACKop -1)); # (FUNCALL key (SEQ-ACCESS sequence1 pointer1))
            pushSTACK(value1); # =: item1
          }
          funcall(*(stackptr STACKop 0),2); # (FUNCALL predicate item2 item1)
          if (nullp(value1))
            # predicate lieferte NIL, item aus sequence1 �bernehmen:
            { pushSTACK(STACK_(10)); pushSTACK(STACK_(2+1));
              funcall(seq_access(STACK_(9+2)),2); # (SEQ-ACCESS sequence1 pointer1)
              pushSTACK(value1); # auf den Stack
              # pointer1 := (SEQ-UPD sequence1 pointer1) :
              pointer_update(STACK_(2+1),STACK_(10+1),STACK_(9+1));
              # count1 := (1- count1) :
              decrement(STACK_(4+1));
            }
            else
            # predicate war erf�llt, item aus sequence2 �bernehmen:
            { pushSTACK(STACK_(8)); pushSTACK(STACK_(1+1));
              funcall(seq_access(STACK_(7+2)),2); # (SEQ-ACCESS sequence2 pointer2)
              pushSTACK(value1); # auf den Stack
              # pointer2 := (SEQ-UPD sequence2 pointer2) :
              pointer_update(STACK_(1+1),STACK_(8+1),STACK_(7+1));
              # count2 := (1- count2) :
              decrement(STACK_(3+1));
            }
          {var object item = popSTACK(); # zu �bernehmendes item
           pushSTACK(STACK_6); pushSTACK(STACK_(0+1)); pushSTACK(item);
           funcall(seq_access_set(STACK_(5+3)),3); # (SEQ-ACCESS-SET sequence3 pointer3 item)
          }
          # pointer3 := (SEQ-UPD sequence3 pointer3) :
          pointer_update(STACK_0,STACK_6,STACK_5);
        }
      /*NOTREACHED*/
      seq1_end:
        # sequence1 zu Ende. Rest aus sequence2 �bernehmen:
        # Falls sequence2 und sequence3 EQ sind, liegt ein Aufruf
        # von SORT oder STABLE-SORT aus vor. Dort sind dann auch die
        # Pointer pointer2 und pointer3 gleich, also braucht gar nicht
        # mehr kopiert zu werden:
        if (eq(STACK_8,STACK_6)) # sequence2 = sequence3 ?
          { return; }
        until (eq(STACK_3,Fixnum_0)) # count2 = 0 ?
          { pushSTACK(STACK_(8)); pushSTACK(STACK_(1+1));
            funcall(seq_access(STACK_(7+2)),2); # (SEQ-ACCESS sequence2 pointer2)
            pushSTACK(STACK_6); pushSTACK(STACK_(0+1)); pushSTACK(value1);
            funcall(seq_access_set(STACK_(5+3)),3); # (SEQ-ACCESS-SET sequence3 pointer3 ...)
            # pointer2 := (SEQ-UPD sequence2 pointer2) :
            pointer_update(STACK_1,STACK_8,STACK_7);
            # count2 := (1- count2) :
            decrement(STACK_3);
            # pointer3 := (SEQ-UPD sequence3 pointer3) :
            pointer_update(STACK_0,STACK_6,STACK_5);
          }
        return;
      seq2_end:
        # sequence2 zu Ende, sequence1 nicht. Rest aus sequence1 nehmen:
        do { pushSTACK(STACK_(10)); pushSTACK(STACK_(2+1));
             funcall(seq_access(STACK_(9+2)),2); # (SEQ-ACCESS sequence1 pointer1)
             pushSTACK(STACK_6); pushSTACK(STACK_(0+1)); pushSTACK(value1);
             funcall(seq_access_set(STACK_(5+3)),3); # (SEQ-ACCESS-SET sequence3 pointer3 ...)
             # pointer1 := (SEQ-UPD sequence1 pointer1) :
             pointer_update(STACK_2,STACK_10,STACK_9);
             # count1 := (1- count1) :
             decrement(STACK_4);
             # pointer3 := (SEQ-UPD sequence3 pointer3) :
             pointer_update(STACK_0,STACK_6,STACK_5);
           }
           until (eq(STACK_4,Fixnum_0)); # count1 = 0 ?
        return;
    }

# UP: Sortiert in sequence ab pointer_left genau k Elemente (k >= 1)
# und liefert einen Pointer nach diesen k Elementen.
# sort_part(pointer_left,k,stackptr)
# pointer_left wird destruktiv ver�ndert.
# > pointer_left
# > k
# > stackptr: Pointer in den Stack:
#       sequence, predicate [stackptr], key, start, end, typdescr, seq2
# < ergebnis: Pointer nach den k Elementen
# kann GC ausl�sen
  local object sort_part (object pointer_left, object k, object* stackptr);
  local object sort_part(pointer_left,k,stackptr)
    var object pointer_left;
    var object k;
    var object* stackptr;
    { if (eq(k,Fixnum_1))
        { # k=1. Fast nichts zu tun
          pushSTACK(*(stackptr STACKop 1)); pushSTACK(pointer_left);
          funcall(seq_upd(*(stackptr STACKop -4)),2); # (SEQ-UPD sequence pointer_left)
          return value1; # als Ergebnis
        }
        else
        { # k>1.
          pushSTACK(pointer_left);
          pushSTACK(k);
          pushSTACK(I_I_ash_I(k,Fixnum_minus1)); # (ASH k -1) = (FLOOR k 2) =: kl
          STACK_1 = I_I_minus_I(STACK_1,STACK_0); # (- k (FLOOR k 2)) = (CEILING k 2) =: kr
          # Stackaufbau: pointer_left, kr, kl.
          # mit kl = (floor k 2) und kr = (ceiling k 2), also k = (+ kl kr).
          # rekursiv die linke H�lfte sortieren:
          { pushSTACK(STACK_2); # pointer_left
            funcall(seq_copy(*(stackptr STACKop -4)),1); # (SEQ-COPY pointer_left)
           {var object pointer_mid = sort_part(value1,STACK_0,stackptr);
            pushSTACK(pointer_mid);
          }}
          # Stackaufbau: pointer_left, kr, kl, pointer_mid.
          # rekursiv die rechte H�lfte sortieren:
          { pushSTACK(STACK_0); # pointer_mid
            funcall(seq_copy(*(stackptr STACKop -4)),1); # (SEQ-COPY pointer_mid)
           {var object pointer_right = sort_part(value1,STACK_2,stackptr);
            pushSTACK(pointer_right);
          }}
          # Stackaufbau: pointer_left, kr, kl, pointer_mid, pointer_right.
          # Linke H�lfte (sortiert) nach seq2 kopieren:
          { var object typdescr = *(stackptr STACKop -4);
            pushSTACK(*(stackptr STACKop 1)); # sequence
            pushSTACK(typdescr); # typdescr
            pushSTACK(*(stackptr STACKop -5)); # seq2
            pushSTACK(typdescr); # typdescr
            pushSTACK(STACK_(2+4)); # kl
            { pushSTACK(STACK_(4+5)); # pointer_left
              funcall(seq_copy(typdescr),1); # (SEQ-COPY pointer_left)
              pushSTACK(value1); # =: pointer1
            }
            typdescr = STACK_2;
            { pushSTACK(STACK_3); # seq2
              funcall(seq_init(typdescr),1); # (SEQ-INIT seq2)
              pushSTACK(value1); # =: pointer2
            }
            # Stackaufbau: pointer_left, kr, kl, pointer_mid, pointer_right,
            #              sequence, typdescr, seq2, typdescr, kl, pointer1, pointer2.
            copy_seqpart_into(); # kopieren
            skipSTACK(3);
          }
          # Stackaufbau: pointer_left, kr, kl, pointer_mid, pointer_right,
          #              sequence, typdescr, seq2, typdescr.
          { pushSTACK(STACK_3); # sequence
            pushSTACK(STACK_(2+1)); # typdescr
            pushSTACK(STACK_(3+2)); # sequence
            pushSTACK(STACK_(2+3)); # typdescr
            pushSTACK(STACK_(2+4+4)); # kl
            pushSTACK(STACK_(3+4+5)); # kr
            { pushSTACK(STACK_(1+6)); # seq2
              funcall(seq_init(STACK_(0+6+1)),1); # (SEQ-INIT seq2)
              pushSTACK(value1); # als Source-Pointer in seq2
            }
            pushSTACK(STACK_(1+4+7)); # pointer_mid als Source in sequence
            pushSTACK(STACK_(4+4+8)); # pointer_left als Destination in sequence
            merge(stackptr); # von seq2 nach sequence hineinmergen
            { var object pointer_right = STACK_(0+4+9); # pointer_right
              skipSTACK(5+4+9);
              return pointer_right; # als Ergebnis
        } } }
    }

# UP f�r SORT und STABLE-SORT: Sortiert einen Teil einer Sequence.
# stable_sort();
# > Stackaufbau: sequence, predicate, key, start, end
# < mv_space/mv_count: Werte
# kann GC ausl�sen
  local Values stable_sort (void);
  local Values stable_sort()
    { # Stackaufbau: sequence, predicate, key, start, end.
      # sequence �berpr�fen:
      pushSTACK(get_valid_seq_type(STACK_4)); # typdescr
      # Stackaufbau: sequence, predicate, key, start, end, typdescr.
      # Defaultwert f�r start ist 0 :
      start_default_0(STACK_2);
      # Defaultwert f�r end:
      end_default_len(STACK_1,STACK_5,STACK_0);
      # Argumente start und end �berpr�fen:
      test_start_end(&O(kwpair_start),&STACK_1);
      # key �berpr�fen:
      test_key_arg(&STACK_7);
      # l := (- end start), ein Integer >=0
     {var object l = I_I_minus_I(STACK_1,STACK_2);
      pushSTACK(l);
      # Stackaufbau: sequence, predicate, key, start, end, typdescr, l.
      if (!(eq(l,Fixnum_0))) # Bei l=0 ist nichts zu tun
        { # Hilfssequence der L�nge (floor l 2) erzeugen:
          { pushSTACK(I_I_ash_I(l,Fixnum_minus1)); # (ASH l -1) = (FLOOR l 2)
            funcall(seq_make(STACK_(1+1)),1); # (SEQ-MAKE (FLOOR l 2))
            pushSTACK(value1); # =: seq2
          }
          # Stackaufbau: sequence, predicate, key, start, end, typdescr, l,
          #              seq2.
          pushSTACK(STACK_(6+1)); pushSTACK(STACK_(3+1+1));
          funcall(seq_init_start(STACK_(1+1+2)),2); # (SEQ-INIT-START sequence start)
          l = STACK_(0+1); STACK_(0+1) = STACK_0; skipSTACK(1); # seq2 ersetzt l im Stack
          sort_part(value1,l,&STACK_5); # St�ck der L�nge l ab start sortieren
        }
      skipSTACK(6); value1 = popSTACK(); mv_count=1; # sortierte sequence als Wert
    }}

LISPFUN(sort,2,0,norest,key,3, (kw(key),kw(start),kw(end)) )
# (SORT sequence predicate [:key] [:start] [:end]), CLTL S. 258
  { return_Values stable_sort(); }

LISPFUN(stable_sort,2,0,norest,key,3, (kw(key),kw(start),kw(end)) )
# (STABLE-SORT sequence predicate [:key] [:start] [:end]), CLTL S. 258
  { return_Values stable_sort(); }

LISPFUN(merge,4,0,norest,key,1, (kw(key)) )
# (MERGE result-type sequence1 sequence2 predicate [:key]), CLTL S. 260
  { # Stackaufbau: result-type, sequence1, sequence2, predicate, key.
    # key-Argument �berpr�fen:
    test_key_arg(&STACK_4);
    # sequence1 �berpr�fen:
    {var object seq1 = STACK_3;
     pushSTACK(seq1);
     pushSTACK(get_valid_seq_type(seq1));
    }
    # sequence2 �berpr�fen:
    {var object seq2 = STACK_(2+2);
     pushSTACK(seq2);
     pushSTACK(get_valid_seq_type(seq2));
    }
    # result-type �berpr�fen:
    {var object typdescr3 = valid_type(STACK_(4+4));
     pushSTACK(typdescr3);
    }
    # Stackaufbau: result-type, sequence1, sequence2, predicate, key,
    #              sequence1, typdescr1, sequence2, typdescr2, result-type-len, typdescr3.
    # L�ngen von sequence1 und sequence2 bestimmen:
    { pushSTACK(STACK_5); funcall(seq_length(STACK_(4+1)),1); # (SEQ-LENGTH sequence1)
      pushSTACK(value1); # =: len1
    }
    { pushSTACK(STACK_(3+1)); funcall(seq_length(STACK_(2+1+1)),1); # (SEQ-LENGTH sequence2)
      pushSTACK(value1); # =: len2
    }
    # beide L�ngen addieren und neue Sequence der Gesamtl�nge bilden:
    { pushSTACK(I_I_plus_I(STACK_1,STACK_0)); # (+ len1 len2)
      if (!(eq(STACK_(1+3),unbound) || eql(STACK_0,STACK_(1+3))))
        { fehler_seqtype_length(STACK_(1+3),STACK_0); }
      funcall(seq_make(STACK_(0+2+1)),1); # (SEQ-MAKE (+ len1 len2))
      STACK_(1+2) = value1; # ersetzt result-type-len im Stack
    }
    # Stackaufbau: result-type, sequence1, sequence2, predicate, key,
    #              sequence1, typdescr1, sequence2, typdescr2, sequence3, typdescr3,
    #              len1, len2.
    # Pointer an den Anfang der Sequences bestimmen:
    { pushSTACK(STACK_(5+2)); funcall(seq_init(STACK_(4+2+1)),1); # (SEQ-INIT sequence1)
      pushSTACK(value1); # =: pointer1
    }
    { pushSTACK(STACK_(3+2+1)); funcall(seq_init(STACK_(2+2+1+1)),1); # (SEQ-INIT sequence2)
      pushSTACK(value1); # =: pointer2
    }
    { pushSTACK(STACK_(1+2+2)); funcall(seq_init(STACK_(0+2+2+1)),1); # (SEQ-INIT sequence3)
      pushSTACK(value1); # =: pointer3
    }
    # Stackaufbau: result-type, sequence1, sequence2, predicate, key,
    #              sequence1, typdescr1, sequence2, typdescr2, sequence3, typdescr3,
    #              len1, len2, pointer1, pointer2, pointer3.
    # Merge-Operation durchf�hren:
    merge(&STACK_(1+6+5));
    value1 = STACK_(1+5); mv_count=1; # sequence3 als Wert
    skipSTACK(5+6+5);
  }

LISPFUN(read_char_sequence,2,0,norest,key,2, (kw(start),kw(end)) )
# (READ-CHAR-SEQUENCE sequence stream [:start] [:end]), cf. dpANS S. 21-26
  { # Stackaufbau: sequence, stream, start, end.
    # sequence �berpr�fen:
    pushSTACK(get_valid_seq_type(STACK_3));
    # Stackaufbau: sequence, stream, start, end, typdescr.
    # Stream �berpr�fen:
    if (!streamp(STACK_3)) { fehler_stream(STACK_3); }
    # Defaultwert f�r start ist 0:
    start_default_0(STACK_2);
    # Defaultwert f�r end ist die L�nge der Sequence:
    end_default_len(STACK_1,STACK_4,STACK_0);
    # start- und end-Argumente �berpr�fen:
    test_start_end(&O(kwpair_start),&STACK_1);
    if (eq(seq_type(STACK_0),S(string))) # Typname = STRING ?
      { var uintL len;
        var uintB* charptr = unpack_string(STACK_4,&len);
        # Ab charptr kommen len Zeichen.
        var uintL start = posfixnum_to_L(STACK_2);
        var uintL end = posfixnum_to_L(STACK_1);
        # Versuche, eine optimierte Lese-Routine aufzurufen:
        var uintB* endptr = read_char_array(STACK_3,&charptr[start],end-start);
        if (!(endptr==NULL))
          { value1 = fixnum(endptr-charptr); mv_count=1;
            skipSTACK(5);
            return;
      }   }
    # Durchlauf-Pointer bestimmen:
    pushSTACK(STACK_4); pushSTACK(STACK_(2+1));
    funcall(seq_init_start(STACK_(0+2)),2); # (SEQ-INIT-START sequence start)
    pushSTACK(value1); # =: pointer
    # Stackaufbau: sequence, stream, index, end, typdescr, pointer.
    until (eql(STACK_3,STACK_2)) # index = end (beides Integers) -> fertig
      { var object item = read_char(&STACK_4); # ein Element lesen
        if (eq(item,eof_value)) break; # EOF -> fertig
        pushSTACK(STACK_5); pushSTACK(STACK_(0+1)); pushSTACK(item);
        funcall(seq_access_set(STACK_(1+3)),3); # (SEQ-ACCESS-SET sequence pointer item)
        # pointer := (SEQ-UPD sequence pointer) :
        pointer_update(STACK_0,STACK_5,STACK_1);
        # index := (1+ index) :
        increment(STACK_3);
      }
    value1 = STACK_3; mv_count=1; # index als Wert
    skipSTACK(6);
  }

LISPFUN(write_char_sequence,2,0,norest,key,2, (kw(start),kw(end)) )
# (WRITE-CHAR-SEQUENCE sequence stream [:start] [:end]), cf. dpANS S. 21-27
  { # Stackaufbau: sequence, stream, start, end.
    # sequence �berpr�fen:
    pushSTACK(get_valid_seq_type(STACK_3));
    # Stackaufbau: sequence, stream, start, end, typdescr.
    # Stream �berpr�fen:
    if (!streamp(STACK_3)) { fehler_stream(STACK_3); }
    # Defaultwert f�r start ist 0:
    start_default_0(STACK_2);
    # Defaultwert f�r end ist die L�nge der Sequence:
    end_default_len(STACK_1,STACK_4,STACK_0);
    # start- und end-Argumente �berpr�fen:
    test_start_end(&O(kwpair_start),&STACK_1);
    if (eq(seq_type(STACK_0),S(string))) # Typname = STRING ?
      { var uintL len;
        var const uintB* charptr = unpack_string(STACK_4,&len);
        # Ab charptr kommen len Zeichen.
        var uintL start = posfixnum_to_L(STACK_2);
        var uintL end = posfixnum_to_L(STACK_1);
        # Versuche, eine optimierte Schreib-Routine aufzurufen:
        var const uintB* endptr = write_char_array(STACK_3,&charptr[start],end-start);
        if (!(endptr==NULL)) goto done;
      }
    # start- und end-Argumente subtrahieren:
    STACK_1 = I_I_minus_I(STACK_1,STACK_2); # (- end start), ein Integer >=0
    # Stackaufbau: sequence, item, start, count, typdescr.
    # Durchlauf-Pointer bestimmen:
    pushSTACK(STACK_4); pushSTACK(STACK_(2+1));
    funcall(seq_init_start(STACK_(0+2)),2); # (SEQ-INIT-START sequence start)
    STACK_2 = value1; # =: pointer
    # Stackaufbau: sequence, stream, pointer, count, typdescr.
    until (eq(STACK_1,Fixnum_0)) # count (ein Integer) = 0 -> fertig
      { pushSTACK(STACK_4); pushSTACK(STACK_(2+1));
        funcall(seq_access(STACK_(0+2)),2); # (SEQ-ACCESS sequence pointer)
        write_char(&STACK_3,value1); # ein Element ausgeben
        # pointer := (SEQ-UPD sequence pointer) :
        pointer_update(STACK_2,STACK_4,STACK_0);
        # count := (1- count) :
        decrement(STACK_1);
      }
    done:
    skipSTACK(4);
    value1 = popSTACK(); mv_count=1; # sequence als Wert
  }

LISPFUN(read_byte_sequence,2,0,norest,key,2, (kw(start),kw(end)) )
# (READ-BYTE-SEQUENCE sequence stream [:start] [:end]), cf. dpANS S. 21-26
  { # Stackaufbau: sequence, stream, start, end.
    # sequence �berpr�fen:
    pushSTACK(get_valid_seq_type(STACK_3));
    # Stackaufbau: sequence, stream, start, end, typdescr.
    # Stream �berpr�fen:
    if (!streamp(STACK_3)) { fehler_stream(STACK_3); }
    # Defaultwert f�r start ist 0:
    start_default_0(STACK_2);
    # Defaultwert f�r end ist die L�nge der Sequence:
    end_default_len(STACK_1,STACK_4,STACK_0);
    # start- und end-Argumente �berpr�fen:
    test_start_end(&O(kwpair_start),&STACK_1);
    if (eq(seq_type(STACK_0),fixnum(8))) # Typname = (VECTOR (UNSIGNED-BYTE 8)) ?
      { var uintL start = posfixnum_to_L(STACK_2);
        var uintL end = posfixnum_to_L(STACK_1);
        var uintL index = 0;
        var object dv = iarray_displace_check(STACK_4,end,&index);
        var uintB* byteptr = &TheSbvector(TheIarray(dv)->data)->data[index];
        # Ab byteptr kommen end Bytes.
        # Versuche, eine optimierte Lese-Routine aufzurufen:
        var uintB* endptr = read_byte_array(STACK_3,&byteptr[start],end-start);
        if (!(endptr==NULL))
          { value1 = fixnum(endptr-byteptr); mv_count=1;
            skipSTACK(5);
            return;
      }   }
    # Durchlauf-Pointer bestimmen:
    pushSTACK(STACK_4); pushSTACK(STACK_(2+1));
    funcall(seq_init_start(STACK_(0+2)),2); # (SEQ-INIT-START sequence start)
    pushSTACK(value1); # =: pointer
    # Stackaufbau: sequence, stream, index, end, typdescr, pointer.
    until (eql(STACK_3,STACK_2)) # index = end (beides Integers) -> fertig
      { var object item = read_byte(STACK_4); # ein Element lesen
        if (eq(item,eof_value)) break; # EOF -> fertig
        pushSTACK(STACK_5); pushSTACK(STACK_(0+1)); pushSTACK(item);
        funcall(seq_access_set(STACK_(1+3)),3); # (SEQ-ACCESS-SET sequence pointer item)
        # pointer := (SEQ-UPD sequence pointer) :
        pointer_update(STACK_0,STACK_5,STACK_1);
        # index := (1+ index) :
        increment(STACK_3);
      }
    value1 = STACK_3; mv_count=1; # index als Wert
    skipSTACK(6);
  }

LISPFUN(write_byte_sequence,2,0,norest,key,2, (kw(start),kw(end)) )
# (WRITE-BYTE-SEQUENCE sequence stream [:start] [:end]), cf. dpANS S. 21-27
  { # Stackaufbau: sequence, stream, start, end.
    # sequence �berpr�fen:
    pushSTACK(get_valid_seq_type(STACK_3));
    # Stackaufbau: sequence, stream, start, end, typdescr.
    # Stream �berpr�fen:
    if (!streamp(STACK_3)) { fehler_stream(STACK_3); }
    # Defaultwert f�r start ist 0:
    start_default_0(STACK_2);
    # Defaultwert f�r end ist die L�nge der Sequence:
    end_default_len(STACK_1,STACK_4,STACK_0);
    # start- und end-Argumente �berpr�fen:
    test_start_end(&O(kwpair_start),&STACK_1);
    if (eq(seq_type(STACK_0),fixnum(8))) # Typname = (VECTOR (UNSIGNED-BYTE 8)) ?
      { var uintL start = posfixnum_to_L(STACK_2);
        var uintL end = posfixnum_to_L(STACK_1);
        var uintL index = 0;
        var object dv = iarray_displace_check(STACK_4,end,&index);
        var const uintB* byteptr = &TheSbvector(TheIarray(dv)->data)->data[index];
        # Ab byteptr kommen end Bytes.
        # Versuche, eine optimierte Schreib-Routine aufzurufen:
        var const uintB* endptr = write_byte_array(STACK_3,&byteptr[start],end-start);
        if (!(endptr==NULL)) goto done;
      }
    # start- und end-Argumente subtrahieren:
    STACK_1 = I_I_minus_I(STACK_1,STACK_2); # (- end start), ein Integer >=0
    # Stackaufbau: sequence, item, start, count, typdescr.
    # Durchlauf-Pointer bestimmen:
    pushSTACK(STACK_4); pushSTACK(STACK_(2+1));
    funcall(seq_init_start(STACK_(0+2)),2); # (SEQ-INIT-START sequence start)
    STACK_2 = value1; # =: pointer
    # Stackaufbau: sequence, stream, pointer, count, typdescr.
    until (eq(STACK_1,Fixnum_0)) # count (ein Integer) = 0 -> fertig
      { pushSTACK(STACK_4); pushSTACK(STACK_(2+1));
        funcall(seq_access(STACK_(0+2)),2); # (SEQ-ACCESS sequence pointer)
        write_byte(STACK_3,value1); # ein Element ausgeben
        # pointer := (SEQ-UPD sequence pointer) :
        pointer_update(STACK_2,STACK_4,STACK_0);
        # count := (1- count) :
        decrement(STACK_1);
      }
    done:
    skipSTACK(4);
    value1 = popSTACK(); mv_count=1; # sequence als Wert
  }

