; Sources f�r DEFSTRUCT Macro.
; Bruno Haible 13.04.1988, 22.08.1988
; umgeschrieben am 02.09.1989 von Bruno Haible

(in-package "SYSTEM")

(defsetf %structure-ref %structure-store)

#| Erkl�rung der auftretenden Datentypen:

   (get name 'DEFSTRUCT-DESCRIPTION) =
     #(names type keyword-constructor slotlist defaultfun0 defaultfun1 ...)

   names ist eine Codierung der INCLUDE-Verschachtelung f�r Structure name:
   names = (name_1 ... name_i-1 name_i) wobei name=name_1,
     name_1 enth�lt name_2, ..., name_i-1 enth�lt name_i.

   type (wenn der Typ der ganzen Structure gemeint ist):
      = T                      Abspeicherung als normale Structure
      = LIST                   Abspeicherung als Liste
      = VECTOR                 Abspeicherung als (simple-)Vector
      = (VECTOR element-type)  Abspeicherung als Vector mit Element-Typ

   keyword-constructor = NIL oder der Name des Keyword-Constructor

   slotlist ist eine gepackte Beschreibung der einzelnen slots einer Structure:
   slotlist = ({slot}*)
   slot = #(name initargs offset initer default type readonly)
   wobei name der Slotname ist,
              (NIL f�r den Slot, in dem der Structure-Name steht)
         default der Defaultwert ist:
              entweder eine Konstante, die zum Defaultwert evaluiert,
              oder eine Form (ein Symbol oder eine Liste (SVREF ...)), die
              bei Auswertung in einem beliebigen Environment eine Funktion
              liefert, die bei Aufruf den Defaultwert liefert.
         type der deklarierte Type f�r diesen Slot ist,
         readonly = NIL oder = T angibt, ob dieser Slot readonly ist, d.h.
              nach dem Aufbau der Structure nicht mehr mit (setf ...)
              ver�ndert werden kann.
   Bei type = T belegt der Structure-Name den Slot 0, wird aber nicht in der
     slotlist aufgef�hrt, da zu seiner Initialisierung nichts zu tun ist.

|#

(defun make-ds-slot (name initargs offset initer default type readonly)
  (vector name initargs offset initer default type readonly)
)
(proclaim '(inline ds-slot-name))
(defun ds-slot-name (slot) (svref slot 0))
;(defun ds-slot-initargs (slot) (svref slot 1)) ; only used in clos.lsp
(defmacro ds-slot-offset (slot) `(svref ,slot 2))
(defmacro ds-slot-initer (slot) `(svref ,slot 3)) ; used in clos.lsp
(defmacro ds-slot-default (slot) `(svref ,slot 4))
(defmacro ds-slot-type (slot) `(svref ,slot 5))
(defmacro ds-slot-readonly (slot) `(svref ,slot 6))
(defun copy-ds-slot (slot) (sys::%copy-simple-vector slot))

#| (ds-symbol-or-error x) liefert eine Fehlermeldung, falls x kein Symbol ist.
|#
(defun ds-symbol-or-error (x)
  (unless (symbolp x)
    (error-of-type 'source-program-error
      (DEUTSCH "~S: Das ist kein Symbol: ~S"
       ENGLISH "~S: this is not a symbol: ~S"
       FRANCAIS "~S : Ceci n'est pas un symbole: ~S")
      'defstruct x
) ) )

#| Hilfsfunktion f�r beide Konstruktoren:
   (ds-arg-default arg slot)
   liefert zu einem Argument arg (Teil einer Argumentliste) den Teil der
   Argumentliste, der dieses Argument mit dem Default f�r slot bindet.
|#

(defun ds-arg-default (arg slot)
  (let ((default (ds-slot-default slot)))
    ; Default ist entweder Konstante oder Funktion oder Symbol
    (if (constantp default)
      (if (null default)
        (if (symbolp arg) arg `(,arg))
        `(,arg ,default)
      )
      `(,arg (SYS::%FUNCALL ,default))
) ) )

#| Hilfsfunktion f�r beide Konstruktoren:
   (ds-make-constructor-body type name names size slotlist)
   liefert den Ausdruck, der eine Structure vom vorgegebenen Typ
   kreiert und f�llt.
|#
(defun ds-make-constructor-body (type name names size slotlist)
  (if (and (eq type 'VECTOR)
           (do ((slotlistr slotlist (cdr slotlistr))
                (index 0 (1+ index)))
               ((null slotlistr) t)
             (unless (eq (ds-slot-offset (car slotlistr)) index) (return nil))
      )    )
    ; optimize the usual case
    `(VECTOR ,@(mapcar #'(lambda (slot)
                           (if (ds-slot-name slot)
                             `(THE ,(ds-slot-type slot) ,(ds-slot-name slot))
                             `(QUOTE ,(ds-slot-default slot))
                         ) )
                       slotlist
               )
     )
    `(LET ((OBJECT
             ,(cond ((eq type 'T) `(%MAKE-STRUCTURE ,names ,size))
                    ((eq type 'LIST) `(MAKE-LIST ,size))
                    ((consp type) `(MAKE-ARRAY ,size :ELEMENT-TYPE ',(second type)))
                    (t `(MAKE-ARRAY ,size))
              )
          ))
       ,@(mapcar
           #'(lambda (slot &aux (offset (ds-slot-offset slot)))
               `(SETF
                  ,(cond ((eq type 'T)
                          `(%STRUCTURE-REF ',name OBJECT ,offset) )
                         ((eq type 'LIST)
                          `(NTH ,offset OBJECT) )
                         ((eq type 'VECTOR)
                          `(SVREF OBJECT ,offset) )
                         (t `(AREF OBJECT ,offset) )
                   )
                  ,(if (ds-slot-name slot)
                     `(THE ,(ds-slot-type slot) ,(ds-slot-name slot))
                     `(QUOTE ,(ds-slot-default slot))
                )  )
             )
           slotlist
         )
       OBJECT
     )
) )

#| Hilfsfunktion f�r ds-make-boa-constructor:

   (ds-arg-with-default arg slotlist)
   liefert zu einem Argument arg (Teil einer Argumentliste) den Teil der
   Argumentliste, der dieses Argument mit dem richtigen Defaultwert bindet.
|#

(defun ds-arg-with-default (arg slotlist)
  (if (and (listp arg) (consp (cdr arg)))
    ; Defaultwert ist bereits mitgegeben
    arg
    ; kein Defaultwert in der Lambda-Liste
    (let* ((var (if (listp arg) (first arg) arg))
           (slot (find (if (consp var) (second var) var) slotlist :key #'ds-slot-name :test #'eq)))
      (if slot
        ; Slot gefunden -> dessen Defaultwert nehmen
        (ds-arg-default arg slot)
        ; Slot nicht gefunden, kein Defaultwert
        arg
) ) ) )

#| (ds-make-boa-constructor descriptor type name names size slotlist)
   liefert die Form, die den BOA-Konstrukor definiert.
|#
(defun ds-make-boa-constructor (descriptor type name names size slotlist)
  (let ((constructorname (first descriptor))
        (arglist (second descriptor)))
    ; angegebene Argumente sammeln:
    (let* ((argnames
             (let ((L nil))
               (dolist (arg arglist)
                 (unless (member arg lambda-list-keywords :test #'eq)
                   (let ((var (if (listp arg) (first arg) arg)))
                     (push (if (consp var) (second var) var) L)
               ) ) )
               (nreverse L)
           ) )
           ; argnames ist die Liste aller bereits in der Parameterliste mit
           ; Werten versehenen Argumente.
           (new-arglist ; neue Argumentliste
             `(; required args:
               ,@(do ((arglistr arglist (cdr arglistr))
                      (arg)
                      (required-args nil))
                     ((or (endp arglistr)
                          (member (setq arg (car arglistr)) lambda-list-keywords :test #'eq)
                      )
                      (nreverse required-args)
                     )
                   (push arg required-args)
                 )
               ; optional args:
               ,@(do ((arglistr (cdr (member '&optional arglist :test #'eq)) (cdr arglistr))
                      (arg)
                      (optionals nil))
                     ((or (endp arglistr)
                          (member (setq arg (car arglistr)) lambda-list-keywords :test #'eq)
                      )
                      (if (null optionals) nil (cons '&optional (nreverse optionals)))
                     )
                   (push (ds-arg-with-default arg slotlist) optionals)
                 )
               ; rest arg:
               ,@(let ((arglistr (member '&rest arglist :test #'eq)))
                   (if arglistr `(&rest ,(second arglistr)) '())
                 )
               ; key args:
               ,@(do ((arglistr (cdr (member '&key arglist :test #'eq)) (cdr arglistr))
                      (arg)
                      (keys nil))
                     ((or (endp arglistr)
                          (member (setq arg (car arglistr)) lambda-list-keywords :test #'eq)
                      )
                      (setq keys (nreverse keys))
                      (if (and (consp arglistr) (eq (car arglistr) '&allow-other-keys))
                        (progn (pop arglistr) `(&key ,@keys &allow-other-keys))
                        (if (null keys) nil `(&key ,@keys))
                     ))
                   (push (ds-arg-with-default arg slotlist) keys)
                 )
               ; aux args:
               &aux
               ,@(do ((aux-args-r (cdr (member '&aux arglist :test #'eq)) (cdr aux-args-r))
                      (aux-arg)
                      (new-aux-args nil))
                     ((or (null aux-args-r)
                          (member (setq aux-arg (car aux-args-r)) lambda-list-keywords :test #'eq)
                      )
                      (nreverse new-aux-args)
                     )
                   (push (ds-arg-with-default aux-arg slotlist) new-aux-args)
                 )
               ,@(let ((slotinitlist nil))
                   (dolist (slot slotlist)
                     (when (ds-slot-name slot)
                       (unless (member (ds-slot-name slot) argnames :test #'eq)
                         (push (ds-arg-with-default (ds-slot-name slot) slotlist) slotinitlist)
                   ) ) )
                   (nreverse slotinitlist)
              )  )
          ))
      `(DEFUN ,constructorname ,new-arglist
         ,(ds-make-constructor-body type name names size slotlist)
       )
) ) )

#| (ds-make-keyword-constructor descriptor type name names size slotlist)
   liefert die Form, die den Keyword-Konstruktor definiert.
|#
(defun ds-make-keyword-constructor (descriptor type name names size slotlist)
  `(DEFUN ,descriptor
     (&KEY
      ,@(mapcap
          #'(lambda (slot)
              (if (ds-slot-name slot)
                (list (ds-arg-default (ds-slot-name slot) slot))
                '()
            ) )
          slotlist
     )  )
     ,(ds-make-constructor-body type name names size slotlist)
)  )

#| (ds-make-pred predname type name name-offset)
   liefert die Form, die das Typtestpr�dikat f�r die Structure name kreiert.
   Dabei ist:
   type         der Typ der Structure,
   name         der Name der Structure,
   predname     der Name des Typtestpr�dikats,
   name-offset  (nur bei type /= T ma�geblich)
                die Stelle, an der der Name abgespeichert wird.
|#
(defun ds-make-pred (predname type name name-offset)
  `(,@(if (eq type 'T) `((PROCLAIM '(INLINE ,predname))) '())
    (DEFUN ,predname (OBJECT)
      ,(if (eq type 'T)
         `(%STRUCTURE-TYPE-P ',name OBJECT)
         (if (eq type 'LIST)
           `(AND (CONSP OBJECT)
                 ,@(if (eql name-offset 0)
                     `((EQ (CAR OBJECT) ',name))
                     `((> (LENGTH OBJECT) ,name-offset)
                       (EQ (NTH ,name-offset OBJECT) ',name)
                      )
            )      )
           `(AND (SIMPLE-VECTOR-P OBJECT)
                 (> (LENGTH OBJECT) ,name-offset)
                 (EQ (SVREF OBJECT ,name-offset) ',name)
            )
       ) )
   ))
)

(defun ds-make-copier (copiername name type)
  (declare (ignore name))
  `(,@(if (or (eq type 'T) (eq type 'LIST))
        `((PROCLAIM '(INLINE ,copiername)))
        '()
      )
    (DEFUN ,copiername (STRUCTURE)
      ,(if (eq type 'T)
         '(COPY-STRUCTURE STRUCTURE)
         (if (eq type 'LIST)
           '(COPY-LIST STRUCTURE)
           (if (consp type)
             `(LET* ((OBJ-LENGTH (ARRAY-TOTAL-SIZE STRUCTURE))
                     (OBJECT (MAKE-ARRAY OBJ-LENGTH :ELEMENT-TYPE (QUOTE ,(second type))))
                    )
                (DOTIMES (I OBJ-LENGTH OBJECT)
                  (SETF (AREF OBJECT I) (AREF STRUCTURE I))
              ) )
             '(%COPY-SIMPLE-VECTOR STRUCTURE)
       ) ) )
)  ))

(defun ds-make-accessors (name type concname slotlist)
  (mapcap
    #'(lambda (slot)
        (if (ds-slot-name slot)
          (let ((accessorname (concat-pnames concname (ds-slot-name slot)))
                (offset (ds-slot-offset slot))
                (slottype (ds-slot-type slot)))
            `((PROCLAIM '(FUNCTION ,accessorname (,name) ,slottype))
              (PROCLAIM '(INLINE ,accessorname))
              (DEFUN ,accessorname (OBJECT)
                (THE ,slottype
                  ,(if (eq type 'T)
                     `(%STRUCTURE-REF ',name OBJECT ,offset)
                     (if (eq type 'LIST)
                       `(NTH ,offset OBJECT)
                       (if (consp type)
                         `(AREF OBJECT ,offset)
                         `(SVREF OBJECT ,offset)
             )) )  ) ) )
          )
          '()
      ) )
    slotlist
) )

(defun ds-make-defsetfs (name type concname slotlist)
  (mapcap
    #'(lambda (slot)
        (if (and (ds-slot-name slot) (not (ds-slot-readonly slot)))
          (let ((accessorname (concat-pnames concname (ds-slot-name slot)))
                (offset (ds-slot-offset slot))
                (slottype (ds-slot-type slot)))
            `((DEFSETF ,accessorname (STRUCT) (VALUE)
                ,(if (eq type 'T)
                   `(LIST '%STRUCTURE-STORE '',name
                      STRUCT
                      ,offset
                      ,(if (eq 'T slottype)
                         `VALUE
                         `(LIST 'THE ',slottype VALUE)
                    )  )
                   (if (eq type 'LIST)
                     `(LIST 'SETF (LIST 'NTH ,offset STRUCT) VALUE)
                     (if (consp type)
                       `(LIST 'SETF (LIST 'AREF STRUCT ,offset) VALUE)
                       `(LIST 'SETF (LIST 'SVREF STRUCT ,offset) VALUE)
             ))  ) ) )
      ) ) )
    slotlist
) )

; Zwei Hooks f�r CLOS
(defun clos::define-structure-class (name) (declare (ignore name)) ; vorl�ufig
  (system::note-new-structure-class)
)
(defun clos::defstruct-remove-print-object-method (name) (declare (ignore name)) ; vorl�ufig
  nil
)

(defmacro defstruct (name-and-options . docstring-and-slotargs)
  (let ((name                              name-and-options)
        (options                           nil)
        (conc-name-option                  t)
        (constructor-option-list           nil)
        (keyword-constructor               nil)
        (copier-option                     t)
        (predicate-option                  0)
        (include-option                    nil)
         names
         namesform
        (namesbinding                      nil)
        (print-object-option               nil)
        (type-option                       t)
        (named-option                      0)
        (initial-offset-option             0)
        (initial-offset                    0)
        (docstring                         nil)
        (slotargs                          docstring-and-slotargs)
         size
        (include-skip                      0)
        (inherited-slot-count              0)
        (slotlist                          nil)
        (slotdefaultvars                   nil)
        (slotdefaultfuns                   nil)
         constructor-forms                      )
    ;; name-and-options �berpr�fen:
    (when (listp name-and-options)
      (setq name (first name-and-options))
      (setq options (rest name-and-options))
    ) ; andernfalls sind name und options schon korrekt.
    (unless (and (symbolp name) (not (keywordp name)))
      (error-of-type 'source-program-error
        (DEUTSCH "~S: Falsche Syntax f�r Name und Optionen: ~S"
         ENGLISH "~S: invalid syntax for name and options: ~S"
         FRANCAIS "~S : Mauvaise syntaxe pour un nom et des options: ~S")
        'defstruct name-and-options
    ) )
    ; name ist ein Symbol, options die Liste der Optionen.
    ;; Abarbeitung der Optionen:
    (dolist (option options)
      (when (keywordp option) (setq option (list option))) ; Option ohne Argumente
      (if (listp option)
        (if (keywordp (car option))
          (case (first option)
            (:CONC-NAME
               (setq conc-name-option (or (second option) ""))
            )
            (:CONSTRUCTOR
               (if (atom (cdr option))
                 ; Default-Keyword-Constructor
                 (push (concat-pnames "MAKE-" name) constructor-option-list)
                 (let ((arg (second option)))
                   (ds-symbol-or-error arg)
                   (push
                     (if (atom (cddr option))
                       arg ; Keyword-Constructor
                       (if (not (listp (third option)))
                         (error-of-type 'source-program-error
                           (DEUTSCH "~S ~S: Argumentliste mu� eine Liste sein: ~S"
                            ENGLISH "~S ~S: argument list should be a list: ~S"
                            FRANCAIS "~S ~S : La liste d'arguments doit �tre une liste: ~S")
                           'defstruct name (third option)
                         )
                         (rest option) ; BOA-Constructor
                     ) )
                     constructor-option-list
            )  ) ) )
            (:COPIER
               (when (consp (cdr option))
                 (let ((arg (second option)))
                   (ds-symbol-or-error arg)
                   (setq copier-option arg)
            )  ) )
            (:PREDICATE
               (when (consp (cdr option))
                 (let ((arg (second option)))
                   (ds-symbol-or-error arg)
                   (setq predicate-option arg)
            )  ) )
            ((:INCLUDE :INHERIT)
               (if (null include-option)
                 (setq include-option option)
                 (error-of-type 'source-program-error
                   (DEUTSCH "~S ~S: Es darf nur ein :INCLUDE-Argument geben: ~S"
                    ENGLISH "~S ~S: At most one :INCLUDE argument may be specified: ~S"
                    FRANCAIS "~S ~S : Il ne peut y avoir qu'un argument :INCLUDE: ~S")
                   'defstruct name options
            )  ) )
            ((:PRINT-FUNCTION :PRINT-OBJECT)
               (if (null (cdr option))
                 (setq print-object-option '(PRINT-STRUCTURE STRUCT STREAM))
                 (let ((arg (second option)))
                   (when (and (consp arg) (eq (first arg) 'FUNCTION))
                     (warn (DEUTSCH "~S: Bei ~S ist FUNCTION bereits implizit.~@
                                     Verwende daher ~S statt ~S."
                            ENGLISH "~S: Use of ~S implicitly applies FUNCTION.~@
                                     Therefore using ~S instead of ~S."
                            FRANCAIS "~S : FUNCTION est d�j� implicite avec ~S.~@
                                      C'est pourquoi ~S est utilis� au lieu de ~S.")
                           'defstruct (first option) (second arg) arg
                     )
                     (setq arg (second arg))
                   )
                   (setq print-object-option
                     `(,arg STRUCT STREAM ,@(if (eq (first option) ':PRINT-FUNCTION) '(*PRIN-LEVEL*) '()))
            )  ) ) )
            (:TYPE (setq type-option (second option)))
            (:NAMED (setq named-option t))
            (:INITIAL-OFFSET (setq initial-offset-option (or (second option) 0)))
            (T (error-of-type 'source-program-error
                 (DEUTSCH "~S ~S: Die Option ~S gibt es nicht."
                  ENGLISH "~S ~S: unknown option ~S"
                  FRANCAIS "~S ~S : Option ~S non reconnue.")
                 'defstruct name (first option)
          ) )  )
          (error-of-type 'source-program-error
            (DEUTSCH "~S ~S: Falsche Syntax in ~S-Option: ~S"
             ENGLISH "~S ~S: invalid syntax in ~S option: ~S"
             FRANCAIS "~S ~S : Mauvaise syntaxe dans l'option ~S: ~S")
            'defstruct name 'defstruct option
        ) )
        (error-of-type 'source-program-error
          (DEUTSCH "~S ~S: Das ist keine ~S-Option: ~S"
           ENGLISH "~S ~S: not a ~S option: ~S"
           FRANCAIS "~S ~S : Ceci n'est pas une option ~S: ~S")
          'defstruct name 'defstruct option
    ) ) )
    ; conc-name-option ist entweder T oder "" oder das :CONC-NAME-Argument.
    ; constructor-option-list ist eine Liste aller :CONSTRUCTOR-Argumente,
    ;   jeweils in der Form  symbol  oder  (symbol arglist . ...).
    ; copier-option ist entweder T oder das :COPIER-Argument.
    ; predicate-option ist entweder 0 oder das :PREDICATE-Argument.
    ; include-option ist entweder NIL oder die gesamte
    ;   :INCLUDE/:INHERIT-Option.
    ; print-object-option ist NIL oder eine Form f�r den Body der PRINT-OBJECT
    ;   Methode.
    ; type-option ist entweder T oder das :TYPE-Argument.
    ; named-option ist entweder 0 oder T.
    ; initial-offset-option ist entweder 0 oder das :INITIAL-OFFSET-Argument.
    ;; �berpr�fung der Optionen:
    (setq named-option (or (eq type-option 'T) (eq named-option 'T)))
    ; named-option (NIL oder T) gibt an, ob der Name in der Structure steckt.
    (if named-option
      (when (eql predicate-option 0)
        (setq predicate-option (concat-pnames name "-P")) ; Defaultname
      )
      (unless (or (eql predicate-option 0) (eq predicate-option 'NIL))
        (error-of-type 'source-program-error
          (DEUTSCH "~S ~S: Bei unbenannten Structures kann es kein :PREDICATE geben."
           ENGLISH "~S ~S: There is no :PREDICATE on unnamed structures."
           FRANCAIS "~S ~S : Il ne peut pas y avoir de :PREDICATE avec des structures anonymes.")
          'defstruct name
    ) ) )
    ; predicate-option ist
    ;   bei named-option=T: entweder NIL oder der Name des Typtestpr�dikats,
    ;   bei named-option=NIL bedeutungslos.
    (if (eq conc-name-option 'T)
      (setq conc-name-option (string-concat (string name) "-"))
    )
    ; conc-name-option ist der Namensprefix.
    (if (null constructor-option-list)
      (setq constructor-option-list (list (concat-pnames "MAKE-" name)))
      (setq constructor-option-list (remove 'NIL constructor-option-list))
    )
    ; constructor-option-list ist eine Liste aller zu kreierenden Konstruktoren,
    ;   jeweils in der Form  symbol  oder  (symbol arglist . ...).
    (if (eq copier-option 'T)
      (setq copier-option (concat-pnames "COPY-" name))
    )
    ; copier-option ist entweder NIL oder der Name der Kopierfunktion.
    (unless (or (eq type-option 'T)
                (eq type-option 'VECTOR)
                (eq type-option 'LIST)
                (and (consp type-option) (eq (first type-option) 'VECTOR))
            )
      (error-of-type 'source-program-error
        (DEUTSCH "~S ~S: Unzul�ssige :TYPE-Option ~S"
         ENGLISH "~S ~S: invalid :TYPE option ~S"
         FRANCAIS "~S ~S : Option :TYPE inadmissible: ~S")
        'defstruct name type-option
    ) )
    ; type-option ist entweder T oder LIST oder VECTOR oder (VECTOR ...)
    (unless (and (integerp initial-offset-option) (>= initial-offset-option 0))
      (error-of-type 'source-program-error
        (DEUTSCH "~S ~S: Der :INITIAL-OFFSET mu� ein Integer >=0 sein, nicht ~S"
         ENGLISH "~S ~S: The :INITIAL-OFFSET must be a nonnegative integer, not ~S"
         FRANCAIS "~S ~S : :INITIAL-OFFSET doit �tre un entier positif ou z�ro et non ~S")
        'defstruct name initial-offset-option
    ) )
    ; initial-offset-option ist ein Integer >=0.
    (when (and (plusp initial-offset-option) (eq type-option 'T))
      (error-of-type 'source-program-error
        (DEUTSCH "~S ~S: :INITIAL-OFFSET darf nur zusammen mit :TYPE angegeben werden: ~S"
         ENGLISH "~S ~S: :INITIAL-OFFSET must not be specified without :TYPE : ~S"
         FRANCAIS "~S ~S : :INITIAL-OFFSET ne peut �tre pr�cis� qu'ensemble avec :TYPE: ~S")
        'defstruct name options
    ) )
    ; Bei type-option=T ist initial-offset-option=0.
    (when (eq type-option 'T) (setq include-skip 1))
    ; include-skip ist 1 bei type-option=T, 0 sonst.
    (when (stringp (first docstring-and-slotargs))
      (setq docstring (first docstring-and-slotargs))
      (setq slotargs (rest docstring-and-slotargs))
    ) ; sonst stimmen docstring und slotargs bereits.
    ; docstring ist entweder NIL oder ein String.
    ; slotargs sind die restlichen Argumente.
    (if include-option
      (let* ((option (rest include-option))
             (subname (first option))
             (incl-desc (get subname 'DEFSTRUCT-DESCRIPTION)))
        (when (null incl-desc)
          (error-of-type 'source-program-error
            (DEUTSCH "~S ~S: Teilstruktur ~S ist nicht definiert."
             ENGLISH "~S ~S: included structure ~S has not been defined."
             FRANCAIS "~S ~S : La structure incluse ~S n'est pas d�finie.")
            'defstruct name subname
        ) )
        (setq names (cons name (svref incl-desc 0)))
        (setq namesbinding
              (list
                (list
                  (setq namesform (gensym))
                  `(CONS ',name (SVREF (GET ',subname 'DEFSTRUCT-DESCRIPTION) 0))
        )     ) )
        (unless (equalp (svref incl-desc 1) type-option)
          (error-of-type 'source-program-error
            (DEUTSCH "~S ~S: Teilstruktur ~S mu� vom selben Typ ~S sein."
             ENGLISH "~S ~S: included structure ~S must be of the same type ~S."
             FRANCAIS "~S ~S : La structure incluse ~S doit �tre du m�me type ~S.")
            'defstruct name subname type-option
        ) )
        (setq slotlist
          (nreverse
            (mapcar #'(lambda (slot)
                        (setq slot (copy-ds-slot slot))
                        (when (car (ds-slot-initer slot))
                          (setf (ds-slot-initer slot)
                                (cons (add-unquote (ds-slot-default slot)) 'NIL)
                        ) )
                        slot
                      )
                    (svref incl-desc 3)
        ) ) )
        ; slotlist ist die umgedrehte Liste der vererbten Slots
        (when slotlist (setq include-skip (1+ (ds-slot-offset (first slotlist)))))
        ; include-skip >=0 ist die Anzahl der bereits von der Teilstruktur
        ;   verbrauchten Slots, das "size" der Teilstruktur.
        ; Weitere Argumente der :INCLUDE-Option abarbeiten:
        (dolist (slotarg (rest option))
          (let* ((slotname (if (atom slotarg) slotarg (first slotarg)))
                 (slot (find slotname slotlist :key #'ds-slot-name :test #'eq)))
            (when (null slot)
              (error-of-type 'source-program-error
                (DEUTSCH "~S ~S: Teilstruktur ~S hat keine Komponente namens ~S."
                 ENGLISH "~S ~S: included structure ~S has no component with name ~S."
                 FRANCAIS "~S ~S : La structure incluse ~S n'a pas de composante de nom ~S.")
                'defstruct name subname slotname
            ) )
            (if (atom slotarg)
              (setf (ds-slot-default slot) 'NIL) ; Default auf NIL �berschreiben
              (progn
                (let ((default (second slotarg)))
                  (unless (constantp default)
                    (push
                      `(FUNCTION ,(concat-pnames "DEFAULT-" slotname)
                         (LAMBDA () ,default)
                       )
                      slotdefaultfuns
                    )
                    (setq default (gensym))
                    (push default slotdefaultvars)
                  )
                  (setf (ds-slot-default slot) default)
                )
                ; slot-options dieses Slot-Specifier abarbeiten:
                (do ((slot-arglistr (cddr slotarg) (cddr slot-arglistr)))
                    ((endp slot-arglistr))
                  (let ((slot-keyword (first slot-arglistr))
                        (slot-key-value (second slot-arglistr)))
                    (cond ((eq slot-keyword ':READ-ONLY)
                           (if slot-key-value
                             (setf (ds-slot-readonly slot) t)
                             (if (ds-slot-readonly slot)
                               (error-of-type 'source-program-error
                                 (DEUTSCH "~S ~S: Der READ-ONLY-Slot ~S von Teilstruktur ~S mu� auch in ~S READ-ONLY bleiben."
                                  ENGLISH "~S ~S: The READ-ONLY slot ~S of the included structure ~S must remain READ-ONLY in ~S."
                                  FRANCAIS "~S ~S : Le composant READ-ONLY ~S de la structure incluse ~S doit rester READ-ONLY dans ~S.")
                                 'defstruct name slotname subname name
                               )
                               (setf (ds-slot-readonly slot) nil)
                          )) )
                          ((eq slot-keyword ':TYPE)
                           (unless (subtypep (type-for-discrimination slot-key-value)
                                             (type-for-discrimination (ds-slot-type slot))
                                   )
                             (error-of-type 'source-program-error
                               (DEUTSCH "~S ~S: Der Typ ~S von Slot ~S mu� ein Untertyp des in Teilstruktur ~S definierten Typs ~S sein."
                                ENGLISH "~S ~S: The type ~S of slot ~S should be a subtype of the type defined for the included strucure ~S, namely ~S."
                                FRANCAIS "~S ~S : Le type ~S du composant ~S doit �tre un sous-type du type d�fini dans la structure incluse ~S, c'est-�-dire ~S.")
                               'defstruct name slot-key-value slotname subname (ds-slot-type slot)
                           ) )
                           (setf (ds-slot-type slot) slot-key-value)
                          )
                          (t (error-of-type 'source-program-error
                               (DEUTSCH "~S ~S: ~S ist keine Slot-Option."
                                ENGLISH "~S ~S: ~S is not a slot option."
                                FRANCAIS "~S ~S : ~S n'est pas une option de composant.")
                               'defstruct name slot-keyword
                          )  )
                ) ) )
        ) ) ) )
        (when (eq (first include-option) ':INHERIT)
          (setq inherited-slot-count (length slotlist))
      ) )
      (if (eq name 'STRUCTURE-OBJECT)
        (progn
          (setq names (list name))
          (setq namesform `',names)
        )
        (progn
          (setq names (cons name (svref (get 'STRUCTURE-OBJECT 'DEFSTRUCT-DESCRIPTION) 0)))
          (setq namesbinding
                (list
                  (list
                    (setq namesform (gensym))
                    `(CONS ',name (SVREF (GET 'STRUCTURE-OBJECT 'DEFSTRUCT-DESCRIPTION) 0))
        ) )     ) )
    ) )
    ; names ist die Include-Verschachtelung, namesform die Form dazu.
    ; slotlist ist die bisherige Slotliste, umgedreht.
    ; inherited-slot-count ist die Anzahl der Slots, die beim Bilden der
    ; Accessoren zu ignorieren sind.
    (when (and named-option ; benannte Structure
               (consp type-option) ; vom Typ (VECTOR ...)
               ; mu� den/die Namen enthalten k�nnen:
               (not (typep names (type-for-discrimination (second type-option))))
          )
      (error-of-type 'source-program-error
        (DEUTSCH "~S ~S: Structure vom Typ ~S kann den Namen nicht enthalten."
         ENGLISH "~S ~S: structure of type ~S can't hold the name."
         FRANCAIS "~S ~S : Une structure de type ~S ne peut pas contenir le nom.")
        'defstruct name type-option
    ) )
    ; Aufbau der Structure:
    ; names, evtl. include-Slots, initial-offset-option mal NIL, Slots.
    ; Aufbau von Vektor oder Liste:
    ; include-Anteil, initial-offset-option mal NIL, evtl. Name, Slots.
    (setq initial-offset (+ include-skip initial-offset-option))
    (unless (eq type-option 'T)
      (when named-option
        (push
          (make-ds-slot nil ; Kennzeichen f�r Typerkennungs-Slot
                        '()
                        (setq initial-offset-option initial-offset)
                        (cons 'NIL name) name ; "Defaultwert" = name
                        'SYMBOL ; Typ = Symbol
                        T ; Read-Only
          )
          slotlist
        )
        (setq initial-offset (1+ initial-offset))
    ) )
    ; Die einzelnen Slots kommen ab initial-offset.
    ; Bei type/=T (also Vektor oder Liste) und named-option sitzt
    ;   der Name in Slot Nummer  initial-offset-option = (1- initial-offset).
    ; Abarbeitung der einzelnen Slots:
    (let ((offset initial-offset))
      (dolist (slotarg slotargs)
        (let (slotname
              default)
          (if (atom slotarg)
            (setq slotname slotarg  default nil)
            (setq slotname (first slotarg)  default (second slotarg))
          )
          (unless (constantp default)
            (push
              `(FUNCTION ,(concat-pnames "DEFAULT-" slotname)
                 (LAMBDA () ,default)
               )
              slotdefaultfuns
            )
            (setq default (gensym))
            (push default slotdefaultvars)
          )
          ; Here we compare slot names through their symbol-names, not through
          ; #'eq, because if we have two slots P::X and Q::X, the two accessor
          ; functions would have the same name FOO-X.
          (when (find (symbol-name slotname) slotlist
                      :key #'(lambda (slot) (symbol-name (ds-slot-name slot)))
                      :test #'string=
                )
            (error-of-type 'source-program-error
              (DEUTSCH "~S ~S: Es kann nicht mehrere Slots mit demselben Namen ~S geben."
               ENGLISH "~S ~S: There may be only one slot with the name ~S."
               FRANCAIS "~S ~S : Il ne peut pas y avoir plusieurs composants avec le m�me nom ~S.")
              'defstruct name slotname
          ) )
          (let ((type t) (read-only nil))
            (when (consp slotarg)
              (do ((slot-arglistr (cddr slotarg) (cddr slot-arglistr)))
                  ((endp slot-arglistr))
                (let ((slot-keyword (first slot-arglistr))
                      (slot-key-value (second slot-arglistr)))
                  (cond ((eq slot-keyword ':READ-ONLY)
                         (setq read-only (if slot-key-value t nil))
                        )
                        ((eq slot-keyword ':TYPE) (setq type slot-key-value))
                        (t (error-of-type 'source-program-error
                             (DEUTSCH "~S ~S: ~S ist keine Slot-Option."
                              ENGLISH "~S ~S: ~S is not a slot option."
                              FRANCAIS "~S ~S : ~S n'est pas une option de composant.")
                             'defstruct name slot-keyword
                        )  )
            ) ) ) )
            (push (make-ds-slot slotname
                                (if slotname
                                  (list (intern (symbol-name slotname) *keyword-package*))
                                  '()
                                ) ; initargs
                                offset ; location
                                (if (constantp default)
                                  (cons 'NIL (eval default)) ; default is a constant
                                  (cons (add-unquote default) 'NIL) ; default is a gensym
                                )
                                default type read-only ; defstruct specific
                  )
              slotlist
        ) ) )
        (incf offset)
      )
      (setq size offset)
    )
    ; size = Gesamtl�nge der Structure
    (setq slotlist (nreverse slotlist))
    (setq slotdefaultfuns (nreverse slotdefaultfuns))
    (setq slotdefaultvars (nreverse slotdefaultvars))
    ; Die slots in slotlist sind jetzt wieder aufsteigend geordnet.
    (setq constructor-forms
      (mapcar
        #'(lambda (constructor-option)
            (if (consp constructor-option)
              (ds-make-boa-constructor
                constructor-option type-option name namesform size slotlist
              )
              (progn
                (if (null keyword-constructor)
                  (setq keyword-constructor constructor-option)
                )
                (ds-make-keyword-constructor
                  constructor-option type-option name namesform size slotlist
          ) ) ) )
        constructor-option-list
    ) )
    ; constructor-forms = Liste der Formen, die die Konstruktoren definieren.
    (let ((index 4))
      (dolist (defaultvar slotdefaultvars)
        (setf (ds-slot-default (find defaultvar slotlist :key #'(lambda (x) (ds-slot-default x)) :test #'eq))
              `(SVREF (GET ',name 'DEFSTRUCT-DESCRIPTION) ,index)
        )
        (incf index)
    ) )
    ; slotlist enth�lt nun keine der slotdefaultvars mehr.
    `(EVAL-WHEN (LOAD COMPILE EVAL)
       (LET ()
         (LET ,(append namesbinding (mapcar #'list slotdefaultvars slotdefaultfuns))
           ,@constructor-forms
           (%PUT ',name 'DEFSTRUCT-DESCRIPTION
                 (VECTOR ,namesform ',type-option ',keyword-constructor
                         ,(add-backquote slotlist)
                         ,@slotdefaultvars
         ) )     )
         ,@(if (eq type-option 'T) `((CLOS::DEFINE-STRUCTURE-CLASS ',name)))
         ,@(if (and named-option predicate-option)
             (ds-make-pred predicate-option type-option name initial-offset-option)
           )
         ,@(if copier-option (ds-make-copier copier-option name type-option))
         ,@(let ((directslotlist (nthcdr inherited-slot-count slotlist)))
             `(,@(ds-make-accessors name type-option conc-name-option directslotlist)
               ,@(ds-make-defsetfs name type-option conc-name-option directslotlist)
              )
           )
         (SETF (DOCUMENTATION ',name 'STRUCTURE) ,docstring)
         ,@(when (eq type-option 'T)
             (list
               (if print-object-option
                 `(CLOS:DEFMETHOD CLOS:PRINT-OBJECT ((STRUCT ,name) STREAM)
                    (PROGN ,print-object-option)
                  )
                 `(CLOS::DEFSTRUCT-REMOVE-PRINT-OBJECT-METHOD ',name)
           ) ) )
         ',name
     ) )
) )

(defstruct (structure-object (:predicate nil) (:copier nil) (:constructor nil)))

