;;;; Apropos, Describe

(in-package "SYSTEM")

;;-----------------------------------------------------------------------------
;; APROPOS

(defun apropos-list (string &optional (package nil))
  (let* ((L nil)
         (fun #'(lambda (sym)
                  (when
                      #| (search string (symbol-name sym) :test #'char-equal) |#
                      (sys::search-string-equal string sym) ; 15 mal schneller!
                    (push sym L)
                ) )
        ))
    (if package
      (system::map-symbols fun package)
      (system::map-all-symbols fun)
    )
    (stable-sort (delete-duplicates L :test #'eq :from-end t)
                 #'string< :key #'symbol-name
    )
) )

(defun apropos (string &optional (package nil))
  (dolist (sym (apropos-list string package))
    (print sym)
    (when (fboundp sym)
      (write-string "   ")
      (write-string (fbound-string sym))
    )
    (when (boundp sym)
      (write-string "   ")
      (if (constantp sym)
        (write-string (DEUTSCH "Konstante"
                       ENGLISH "constant"
                       FRANCAIS "constante")
        )
        (write-string (DEUTSCH "Variable"
                       ENGLISH "variable"
                       FRANCAIS "variable")
    ) ) )
    (when (or (get sym 'system::type-symbol)
              (get sym 'system::defstruct-description)
          )
      (write-string "   ")
      (write-string (DEUTSCH "Typ"
                     ENGLISH "type"
                     FRANCAIS "type")
    ) )
    (when (get sym 'clos::closclass)
      (write-string "   ")
      (write-string (DEUTSCH "Klasse"
                     ENGLISH "class"
                     FRANCAIS "classe")
    ) )
  )
  (values)
)

;;-----------------------------------------------------------------------------
;; DESCRIBE

(defun describe (obj &optional s &aux (more '()))
  (cond ((eq s 'nil) (setq s *standard-output*))
        ((eq s 't) (setq s *terminal-io*))
  )
  (format s (DEUTSCH "~%Beschreibung von~%"
             ENGLISH "~%Description of~%"
             FRANCAIS "~%Description de~%")
  )
  (format s "~A" (write-to-short-string obj sys::*prin-linelength*))
  (format s (DEUTSCH "~%Das ist "
             ENGLISH "~%This is "
             FRANCAIS "~%Ceci est ")
  )
  (let ((type (type-of obj)))
    ; Dispatch nach den m�glichen Resultaten von TYPE-OF:
    (if (atom type)
      (case type
        (CONS
          (flet ((list-length (list)  ; vgl. CLTL, S. 265
                   (do ((n 0 (+ n 2))
                        (fast list (cddr fast))
                        (slow list (cdr slow))
                       )
                       (nil)
                     (when (atom fast) (return n))
                     (when (atom (cdr fast)) (return (1+ n)))
                     (when (eq (cdr fast) slow) (return nil))
                )) )
            (let ((len (list-length obj)))
              (if len
                (if (null (nthcdr len obj))
                  (format s (DEUTSCH "eine Liste der L�nge ~S."
                             ENGLISH "a list of length ~S."
                             FRANCAIS "une liste de longueur ~S.")
                            len
                  )
                  (if (> len 1)
                    (format s (DEUTSCH "eine punktierte Liste der L�nge ~S."
                               ENGLISH "a dotted list of length ~S."
                               FRANCAIS "une liste point�e de longueur ~S.")
                              len
                    )
                    (format s (DEUTSCH "ein Cons."
                               ENGLISH "a cons."
                               FRANCAIS "un �cons�.")
                ) ) )
                (format s (DEUTSCH "eine zyklische Liste."
                           ENGLISH "a cyclic list."
                           FRANCAIS "une liste circulaire.")
        ) ) ) ) )
        ((SYMBOL NULL BOOLEAN)
          (when (null obj)
            (format s (DEUTSCH "die leere Liste, "
                       ENGLISH "the empty list, "
                       FRANCAIS "la liste vide, ")
          ) )
          (format s (DEUTSCH "das Symbol ~S"
                     ENGLISH "the symbol ~S"
                     FRANCAIS "le symbole ~S")
                    obj
          )
          (when (keywordp obj)
            (format s (DEUTSCH ", ein Keyword"
                       ENGLISH ", a keyword"
                       FRANCAIS ", un mot-cl�")
          ) )
          (when (boundp obj)
            (if (constantp obj)
              (format s (DEUTSCH ", eine Konstante"
                         ENGLISH ", a constant"
                         FRANCAIS ", une constante")
              )
              (if (sys::special-variable-p obj)
                (format s (DEUTSCH ", eine SPECIAL-deklarierte Variable"
                           ENGLISH ", a variable declared SPECIAL"
                           FRANCAIS ", une variable declar�e SPECIAL")
                )
                (format s (DEUTSCH ", eine Variable"
                           ENGLISH ", a variable"
                           FRANCAIS ", une variable")
            ) ) )
            (when (symbol-macro-expand obj)
              (format s (DEUTSCH " (Macro)"
                         ENGLISH " (macro)"
                         FRANCAIS " (macro)")
              )
              (push `(MACROEXPAND-1 ',obj) more)
            )
            (push `,obj more)
            (push `(SYMBOL-VALUE ',obj) more)
          )
          (when (fboundp obj)
            (format s (DEUTSCH ", benennt "
                       ENGLISH ", names "
                       FRANCAIS ", le nom ")
            )
            (cond ((special-operator-p obj)
                   (format s (DEUTSCH "eine Special-Form"
                              ENGLISH "a special form"
                              FRANCAIS "d'une forme sp�ciale")
                   )
                   (when (macro-function obj)
                     (format s (DEUTSCH " mit Macro-Definition"
                                ENGLISH " with macro definition"
                                FRANCAIS ", aussi d'un macro")
                  )) )
                  ((functionp (symbol-function obj))
                   (format s (DEUTSCH "eine Funktion"
                              ENGLISH "a function"
                              FRANCAIS "d'une fonction")
                   )
                   (push `#',obj more)
                   (push `(SYMBOL-FUNCTION ',obj) more)
                  )
                  (t ; (macro-function obj)
                   (format s (DEUTSCH "einen Macro"
                              ENGLISH "a macro"
                              FRANCAIS "d'un macro")
                  ))
          ) )
          (when (or (get obj 'system::type-symbol)
                    (get obj 'system::defstruct-description)
                    (get obj 'system::deftype-expander)
                )
            (format s (DEUTSCH ", benennt einen Typ"
                       ENGLISH ", names a type"
                       FRANCAIS ", le nom d'un type")
            )
            (when (get obj 'system::deftype-expander)
              (push `(TYPE-EXPAND-1 ',obj) more)
          ) )
          (when (get obj 'clos::closclass)
            (format s (DEUTSCH ", benennt eine Klasse"
                       ENGLISH ", names a class"
                       FRANCAIS ", le nom d'une classe")
          ) )
          (when (symbol-plist obj)
            (let ((properties
                    (do ((l nil)
                         (pl (symbol-plist obj) (cddr pl)))
                        ((null pl) (nreverse l))
                      (push (car pl) l)
                 )) )
              (format s (DEUTSCH ", hat die Propert~@P ~{~S~^, ~}"
                         ENGLISH ", has the propert~@P ~{~S~^, ~}"
                         FRANCAIS ", a ~[~;la propri�t�~:;les propri�t�s~] ~{~S~^, ~}")
                        (length properties) properties
            ) )
            (push `(SYMBOL-PLIST ',obj) more)
          )
          (format s (DEUTSCH "."
                     ENGLISH "."
                     FRANCAIS ".")
          )
          (format s (DEUTSCH "~%Das Symbol "
                     ENGLISH "~%The symbol "
                     FRANCAIS "~%Le symbole ")
          )
          (let ((home (symbol-package obj)))
            (if home
              (format s (DEUTSCH "liegt in ~S"
                         ENGLISH "lies in ~S"
                         FRANCAIS "est situ� dans ~S")
                        home
              )
              (format s (DEUTSCH "ist uninterniert"
                         ENGLISH "is uninterned"
                         FRANCAIS "n'appartient � aucun paquetage")
            ) )
            (let ((accessible-packs nil))
              (let ((*print-escape* t)
                    (*print-readably* nil))
                (let ((normal-printout ; externe Repr�sentation ohne Package-Marker
                        (if home
                          (let ((*package* home)) (prin1-to-string obj))
                          (let ((*print-gensym* nil)) (prin1-to-string obj))
                     )) )
                  (dolist (pack (list-all-packages))
                    (when ; obj in pack accessible?
                          (string=
                            (let ((*package* pack)) (prin1-to-string obj))
                            normal-printout
                          )
                      (push pack accessible-packs)
              ) ) ) )
              (when accessible-packs
                (format s (DEUTSCH " und ist in ~:[der Package~;den Packages~] ~{~A~^, ~} accessible"
                           ENGLISH " and is accessible in the package~:[~;s~] ~{~A~^, ~}"
                           FRANCAIS " et est visible dans le~:[ paquetage~;s paquetages~] ~{~A~^, ~}")
                          (cdr accessible-packs)
                          (sort (mapcar #'package-name accessible-packs) #'string<)
          ) ) ) )
          (format s (DEUTSCH "."
                     ENGLISH "."
                     FRANCAIS ".")
        ) )
        ((FIXNUM BIGNUM)
          (format s (DEUTSCH "eine ganze Zahl, belegt ~S Bits, ist als ~:(~A~) repr�sentiert."
                     ENGLISH "an integer, uses ~S bits, is represented as a ~(~A~)."
                     FRANCAIS "un nombre entier, occupant ~S bits, est repr�sent� comme ~(~A~).")
                    (integer-length obj) type
        ) )
        (RATIO
          (format s (DEUTSCH "eine rationale, nicht ganze Zahl."
                     ENGLISH "a rational, not integral number."
                     FRANCAIS "un nombre rationnel mais pas entier.")
        ) )
        ((SHORT-FLOAT SINGLE-FLOAT DOUBLE-FLOAT LONG-FLOAT)
          (format s (DEUTSCH "eine Flie�kommazahl mit ~S Mantissenbits (~:(~A~))."
                     ENGLISH "a float with ~S bits of mantissa (~(~A~))."
                     FRANCAIS "un nombre � virgule flottante avec une pr�cision de ~S bits (un ~(~A~)).")
                    (float-digits obj) type
        ) )
        (COMPLEX
          (format s (DEUTSCH "eine komplexe Zahl "
                     ENGLISH "a complex number "
                     FRANCAIS "un nombre complexe ")
          )
          (let ((x (realpart obj))
                (y (imagpart obj)))
            (if (zerop y)
              (if (zerop x)
                (format s (DEUTSCH "im Ursprung"
                           ENGLISH "at the origin"
                           FRANCAIS "� l'origine")
                )
                (format s (DEUTSCH "auf der ~:[posi~;nega~]tiven reellen Achse"
                           ENGLISH "on the ~:[posi~;nega~]tive real axis"
                           FRANCAIS "sur la partie ~:[posi~;nega~]tive de l'axe r�elle")
                          (minusp x)
              ) )
              (if (zerop x)
                (format s (DEUTSCH "auf der ~:[posi~;nega~]tiven imagin�ren Achse"
                           ENGLISH "on the ~:[posi~;nega~]tive imaginary axis"
                           FRANCAIS "sur la partie ~:[posi~;nega~]tive de l'axe imaginaire")
                          (minusp y)
                )
                (format s (DEUTSCH "im ~:[~:[ers~;vier~]~;~:[zwei~;drit~]~]ten Quadranten"
                           ENGLISH "in ~:[~:[first~;fourth~]~;~:[second~;third~]~] the quadrant"
                           FRANCAIS "dans le ~:[~:[premier~;quatri�me~]~;~:[deuxi�me~;troisi�me~]~] quartier")
                          (minusp x) (minusp y)
          ) ) ) )
          (format s (DEUTSCH " der Gau�schen Zahlenebene."
                     ENGLISH " of the Gaussian number plane."
                     FRANCAIS " du plan Gaussien.")
        ) )
        (CHARACTER
          (format s (DEUTSCH "ein Zeichen"
                     ENGLISH "a character"
                     FRANCAIS "un caract�re")
          )
          (format s (DEUTSCH "."
                     ENGLISH "."
                     FRANCAIS ".")
          )
          (format s (DEUTSCH "~%Es ist ein ~:[nicht ~;~]druckbares Zeichen."
                     ENGLISH "~%It is a ~:[non-~;~]printable character."
                     FRANCAIS "~%C'est un caract�re ~:[non ~;~]imprimable.")
                    (graphic-char-p obj)
          )
          (unless (standard-char-p obj)
            (format s (DEUTSCH "~%Seine Verwendung ist nicht portabel."
                       ENGLISH "~%Its use is non-portable."
                       FRANCAIS "~%Il n'est pas portable de l'utiliser.")
          ) )
        )
        (FUNCTION ; (SYS::CLOSUREP obj) ist erf�llt
          (let ((compiledp (compiled-function-p obj)))
            (format s (DEUTSCH "eine ~:[interpret~;compil~]ierte Funktion."
                       ENGLISH "a~:[n interpret~; compil~]ed function."
                       FRANCAIS "une fonction ~:[interpr�t~;compil~]�e.")
                      compiledp
            )
            (if compiledp
              (multiple-value-bind (req-anz opt-anz rest-p key-p keyword-list allow-other-keys-p)
                  (sys::signature obj)
                (describe-signature s req-anz opt-anz rest-p key-p keyword-list allow-other-keys-p)
                (push `(DISASSEMBLE #',(sys::closure-name obj)) more)
                (push `(DISASSEMBLE ',obj) more)
              )
              (progn
                (format s (DEUTSCH "~%Argumentliste: ~S"
                           ENGLISH "~%argument list: ~S"
                           FRANCAIS "~%Liste des arguments: ~S")
                          (car (sys::%record-ref obj 1))
                )
                (let ((doc (sys::%record-ref obj 2)))
                  (when doc
                    (format s (DEUTSCH "~%Dokumentation: ~A"
                               ENGLISH "~%documentation: ~A"
                               FRANCAIS "~%Documentation: ~A")
                              doc
              ) ) ) )
        ) ) )
        (COMPILED-FUNCTION ; nur SUBRs und FSUBRs
          (if (functionp obj)
            ; SUBR
            (progn
              (format s (DEUTSCH "eine eingebaute System-Funktion."
                         ENGLISH "a built-in system function."
                         FRANCAIS "une fonction pr�d�finie du syst�me.")
              )
              (multiple-value-bind (name req-anz opt-anz rest-p keywords allow-other-keys)
                  (sys::subr-info obj)
                (when name
                  (describe-signature s req-anz opt-anz rest-p keywords keywords allow-other-keys)
            ) ) )
            ; FSUBR
            (format s (DEUTSCH "ein Special-Form-Handler."
                       ENGLISH "a special form handler."
                       FRANCAIS "un interpr�teur de forme sp�ciale.")
        ) ) )
        #+(or AMIGA FFI)
        (FOREIGN-POINTER
          (format s (DEUTSCH "ein Foreign-Pointer."
                     ENGLISH "a foreign pointer"
                     FRANCAIS "un pointeur �tranger.")
        ) )
        #+FFI
        (FOREIGN-ADDRESS
          (format s (DEUTSCH "eine Foreign-Adresse."
                     ENGLISH "a foreign address"
                     FRANCAIS "une addresse �trang�re.")
        ) )
        #+FFI
        (FOREIGN-VARIABLE
          (format s (DEUTSCH "eine Foreign-Variable vom Foreign-Typ ~S."
                     ENGLISH "a foreign variable of foreign type ~S."
                     FRANCAIS "une variable �trang�re de type �tranger ~S.")
                    (deparse-c-type (sys::%record-ref obj 3))
        ) )
        #+FFI
        (FOREIGN-FUNCTION
          (format s (DEUTSCH "eine Foreign-Funktion."
                     ENGLISH "a foreign function."
                     FRANCAIS "une fonction �trang�re.")
        ) )
        ((STREAM FILE-STREAM SYNONYM-STREAM BROADCAST-STREAM
          CONCATENATED-STREAM TWO-WAY-STREAM ECHO-STREAM STRING-STREAM
         )
          (format s (DEUTSCH "ein ~:[~:[geschlossener ~;Output-~]~;~:[Input-~;bidirektionaler ~]~]Stream."
                     ENGLISH "a~:[~:[ closed ~;n output-~]~;~:[n input-~;n input/output-~]~]stream."
                     FRANCAIS "un �stream� ~:[~:[ferm�~;de sortie~]~;~:[d'entr�e~;d'entr�e/sortie~]~].")
                    (input-stream-p obj) (output-stream-p obj)
        ) )
        (PACKAGE
          (if (package-name obj)
            (progn
              (format s (DEUTSCH "die Package mit Namen ~A"
                         ENGLISH "the package named ~A"
                         FRANCAIS "le paquetage de nom ~A")
                        (package-name obj)
              )
              (let ((nicknames (package-nicknames obj)))
                (when nicknames
                  (format s (DEUTSCH " und zus�tzlichen Namen ~{~A~^, ~}"
                             ENGLISH ". It has the nicknames ~{~A~^, ~}"
                             FRANCAIS ". Il porte aussi les noms ~{~A~^, ~}")
                            nicknames
              ) ) )
              (format s (DEUTSCH "."
                         ENGLISH "."
                         FRANCAIS ".")
              )
              (let ((use-list (package-use-list obj))
                    (used-by-list (package-used-by-list obj)))
                (format s (DEUTSCH "~%Sie "
                           ENGLISH "~%It "
                           FRANCAIS "~%Il ")
                )
                (when use-list
                  (format s (DEUTSCH "importiert die externen Symbole der Package~:[~;s~] ~{~A~^, ~} und "
                             ENGLISH "imports the external symbols of the package~:[~;s~] ~{~A~^, ~} and "
                             FRANCAIS "importe les symboles externes d~:[u paquetage~;es paquetages~] ~{~A~^, ~} et ")
                            (cdr use-list) (mapcar #'package-name use-list)
                ) )
                (format s (DEUTSCH "exportiert ~:[keine Symbole~;die Symbole~:*~{~<~%~:; ~S~>~^~}~]"
                           ENGLISH "exports ~:[no symbols~;the symbols~:*~{~<~%~:; ~S~>~^~}~]"
                           FRANCAIS "~:[n'exporte pas de symboles~;exporte les symboles~:*~{~<~%~:; ~S~>~^~}~]")
                          ; Liste aller exportierten Symbole:
                          (let ((L nil))
                            (do-external-symbols (s obj) (push s L))
                            (sort L #'string< :key #'symbol-name)
                )         )
                (when used-by-list
                  (format s (DEUTSCH " an die Package~:[~;s~] ~{~A~^, ~}"
                             ENGLISH " to the package~:[~;s~] ~{~A~^, ~}"
                             FRANCAIS " vers le~:[ paquetage~;s paquetages~] ~{~A~^, ~}")
                            (cdr used-by-list) (mapcar #'package-name used-by-list)
                ) )
                (format s (DEUTSCH "."
                           ENGLISH "."
                           FRANCAIS ".")
            ) ) )
            (format s (DEUTSCH "eine gel�schte Package."
                       ENGLISH "a deleted package."
                       FRANCAIS "un paquetage �limin�.")
        ) ) )
        (HASH-TABLE
          (format s (DEUTSCH "eine Hash-Tabelle mit ~S Eintr~:*~[�gen~;ag~:;�gen~]."
                     ENGLISH "a hash table with ~S entr~:@P."
                     FRANCAIS "un tableau de hachage avec ~S entr�e~:*~[s~;~:;s~].")
                    (hash-table-count obj)
        ) )
        (READTABLE
          (format s (DEUTSCH "~:[eine ~;die Common-Lisp-~]Readtable."
                     ENGLISH "~:[a~;the Common Lisp~] readtable."
                     FRANCAIS "~:[un~;le~] tableau de lecture~:*~:[~; de Common Lisp~].")
                    (equalp obj (copy-readtable))
        ) )
        ((PATHNAME #+LOGICAL-PATHNAMES LOGICAL-PATHNAME)
          (format s (DEUTSCH "ein ~:[~;portabler ~]Pathname~:[.~;~:*, aufgebaut aus:~{~A~}~]"
                     ENGLISH "a ~:[~;portable ~]pathname~:[.~;~:*, with the following components:~{~A~}~]"
                     FRANCAIS "un �pathname�~:[~; portable~]~:[.~;~:*, compos� de:~{~A~}~]")
                    (sys::logical-pathname-p obj)
                    (mapcan #'(lambda (kw component)
                                (when component
                                  (list (format nil "~%~A = ~A"
                                                    (symbol-name kw)
                                                    (make-pathname kw component)
                              ) ) )     )
                      '(:host :device :directory :name :type :version)
                      (list
                        (pathname-host obj)
                        (pathname-device obj)
                        (pathname-directory obj)
                        (pathname-name obj)
                        (pathname-type obj)
                        (pathname-version obj)
        ) )         ) )
        (RANDOM-STATE
          (format s (DEUTSCH "ein Random-State."
                     ENGLISH "a random-state."
                     FRANCAIS "un �random-state�.")
        ) )
        (BYTE
          (format s (DEUTSCH "ein Byte-Specifier, bezeichnet die ~S Bits ab Bitposition ~S eines Integers."
                     ENGLISH "a byte specifier, denoting the ~S bits starting at bit position ~S of an integer."
                     FRANCAIS "un intervalle de bits, comportant ~S bits � partir de la position ~S d'un entier.")
                    (byte-size obj) (byte-position obj)
        ) )
        (LOAD-TIME-EVAL
          (format s (DEUTSCH "eine Absicht der Evaluierung zur Ladezeit." ; ??
                     ENGLISH "a load-time evaluation promise." ; ??
                     FRANCAIS "une promesse d'�valuation au moment du chargement.") ; ??
        ) )
        (WEAK-POINTER
          (multiple-value-bind (value validp) (weak-pointer-value obj)
            (if validp
              (format s (DEUTSCH "ein f�r die GC unsichtbarer Pointer auf ~S."
                         ENGLISH "a GC-invisible pointer to ~S."
                         FRANCAIS "un pointeur, invisible pour le GC, sur ~S.")
                        value
              )
              (format s (DEUTSCH "ein f�r die GC unsichtbarer Pointer auf ein nicht mehr existierendes Objekt."
                         ENGLISH "a GC-invisible pointer to a now defunct object."
                         FRANCAIS "un pointeur, invisible pour le GC, sur un objet qui n'existe plus.")
        ) ) ) )
        (READ-LABEL
          (format s (DEUTSCH "eine Markierung zur Aufl�sung von #~D#-Verweisen bei READ."
                     ENGLISH "a label used for resolving #~D# references during READ."
                     FRANCAIS "une marque destin�e � r�soudre #~D# au cours de READ.")
                    (logand (sys::address-of obj) '#,(ash most-positive-fixnum -1))
        ) )
        (FRAME-POINTER
          (format s (DEUTSCH "ein Pointer in den Stack. Er zeigt auf:"
                     ENGLISH "a pointer into the stack. It points to:"
                     FRANCAIS "un pointeur dans la pile. Il pointe vers :")
          )
          (sys::describe-frame s obj)
        )
        (SYSTEM-INTERNAL
          (format s (DEUTSCH "ein Objekt mit besonderen Eigenschaften."
                     ENGLISH "a special-purpose object."
                     FRANCAIS "un objet distingu�.")
        ) )
        (ADDRESS
          (format s (DEUTSCH "eine Maschinen-Adresse."
                     ENGLISH "a machine address."
                     FRANCAIS "une addresse au niveau de la machine.")
        ) )
        (t
         (if (and (symbolp type) (sys::%structure-type-p type obj))
           ; Structure
           (progn
             (format s (DEUTSCH "eine Structure vom Typ ~S."
                        ENGLISH "a structure of type ~S."
                        FRANCAIS "une structure de type ~S.")
                       type
             )
             (let ((types (butlast (cdr (sys::%record-ref obj 0)))))
               (when types
                 (format s (DEUTSCH "~%Als solche ist sie auch eine Structure vom Typ ~{~S~^, ~}."
                            ENGLISH "~%As such, it is also a structure of type ~{~S~^, ~}."
                            FRANCAIS "~%En tant que telle, c'est aussi une structure de type ~{~S~^, ~}.")
                           types
             ) ) )
             (clos:describe-object obj s)
           )
           ; CLOS-Instanz
           (progn
             (format s (DEUTSCH "eine Instanz der CLOS-Klasse ~S."
                        ENGLISH "an instance of the CLOS class ~S."
                        FRANCAIS "un objet appartenant � la classe ~S de CLOS.")
                       (clos:class-of obj)
             )
             (clos:describe-object obj s)
         ) )
      ) )
      ; Array-Typen
      (let ((rank (array-rank obj))
            (eltype (array-element-type obj)))
        (format s (DEUTSCH "ein~:[~; einfacher~] ~A-dimensionaler Array"
                   ENGLISH "a~:[~; simple~] ~A dimensional array"
                   FRANCAIS "une matrice~:[~; simple~] � ~A dimension~:P")
                  (simple-array-p obj) rank
        )
        (when (eql rank 1)
          (format s (DEUTSCH " (Vektor)"
                     ENGLISH " (vector)"
                     FRANCAIS " (vecteur)")
        ) )
        (unless (eq eltype 'T)
          (format s (DEUTSCH " von ~:(~A~)s"
                     ENGLISH " of ~(~A~)s"
                     FRANCAIS " de ~(~A~)s")
                    eltype
        ) )
        (when (adjustable-array-p obj)
          (format s (DEUTSCH ", adjustierbar"
                     ENGLISH ", adjustable"
                     FRANCAIS ", ajustable")
        ) )
        (when (plusp rank)
          (format s (DEUTSCH ", der Gr��e ~{~S~^ x ~}"
                     ENGLISH ", of size ~{~S~^ x ~}"
                     FRANCAIS ", de grandeur ~{~S~^ x ~}")
                    (array-dimensions obj)
          )
          (when (array-has-fill-pointer-p obj)
            (format s (DEUTSCH " und der momentanen L�nge (Fill-Pointer) ~S"
                       ENGLISH " and current length (fill-pointer) ~S"
                       FRANCAIS " et longueur courante (fill-pointer) ~S")
                      (fill-pointer obj)
        ) ) )
        (format s (DEUTSCH "."
                   ENGLISH "."
                   FRANCAIS ".")
      ) )
  ) )
  (when more
    (format s (DEUTSCH "~%Mehr Information durch Auswerten von ~{~S~^ oder ~}."
               ENGLISH "~%For more information, evaluate ~{~S~^ or ~}."
               FRANCAIS "~%Pour obtenir davantage d'information, �valuez ~{~S~^ ou ~}.")
              (nreverse more)
  ) )
  (values)
)

; Liefert die Signatur eines funktionalen Objekts, als Werte:
; 1. req-anz
; 2. opt-anz
; 3. rest-p
; 4. key-p
; 5. keyword-list
; 6. allow-other-keys-p
(defun function-signature (obj)
  (if (sys::closurep obj)
    (if (compiled-function-p obj)
      ; compilierte Closure
      (multiple-value-bind (req-anz opt-anz rest-p key-p keyword-list allow-other-keys-p)
          (sys::signature obj) ; siehe compiler.lsp
        (values req-anz opt-anz rest-p key-p keyword-list allow-other-keys-p)
      )
      ; interpretierte Closure
      (let ((clos_keywords (sys::%record-ref obj 16)))
        (values (sys::%record-ref obj 12) ; req_anz
                (sys::%record-ref obj 13) ; opt_anz
                (sys::%record-ref obj 19) ; rest_flag
                (not (numberp clos_keywords))
                (if (not (numberp clos_keywords)) (copy-list clos_keywords))
                (sys::%record-ref obj 18) ; allow_flag
      ) )
    )
    (cond #+FFI
          ((eq (type-of obj) 'FOREIGN-FUNCTION)
           (values (sys::foreign-function-signature obj) 0 nil nil nil nil)
          )
          (t
           (multiple-value-bind (name req-anz opt-anz rest-p keywords allow-other-keys)
               (sys::subr-info obj)
             (if name
               (values req-anz opt-anz rest-p keywords keywords allow-other-keys)
               (error (DEUTSCH "~S: ~S ist keine Funktion."
                       ENGLISH "~S: ~S is not a function."
                       FRANCAIS "~S : ~S n'est pas une fonction.")
                      'function-signature obj
               )
) ) )     )) )

(defun signature-to-list (req-anz opt-anz rest-p keyword-p keywords
                          allow-other-keys)
  (let ((args '()) (count -1))
      (dotimes (i req-anz)
      (push (intern (format nil "ARG~D" (incf count)) :sys) args))
      (when (plusp opt-anz)
        (push '&OPTIONAL args)
        (dotimes (i opt-anz)
        (push (intern (format nil "ARG~D" (incf count)) :sys) args)))
      (when rest-p
        (push '&REST args)
      (push 'other-args args))
      (when keyword-p
        (push '&KEY args)
      (dolist (kw keywords) (push kw args))
      (when allow-other-keys (push '&ALLOW-OTHER-KEYS args)))
    (nreverse args)))

(defun arglist (func)
  (multiple-value-call #'signature-to-list (function-signature func)))

(defun describe-signature (s req-anz opt-anz rest-p keyword-p keywords
                           allow-other-keys)
  (when s
    (format s (DEUTSCH "~%Argumentliste: "
               ENGLISH "~%argument list: "
               FRANCAIS "~%Liste des arguments : ")))
  (format s "(~{~A~^ ~})"
          (signature-to-list req-anz opt-anz rest-p keyword-p keywords
                             allow-other-keys)))

;; DOCUMENTATION mit abfragen und ausgeben??
;; function, variable, type, structure, setf

; Gibt object in einen String aus, der nach M�glichkeit h�chstens max Zeichen
; lang sein soll.
(defun write-to-short-string (object max)
  ; Methode: probiere
  ; level = 0: length = 0,1,2
  ; level = 1: length = 1,2,3,4
  ; level = 2: length = 2,...,6
  ; usw. bis maximal level = 16.
  ; Dabei level m�glichst gro�, und bei festem level length m�glichst gro�.
  (if (or (numberp object) (symbolp object)) ; von length und level unbeeinflusst?
    (write-to-string object)
    (macrolet ((minlength (level) `,level)
               (maxlength (level) `(* 2 (+ ,level 1))))
      ; Um level m�glist gro� zu bekommen, dabei length = minlength w�hlen.
      (let* ((level ; Bin�rsuche nach dem richtigen level
               (let ((level1 0) (level2 16))
                 (loop
                   (when (= (- level2 level1) 1) (return))
                   (let ((levelm (floor (+ level1 level2) 2)))
                     (if (<= (length (write-to-string object :level levelm :length (minlength levelm))) max)
                       (setq level1 levelm) ; levelm passt, probiere gr��ere
                       (setq level2 levelm) ; levelm passt nicht, probiere kleinere
                 ) ) )
                 level1
             ) )
             (length ; Bin�rsuche nach dem richtigen length
               (let ((length1 (minlength level)) (length2 (maxlength level)))
                 (loop
                   (when (= (- length2 length1) 1) (return))
                   (let ((lengthm (floor (+ length1 length2) 2)))
                     (if (<= (length (write-to-string object :level level :length lengthm)) max)
                       (setq length1 lengthm) ; lengthm passt, probiere gr��ere
                       (setq length2 lengthm) ; lengthm passt nicht, probiere kleinere
                 ) ) )
                 length1
            )) )
        (write-to-string object :level level :length length)
) ) ) )
