;;; German translations of DEFINTERNATIONALed values.
;;; Bruno Haible, Michael Stoll

(in-package "LISP")

(export 'DEUTSCH)

(deflanguage DEUTSCH)

(in-package "SYSTEM")

(deflocalized date-format DEUTSCH
  (formatter "~1{~3@*~D.~4@*~D.~5@*~D ~2@*~2,'0D:~1@*~2,'0D:~0@*~2,'0D~:}")
)
(deflocalized room-format DEUTSCH
  (list (formatter "Klasse~VT Instanzen   Gr��e (Bytes)   �-Gr��e~%")
        (formatter "------~VT ---------   -------------  ---------~%")
        (formatter       "~VT~8D     ~9D  ~13,3F~%")
) )
(deflocalized space-format DEUTSCH
  (list (formatter       "~VT     dauerhaft             tempor�r~%")
        (formatter "Klasse~VTInstanzen   Bytes    Instanzen   Bytes~%")
        (formatter "------~VT--------- ---------  --------- ---------~%")
        (formatter       "~VT~9D ~9D  ~9D ~9D~%")
) )
(deflocalized y-or-n DEUTSCH '((#\N) . (#\J #\Y)))
(deflocalized yes-or-no DEUTSCH '(("nein" "nee" "n�") . ("ja")))
(deflocalized print-condition-format DEUTSCH
  (formatter "Ausnahmefall vom Typ ~S.")
)

