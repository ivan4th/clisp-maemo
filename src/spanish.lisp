;;; Spanish translations of DEFINTERNATIONALed values.
;;; Bruno Haible, Carlos Linares

(in-package "LISP")

(export 'ESPA�OL)

(deflanguage ESPA�OL)

(in-package "SYSTEM")

(deflocalized y-or-n ESPA�OL '((#\N) . (#\S #\Y)))
(deflocalized yes-or-no ESPA�OL '(("no") . ("si")))

