;;; ENGLISH: Site specific definitions, to be modified on installation
;;; DEUTSCH: Funktionen, die beim Transportieren zu �ndern sind
;;; FRANCAIS: Fonctions d�pendantes de l'installation

(in-package "LISP")
(mapcar #'fmakunbound '(machine-type machine-version machine-instance
                        short-site-name long-site-name editor-tempfile))

(defun machine-type () "Amiga")
(defun machine-version () "Amiga, OS 2.04-3.1")
(defun machine-instance () (or (sys::getenv "HOSTNAME") "edit config.lsp"))

(defun short-site-name () (or (sys::getenv "ORGANIZATION") "edit config.lsp"))

(defun long-site-name () (or (sys::getenv "ORGANIZATION") "edit config.lsp"))

;; ENGLISH: The name of the editor:
;; DEUTSCH: Der Name des Editors:
;; FRANCAIS: Nom de l'�diteur :
(defparameter *editor* "emacs")
(defun editor-name () (or (sys::getenv "EDITOR") *editor*))

;; ENGLISH: The temporary file LISP creates for editing:
;; DEUTSCH: Das tempor�re File, das LISP beim Editieren anlegt:
;; FRANCAIS: Fichier temporaire cr�� par LISP pour l'�dition :
(defun editor-tempfile () "T:lisptemp.lsp")

;; ENGLISH: The list of directories where programs are searched on LOAD etc.
;;          if device and directory are unspecified:
;; DEUTSCH: Die Liste von Directories, in denen Programme bei LOAD etc. gesucht
;;          werden, wenn dabei Laufwerk und Directory nicht angegeben ist:
;; FRANCAIS: Liste de r�pertoires o� chercher un fichier lorsqu'un r�pertoire
;;           particulier n'est pas indiqu� :
(defparameter *load-paths*
  '(#"**/"      ; erst in allen Directories unterhalb von hier
    #"LISP:**/" ; dann in allen Directories unterhalb von LISP:
   )
)

;; ENGLISH: This makes screen output both faster and output prettier:
;; DEUTSCH: Dadurch sehen Bildschirmausgaben schneller und besser aus:
;; FRANCAIS: Pour que les sorties sur l'�cran soient plus rapides et plus lisibles:
(setq *print-pretty* t)

;; ENGLISH: Also set the variable *default-time-zone* in TIMEZONE.LSP according
;;          to your time zone.
;; DEUTSCH: Setzen Sie auch die Variable *default-time-zone* in TIMEZONE.LSP
;;          auf die bei Ihnen g�ltige Zeitzone.
;; FRANCAIS: Dans TIMEZONE.LSP, affectez � *default-time-zone* la valeur
;;           correspondante � votre fuseau horaire.
;; (setq *default-time-zone* 0)

;; ENGLISH: Common Lisp HyperSpec access
(defvar *clhs-root-default*)
(defun clhs-root ()
  "This returns the root URL for the Common Lisp HyperSpec.
You can set the environment variable `CLHSROOT' or redefine this function
in ~/.clisprc.  On win32 you can also use the Registry."
  (or (sys::getenv "CLHSROOT") *clhs-root-default*))
(setq *clhs-root-default* "http://www.lisp.org/HyperSpec")
