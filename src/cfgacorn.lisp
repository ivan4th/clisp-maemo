#0Y UTF-8 ;;;  This file is Unicode/UTF-8 encoded.  -*- coding: utf-8 -*-

;;; ENGLISH: Site specific definitions, to be modified on installation
;;; DEUTSCH: Funktionen, die beim Transportieren zu ändern sind
;;; FRANCAIS: Fonctions dépendantes de l'installation

(in-package "LISP")
(export '(clhs-root *clhs-root-default*))
(mapcar #'fmakunbound '(machine-type machine-version machine-instance
                        short-site-name long-site-name
                        edit-file editor-tempfile))

(defun machine-type () "Acorn")
(defun machine-version () "Risc PC, OS 3.7")
(defun machine-instance () (or (sys::getenv "HOSTNAME") "edit config.lisp"))

(defun short-site-name () (or (sys::getenv "ORGANIZATION") "edit config.lisp"))
(defun long-site-name () (or (sys::getenv "ORGANIZATION") "edit config.lisp"))

;; ENGLISH: The name of the editor:
;; DEUTSCH: Der Name des Editors:
;; FRANCAIS: Nom de l'éditeur :
(defparameter *editor* "filer_run")
(defun editor-name () (or (sys::getenv "EDITOR") *editor*))

;; ENGLISH: (edit-file file) edits a file.
;; DEUTSCH: (edit-file file) editiert eine Datei.
;; FRANCAIS: (edit-file file) permet l'édition d'un fichier.
(defun edit-file (file)
  (open file :direction :probe :if-does-not-exist :create)
  (let ((pathname (truename file)))
    (shell
      (format nil "~A ~A"
                  (editor-name)
                  (if (pathname-type pathname)
                    ; swap pathname's name and type
                    (merge-pathnames
                      (make-pathname :name (pathname-type pathname)
                                     :type (pathname-name pathname)
                      )
                      pathname
                    )
                    pathname
                  )
) ) ) )

;; ENGLISH: The temporary file LISP creates for editing:
;; DEUTSCH: Das temporäre File, das LISP beim Editieren anlegt:
;; FRANCAIS: Fichier temporaire créé par LISP pour l'édition :
(defun editor-tempfile ()
  ; We write this instead of "<Wimp$ScrapDir>.lisptemp" in order to
  ; make sure that all the components of (sys::getenv "Wimp$ScrapDir")
  ; are treated as directory components.
  (merge-pathnames "lisptemp" "<Wimp$ScrapDir>.")
)

;; ENGLISH: The list of directories where programs are searched on LOAD etc.:
;; DEUTSCH: Die Liste von Directories, in denen Programme bei LOAD etc. gesucht
;;          werden:
;; FRANCAIS: Liste de répertoires où chercher un fichier programme:
(defparameter *load-paths* '(#"@.")) ; may add #"@.***." when this will be implemented

;; ENGLISH: This makes screen output prettier:
;; DEUTSCH: Dadurch sehen Bildschirmausgaben besser aus:
;; FRANCAIS: Pour que les sorties sur l'écran soient plus lisibles:
(setq *print-pretty* t)

;; ENGLISH: Common Lisp HyperSpec access
(defvar *clhs-root-default*)
(defun clhs-root ()
  "This returns the root URL for the Common Lisp HyperSpec.
You can set the environment variable `CLHSROOT' or redefine this function
in ~/.clisprc.  On win32 you can also use the Registry."
  (or (sys::getenv "CLHSROOT") *clhs-root-default*))
(setq *clhs-root-default* "http://www.lisp.org/HyperSpec")
