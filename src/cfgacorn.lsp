;;; ENGLISH: Site specific definitions, to be modified on installation
;;; DEUTSCH: Funktionen, die beim Transportieren zu �ndern sind
;;; FRANCAIS: Fonctions d�pendantes de l'installation

(in-package "LISP")
(mapcar #'fmakunbound '(machine-type machine-version machine-instance
                        short-site-name long-site-name
                        edit-file editor-tempfile))

(defun machine-type () "Acorn")
(defun machine-version () "Risc PC, OS 3.7")
(defun machine-instance () "Burwood's Risc PC")

(defun short-site-name () "Home")
(defun long-site-name () "Burwood's Home, England")

;; ENGLISH: The name of the editor:
;; DEUTSCH: Der Name des Editors:
;; FRANCAIS: Nom de l'�diteur :
(defparameter *editor* "filer_run")
(defun editor-name () (or (sys::getenv "EDITOR") *editor*))

;; ENGLISH: (edit-file file) edits a file.
;; DEUTSCH: (edit-file file) editiert eine Datei.
;; FRANCAIS: (edit-file file) permet l'�dition d'un fichier.
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
;; DEUTSCH: Das tempor�re File, das LISP beim Editieren anlegt:
;; FRANCAIS: Fichier temporaire cr�� par LISP pour l'�dition :
(defun editor-tempfile ()
  ; We write this instead of "<Wimp$ScrapDir>.lisptemp" in order to
  ; make sure that all the components of (sys::getenv "Wimp$ScrapDir")
  ; are treated as directory components.
  (merge-pathnames "lisptemp" "<Wimp$ScrapDir>.")
)

;; ENGLISH: The list of directories where programs are searched on LOAD etc.:
;; DEUTSCH: Die Liste von Directories, in denen Programme bei LOAD etc. gesucht
;;          werden:
;; FRANCAIS: Liste de r�pertoires o� chercher un fichier programme:
(defparameter *load-paths* '(#"@.")) ; may add #"@.***." when this will be implemented

;; ENGLISH: This makes screen output prettier:
;; DEUTSCH: Dadurch sehen Bildschirmausgaben besser aus:
;; FRANCAIS: Pour que les sorties sur l'�cran soient plus lisibles:
(setq *print-pretty* t)

