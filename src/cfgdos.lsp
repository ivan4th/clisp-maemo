;;; ENGLISH: Site specific definitions, to be modified on installation
;;; DEUTSCH: Funktionen, die beim Transportieren zu �ndern sind
;;; FRANCAIS: Fonctions d�pendantes de l'installation

(in-package "LISP")
(mapcar #'fmakunbound '(machine-type machine-version machine-instance
                        short-site-name long-site-name
                        editor-name editor-tempfile edit-file))

(defun machine-type () "PC/486")
(defun machine-version () "486/33")
(defun machine-instance () (or (sys::getenv "HOSTNAME") "edit config.lsp"))

(defun short-site-name () (or (sys::getenv "ORGANIZATION") "edit config.lsp"))
(defun long-site-name () (or (sys::getenv "ORGANIZATION") "edit config.lsp"))

;; ENGLISH: The name of the editor:
;; DEUTSCH: Der Name des Editors:
;; FRANCAIS: Nom de l'�diteur :
(defparameter *editor* "C:\\UTIL\\PRODIT.EXE")
(defun editor-name () (or (sys::getenv "EDITOR") *editor*))

;; ENGLISH: The temporary file LISP creates for editing:
;; DEUTSCH: Das tempor�re File, das LISP beim Editieren anlegt:
;; FRANCAIS: Fichier temporaire cr�� par LISP pour l'�dition :
(defun editor-tempfile ()
  #+DOS "LISPTEMP.LSP"
  #+OS/2 "lisptemp.lsp"
)

;; ENGLISH: (edit-file file) edits a file.
;; DEUTSCH: (edit-file file) editiert eine Datei.
;; FRANCAIS: (edit-file file) permet l'�dition d'un fichier.
(defun edit-file (file)
  ; The function EXECUTE apparently crashes on batch files. Work around.
  (let ((editor (editor-name))
        (filename (namestring file t)))
    (if #-OS/2 (string= (pathname-type editor) "BAT")
        #+OS/2 (string-equal (pathname-type editor) "cmd")
      (shell (format nil "~A ~A" editor filename))
      (execute editor filename)
) ) )

;; ENGLISH: Treat Ctrl-Z in files as whitespace. Some losing middle-age
;;          editors insist on appending this to files.
;; DEUTSCH: Behandle Ctrl-Z in Dateien als Leerstelle. Einige dumme
;;          Steinzeit-Editoren bestehen darauf, das an Dateien anzuh�ngen.
;; FRANCAIS: Traite Ctrl-Z dans les fichiers comme un espace. Quelques
;;           �diteurs du moyen age n'arr�tent pas d'ajouter cela aux fichiers.
(eval-when (load eval compile)
  (set-syntax-from-char #\Code26 #\Space)
)

;; ENGLISH: The list of directories where programs are searched on LOAD etc.
;;          if device and directory are unspecified:
;; DEUTSCH: Die Liste von Directories, in denen Programme bei LOAD etc. gesucht
;;          werden, wenn dabei Laufwerk und Directory nicht angegeben ist:
;; FRANCAIS: Liste de r�pertoires o� chercher un fichier lorsqu'un r�pertoire
;;           particulier n'est pas indiqu� :
(defparameter *load-paths*
  '(#"C:"               ; erst im Current-Directory von Laufwerk C:
    #"C:\\CLISP\\...\\" ; dann in allen Directories unterhalb C:\CLISP
   )
)

;; ENGLISH: This makes screen output prettier:
;; DEUTSCH: Dadurch sehen Bildschirmausgaben besser aus:
;; FRANCAIS: Pour que les sorties sur l'�cran soient plus lisibles:
(setq *print-pretty* t)

;; ENGLISH: Also set the variable *default-time-zone* in TIMEZONE.LSP according
;;          to your time zone.
;; DEUTSCH: Setzen Sie auch die Variable *default-time-zone* in TIMEZONE.LSP
;;          auf die bei Ihnen g�ltige Zeitzone.
;; FRANCAIS: Dans TIMEZONE.LSP, affectez � *default-time-zone* la valeur
;;           correspondante � votre fuseau horaire.

