#+CLISP (progn (setf (symbol-function 'setf-gethash)
                     (symbol-function 'sys::puthash)) t)
#+CLISP t
#+AKCL (progn (setf (symbol-function 'setf-gethash)
                    (symbol-function 'sys:hash-set)) t)
#+AKCL t
#+ALLEGRO (progn (setf (symbol-function 'setf-gethash)
                       (symbol-function 'excl::%puthash)) t)
#+ALLEGRO t
#+CMU (progn (setf (symbol-function 'setf-gethash)
                   (symbol-function 'cl::%puthash)) t)
#+CMU t

(DEFUN SYMBOLE ()
  (LET ((B 0.)
        (HASH-TABLE (MAKE-HASH-TABLE :SIZE 20. :REHASH-THRESHOLD #+XCL 15. #-XCL 0.75))
        (LISTE (MAKE-LIST 50.))
        (LISTE2 (MAKE-LIST 50.)))
    (RPLACD (LAST LISTE) LISTE)
    (RPLACD (LAST LISTE2) LISTE2)
    (DO-SYMBOLS (X (FIND-PACKAGE #+XCL 'lisptest #-XCL "LISP"))
;     (PRINT X) (FINISH-OUTPUT)
      (COND ((CAR LISTE)
             (LET ((HVAL (GETHASH (CAR LISTE) HASH-TABLE))
                   (LVAL (CAR LISTE2)))
               (UNLESS (EQ HVAL LVAL)
                 (PRINT "mist, hash-tabelle kaputt")
                 (PRINT (CAR LISTE))
                 (PRINT HASH-TABLE)
                 (PRINT (HASH-TABLE-COUNT HASH-TABLE))
                 (PRINT "hval:") (PRINT HVAL)
                 (PRINT "lval:") (PRINT LVAL)
                 (RETURN-FROM SYMBOLE 'ERROR))
               (REMHASH (CAR LISTE) HASH-TABLE)
               #+XCL (WHEN (< (ROOM) 30000.) (SYSTEM::%GARBAGE-COLLECTION))
               (SETF-GETHASH X HASH-TABLE (SETQ B (+ 1. B)))
               (RPLACA LISTE X)
               (RPLACA LISTE2 B)
               (SETQ LISTE (CDR LISTE))
               (SETQ LISTE2 (CDR LISTE2))))
            (T (SETF-GETHASH X HASH-TABLE (SETQ B (+ 1. B)))
               (RPLACA LISTE X)
               (RPLACA LISTE2 B)
               (SETQ LISTE (CDR LISTE))
               (SETQ LISTE2 (CDR LISTE2)))))))
symbole


(SYMBOLE) nil

