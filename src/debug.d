# Top-Level-Schleife, Hilfsfunktionen f�r Debugger, Stepper von CLISP
# Bruno Haible 30.8.1997
# ILISP friendliness: Marcus Daniels 8.4.1994

#include "lispbibl.c"


# ---------------------------------------------------------------------------- #
#                             Top-Level-Schleifen

# (SYS::READ-FORM ostream istream prompt [commandlist])
# Liest eine Form (interaktiv) von einem Input-Stream.
# Statt einer Form kann auch eine Sondertaste aus commandlist (eine frische
# Aliste) oder SYS::*KEY-BINDINGS* eingegeben werden.
# > STACK_1: prompt, ein String
# > STACK_0: Befehlsliste (frische Aliste) oder #<UNBOUND>
# < STACK_1: Output-Stream *standard-output*
# < STACK_0: Input-Stream *standard-input*
# < mv_space/mv_count: Werte form, NIL oder (bei EOF) T, T
# kann GC ausl�sen
  local Values read_form (void);
# (defun read-form (ostream istream prompt &optional (command-list nil))
#   (loop
#     (let ((raw (terminal-raw istream nil)))
#       (when (interactive-stream-p istream)
#         (terpri ostream)
#         (write-string prompt ostream)
#         (force-output ostream)
#       )
#       (let* ((eof-value "EOF")
#              (form (let ((*read-suppress* nil)
#                          (*key-bindings* (nreconc command-list *key-bindings*)))
#                      (read istream nil eof-value nil)
#             ))     )
#         (terminal-raw istream raw)
#         (if (eql form eof-value)
#           (progn (clear-input istream) (setq istream *debug-io*))
#           (progn (clear-input-upto-newline istream) (return (values form nil)))
# ) ) ) ) )
  local Values read_form()
  { pushSTACK(STACK_1); pushSTACK(STACK_1);
    STACK_3 = var_stream(S(standard_output),strmflags_wr_ch_B); # ostream := Wert von *STANDARD-OUTPUT*
    STACK_2 = var_stream(S(standard_input),strmflags_rd_ch_B); # istream := Wert von *STANDARD-INPUT*
    # Stackaufbau: ostream, istream, prompt, command-list.
    pushSTACK(STACK_2); pushSTACK(NIL); funcall(L(terminal_raw),2); pushSTACK(value1);
    # Stackaufbau: ostream, istream, prompt, command-list, raw.
   {var signean status = stream_listen(STACK_3); # horchen
    if (status<0) goto eof;
    # bereits Zeichen verf�gbar (und nicht im ilisp_mode) -> kein Prompt
    if (ilisp_mode || interactive_stream_p(STACK_3))
      { # interaktiver Input-Stream -> Prompt ausgeben:
        #if 0
          terpri(&STACK_4); # (TERPRI ostream)
        #else
          # Dasselbe mit Abfangen von Endlosrekursion:
          # (let ((*recurse-count-standard-output* (1+ *recurse-count-standard-output*)))
          #   (when (> *recurse-count-standard-output* 3)
          #     (setq *recurse-count-standard-output* 0)
          #     (makunbound '*standard-output*)
          #     (let ((*recurse-count-debug-io* (1+ *recurse-count-debug-io*)))
          #       (when (> *recurse-count-debug-io* 3)
          #         (setq *recurse-count-debug-io* 0)
          #         (makunbound '*debug-io*)
          #         (symbol-stream '*debug-io* :io)
          #       )
          #       (symbol-stream '*standard-output* :output)
          #   ) )
          #   (terpri *standard-output*)
          # )
          dynamic_bind(S(recurse_count_standard_output),fixnum_inc(Symbol_value(S(recurse_count_standard_output)),1)); # sys::*recurse-count-standard-output* erh�hen
          if (!posfixnump(Symbol_value(S(recurse_count_standard_output)))) # sollte ein Fixnum >=0 sein
            { Symbol_value(S(recurse_count_standard_output)) = Fixnum_0; } # sonst Notkorrektur
          if (posfixnum_to_L(Symbol_value(S(recurse_count_standard_output))) > 3)
            { # Mehrfach verschachtelte Fehlermeldung.
              Symbol_value(S(recurse_count_standard_output)) = Fixnum_0;
              Symbol_value(S(standard_output)) = unbound;
              dynamic_bind(S(recurse_count_debug_io),fixnum_inc(Symbol_value(S(recurse_count_debug_io)),1)); # sys::*recurse-count-debug-io* erh�hen
              if (!posfixnump(Symbol_value(S(recurse_count_debug_io)))) # sollte ein Fixnum >=0 sein
                { Symbol_value(S(recurse_count_debug_io)) = Fixnum_0; } # sonst Notkorrektur
              if (posfixnum_to_L(Symbol_value(S(recurse_count_debug_io))) > 3)
                { # Mehrfach verschachtelte Fehlermeldung.
                  Symbol_value(S(recurse_count_debug_io)) = Fixnum_0;
                  Symbol_value(S(debug_io)) = unbound;
                  var_stream(S(debug_io),strmflags_rd_ch_B|strmflags_wr_ch_B);
                }
              STACK_(4+3+3) = var_stream(S(standard_output),strmflags_wr_ch_B); # ostream := Wert von *STANDARD-OUTPUT*
              dynamic_unbind();
            }
          terpri(&STACK_(4+3)); # (TERPRI ostream)
          dynamic_unbind();
        #endif
        write_string(&STACK_4,STACK_2); # (WRITE-STRING prompt ostream)
        force_output(STACK_4);
      }
    # Prompt OK
    { var object* istream_ = &STACK_3;
      #if 0 # Das erweist sich doch als ungeschickt: Dr�ckt man Ctrl-C w�hrend
            # der Eingabe, so hat man dann in der Break-Schleife manche Kommandos
            # doppelt in der Liste!
      {var object list = Symbol_value(S(key_bindings)); # bisherige Key-Bindings
       if (!eq(STACK_1,unbound)) # command-list angegeben?
         { list = nreconc(STACK_1,list); } # ja -> davorh�ngen
       dynamic_bind(S(key_bindings),list); # SYS::*KEY-BINDINGS* binden
      }
      #else
      # statt        (nreconc command-list *key-bindings*)
      # doch lieber  (nreverse command-list)
      {var object list = (eq(STACK_1,unbound) ? NIL : nreverse(STACK_1));
       dynamic_bind(S(key_bindings),list); # SYS::*KEY-BINDINGS* binden
      }
      #endif
      #if !defined(TERMINAL_USES_KEYBOARD) # auf dem Atari ging's �ber Funktionstasten
      if (status>0) # nur bei interaktivem Input-Stream
        { # Erkennung von Kommandos statt Formen:
          # (multiple-value-bind (line flag) (read-line istream)
          #   (let ((h (assoc line *key-bindings* :test #'string-equal)))
          #     (when h (funcall (cdr h)) (return t))
          #   )
          #   (setq istream
          #     (make-concatenated-stream
          #       (make-string-input-stream
          #         (if flag line (concatenate 'string line (string #\Newline)))
          #       )
          #       istream
          # ) ) )
          pushSTACK(*istream_); pushSTACK(NIL); pushSTACK(NIL);
          funcall(L(read_line),3); # (READ-LINE istream nil nil)
         {var object line = value1;
          if (nullp(line)) { dynamic_unbind(); goto eof; } # EOF am Zeilenanfang?
          # line in *KEY-BINDINGS* suchen:
          {var object alist = Symbol_value(S(key_bindings));
           while (consp(alist))
             { if (mconsp(Car(alist)) && simple_string_p(Car(Car(alist)))
                   && string_equal(line,Car(Car(alist)))
                  )
                 # gefunden -> Funktion dazu aufrufen:
                 { funcall(Cdr(Car(alist)),0); dynamic_unbind(); goto eof; }
               alist = Cdr(alist);
          }  }
          # String-Input-Stream f�r diese Zeile basteln:
          if (nullp(value2))
            { pushSTACK(line); pushSTACK(O(newline_string));
              line = string_concat(2); # evtl. noch ein Newline anh�ngen
            }
          pushSTACK(line); funcall(L(make_string_input_stream),1);
          # Concatenated-Stream basteln:
          pushSTACK(value1); pushSTACK(*istream_);
          funcall(L(make_concatenated_stream),2);
          *istream_ = value1; # und an istream zuweisen
        }}
      #endif
     {var object obj;
      dynamic_bind(S(read_suppress),NIL); # *READ-SUPPRESS* = NIL
      obj = stream_read(istream_,NIL,NIL); # Objekt lesen (recursive-p=NIL, whitespace-p=NIL)
      dynamic_unbind();
      dynamic_unbind();
      if (!eq(obj,eof_value)) # EOF (nach Whitespace) abfragen
        { pushSTACK(obj);
          pushSTACK(STACK_(3+1)); pushSTACK(STACK_(0+1+1)); funcall(L(terminal_raw),2);
          # wartenden Input bis Zeilenende l�schen
          if (interactive_stream_p(STACK_(3+1)))
            { while (stream_listen(STACK_(3+1)) == 0)
                { var object ch = peek_char(&STACK_(3+1));
                  if (eq(ch,eof_value))
                    break;
                  read_char(&STACK_(3+1));
                  if (eq(ch,code_char(NL)))
                    break;
            }   }
          value1 = popSTACK(); value2 = NIL; mv_count=2; # obj, NIL als Werte
          skipSTACK(3); return;
        }
    }}
    eof: # bei EOF angelangt
    pushSTACK(STACK_3); pushSTACK(STACK_(0+1)); funcall(L(terminal_raw),2);
    # (clear-input istream) ausf�hren (um bei interaktivem Stream das EOF zu
    # schlucken: das fortzusetzende Programm k�nnte das EOF mi�verstehen):
    clear_input(STACK_3);
    value1 = value2 = T; mv_count=2; # T, T als Werte
    skipSTACK(3); return;
  }}

# (SYS::READ-FORM prompt [commandlist])
# liest eine Form (interaktiv) von *standard-input*.
# prompt mu� ein String sein.
# Statt einer Form kann auch eine Sondertaste aus commandlist (eine frische
# Aliste) oder SYS::*KEY-BINDINGS* eingegeben werden.
# Werte: form, NIL oder (bei EOF) T, T
LISPFUN(read_form,1,1,norest,nokey,0,NIL)
  { read_form(); skipSTACK(2); }

# (SYS::READ-EVAL-PRINT prompt [commandlist])
# liest eine Form, wertet sie aus und gibt die Werte aus.
# prompt mu� ein String sein.
# Statt einer Form kann auch eine Sondertaste aus commandlist (eine frische
# Aliste) oder SYS::*KEY-BINDINGS* eingegeben werden.
# Werte: NIL oder (bei Sondertaste oder EOF) T
LISPFUN(read_eval_print,1,1,norest,nokey,0,NIL)
# (defun read-eval-print (prompt &optional (command-list nil))
#   (multiple-value-bind (form flag)
#       (read-form *standard-output* *standard-input* prompt command-list)
#     (if flag
#       form ; T zur�ck
#       (progn
#         (setq +++ ++ ++ + + - - form)
#         (let ((vals (multiple-value-list (eval-env form [aktuellesEnvironment]))))
#           (setq /// // // / / vals)
#           (setq *** ** ** * * (first vals))
#           ; primitiv:
#         #|(do ((ostream *standard-output*)
#                (L vals (cdr L)))
#               ((atom L))
#             (write (car L) ostream)
#             (when (consp (cdr L))
#               (write-string " ;" ostream)
#               (terpri ostream)
#           ) )
#         |#; unn�tige Leerzeile zwischen Input und Output vermeiden:
#           (let ((ostream *standard-output*))
#             (fresh-line ostream)
#             (when (consp vals)
#               (write (car vals) ostream)
#               (do ((L (cdr vals) (cdr L)))
#                   ((atom L))
#                 (write-string " ;" ostream)
#                 (terpri ostream)
#                 (write (car L) ostream)
#           ) ) )
#         )
#         nil
# ) ) ) )
  { read_form(); # Form lesen
    # Stackaufbau: ostream, istream.
    if (!nullp(value2)) # flag ?
      { mv_count=1; skipSTACK(2); return; } # T als Wert zur�ck
    Symbol_value(S(plus3)) = Symbol_value(S(plus2)); # (SETQ +++ ++)
    Symbol_value(S(plus2)) = Symbol_value(S(plus)); # (SETQ ++ +)
    Symbol_value(S(plus)) = Symbol_value(S(minus)); # (SETQ + -)
    Symbol_value(S(minus)) = value1; # (SETQ - form)
    eval(value1); # Form auswerten (im aktuellen Environment)
    pushSTACK(value1); # einen Wert retten
    mv_to_list(); # Werte in Liste packen
    # Stackaufbau: ..., val1, vals.
    Symbol_value(S(durch3)) = Symbol_value(S(durch2)); # (SETQ /// //)
    Symbol_value(S(durch2)) = Symbol_value(S(durch)); # (SETQ // /)
    Symbol_value(S(durch)) = STACK_0; # (SETQ / vals)
    Symbol_value(S(mal3)) = Symbol_value(S(mal2)); # (SETQ *** **)
    Symbol_value(S(mal2)) = Symbol_value(S(mal)); # (SETQ ** *)
    Symbol_value(S(mal)) = STACK_1; # (SETQ * val1)
    # Werte ausgeben:
    STACK_(1+2) = var_stream(S(standard_output),strmflags_wr_ch_B); # ostream := Wert von *STANDARD-OUTPUT*
    #if 0
    if (mconsp(STACK_0))
      { loop
          { var object valsr = STACK_0;
            STACK_0 = Cdr(valsr);
            terpri(&STACK_(1+2));
            prin1(&STACK_(1+2),Car(valsr)); # n�chsten Wert ausgeben
            # ';' als Trennzeichen vorm Zeilenende:
            if (matomp(STACK_0)) break;
            write_schar(&STACK_(1+2),' ');
            write_schar(&STACK_(1+2),';');
      }   }
    #else
    # unn�tige Leerzeile zwischen Input und Output vermeiden:
    # (Es erscheint immer noch eine unn�tige Leerzeile am Bildschirm,
    # wenn stdin vom Terminal kommt und stdout eine Pipe ist, die
    # letztendlich wieder aufs Terminal geht - z.B. via '| tee logfile'.
    # In diesem Fall m�ssen wir aber - eben wegen 'logfile' - ein NL auf
    # stdout ausgeben, und da stdin am Zeilenende von selbst ein NL aus-
    # gibt, ist diese Leerzeile wirklich unvermeidlich.)
    if (!eq(get_line_position(STACK_(1+2)),Fixnum_0))
      { terpri(&STACK_(1+2)); } # (fresh-line ostream)
    if (mconsp(STACK_0))
      { loop
          { var object valsr = STACK_0;
            STACK_0 = Cdr(valsr);
            prin1(&STACK_(1+2),Car(valsr)); # n�chsten Wert ausgeben
            # ';' als Trennzeichen vorm Zeilenende:
            if (matomp(STACK_0)) break;
            write_schar(&STACK_(1+2),' ');
            write_schar(&STACK_(1+2),';');
            terpri(&STACK_(1+2));
      }   }
    #endif
    skipSTACK(4);
    value1 = NIL; mv_count=1; # NIL als Wert
  }

# Startet den normalen Driver (Read-Eval-Print-Loop)
# driver();
  global void driver (void);
  global void driver()
    { loop
        { var object driverfun = Symbol_value(S(driverstern)); # Wert von *DRIVER*
          if (nullp(driverfun)) break;
          funcall(driverfun,0); # mit 0 Argumenten aufrufen
        }
      # Default-Driver:
      Symbol_value(S(break_count)) = Fixnum_0; # SYS::*BREAK-COUNT* := 0
      # dann einen Driver-Frame aufbauen:
      { var object* top_of_frame = STACK; # Pointer �bern Frame
        var DRIVER_frame_data returner_and_data; # R�cksprungpunkt merken
        #ifdef HAVE_NUM_STACK
        returner_and_data.old_NUM_STACK_normal = NUM_STACK_normal;
        #endif
        finish_entry_frame(DRIVER,&!returner_and_data.returner,,;);
        # Hier ist der Einsprungpunkt.
        loop
          { # (SYS::READ-EVAL-PRINT "> ") ausf�hren:
            pushSTACK(O(prompt_string)); # Prompt "> "
            funcall(L(read_eval_print),1);
            if (eq(value1,T)) break; # EOF gelesen -> Schleife beenden
          }
        skipSTACK(2); # Driver-Frame aufl�sen
    } }

# Startet einen untergeordneten Driver (Read-Eval-Print-Loop)
# break_driver(continuable);
# > continuable: Flag, ob nach Beendigung des Drivers fortgefahren werden kann.
# kann GC ausl�sen
  global void break_driver (object continuable);
  global void break_driver(continuable)
    var object continuable;
    { pushSTACK(continuable);
     {var object driverfun = Symbol_value(S(break_driver)); # Wert von *BREAK-DRIVER*
      if (!nullp(driverfun))
        {
          #ifdef HAVE_NUM_STACK
          var uintD* old_NUM_STACK = NUM_STACK;
          var uintD* old_NUM_STACK_normal = NUM_STACK_normal;
          #endif
          pushSTACK(STACK_0); funcall(driverfun,1); # mit Argument continuable aufrufen
          if (nullp(popSTACK())) # nicht continuable?
            { reset(); } # -> dann zur n�chsten Schleife zur�ck
          #ifdef HAVE_NUM_STACK
          NUM_STACK = old_NUM_STACK;
          NUM_STACK_normal = old_NUM_STACK_normal;
          #endif
        }
        else
        { # Default-Driver:
          # (CLEAR-INPUT *DEBUG-IO*) ausf�hren (weil das, was der Benutzer bisher
          # getippt hat, sicher nicht in Erwartung des Errors getippt wurde):
          clear_input(var_stream(S(debug_io),strmflags_rd_ch_B|strmflags_wr_ch_B));
          # SYS::*BREAK-COUNT* erh�hen:
          dynamic_bind(S(break_count),fixnum_inc(Symbol_value(S(break_count)),1));
          if (!posfixnump(Symbol_value(S(break_count)))) # sollte ein Fixnum >=0 sein
            { Symbol_value(S(break_count)) = Fixnum_0; } # sonst Notkorrektur
          # *STANDARD-INPUT* und *STANDARD-OUTPUT* an *DEBUG-IO* binden:
          {var object stream = var_stream(S(debug_io),strmflags_rd_ch_B|strmflags_wr_ch_B);
           dynamic_bind(S(standard_input),stream);
           dynamic_bind(S(standard_output),stream);
          }
          # *PRINT-ESCAPE* an T binden:
          dynamic_bind(S(print_escape),T);
          # Prompt aufbauen:
          { # (format nil "~S. Break> " SYS::*BREAK-COUNT*)
            #   ==
            # (with-output-to-string (s)
            #   (prin1 SYS::*BREAK-COUNT* s) (write-string ". Break> " s)
            # )
            #   ==
            # (let ((s (make-string-output-stream)))
            #   (prin1 SYS::*BREAK-COUNT* s) (write-string ". Break> " s)
            #   (get-output-stream-string s)
            # )
            pushSTACK(make_string_output_stream());
            prin1(&STACK_0,Symbol_value(S(break_count)));
            write_sstring(&STACK_0,O(breakprompt_string));
            STACK_0 = get_output_stream_string(&STACK_0);
          }
          # Driver-Frame aufbauen:
         {var object* top_of_frame = STACK; # Pointer �bern Frame
          var DRIVER_frame_data returner_and_data; # R�cksprungpunkt merken
          #ifdef HAVE_NUM_STACK
          var uintD* old_NUM_STACK = NUM_STACK;
          returner_and_data.old_NUM_STACK_normal = NUM_STACK_normal;
          #endif
          finish_entry_frame(DRIVER,&!returner_and_data.returner,,;);
          # Hier ist der Einsprungpunkt.
          #ifdef HAVE_NUM_STACK
          NUM_STACK_normal = old_NUM_STACK;
          #endif
          loop
            { # (SYS::READ-EVAL-PRINT Prompt) ausf�hren:
              pushSTACK(STACK_(0+2)); # Prompt "nnn. Break> "
              funcall(L(read_eval_print),1);
              if (eq(value1,T)) break; # EOF gelesen -> Schleife beenden
            }
          if (nullp(STACK_(0+4*3+1+2))) # nicht continuable?
            { unwind(); reset(); } # -> dann zur n�chsten Schleife zur�ck
          #ifdef HAVE_NUM_STACK
          NUM_STACK = old_NUM_STACK;
          NUM_STACK_normal = returner_and_data.old_NUM_STACK_normal;
          #endif
          skipSTACK(1+2); # Driver-Frame aufl�sen, Prompt vergessen
          dynamic_unbind(); dynamic_unbind(); dynamic_unbind(); dynamic_unbind();
          skipSTACK(1);
    }}  }}

LISPFUNN(load,1)
# (LOAD filename), primitivere Version als in CLTL S. 426
  # Methode:
  # (defun load (filename)
  #   (let ((stream (open filename))
  #         (end-of-file "EOF")) ; einmaliges Objekt
  #     (loop
  #       (let ((obj (read stream nil end-of-file)))
  #         (when (eql obj end-of-file) (return))
  #         (if (compiled-function-p obj) (funcall obj) (eval obj))
  #     ) )
  #     (close stream)
  #     t
  # ) )
  { funcall(L(open),1); # (OPEN filename)
    pushSTACK(value1); # stream retten
    loop
      { var object obj = stream_read(&STACK_0,NIL,NIL); # Objekt lesen
        if (eq(obj,eof_value)) break; # EOF -> fertig
        if (closurep(obj))
          { funcall(obj,0); } # Closure (vermutlich compilierte Closure) aufrufen
          else
          { eval_noenv(obj); } # sonstige Form evaluieren
      }
    stream_close(&STACK_0); # stream schlie�en
    skipSTACK(1); value1 = T; mv_count=1; # Wert T
  }

# ---------------------------------------------------------------------------- #
#                   Hilfsfunktionen f�r Debugger und Stepper

# Die folgenden Funktionen klettern im Stack herum, �berschreiten jedoch
# keinen Driver-Frame und auch nicht das obere Stackende.
# G�ltige "Stackpointer" sind hierbei Pointer auf Stackelemente oder
# Frames, wo nicht das Stackende und auch kein Driver-Frame ist.
# Modus 1: alle Stackitems
# Modus 2: Frames
# Modus 3: lexikalische Frames: Frame-Info hat FRAME_BIT = 1 und
#          (SKIP2_BIT = 1 oder ENTRYPOINT_BIT = 0 oder BLOCKGO_BIT = 1)
# Modus 4: EVAL- und APPLY-Frames: Frame-Info = [TRAPPED_]EVAL/APPLY_FRAME_INFO
# Modus 5: APPLY-Frames: Frame-Info = [TRAPPED_]APPLY_FRAME_INFO

# Macro: Testet, ob FRAME ein Stackende erreicht hat.
#define stack_upend_p()  \
  (   eq(FRAME_(0),nullobj) # Nullword = oberes Stackende                    \
   || (framecode(FRAME_(0)) == DRIVER_frame_info) # Driver-Frame = Stackende \
   || ((framepointerp(Symbol_value(S(frame_limit2))))                        \
       && (uTheFramepointer(Symbol_value(S(frame_limit2))) cmpSTACKop FRAME) # FRAME > *frame-limit2* ? \
  )   )
#define stack_downend_p()  \
  (   (framecode(FRAME_(0)) == DRIVER_frame_info) # Driver-Frame = Stackende \
   || ((framepointerp(Symbol_value(S(frame_limit1))))                        \
       && (FRAME cmpSTACKop uTheFramepointer(Symbol_value(S(frame_limit1)))) # FRAME < *frame-limit1* ? \
  )   )

# Macro: Testet, ob FRAME auf einen Frame zeigt.
# in erster N�herung:
# #define frame_p()  (!( (as_oint(FRAME_(0)) & wbit(frame_bit_o)) ==0))
# in zweiter N�herung, unter Ber�cksichtigung der Frames mit Skip2-bit:
  #define frame_p()  framep(FRAME)
  local boolean framep (object* FRAME);
  local boolean framep(FRAME)
    var object* FRAME;
    { # Ein normales Lisp-Objekt ist kein Frame:
      if ((as_oint(FRAME_(0)) & wbit(frame_bit_o)) ==0) return FALSE;
      # Beginnt bei FRAME_(-1) ein Frame ohne Skip2-Bit, so ist FRAME_(0)
      # Teil dieses Frames, also nicht selber Beginn eines Frames:
      if (   (!(FRAME==STACK)) # nicht die STACK-Grenzen �berschreiten!
          && ((as_oint(FRAME_(-1)) & wbit(skip2_bit_o)) == 0)
          && framep(FRAME STACKop -1)
         )
        return FALSE;
      return TRUE; # Sonst beginnt hier ein Frame.
    }

# Macro: Erniedrigt FRAME bis zum n�chsten Frame.
#define next_frame_down()  do { FRAME skipSTACKop -1; } until (frame_p());

# Macro: Testet, ob der Frame bei FRAME ein lexikalischer Frame ist.
#ifdef entrypoint_bit_t
#define lexical_frame_p()  \
  (   (!( (as_oint(FRAME_(0)) & wbit(skip2_bit_o)) ==0))   \
   || ( (as_oint(FRAME_(0)) & wbit(entrypoint_bit_o)) ==0) \
   || (!( (as_oint(FRAME_(0)) & wbit(blockgo_bit_o)) ==0)) \
  )
#else
#define lexical_frame_p()  \
  (/* (!( (as_oint(FRAME_(0)) & wbit(skip2_bit_o)) ==0))   \
   || */ (framecode(FRAME_(0)) >= entrypoint_limit_t)      \
   || (!( (as_oint(FRAME_(0)) & wbit(blockgo_bit_o)) ==0)) \
  )
#endif

# Macro: Testet, ob der Frame bei FRAME ein EVAL/APPLY-Frame ist.
#define evalapply_frame_p()  \
  ((framecode(FRAME_(0)) & ~(bit(eval_bit_t)|bit(trapped_bit_t))) == \
   ((EVAL_frame_info|APPLY_frame_info) & ~(bit(eval_bit_t)|bit(trapped_bit_t))))

# Macro: Testet, ob der Frame bei FRAME ein APPLY-Frame ist.
#define apply_frame_p()  \
  ((framecode(FRAME_(0)) & ~bit(trapped_bit_t)) == (APPLY_frame_info & ~bit(trapped_bit_t)))

# UP: �berspringt ein Stackitem nach oben
  local object* frame_up_1 (object* stackptr);
  local object* frame_up_1(stackptr)
    var object* stackptr;
    { var object* FRAME = stackptr;
      if (frame_p())
        { FRAME = topofframe(FRAME_(0)); } # Pointer �bern Frame
        else
        { FRAME skipSTACKop 1; } # Pointer aufs n�chste Objekt
      return (stack_upend_p() ? stackptr : FRAME);
    }

# UP: �berspringt ein Stackitem nach unten
  local object* frame_down_1 (object* stackptr);
  local object* frame_down_1(stackptr)
    var object* stackptr;
    { var object* FRAME = stackptr;
      next_frame_down(); # n�chsten Frame drunter suchen
      if (!(topofframe(FRAME_(0)) == stackptr)) # nicht direkt unterhalb stackptr?
        { FRAME = stackptr STACKop -1; }
      return (stack_downend_p() ? stackptr : FRAME);
    }

# UP: springt zum n�chsth�heren Frame
  local object* frame_up_2 (object* stackptr);
  local object* frame_up_2(stackptr)
    var object* stackptr;
    { var object* FRAME = stackptr;
      if (frame_p())
        { FRAME = topofframe(FRAME_(0)); } # Pointer �bern Frame
        else
        { FRAME skipSTACKop 1; } # Pointer aufs n�chste Objekt
      loop
        { if (stack_upend_p()) return stackptr;
          if (as_oint(FRAME_(0)) & wbit(frame_bit_o)) return FRAME;
          FRAME skipSTACKop 1;
        }
    }

# UP: springt zum n�chstniedrigeren Frame
  local object* frame_down_2 (object* stackptr);
  local object* frame_down_2(stackptr)
    var object* stackptr;
    { var object* FRAME = stackptr;
      next_frame_down(); # n�chsten Frame drunter suchen
      return (stack_downend_p() ? stackptr : FRAME);
    }

# UP: springt zum n�chsth�heren lexikalischen Frame
  local object* frame_up_3 (object* stackptr);
  local object* frame_up_3(stackptr)
    var object* stackptr;
    { var object* FRAME = stackptr;
      if (frame_p())
        { FRAME = topofframe(FRAME_(0)); } # Pointer �bern Frame
        else
        { FRAME skipSTACKop 1; } # Pointer aufs n�chste Objekt
      loop
        { if (stack_upend_p()) return stackptr;
          if (frame_p())
            { if (lexical_frame_p())
                { return FRAME; }
                else
                { FRAME = topofframe(FRAME_(0)); } # Pointer �bern Frame
            }
            else
            { FRAME skipSTACKop 1; }
        }
    }

# UP: springt zum n�chstniedrigeren lexikalischen Frame
  local object* frame_down_3 (object* stackptr);
  local object* frame_down_3(stackptr)
    var object* stackptr;
    { var object* FRAME = stackptr;
      loop
        { next_frame_down(); # n�chsten Frame drunter suchen
          if (stack_downend_p()) return stackptr;
          if (lexical_frame_p()) break;
        }
      return FRAME;
    }

# UP: springt zum n�chsth�heren EVAL/APPLY-Frame
  local object* frame_up_4 (object* stackptr);
  local object* frame_up_4(stackptr)
    var object* stackptr;
    { var object* FRAME = stackptr;
      if (frame_p())
        { FRAME = topofframe(FRAME_(0)); } # Pointer �bern Frame
        else
        { FRAME skipSTACKop 1; } # Pointer aufs n�chste Objekt
      loop
        { if (stack_upend_p()) return stackptr;
          if (frame_p())
            { if (evalapply_frame_p())
                { return FRAME; }
                else
                { FRAME = topofframe(FRAME_(0)); } # Pointer �bern Frame
            }
            else
            { FRAME skipSTACKop 1; }
        }
    }

# UP: springt zum n�chstniedrigeren EVAL/APPLY-Frame
  local object* frame_down_4 (object* stackptr);
  local object* frame_down_4(stackptr)
    var object* stackptr;
    { var object* FRAME = stackptr;
      loop
        { next_frame_down(); # n�chsten Frame drunter suchen
          if (stack_downend_p()) return stackptr;
          if (evalapply_frame_p()) break;
        }
      return FRAME;
    }

# UP: springt zum n�chsth�heren APPLY-Frame
  local object* frame_up_5 (object* stackptr);
  local object* frame_up_5(stackptr)
    var object* stackptr;
    { var object* FRAME = stackptr;
      if (frame_p())
        { FRAME = topofframe(FRAME_(0)); } # Pointer �bern Frame
        else
        { FRAME skipSTACKop 1; } # Pointer aufs n�chste Objekt
      loop
        { if (stack_upend_p()) return stackptr;
          if (frame_p())
            { if (apply_frame_p())
                { return FRAME; }
                else
                { FRAME = topofframe(FRAME_(0)); } # Pointer �bern Frame
            }
            else
            { FRAME skipSTACKop 1; }
        }
    }

# UP: springt zum n�chstniedrigeren APPLY-Frame
  local object* frame_down_5 (object* stackptr);
  local object* frame_down_5(stackptr)
    var object* stackptr;
    { var object* FRAME = stackptr;
      loop
        { next_frame_down(); # n�chsten Frame drunter suchen
          if (stack_downend_p()) return stackptr;
          if (apply_frame_p()) break;
        }
      return FRAME;
    }

# Typ eines Pointers auf eine Hochsteige- bzw. Absteige-Routine:
  typedef object* (*kletterfun) (object* stackptr);

local const kletterfun frame_up_table[] =
  { &frame_up_1, &frame_up_2, &frame_up_3, &frame_up_4, &frame_up_5, };
local const kletterfun frame_down_table[] =
  { &frame_down_1, &frame_down_2, &frame_down_3, &frame_down_4, &frame_down_5, };

# UP: �berpr�ft und decodiert das mode-Argument.
# test_mode_arg(table)
# > STACK_0: mode
# > table: Tabelle der Routinen zum Hochsteigen bzw. zum Absteigen
# > subr_self: Aufrufer (ein SUBR)
# < ergebnis: Routine zum Hochsteigen bzw. zum Absteigen
# erh�ht STACK um 1
  local kletterfun test_mode_arg (const kletterfun* table);
  local kletterfun test_mode_arg(table)
    var const kletterfun* table;
    { var object arg = popSTACK();
      var uintL mode;
      if (!(posfixnump(arg)
            && ((mode = posfixnum_to_L(arg)) > 0)
            && (mode<=5)
         ) )
        { pushSTACK(arg); # Wert f�r Slot DATUM von TYPE-ERROR
          pushSTACK(O(type_climb_mode)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
          pushSTACK(arg);
          pushSTACK(TheSubr(subr_self)->name);
          fehler(type_error,
                 DEUTSCH ? "~: Ung�ltiger Frame-Kletter-Modus ~" :
                 ENGLISH ? "~: bad frame climbing mode ~" :
                 FRANCAIS ? "~: Mauvais mode de saut d'environnement ~." :
                 ""
                );
        }
      return table[mode-1];
    }

# UP: �berpr�ft ein Frame-Pointer-Argument.
# test_framepointer_arg()
# > STACK_0: Lisp-Objekt, sollte ein Frame-Pointer sein
# > subr_self: Aufrufer (ein SUBR)
# < ergebnis: Frame-Pointer
# erh�ht STACK um 1
  local object* test_framepointer_arg (void);
  local object* test_framepointer_arg()
    { var object arg = popSTACK();
      if (!framepointerp(arg))
        { pushSTACK(arg);
          pushSTACK(TheSubr(subr_self)->name);
          fehler(error,
                 DEUTSCH ? "~: ~ ist kein Stackpointer." :
                 ENGLISH ? "~: ~ is not a stack pointer" :
                 FRANCAIS ? "~: ~ n'est pas un pointeur de pile." :
                 ""
                );
        }
      return uTheFramepointer(arg);
    }

LISPFUNN(frame_up_1,2)
# (SYS::FRAME-UP-1 framepointer mode) liefert den Frame-Pointer 1 h�her.
  { var kletterfun frame_up_x = test_mode_arg(&frame_up_table[0]);
    var object* stackptr = test_framepointer_arg();
    stackptr = (*frame_up_x)(stackptr); # einmal hochsteigen
    value1 = make_framepointer(stackptr); mv_count=1;
  }

LISPFUNN(frame_up,2)
# (SYS::FRAME-UP framepointer mode) liefert den Frame-Pointer ganz oben.
  { var kletterfun frame_up_x = test_mode_arg(&frame_up_table[0]);
    var object* stackptr = test_framepointer_arg();
    # hochsteigen, bis es nicht mehr weiter geht:
    loop
      { var object* next_stackptr = (*frame_up_x)(stackptr);
        if (next_stackptr == stackptr) break;
        stackptr = next_stackptr;
      }
    value1 = make_framepointer(stackptr); mv_count=1;
  }

LISPFUNN(frame_down_1,2)
# (SYS::FRAME-DOWN-1 framepointer mode) liefert den Frame-Pointer 1 drunter.
  { var kletterfun frame_down_x = test_mode_arg(&frame_down_table[0]);
    var object* stackptr = test_framepointer_arg();
    stackptr = (*frame_down_x)(stackptr); # einmal hinabsteigen
    value1 = make_framepointer(stackptr); mv_count=1;
  }

LISPFUNN(frame_down,2)
# (SYS::FRAME-DOWN framepointer mode) liefert den Frame-Pointer ganz unten.
  { var kletterfun frame_down_x = test_mode_arg(&frame_down_table[0]);
    var object* stackptr = test_framepointer_arg();
    # hinabsteigen, bis es nicht mehr weiter geht:
    loop
      { var object* next_stackptr = (*frame_down_x)(stackptr);
        if (next_stackptr == stackptr) break;
        stackptr = next_stackptr;
      }
    value1 = make_framepointer(stackptr); mv_count=1;
  }

LISPFUNN(the_frame,0)
# (SYS::THE-FRAME) liefert den aktuellen Stackpointer als Frame-Pointer.
  { var object* stackptr = STACK;
    stackptr = frame_up_2(stackptr); # bis zum n�chsth�heren Frame hoch
    value1 = make_framepointer(stackptr); mv_count=1;
  }

# UP: aktiviert dasselbe lexikalische Environment, das beim Framepointer
# STACK_0 aktiv war.
# same_env_as();
# erh�ht STACK um 1, baut auf dem STACK einen ENV5-Frame auf
  local void same_env_as (void);
  local void same_env_as()
    { var object* FRAME = test_framepointer_arg();
      var environment env;
      # 5 Environments noch "leer":
      env.var_env = nullobj;
      env.fun_env = nullobj;
      env.block_env = nullobj;
      env.go_env = nullobj;
      env.decl_env = nullobj;
      # und f�llen:
      loop
        { # ab FRAME abw�rts nach ENV-Frames suchen:
          loop
            { FRAME skipSTACKop -1;
              if (FRAME==STACK) goto end; # Stack zu Ende?
              if (frame_p()
                  && (!( (as_oint(FRAME_(0)) & wbit(skip2_bit_o)) ==0))
                  && (!( (as_oint(FRAME_(0)) & wbit(envbind_bit_o)) ==0))
                 )
                break;
            }
          # N�chster ENV-Frame gefunden.
          # Sein Inhalt f�llt die noch leeren Komponenten von env:
          switch (framecode(FRAME_(0)) & envbind_case_mask_t)
            { case (ENV1V_frame_info & envbind_case_mask_t): # 1 VAR_ENV
                if (eq(env.var_env,nullobj)) { env.var_env = FRAME_(1); }
                break;
              case (ENV1F_frame_info & envbind_case_mask_t): # 1 FUN_ENV
                if (eq(env.fun_env,nullobj)) { env.fun_env = FRAME_(1); }
                break;
              case (ENV1B_frame_info & envbind_case_mask_t): # 1 BLOCK_ENV
                if (eq(env.block_env,nullobj)) { env.block_env = FRAME_(1); }
                break;
              case (ENV1G_frame_info & envbind_case_mask_t): # 1 GO_ENV
                if (eq(env.go_env,nullobj)) { env.go_env = FRAME_(1); }
                break;
              case (ENV1D_frame_info & envbind_case_mask_t): # 1 DECL_ENV
                if (eq(env.decl_env,nullobj)) { env.decl_env = FRAME_(1); }
                break;
              case (ENV2VD_frame_info & envbind_case_mask_t): # 1 VAR_ENV und 1 DECL_ENV
                if (eq(env.var_env,nullobj)) { env.var_env = FRAME_(1); }
                if (eq(env.decl_env,nullobj)) { env.decl_env = FRAME_(2); }
                break;
              case (ENV5_frame_info & envbind_case_mask_t): # alle 5 Environments
                if (eq(env.var_env,nullobj)) { env.var_env = FRAME_(1); }
                if (eq(env.fun_env,nullobj)) { env.fun_env = FRAME_(2); }
                if (eq(env.block_env,nullobj)) { env.block_env = FRAME_(3); }
                if (eq(env.go_env,nullobj)) { env.go_env = FRAME_(4); }
                if (eq(env.decl_env,nullobj)) { env.decl_env = FRAME_(5); }
                break;
              default: NOTREACHED
            }
          # Falls alle einzelnen Environments von env gef�llt (/=nullobj) sind,
          # ist das Environment fertig:
          if (   (!eq(env.var_env,nullobj))
              && (!eq(env.fun_env,nullobj))
              && (!eq(env.block_env,nullobj))
              && (!eq(env.go_env,nullobj))
              && (!eq(env.decl_env,nullobj))
             )
            goto fertig;
        }
      end: # Stack zu Ende.
      # Hole restliche Environment-Komponenten aus dem aktuellen Environment:
      if (eq(env.var_env,nullobj)) { env.var_env = aktenv.var_env; }
      if (eq(env.fun_env,nullobj)) { env.fun_env = aktenv.fun_env; }
      if (eq(env.block_env,nullobj)) { env.block_env = aktenv.block_env; }
      if (eq(env.go_env,nullobj)) { env.go_env = aktenv.go_env; }
      if (eq(env.decl_env,nullobj)) { env.decl_env = aktenv.decl_env; }
      fertig: # env fertig.
      # Environment-Frame aufbauen:
      make_ENV5_frame();
      # aktuelle Environments setzen:
      aktenv = env;
    }

LISPFUNN(same_env_as,2)
# (SYS::SAME-ENV-AS framepointer fun) aktiviert dasselbe lexikalische
# Environment, das bei framepointer aktiv war, und ruft dann fun auf.
  { var object fun = popSTACK();
    same_env_as(); # Environment von framepointer aktivieren
    funcall(fun,0); # fun aufrufen
    unwind(); # Environment-Frame aufl�sen
  }

LISPFUNN(eval_at,2)
# (SYS::EVAL-AT framepointer form) aktiviert dasselbe lexikalische
# Environment, das bei framepointer aktiv war, und wertet darin die Form aus.
  { var object form = popSTACK();
    same_env_as(); # Environment von framepointer aktivieren
    eval(form); # form auswerten
    unwind(); # Environment-Frame aufl�sen
  }

LISPFUNN(eval_frame_p,1)
# (SYS::EVAL-FRAME-P framepointer)
# gibt an, ob framepointer auf einen EVAL/APPLY-Frame zeigt.
  { var object* FRAME = test_framepointer_arg();
    value1 = (evalapply_frame_p() ? T : NIL); mv_count=1;
  }

LISPFUNN(driver_frame_p,1)
# (SYS::DRIVER-FRAME-P framepointer)
# gibt an, ob framepointer auf einen Driver-Frame zeigt.
  { var object* FRAME = test_framepointer_arg();
    value1 = (framecode(FRAME_(0)) == DRIVER_frame_info ? T : NIL); mv_count=1;
  }

# Fehlermeldung, wenn kein EVAL/APPLY-Frame-Pointer vorliegt.
# fehler_evalframe(obj);
# > subr_self: Aufrufer (ein SUBR)
# > obj: kein EVAL/APPLY-Frame-Pointer
  nonreturning_function(local, fehler_evalframe, (object obj));
  local void fehler_evalframe(obj)
    var object obj;
    { pushSTACK(obj);
      pushSTACK(TheSubr(subr_self)->name);
      fehler(error,
             DEUTSCH ? "~: ~ ist kein Pointer auf einen EVAL/APPLY-Frame." :
             ENGLISH ? "~: ~ is not a pointer to an EVAL/APPLY frame" :
             FRANCAIS ? "~: ~ n'est pas une pointeur vers un environnement EVAL/APPLY." :
             ""
            );
    }

LISPFUNN(trap_eval_frame,2)
# (SYS::TRAP-EVAL-FRAME framepointer flag) schaltet den Breakpoint am
# angegebenen EVAL/APPLY-Frame je nach flag an bzw. aus.
  { var object flag = popSTACK();
    var object frame = popSTACK();
    if (!framepointerp(frame)) { fehler_evalframe(frame); }
   {var object* FRAME = uTheFramepointer(frame);
    if (!evalapply_frame_p()) { fehler_evalframe(frame); }
    # FRAME zeigt auf den EVAL/APPLY-Frame.
    if (!nullp(flag))
      # Breakpoint einschalten
      { *(oint*)(&FRAME_(0)) |= wbit(trapped_bit_o); }
      else
      # Breakpoint ausschalten
      { *(oint*)(&FRAME_(0)) &= ~wbit(trapped_bit_o); }
    value1 = frame; mv_count=1; # framepointer als Wert
  }}

LISPFUNN(redo_eval_frame,1)
# (SYS::REDO-EVAL-FRAME framepointer) unwindet bis zum angegebenen
# EVAL/APPLY-Frame und f�ngt erneut an, diesen abzuarbeiten.
  { var object frame = popSTACK();
    if (!framepointerp(frame)) { fehler_evalframe(frame); }
   {var object* FRAME = uTheFramepointer(frame);
    if (!evalapply_frame_p()) { fehler_evalframe(frame); }
    # FRAME zeigt auf den EVAL/APPLY-Frame.
    value1 = NIL; mv_count=0; # keine Werte zu retten
    unwind_upto(FRAME); # bis zum EVAL/APPLY-Frame alles aufl�sen, dorthin springen
  }}

LISPFUNN(return_from_eval_frame,2)
# (SYS::RETURN-FROM-EVAL-FRAME framepointer form)
# unwindet bis zum angegebenen EVAL/APPLY-Frame und gibt als dessen Werte die
# Werte der Evaluierung der angegebenen form zur�ck.
  { var object form = popSTACK();
    var object frame = popSTACK();
    if (!framepointerp(frame)) { fehler_evalframe(frame); }
   {var object* FRAME = uTheFramepointer(frame);
    if (!evalapply_frame_p()) { fehler_evalframe(frame); }
    # FRAME zeigt auf den EVAL/APPLY-Frame.
    value1 = form; mv_count=1; # form retten und �bergeben
    unwind_upto(FRAME); # bis zum EVAL/APPLY-Frame alles aufl�sen, dorthin springen
  }}

# ---------------------------------------------------------------------------- #
#                                 Debughilfen

# UP: Gibt das Stackitem FRAME_(0) detailliert auf den Stream aus
# und liefert den n�chsth�heren stackptr.
# print_stackitem(&stream,FRAME)
# kann GC ausl�sen
  local object* print_stackitem (object* stream_, object* FRAME);
  local object* print_stackitem(stream_,FRAME)
    var object* stream_;
    var object* FRAME;
    { if (!frame_p())
        # kein Frame, normales LISP-Objekt
        { write_sstring(stream_,O(showstack_string_lisp_obj)); # "�- "
         {var object obj = FRAME_(0);
          #if !defined(NO_symbolflags)
          switch (typecode(obj)) # evtl. Symbol-Flags entfernen
            { case_symbolflagged: obj = symbol_without_flags(obj);
              default: break;
            }
          #endif
          prin1(stream_,obj); # LISP-Objekt ausgeben
          return FRAME STACKop 1;
        }}
        else
        # Frame angetroffen
        { var object* FRAME_top = topofframe(FRAME_(0)); # Pointer �bern Frame
          switch (framecode(FRAME_(0))) # je nach Frametyp
            { case TRAPPED_APPLY_frame_info:
                # getrapte APPLY-Frames:
                write_sstring(stream_,OLS(showstack_string_TRAPPED_APPLY_frame)); # "�APPLY-Frame mit Breakpoint f�r Aufruf "
                goto APPLY_frame;
              case APPLY_frame_info:
                # APPLY-Frames:
                write_sstring(stream_,OLS(showstack_string_APPLY_frame)); # "�APPLY-Frame f�r Aufruf "
              APPLY_frame:
                # Funktionsnamen und Argumente ausgeben:
                write_schar(stream_,'('); # '(' ausgeben
                prin1(stream_,TheIclosure(FRAME_(frame_closure))->clos_name); # Namen ausgeben
                { var object* argptr = FRAME_top;
                  var uintL count = STACK_item_count(FRAME STACKop frame_args,FRAME_top);
                  dotimesL(count,count,
                    { write_schar(stream_,' '); # ' ' ausgeben
                      write_schar(stream_,'\''); # "'" ausgeben
                      prin1(stream_,NEXT(argptr)); # n�chstes Argument ausgeben
                    });
                }
                write_schar(stream_,')'); # ')' ausgeben
                break;
              case TRAPPED_EVAL_frame_info:
                # getrapte EVAL-Frames:
                write_sstring(stream_,OLS(showstack_string_TRAPPED_EVAL_frame)); # "�EVAL-Frame mit Breakpoint f�r Form "
                goto EVAL_frame;
              case EVAL_frame_info:
                # EVAL-Frames:
                write_sstring(stream_,OLS(showstack_string_EVAL_frame)); # "�EVAL-Frame f�r Form "
              EVAL_frame:
                prin1(stream_,FRAME_(frame_form)); # Form ausgeben
                break;
              case DYNBIND_frame_info:
                # dynamische Variablenbindungsframes:
                write_sstring(stream_,OLS(showstack_string_DYNBIND_frame)); # "�Variablenbindungs-Frame bindet (~ = dynamisch):"
                # Bindungen ausgeben:
                FRAME skipSTACKop 1;
                until (FRAME==FRAME_top)
                  { # Bindung von Symbol FRAME_(0) an Wert FRAME_(1) ausgeben:
                    write_sstring(stream_,O(showstack_string_bindung)); # "�  | "
                    write_schar(stream_,'~'); # '~' ausgeben
                    write_schar(stream_,' '); # ' ' ausgeben
                    prin1(stream_,FRAME_(0)); # Symbol ausgeben
                    write_sstring(stream_,O(showstack_string_zuord)); # " <--> "
                    prin1(stream_,FRAME_(1)); # Wert ausgeben
                    FRAME skipSTACKop 2;
                  }
                break;
              #ifdef HAVE_SAVED_REGISTERS
              case CALLBACK_frame_info:
                # Callback-Register-Frames:
                write_sstring(stream_,OLS(showstack_string_CALLBACK_frame)); # "�CALLBACK-Frame"
                break;
              #endif
              # Variablen- und Funktionsbindungsframes:
              case VAR_frame_info:
                write_sstring(stream_,OLS(showstack_string_VAR_frame)); # "�Variablenbindungs-Frame "
                #ifdef NO_symbolflags
                prin1(stream_,make_framepointer(FRAME)); # Frame-Pointer ausgeben
                write_sstring(stream_,OLS(showstack_string_binds)); # " bindet (~ = dynamisch):"
                pushSTACK(FRAME_(frame_next_env)); # weiteres Environment retten
                # Bindungen ausgeben:
                FRAME skipSTACKop frame_bindings;
                until (FRAME==FRAME_top)
                  { if (!( (as_oint(FRAME_(varframe_binding_mark)) & wbit(active_bit_o)) ==0))
                      # Bindung von Symbol FRAME_(1) an Wert FRAME_(2) ausgeben:
                      { write_sstring(stream_,O(showstack_string_bindung)); # "�  | "
                        if (!( (as_oint(FRAME_(varframe_binding_mark)) & wbit(dynam_bit_o)) ==0)) # Bindung dynamisch?
                          { write_schar(stream_,'~'); } # ja -> '~' ausgeben
                        write_schar(stream_,' '); # ' ' ausgeben
                        prin1(stream_,symbol_without_flags(FRAME_(varframe_binding_sym))); # Symbol ausgeben
                        write_sstring(stream_,O(showstack_string_zuord)); # " <--> "
                        prin1(stream_,FRAME_(varframe_binding_value)); # Wert ausgeben
                      }
                    FRAME skipSTACKop varframe_binding_size;
                  }
                goto VARFUN_frame_next;
                #else
                goto VARFUN_frame;
                #endif
              case FUN_frame_info:
                write_sstring(stream_,OLS(showstack_string_FUN_frame)); # "�Funktionsbindungs-Frame "
                goto VARFUN_frame;
              VARFUN_frame:
                prin1(stream_,make_framepointer(FRAME)); # Frame-Pointer ausgeben
                write_sstring(stream_,OLS(showstack_string_binds)); # " bindet (~ = dynamisch):"
                pushSTACK(FRAME_(frame_next_env)); # weiteres Environment retten
                # Bindungen ausgeben:
                FRAME skipSTACKop frame_bindings;
                until (FRAME==FRAME_top)
                  { if (!( (as_oint(FRAME_(0)) & wbit(active_bit_o)) ==0))
                      # Bindung von Symbol FRAME_(0) an Wert FRAME_(1) ausgeben:
                      { write_sstring(stream_,O(showstack_string_bindung)); # "�  | "
                        if (!( (as_oint(FRAME_(0)) & wbit(dynam_bit_o)) ==0)) # Bindung dynamisch?
                          { write_schar(stream_,'~'); } # ja -> '~' ausgeben
                        write_schar(stream_,' '); # ' ' ausgeben
                        prin1(stream_,symbol_without_flags(FRAME_(0))); # Symbol ausgeben
                        write_sstring(stream_,O(showstack_string_zuord)); # " <--> "
                        prin1(stream_,FRAME_(1)); # Wert ausgeben
                      }
                    FRAME skipSTACKop 2;
                  }
              VARFUN_frame_next:
                # Weiteres Environment ausgeben:
                write_sstring(stream_,OLS(showstack_string_next_env)); # "�  Weiteres Environment: "
                { var object env = popSTACK(); # weiteres Environment
                  if (!simple_vector_p(env))
                    { prin1(stream_,env); }
                    else
                    # weiteres Environment ist ein Vektor, der L�nge 2n+1
                    do { pushSTACK(env);
                        {var uintL count = floor(Svector_length(env),2); # = n = Bindungszahl
                         var uintL index = 0;
                         dotimesL(count,count,
                           { write_sstring(stream_,O(showstack_string_bindung)); # "�  | "
                             prin1(stream_,TheSvector(STACK_0)->data[index++]); # Symbol ausgeben
                             write_sstring(stream_,O(showstack_string_zuord)); # " <--> "
                             prin1(stream_,TheSvector(STACK_0)->data[index++]); # Symbol ausgeben
                           });
                         env = TheSvector(popSTACK())->data[index]; # letztes Vektor-Element
                       }}
                       while (simple_vector_p(env));
                }
                break;
              # Interpretierte Block-Frames:
              case IBLOCK_frame_info:
                write_sstring(stream_,OLS(showstack_string_IBLOCK_frame)); # "�Block-Frame "
                goto IBLOCK_frame;
              case NESTED_IBLOCK_frame_info:
                write_sstring(stream_,OLS(showstack_string_NESTED_IBLOCK_frame)); # "�Block-Frame (genestet) "
                goto IBLOCK_frame;
              IBLOCK_frame:
                pushSTACK(FRAME_(frame_next_env));
                prin1(stream_,make_framepointer(FRAME)); # Frame-Pointer ausgeben
                write_sstring(stream_,OLS(showstack_string_for1)); # " f�r "
                prin1(stream_,FRAME_(frame_name)); # Blockname
                goto NEXT_ENV;
              case CBLOCK_frame_info:
                # compilierte Block-Frames:
                write_sstring(stream_,OLS(showstack_string_CBLOCK_frame)); # "�Block-Frame (compiliert) f�r "
                prin1(stream_,FRAME_(frame_ctag)); # Blockname
                break;
              # Interpretierte Tagbody-Frames:
              case ITAGBODY_frame_info:
                write_sstring(stream_,OLS(showstack_string_ITAGBODY_frame)); # "�Tagbody-Frame "
                goto ITAGBODY_frame;
              case NESTED_ITAGBODY_frame_info:
                write_sstring(stream_,OLS(showstack_string_NESTED_ITAGBODY_frame)); # "�Tagbody-Frame (genestet) "
                goto ITAGBODY_frame;
              ITAGBODY_frame:
                pushSTACK(FRAME_(frame_next_env));
                prin1(stream_,make_framepointer(FRAME)); # Frame-Pointer ausgeben
                write_sstring(stream_,OLS(showstack_string_for2)); # " f�r"
                # Tags/Bodys ausgeben:
                FRAME skipSTACKop frame_bindings;
                until (FRAME==FRAME_top)
                  { # Bindung von Tag FRAME_(0) an Body FRAME_(1) ausgeben:
                    write_sstring(stream_,O(showstack_string_bindung)); # "�  | "
                    prin1(stream_,FRAME_(0)); # Tag ausgeben
                    write_sstring(stream_,O(showstack_string_zuordtag)); # " --> "
                    prin1(stream_,FRAME_(1)); # Body ausgeben
                    FRAME skipSTACKop 2;
                  }
                goto NEXT_ENV;
              NEXT_ENV: # Ausgeben eines Block- oder Tagbody-Environments STACK_0
                write_sstring(stream_,OLS(showstack_string_next_env)); # "�  Weiteres Environment: "
                { var object env = popSTACK();
                  if (!consp(env))
                    { prin1(stream_,env); }
                    else
                    # weiteres Environment ist eine Aliste
                    do { pushSTACK(Cdr(env));
                         env = Car(env);
                         if (atomp(env))
                           { pushSTACK(S(show_stack));
                             fehler(error,
                                    DEUTSCH ? "~: Environment ist keine Aliste" :
                                    ENGLISH ? "~: environment is not an alist" :
                                    FRANCAIS ? "~: L'environnement n'est pas une liste d'association." :
                                    ""
                                   );
                           }
                         pushSTACK(Cdr(env));
                         pushSTACK(Car(env));
                         write_sstring(stream_,O(showstack_string_bindung)); # "�  | "
                         prin1(stream_,popSTACK());
                         write_sstring(stream_,O(showstack_string_zuordtag)); # " --> "
                         prin1(stream_,popSTACK());
                         env = popSTACK();
                       }
                       while (consp(env));
                }
                break;
              case CTAGBODY_frame_info:
                # compilierte Tagbody-Frames:
                write_sstring(stream_,OLS(showstack_string_CTAGBODY_frame)); # "�Tagbody-Frame (compiliert) f�r "
                prin1(stream_,Car(FRAME_(frame_ctag))); # Tag-Vektor
                break;
              case CATCH_frame_info:
                # Catch-Frames:
                write_sstring(stream_,OLS(showstack_string_CATCH_frame)); # "�Catch-Frame f�r Tag "
                prin1(stream_,FRAME_(frame_tag)); # Tag
                break;
              case HANDLER_frame_info:
                # Handler-Frames:
                write_sstring(stream_,OLS(showstack_string_HANDLER_frame)); # "�Handler-Frame f�r Conditions"
                { var uintL m2 = Svector_length(Car(FRAME_(frame_handlers))); # 2*m
                  var uintL i = 0;
                  do { write_schar(stream_,' '); # ' ' ausgeben
                       prin1(stream_,TheSvector(Car(FRAME_(frame_handlers)))->data[i]); # Typ i ausgeben
                       i += 2;
                     }
                     while (i < m2);
                }
                break;
              case UNWIND_PROTECT_frame_info:
                # Unwind-Protect-Frames:
                write_sstring(stream_,OLS(showstack_string_UNWIND_PROTECT_frame)); # "�Unwind-Protect-Frame"
                break;
              case DRIVER_frame_info:
                # Driver-Frames:
                write_sstring(stream_,OLS(showstack_string_DRIVER_frame)); # "��Driver-Frame"
                break;
              # Environment-Frames:
              case ENV1V_frame_info:
                write_sstring(stream_,OLS(showstack_string_ENV_frame)); # "�Environment-Bindungs-Frame"
                write_sstring(stream_,O(showstack_string_VENV_frame)); # "�  VAR_ENV <--> "
                prin1(stream_,FRAME_(1));
                break;
              case ENV1F_frame_info:
                write_sstring(stream_,OLS(showstack_string_ENV_frame)); # "�Environment-Bindungs-Frame"
                write_sstring(stream_,O(showstack_string_FENV_frame)); # "�  FUN_ENV <--> "
                prin1(stream_,FRAME_(1));
                break;
              case ENV1B_frame_info:
                write_sstring(stream_,OLS(showstack_string_ENV_frame)); # "�Environment-Bindungs-Frame"
                write_sstring(stream_,O(showstack_string_BENV_frame)); # "�  BLOCK_ENV <--> "
                prin1(stream_,FRAME_(1));
                break;
              case ENV1G_frame_info:
                write_sstring(stream_,OLS(showstack_string_ENV_frame)); # "�Environment-Bindungs-Frame"
                write_sstring(stream_,O(showstack_string_GENV_frame)); # "�  GO_ENV <--> "
                prin1(stream_,FRAME_(1));
                break;
              case ENV1D_frame_info:
                write_sstring(stream_,OLS(showstack_string_ENV_frame)); # "�Environment-Bindungs-Frame"
                write_sstring(stream_,O(showstack_string_DENV_frame)); # "�  DECL_ENV <--> "
                prin1(stream_,FRAME_(1));
                break;
              case ENV2VD_frame_info:
                write_sstring(stream_,OLS(showstack_string_ENV_frame)); # "�Environment-Bindungs-Frame"
                write_sstring(stream_,O(showstack_string_VENV_frame)); # "�  VAR_ENV <--> "
                prin1(stream_,FRAME_(1));
                write_sstring(stream_,O(showstack_string_DENV_frame)); # "�  DECL_ENV <--> "
                prin1(stream_,FRAME_(2));
                break;
              case ENV5_frame_info:
                write_sstring(stream_,OLS(showstack_string_ENV_frame)); # "�Environment-Bindungs-Frame"
                write_sstring(stream_,O(showstack_string_VENV_frame)); # "�  VAR_ENV <--> "
                prin1(stream_,FRAME_(1));
                write_sstring(stream_,O(showstack_string_FENV_frame)); # "�  FUN_ENV <--> "
                prin1(stream_,FRAME_(2));
                write_sstring(stream_,O(showstack_string_BENV_frame)); # "�  BLOCK_ENV <--> "
                prin1(stream_,FRAME_(3));
                write_sstring(stream_,O(showstack_string_GENV_frame)); # "�  GO_ENV <--> "
                prin1(stream_,FRAME_(4));
                write_sstring(stream_,O(showstack_string_DENV_frame)); # "�  DECL_ENV <--> "
                prin1(stream_,FRAME_(5));
                break;
              default:
                pushSTACK(S(show_stack));
                fehler(serious_condition,
                       DEUTSCH ? "~: Unbekannter Frame-Typ" :
                       ENGLISH ? "~: unknown frame type" :
                       FRANCAIS ? "~: Type d'environnement inconnu." :
                       ""
                      );
            }
          return FRAME_top; # Pointer �bern Frame
        }
    }

LISPFUNN(describe_frame,2)
# (SYS::DESCRIBE-FRAME stream framepointer) gibt das Stackitem, auf das der
# Pointer zeigt, detailliert aus.
  { var object* FRAME = test_framepointer_arg(); # Pointer in den Stack
    if (!streamp(STACK_0)) { fehler_stream(STACK_0); }
    print_stackitem(&STACK_0,FRAME); # Stack-Item ausgeben
    skipSTACK(1); value1 = NIL; mv_count=0; # keine Werte
  }

LISPFUNN(show_stack,0)
# (SHOW-STACK) zeigt den Inhalt des Stacks an.
  { var object* FRAME = STACK; # l�uft durch den Stack nach oben
    pushSTACK(var_stream(S(standard_output),strmflags_wr_ch_B)); # Stream *STANDARD-OUTPUT*
   {var object* stream_ = &STACK_0;
    until (eq(FRAME_(0),nullobj)) # Nullword = oberes Stackende
      { FRAME = print_stackitem(stream_,FRAME); } # Stack-Item ausgeben
    skipSTACK(1); value1 = NIL; mv_count=0; # keine Werte
  }}

LISPFUNN(debug,0)
# (SYSTEM::DEBUG) springt in einen im Hintergrund sitzenden Debugger.
  {
    #if !defined(AMIGAOS)
      abort();
    #else # AMIGAOS
      Debug(0);
    #endif
    value1 = NIL; mv_count=0; # keine Werte
  }

LISPFUNN(proom,0)
# (SYSTEM::%ROOM), liefert 3 Werte:
# - von LISP-Objekten belegter Platz
# - f�r LISP-Objekte freier Platz
# - von LISP-Objekten statisch belegter Platz
# bei SPVW_PAGES ausf�hrlicher machen??
  { value1 = fixnum(used_space());
    value2 = fixnum(free_space());
    value3 = fixnum(static_space());
    mv_count=3;
  }

LISPFUNN(gc,0)
# (GC) f�hrt eine GC aus
# und liefert den f�r LISP-Objekte freien Platz (in Bytes)
  { gar_col(); # GC ausf�hren
    value1 = fixnum(free_space()); mv_count=1;
  }

# read-form neu schreiben, in Zusammenarbeit mit dem Terminal-Stream??

