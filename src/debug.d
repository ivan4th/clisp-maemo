# Top-Level-Schleife, Hilfsfunktionen für Debugger, Stepper von CLISP
# Bruno Haible 1990-2001
# ILISP friendliness: Marcus Daniels 8.4.1994
# Sam Steingold 2001

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
# can trigger GC
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
  {
    pushSTACK(STACK_1); pushSTACK(STACK_1);
    STACK_3 = var_stream(S(standard_output),strmflags_wr_ch_B); # ostream := Wert von *STANDARD-OUTPUT*
    STACK_2 = var_stream(S(standard_input),strmflags_rd_ch_B); # istream := Wert von *STANDARD-INPUT*
    # Stackaufbau: ostream, istream, prompt, command-list.
    pushSTACK(STACK_2);
    pushSTACK(STACK_3); pushSTACK(NIL); funcall(L(terminal_raw),2); pushSTACK(value1);
    # Stackaufbau: ostream, istream, prompt, command-list, inputstream, raw.
    var signean status = listen_char(STACK_4); # horchen
    if (ls_eof_p(status))
      goto eof;
    # bereits Zeichen verfügbar (und nicht im ilisp_mode) -> kein Prompt
    if (ilisp_mode || interactive_stream_p(STACK_4)) {
      # interaktiver Input-Stream -> Prompt ausgeben:
      #if 0
        terpri(&STACK_5); # (TERPRI ostream)
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
        dynamic_bind(S(recurse_count_standard_output),fixnum_inc(Symbol_value(S(recurse_count_standard_output)),1)); # sys::*recurse-count-standard-output* erhöhen
        if (!posfixnump(Symbol_value(S(recurse_count_standard_output)))) # sollte ein Fixnum >=0 sein
          Symbol_value(S(recurse_count_standard_output)) = Fixnum_0; # sonst Notkorrektur
        if (posfixnum_to_L(Symbol_value(S(recurse_count_standard_output))) > 3) {
          # Mehrfach verschachtelte Fehlermeldung.
          Symbol_value(S(recurse_count_standard_output)) = Fixnum_0;
          Symbol_value(S(standard_output)) = unbound;
          dynamic_bind(S(recurse_count_debug_io),fixnum_inc(Symbol_value(S(recurse_count_debug_io)),1)); # sys::*recurse-count-debug-io* erhöhen
          if (!posfixnump(Symbol_value(S(recurse_count_debug_io)))) # sollte ein Fixnum >=0 sein
            Symbol_value(S(recurse_count_debug_io)) = Fixnum_0; # sonst Notkorrektur
          if (posfixnum_to_L(Symbol_value(S(recurse_count_debug_io))) > 3) {
            # Mehrfach verschachtelte Fehlermeldung.
            Symbol_value(S(recurse_count_debug_io)) = Fixnum_0;
            Symbol_value(S(debug_io)) = unbound;
            var_stream(S(debug_io),strmflags_rd_ch_B|strmflags_wr_ch_B);
          }
          STACK_(5+3+3) = var_stream(S(standard_output),strmflags_wr_ch_B); # ostream := Wert von *STANDARD-OUTPUT*
          dynamic_unbind();
        }
        terpri(&STACK_(5+3)); # (TERPRI ostream)
        dynamic_unbind();
      #endif
      write_string(&STACK_5,STACK_3); # (WRITE-STRING prompt ostream)
      force_output(STACK_5);
    }
    # Prompt OK
    {
      var object* inputstream_ = &STACK_1;
      #if 0 # Das erweist sich doch als ungeschickt: Drückt man Ctrl-C während
            # der Eingabe, so hat man dann in der Break-Schleife manche Kommandos
            # doppelt in der Liste!
      {
        var object list = Symbol_value(S(key_bindings)); # bisherige Key-Bindings
        if (!eq(STACK_2,unbound)) # command-list angegeben?
          list = nreconc(STACK_2,list); # ja -> davorhängen
        dynamic_bind(S(key_bindings),list); # SYS::*KEY-BINDINGS* binden
      }
      #else
      # statt        (nreconc command-list *key-bindings*)
      # doch lieber  (nreverse command-list)
      {
        var object list = (eq(STACK_2,unbound) ? NIL : nreverse(STACK_2));
        dynamic_bind(S(key_bindings),list); # SYS::*KEY-BINDINGS* binden
      }
      #endif
      #if !defined(TERMINAL_USES_KEYBOARD) # auf dem Atari ging's über Funktionstasten
      if (!ls_avail_p(status)) { # nur bei interaktivem Input-Stream
        # Erkennung von Kommandos statt Formen:
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
        pushSTACK(*inputstream_); pushSTACK(NIL); pushSTACK(NIL);
        funcall(L(read_line),3); # (READ-LINE istream nil nil)
        var object line = value1;
        if (nullp(line)) { # EOF am Zeilenanfang?
          dynamic_unbind(); # S(key_bindings)
          goto eof;
        }
        # NB: line is a simple-string, due to our particular READ-LINE
        # implementation.
        # search for line in *KEY-BINDINGS*:
        {
          var object alist = Symbol_value(S(key_bindings));
          var uintL input_len = Sstring_length(line);
          for (;consp(alist);alist = Cdr(alist))
            if (mconsp(Car(alist)) && simple_string_p(Car(Car(alist)))) {
              var object key = Car(Car(alist));
              var uintL len = Sstring_length(key);
              # check whether the line starts with the key and a whitespace
              if ((len <= input_len) && string_eqcomp_ci(line,0,key,0,len)) {
                if (len == input_len) goto found;
                # now len < input_len
                var cint ch;
                SstringDispatch(line,
                 { ch = as_cint(TheSstring(line)->data[len]); },
                 { ch = as_cint(as_chart(TheSmallSstring(line)->data[len])); });
                if (ch == '\t' || ch == '\n' || ch == ' ' ||
                    ch == '\r' || ch == '\f' || ch == '\v') {
                 found:
                  funcall(Cdr(Car(alist)),0); # call the appropriate function
                  dynamic_unbind(); # S(key_bindings)
                  goto eof;
                }
              }
            }
        }
        # create string-input-stream for this line:
        if (nullp(value2)) {
          pushSTACK(line); pushSTACK(O(newline_string));
          line = string_concat(2); # maybe need another Newline
        }
        pushSTACK(line); funcall(L(make_string_input_stream),1);
        # make concatenated-stream:
        pushSTACK(value1); pushSTACK(*inputstream_);
        funcall(L(make_concatenated_stream),2);
        dynamic_bind(S(terminal_read_stream),value1);
        *inputstream_ = Symbol_value(S(terminal_read_stream));
      }
      #endif
      dynamic_bind(S(read_suppress),NIL); # *READ-SUPPRESS* = NIL
      var object obj = stream_read(inputstream_,NIL,NIL); # read object (recursive-p=NIL, whitespace-p=NIL)
      dynamic_unbind(); # S(read_suppress)
      #if !defined(TERMINAL_USES_KEYBOARD)
      if (!ls_avail_p(status)) dynamic_unbind(); # S(terminal_read_stream)
      #endif
      dynamic_unbind(); # S(key_bindings)
      if (!eq(obj,eof_value)) { # EOF test (after whitespace)
        pushSTACK(obj);
        pushSTACK(STACK_(4+1)); pushSTACK(STACK_(0+1+1)); funcall(L(terminal_raw),2);
        # delete input till EOL
        if (interactive_stream_p(STACK_(4+1))) {
          while (ls_avail_p(listen_char(STACK_(4+1)))) {
            var object ch = peek_char(&STACK_(4+1));
            if (eq(ch,eof_value))
              break;
            read_char(&STACK_(4+1));
            if (eq(ch,ascii_char(NL)))
              break;
          }
        }
        value1 = popSTACK(); value2 = NIL; mv_count=2; # obj, NIL als Werte
        skipSTACK(4); return;
      }
    }
   eof: # bei EOF angelangt
    pushSTACK(STACK_4); pushSTACK(STACK_(0+1)); funcall(L(terminal_raw),2);
    # (clear-input istream) ausführen (um bei interaktivem Stream das EOF zu
    # schlucken: das fortzusetzende Programm könnte das EOF missverstehen):
    clear_input(STACK_4);
    value1 = value2 = T; mv_count=2; # T, T als Werte
    skipSTACK(4); return;
  }

# (SYS::READ-FORM prompt [commandlist])
# liest eine Form (interaktiv) von *standard-input*.
# prompt muss ein String sein.
# Statt einer Form kann auch eine Sondertaste aus commandlist (eine frische
# Aliste) oder SYS::*KEY-BINDINGS* eingegeben werden.
# Werte: form, NIL oder (bei EOF) T, T
LISPFUN(read_form,1,1,norest,nokey,0,NIL)
  {
    read_form(); skipSTACK(2);
  }

# (SYS::READ-EVAL-PRINT prompt [commandlist])
# liest eine Form, wertet sie aus und gibt die Werte aus.
# prompt muss ein String sein.
# Statt einer Form kann auch eine Sondertaste aus commandlist (eine frische
# Aliste) oder SYS::*KEY-BINDINGS* eingegeben werden.
# Werte: NIL oder (bei Sondertaste oder EOF) T
LISPFUN(read_eval_print,1,1,norest,nokey,0,NIL)
# (defun read-eval-print (prompt &optional (command-list nil))
#   (multiple-value-bind (form flag)
#       (read-form *standard-output* *standard-input* prompt command-list)
#     (if flag
#       form ; T zurück
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
#         |#; unnötige Leerzeile zwischen Input und Output vermeiden:
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
  {
    read_form(); # Form lesen
    # Stackaufbau: ostream, istream.
    if (!nullp(value2)) { # flag ?
      mv_count=1; skipSTACK(2); return; # T als Wert zurück
    }
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
    if (mconsp(STACK_0)) {
      loop {
        var object valsr = STACK_0;
        STACK_0 = Cdr(valsr);
        terpri(&STACK_(1+2));
        prin1(&STACK_(1+2),Car(valsr)); # nächsten Wert ausgeben
        # ';' als Trennzeichen vorm Zeilenende:
        if (matomp(STACK_0))
          break;
        write_ascii_char(&STACK_(1+2),' ');
        write_ascii_char(&STACK_(1+2),';');
      }
    }
    #else
    # unnötige Leerzeile zwischen Input und Output vermeiden:
    # (Es erscheint immer noch eine unnötige Leerzeile am Bildschirm,
    # wenn stdin vom Terminal kommt und stdout eine Pipe ist, die
    # letztendlich wieder aufs Terminal geht - z.B. via '| tee logfile'.
    # In diesem Fall müssen wir aber - eben wegen 'logfile' - ein NL auf
    # stdout ausgeben, und da stdin am Zeilenende von selbst ein NL aus-
    # gibt, ist diese Leerzeile wirklich unvermeidlich.)
    if (!eq(get_line_position(STACK_(1+2)),Fixnum_0))
      terpri(&STACK_(1+2)); # (fresh-line ostream)
    if (mconsp(STACK_0)) {
      loop {
        var object valsr = STACK_0;
        STACK_0 = Cdr(valsr);
        prin1(&STACK_(1+2),Car(valsr)); # nächsten Wert ausgeben
        # ';' als Trennzeichen vorm Zeilenende:
        if (matomp(STACK_0))
          break;
        write_ascii_char(&STACK_(1+2),' ');
        write_ascii_char(&STACK_(1+2),';');
        terpri(&STACK_(1+2));
      }
    }
    #endif
    skipSTACK(4);
    value1 = NIL; mv_count=1; # NIL als Wert
  }

# Startet den normalen Driver (Read-Eval-Print-Loop)
# driver();
  global void driver (void);
  global void driver()
    {
      loop {
        var object driverfun = Symbol_value(S(driverstern)); # Wert von *DRIVER*
        if (nullp(driverfun))
          break;
        funcall(driverfun,0); # mit 0 Argumenten aufrufen
      }
      # Default-Driver:
      Symbol_value(S(break_count)) = Fixnum_0; # SYS::*BREAK-COUNT* := 0
      # dann einen Driver-Frame aufbauen:
      {
        var object* top_of_frame = STACK; # Pointer übern Frame
        var sp_jmp_buf returner; # Rücksprungpunkt merken
        finish_entry_frame(DRIVER,&!returner,,;);
        # Hier ist der Einsprungpunkt.
        loop {
          # (SYS::READ-EVAL-PRINT "> ") ausführen:
          pushSTACK(O(prompt_string)); # Prompt "> "
          funcall(L(read_eval_print),1);
          if (eq(value1,T)) # EOF gelesen -> Schleife beenden
            break;
        }
        skipSTACK(2); # Driver-Frame auflösen
      }
    }

# Startet einen untergeordneten Driver (Read-Eval-Print-Loop)
# break_driver(continuable);
# > continuable: Flag, ob nach Beendigung des Drivers fortgefahren werden kann.
# can trigger GC
  global void break_driver (object continuable);
  global void break_driver(continuable)
    var object continuable;
    {
      pushSTACK(continuable);
      var object driverfun = Symbol_value(S(break_driver)); # Wert von *BREAK-DRIVER*
      if (!nullp(driverfun)) {
        pushSTACK(STACK_0); funcall(driverfun,1); # mit Argument continuable aufrufen
        if (nullp(popSTACK())) # nicht continuable?
          reset(); # -> dann zur nächsten Schleife zurück
      } else {
        # Default-Driver:
        # (CLEAR-INPUT *DEBUG-IO*) ausführen (weil das, was der Benutzer bisher
        # getippt hat, sicher nicht in Erwartung des Errors getippt wurde):
        clear_input(var_stream(S(debug_io),strmflags_rd_ch_B|strmflags_wr_ch_B));
        # SYS::*BREAK-COUNT* erhöhen:
        dynamic_bind(S(break_count),fixnum_inc(Symbol_value(S(break_count)),1));
        if (!posfixnump(Symbol_value(S(break_count)))) # sollte ein Fixnum >=0 sein
          Symbol_value(S(break_count)) = Fixnum_0; # sonst Notkorrektur
        # *STANDARD-INPUT* und *STANDARD-OUTPUT* an *DEBUG-IO* binden:
        {
          var object stream = var_stream(S(debug_io),strmflags_rd_ch_B|strmflags_wr_ch_B);
          dynamic_bind(S(standard_input),stream);
          dynamic_bind(S(standard_output),stream);
        }
        # *PRINT-ESCAPE* an T binden:
        dynamic_bind(S(print_escape),T);
        # Prompt aufbauen:
        {
          # (format nil "~S. Break> " SYS::*BREAK-COUNT*)
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
        {
          var object* top_of_frame = STACK; # Pointer übern Frame
          var sp_jmp_buf returner; # Rücksprungpunkt merken
          finish_entry_frame(DRIVER,&!returner,,;);
          # Hier ist der Einsprungpunkt.
          loop {
            # (SYS::READ-EVAL-PRINT Prompt) ausführen:
            pushSTACK(STACK_(0+2)); # Prompt "nnn. Break> "
            funcall(L(read_eval_print),1);
            if (eq(value1,T)) # EOF gelesen -> Schleife beenden
              break;
          }
          if (nullp(STACK_(0+4*3+1+2))) { # nicht continuable?
            unwind(); reset(); # -> dann zur nächsten Schleife zurück
          }
          skipSTACK(1+2); # Driver-Frame auflösen, Prompt vergessen
          dynamic_unbind(); dynamic_unbind(); dynamic_unbind(); dynamic_unbind();
          skipSTACK(1);
        }
      }
    }

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
  {
    funcall(L(open),1); # (OPEN filename)
    pushSTACK(value1); # stream retten
    loop {
      var object obj = stream_read(&STACK_0,NIL,NIL); # Objekt lesen
      if (eq(obj,eof_value)) # EOF -> fertig
        break;
      if (closurep(obj)) {
        funcall(obj,0); # Closure (vermutlich compilierte Closure) aufrufen
      } else {
        eval_noenv(obj); # sonstige Form evaluieren
      }
    }
    builtin_stream_close(&STACK_0); # stream schließen
    skipSTACK(1); value1 = T; mv_count=1; # Wert T
  }

# ---------------------------------------------------------------------------- #
#                   Hilfsfunktionen für Debugger und Stepper

# Die folgenden Funktionen klettern im Stack herum, überschreiten jedoch
# keinen Driver-Frame und auch nicht das obere Stackende.
# Gültige "Stackpointer" sind hierbei Pointer auf Stackelemente oder
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
# in erster Näherung:
# #define frame_p()  (!( (as_oint(FRAME_(0)) & wbit(frame_bit_o)) ==0))
# in zweiter Näherung, unter Berücksichtigung der Frames mit Skip2-bit:
  #define frame_p()  framep(FRAME)
  local bool framep (object* FRAME);
  local bool framep(FRAME)
    var object* FRAME;
    {
      # Ein normales Lisp-Objekt ist kein Frame:
      if ((as_oint(FRAME_(0)) & wbit(frame_bit_o)) ==0)
        return false;
      # Beginnt bei FRAME_(-1) ein Frame ohne Skip2-Bit, so ist FRAME_(0)
      # Teil dieses Frames, also nicht selber Beginn eines Frames:
      if (   (!(FRAME==STACK)) # nicht die STACK-Grenzen überschreiten!
          && ((as_oint(FRAME_(-1)) & wbit(skip2_bit_o)) == 0)
          && framep(FRAME STACKop -1)
         )
        return false;
      return true; # Sonst beginnt hier ein Frame.
    }

# Macro: Erniedrigt FRAME bis zum nächsten Frame.
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

# UP: überspringt ein Stackitem nach oben
  local object* frame_up_1 (object* stackptr);
  local object* frame_up_1(stackptr)
    var object* stackptr;
    {
      var object* FRAME = stackptr;
      if (frame_p())
        FRAME = topofframe(FRAME_(0)); # Pointer übern Frame
      else
        FRAME skipSTACKop 1; # Pointer aufs nächste Objekt
      return (stack_upend_p() ? stackptr : FRAME);
    }

# UP: überspringt ein Stackitem nach unten
  local object* frame_down_1 (object* stackptr);
  local object* frame_down_1(stackptr)
    var object* stackptr;
    {
      var object* FRAME = stackptr;
      next_frame_down(); # nächsten Frame drunter suchen
      if (!(topofframe(FRAME_(0)) == stackptr)) # nicht direkt unterhalb stackptr?
        FRAME = stackptr STACKop -1;
      return (stack_downend_p() ? stackptr : FRAME);
    }

# UP: springt zum nächsthöheren Frame
  local object* frame_up_2 (object* stackptr);
  local object* frame_up_2(stackptr)
    var object* stackptr;
    {
      var object* FRAME = stackptr;
      if (frame_p())
        FRAME = topofframe(FRAME_(0)); # Pointer übern Frame
      else
        FRAME skipSTACKop 1; # Pointer aufs nächste Objekt
      loop {
        if (stack_upend_p())
          return stackptr;
        if (as_oint(FRAME_(0)) & wbit(frame_bit_o))
          return FRAME;
        FRAME skipSTACKop 1;
      }
    }

# UP: springt zum nächstniedrigeren Frame
  local object* frame_down_2 (object* stackptr);
  local object* frame_down_2(stackptr)
    var object* stackptr;
    {
      var object* FRAME = stackptr;
      next_frame_down(); # nächsten Frame drunter suchen
      return (stack_downend_p() ? stackptr : FRAME);
    }

# UP: springt zum nächsthöheren lexikalischen Frame
  local object* frame_up_3 (object* stackptr);
  local object* frame_up_3(stackptr)
    var object* stackptr;
    {
      var object* FRAME = stackptr;
      if (frame_p())
        FRAME = topofframe(FRAME_(0)); # Pointer übern Frame
      else
        FRAME skipSTACKop 1; # Pointer aufs nächste Objekt
      loop {
        if (stack_upend_p())
          return stackptr;
        if (frame_p()) {
          if (lexical_frame_p())
            return FRAME;
          FRAME = topofframe(FRAME_(0)); # Pointer übern Frame
        } else {
          FRAME skipSTACKop 1;
        }
      }
    }

# UP: springt zum nächstniedrigeren lexikalischen Frame
  local object* frame_down_3 (object* stackptr);
  local object* frame_down_3(stackptr)
    var object* stackptr;
    {
      var object* FRAME = stackptr;
      loop {
        next_frame_down(); # nächsten Frame drunter suchen
        if (stack_downend_p())
          return stackptr;
        if (lexical_frame_p())
          break;
      }
      return FRAME;
    }

# UP: springt zum nächsthöheren EVAL/APPLY-Frame
  local object* frame_up_4 (object* stackptr);
  local object* frame_up_4(stackptr)
    var object* stackptr;
    {
      var object* FRAME = stackptr;
      if (frame_p())
        FRAME = topofframe(FRAME_(0)); # Pointer übern Frame
      else
        FRAME skipSTACKop 1; # Pointer aufs nächste Objekt
      loop {
        if (stack_upend_p())
          return stackptr;
        if (frame_p()) {
          if (evalapply_frame_p())
            return FRAME;
          FRAME = topofframe(FRAME_(0)); # Pointer übern Frame
        } else {
          FRAME skipSTACKop 1;
        }
      }
    }

# UP: springt zum nächstniedrigeren EVAL/APPLY-Frame
  local object* frame_down_4 (object* stackptr);
  local object* frame_down_4(stackptr)
    var object* stackptr;
    {
      var object* FRAME = stackptr;
      loop {
        next_frame_down(); # nächsten Frame drunter suchen
        if (stack_downend_p())
          return stackptr;
        if (evalapply_frame_p())
          break;
      }
      return FRAME;
    }

# UP: springt zum nächsthöheren APPLY-Frame
  local object* frame_up_5 (object* stackptr);
  local object* frame_up_5(stackptr)
    var object* stackptr;
    {
      var object* FRAME = stackptr;
      if (frame_p())
        FRAME = topofframe(FRAME_(0)); # Pointer übern Frame
      else
        FRAME skipSTACKop 1; # Pointer aufs nächste Objekt
      loop {
        if (stack_upend_p())
          return stackptr;
        if (frame_p()) {
          if (apply_frame_p())
            return FRAME;
          FRAME = topofframe(FRAME_(0)); # Pointer übern Frame
        } else {
          FRAME skipSTACKop 1;
        }
      }
    }

# UP: springt zum nächstniedrigeren APPLY-Frame
  local object* frame_down_5 (object* stackptr);
  local object* frame_down_5(stackptr)
    var object* stackptr;
    {
      var object* FRAME = stackptr;
      loop {
        next_frame_down(); # nächsten Frame drunter suchen
        if (stack_downend_p())
          return stackptr;
        if (apply_frame_p())
          break;
      }
      return FRAME;
    }

# Typ eines Pointers auf eine Hochsteige- bzw. Absteige-Routine:
  typedef object* (*kletterfun) (object* stackptr);

local const kletterfun frame_up_table[] =
  { &frame_up_1, &frame_up_2, &frame_up_3, &frame_up_4, &frame_up_5, };
local const kletterfun frame_down_table[] =
  { &frame_down_1, &frame_down_2, &frame_down_3, &frame_down_4, &frame_down_5, };

# UP: Überprüft und decodiert das mode-Argument.
# test_mode_arg(table)
# > STACK_0: mode
# > table: Tabelle der Routinen zum Hochsteigen bzw. zum Absteigen
# > subr_self: Aufrufer (ein SUBR)
# < ergebnis: Routine zum Hochsteigen bzw. zum Absteigen
# erhöht STACK um 1
  local kletterfun test_mode_arg (const kletterfun* table);
  local kletterfun test_mode_arg(table)
    var const kletterfun* table;
    {
      var object arg = popSTACK();
      var uintL mode;
      if (!(posfixnump(arg)
            && ((mode = posfixnum_to_L(arg)) > 0)
            && (mode<=5)
         ) ) {
        pushSTACK(arg); # TYPE-ERROR slot DATUM
        pushSTACK(O(type_climb_mode)); # TYPE-ERROR slot EXPECTED-TYPE
        pushSTACK(arg);
        pushSTACK(TheSubr(subr_self)->name);
        fehler(type_error,
               GETTEXT("~: bad frame climbing mode ~")
              );
      }
      return table[mode-1];
    }

# UP: Überprüft ein Frame-Pointer-Argument.
# test_framepointer_arg()
# > STACK_0: Lisp-Objekt, sollte ein Frame-Pointer sein
# > subr_self: Aufrufer (ein SUBR)
# < ergebnis: Frame-Pointer
# erhöht STACK um 1
  local object* test_framepointer_arg (void);
  local object* test_framepointer_arg()
    {
      var object arg = popSTACK();
      if (!framepointerp(arg)) {
        pushSTACK(arg);
        pushSTACK(TheSubr(subr_self)->name);
        fehler(error,
               GETTEXT("~: ~ is not a stack pointer")
              );
      }
      return uTheFramepointer(arg);
    }

LISPFUNN(frame_up_1,2)
# (SYS::FRAME-UP-1 framepointer mode) liefert den Frame-Pointer 1 höher.
  {
    var kletterfun frame_up_x = test_mode_arg(&frame_up_table[0]);
    var object* stackptr = test_framepointer_arg();
    stackptr = (*frame_up_x)(stackptr); # einmal hochsteigen
    value1 = make_framepointer(stackptr); mv_count=1;
  }

LISPFUNN(frame_up,2)
# (SYS::FRAME-UP framepointer mode) liefert den Frame-Pointer ganz oben.
  {
    var kletterfun frame_up_x = test_mode_arg(&frame_up_table[0]);
    var object* stackptr = test_framepointer_arg();
    # hochsteigen, bis es nicht mehr weiter geht:
    loop {
      var object* next_stackptr = (*frame_up_x)(stackptr);
      if (next_stackptr == stackptr)
        break;
      stackptr = next_stackptr;
    }
    value1 = make_framepointer(stackptr); mv_count=1;
  }

LISPFUNN(frame_down_1,2)
# (SYS::FRAME-DOWN-1 framepointer mode) liefert den Frame-Pointer 1 drunter.
  {
    var kletterfun frame_down_x = test_mode_arg(&frame_down_table[0]);
    var object* stackptr = test_framepointer_arg();
    stackptr = (*frame_down_x)(stackptr); # einmal hinabsteigen
    value1 = make_framepointer(stackptr); mv_count=1;
  }

LISPFUNN(frame_down,2)
# (SYS::FRAME-DOWN framepointer mode) liefert den Frame-Pointer ganz unten.
  {
    var kletterfun frame_down_x = test_mode_arg(&frame_down_table[0]);
    var object* stackptr = test_framepointer_arg();
    # hinabsteigen, bis es nicht mehr weiter geht:
    loop {
      var object* next_stackptr = (*frame_down_x)(stackptr);
      if (next_stackptr == stackptr)
        break;
      stackptr = next_stackptr;
    }
    value1 = make_framepointer(stackptr); mv_count=1;
  }

LISPFUNN(the_frame,0)
# (SYS::THE-FRAME) liefert den aktuellen Stackpointer als Frame-Pointer.
  {
    var object* stackptr = STACK;
    stackptr = frame_up_2(stackptr); # bis zum nächsthöheren Frame hoch
    value1 = make_framepointer(stackptr); mv_count=1;
  }

# UP: aktiviert dasselbe lexikalische Environment, das beim Framepointer
# STACK_0 aktiv war.
# same_env_as();
# erhöht STACK um 1, baut auf dem STACK einen ENV5-Frame auf
  local void same_env_as (void);
  local void same_env_as()
    {
      var object* FRAME = test_framepointer_arg();
      var environment env;
      # 5 Environments noch "leer":
      env.var_env = nullobj;
      env.fun_env = nullobj;
      env.block_env = nullobj;
      env.go_env = nullobj;
      env.decl_env = nullobj;
      # und füllen:
      loop {
        # ab FRAME abwärts nach ENV-Frames suchen:
        loop {
          FRAME skipSTACKop -1;
          if (FRAME==STACK) # Stack zu Ende?
            goto end;
          if (frame_p()
              && (!( (as_oint(FRAME_(0)) & wbit(skip2_bit_o)) ==0))
              && (!( (as_oint(FRAME_(0)) & wbit(envbind_bit_o)) ==0))
             )
            break;
        }
        # Nächster ENV-Frame gefunden.
        # Sein Inhalt füllt die noch leeren Komponenten von env:
        switch (framecode(FRAME_(0)) & envbind_case_mask_t) {
          case (ENV1V_frame_info & envbind_case_mask_t): # 1 VAR_ENV
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
        # Falls alle einzelnen Environments von env gefüllt (/=nullobj) sind,
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
  {
    var object fun = popSTACK();
    same_env_as(); # Environment von framepointer aktivieren
    funcall(fun,0); # fun aufrufen
    unwind(); # Environment-Frame auflösen
  }

LISPFUNN(eval_at,2)
# (SYS::EVAL-AT framepointer form) aktiviert dasselbe lexikalische
# Environment, das bei framepointer aktiv war, und wertet darin die Form aus.
  {
    var object form = popSTACK();
    same_env_as(); # Environment von framepointer aktivieren
    eval(form); # form auswerten
    unwind(); # Environment-Frame auflösen
  }

LISPFUNN(eval_frame_p,1)
# (SYS::EVAL-FRAME-P framepointer)
# gibt an, ob framepointer auf einen EVAL/APPLY-Frame zeigt.
  {
    var object* FRAME = test_framepointer_arg();
    value1 = (evalapply_frame_p() ? T : NIL); mv_count=1;
  }

LISPFUNN(driver_frame_p,1)
# (SYS::DRIVER-FRAME-P framepointer)
# gibt an, ob framepointer auf einen Driver-Frame zeigt.
  {
    var object* FRAME = test_framepointer_arg();
    value1 = (framecode(FRAME_(0)) == DRIVER_frame_info ? T : NIL); mv_count=1;
  }

# Fehlermeldung, wenn kein EVAL/APPLY-Frame-Pointer vorliegt.
# fehler_evalframe(obj);
# > subr_self: Aufrufer (ein SUBR)
# > obj: kein EVAL/APPLY-Frame-Pointer
  nonreturning_function(local, fehler_evalframe, (object obj)) {
    pushSTACK(obj);
    pushSTACK(TheSubr(subr_self)->name);
    fehler(error,
           GETTEXT("~: ~ is not a pointer to an EVAL/APPLY frame")
          );
  }

LISPFUNN(trap_eval_frame,2)
# (SYS::TRAP-EVAL-FRAME framepointer flag) schaltet den Breakpoint am
# angegebenen EVAL/APPLY-Frame je nach flag an bzw. aus.
  {
    var object flag = popSTACK();
    var object frame = popSTACK();
    if (!framepointerp(frame))
      fehler_evalframe(frame);
    var object* FRAME = uTheFramepointer(frame);
    if (!evalapply_frame_p())
      fehler_evalframe(frame);
    # FRAME zeigt auf den EVAL/APPLY-Frame.
    if (!nullp(flag)) {
      # Breakpoint einschalten
      *(oint*)(&FRAME_(0)) |= wbit(trapped_bit_o);
    } else {
      # Breakpoint ausschalten
      *(oint*)(&FRAME_(0)) &= ~wbit(trapped_bit_o);
    }
    value1 = frame; mv_count=1; # framepointer als Wert
  }

LISPFUNN(redo_eval_frame,1)
# (SYS::REDO-EVAL-FRAME framepointer) unwindet bis zum angegebenen
# EVAL/APPLY-Frame und fängt erneut an, diesen abzuarbeiten.
  {
    var object frame = popSTACK();
    if (!framepointerp(frame))
      fehler_evalframe(frame);
    var object* FRAME = uTheFramepointer(frame);
    if (!evalapply_frame_p())
      fehler_evalframe(frame);
    # FRAME zeigt auf den EVAL/APPLY-Frame.
    value1 = NIL; mv_count=0; # keine Werte zu retten
    unwind_upto(FRAME); # bis zum EVAL/APPLY-Frame alles auflösen, dorthin springen
  }

LISPFUNN(return_from_eval_frame,2)
# (SYS::RETURN-FROM-EVAL-FRAME framepointer form)
# unwindet bis zum angegebenen EVAL/APPLY-Frame und gibt als dessen Werte die
# Werte der Evaluierung der angegebenen form zurück.
  {
    var object form = popSTACK();
    var object frame = popSTACK();
    if (!framepointerp(frame))
      fehler_evalframe(frame);
    var object* FRAME = uTheFramepointer(frame);
    if (!evalapply_frame_p())
      fehler_evalframe(frame);
    # FRAME zeigt auf den EVAL/APPLY-Frame.
    value1 = form; mv_count=1; # form retten und übergeben
    unwind_upto(FRAME); # bis zum EVAL/APPLY-Frame alles auflösen, dorthin springen
  }

# ---------------------------------------------------------------------------- #
#                                 Debughilfen

# UP: Gibt das Stackitem FRAME_(0) detailliert auf den Stream aus
# und liefert den nächsthöheren stackptr.
# print_stackitem(&stream,FRAME)
# can trigger GC
  local object* print_stackitem (const object* stream_, object* FRAME);
  local object* print_stackitem(stream_,FRAME)
    var const object* stream_;
    var object* FRAME;
    {
      if (!frame_p()) {
        # kein Frame, normales LISP-Objekt
        write_sstring(stream_,O(showstack_string_lisp_obj)); # "¿- "
        var object obj = FRAME_(0);
        #if !defined(NO_symbolflags)
        switch (typecode(obj)) { # evtl. Symbol-Flags entfernen
          case_symbolflagged: obj = symbol_without_flags(obj);
          default: break;
        }
        #endif
        prin1(stream_,obj); # LISP-Objekt ausgeben
        return FRAME STACKop 1;
      } else {
        # Frame angetroffen
        var object* FRAME_top = topofframe(FRAME_(0)); # Pointer übern Frame
        switch (framecode(FRAME_(0))) { # je nach Frametyp
          case TRAPPED_APPLY_frame_info:
            # getrapte APPLY-Frames:
            write_sstring(stream_,OLS(showstack_string_TRAPPED_APPLY_frame)); # "¿APPLY-Frame mit Breakpoint für Aufruf "
            goto APPLY_frame;
          case APPLY_frame_info:
            # APPLY-Frames:
            write_sstring(stream_,OLS(showstack_string_APPLY_frame)); # "¿APPLY-Frame für Aufruf "
          APPLY_frame:
            # Funktionsnamen und Argumente ausgeben:
            write_ascii_char(stream_,'('); # '(' ausgeben
            prin1(stream_,TheIclosure(FRAME_(frame_closure))->clos_name); # Namen ausgeben
            {
              var object* argptr = FRAME_top;
              var uintL count = STACK_item_count(FRAME STACKop frame_args,FRAME_top);
              dotimesL(count,count, {
                write_ascii_char(stream_,' '); # ' ' ausgeben
                write_ascii_char(stream_,'\''); # "'" ausgeben
                prin1(stream_,NEXT(argptr)); # nächstes Argument ausgeben
              });
            }
            write_ascii_char(stream_,')'); # ')' ausgeben
            break;
          case TRAPPED_EVAL_frame_info:
            # getrapte EVAL-Frames:
            write_sstring(stream_,OLS(showstack_string_TRAPPED_EVAL_frame)); # "¿EVAL-Frame mit Breakpoint für Form "
            goto EVAL_frame;
          case EVAL_frame_info:
            # EVAL-Frames:
            write_sstring(stream_,OLS(showstack_string_EVAL_frame)); # "¿EVAL-Frame für Form "
          EVAL_frame:
            prin1(stream_,FRAME_(frame_form)); # Form ausgeben
            break;
          case DYNBIND_frame_info:
            # dynamische Variablenbindungsframes:
            write_sstring(stream_,OLS(showstack_string_DYNBIND_frame)); # "¿Variablenbindungs-Frame bindet (~ = dynamisch):"
            # Bindungen ausgeben:
            FRAME skipSTACKop 1;
            until (FRAME==FRAME_top) {
              # Bindung von Symbol FRAME_(0) an Wert FRAME_(1) ausgeben:
              write_sstring(stream_,O(showstack_string_bindung)); # "¿  | "
              write_ascii_char(stream_,'~'); # '~' ausgeben
              write_ascii_char(stream_,' '); # ' ' ausgeben
              prin1(stream_,FRAME_(0)); # Symbol ausgeben
              write_sstring(stream_,O(showstack_string_zuord)); # " <--> "
              prin1(stream_,FRAME_(1)); # Wert ausgeben
              FRAME skipSTACKop 2;
            }
            break;
          #ifdef HAVE_SAVED_REGISTERS
          case CALLBACK_frame_info:
            # Callback-Register-Frames:
            write_sstring(stream_,OLS(showstack_string_CALLBACK_frame)); # "¿CALLBACK-Frame"
            break;
          #endif
          # Variablen- und Funktionsbindungsframes:
          case VAR_frame_info:
            write_sstring(stream_,OLS(showstack_string_VAR_frame)); # "¿Variablenbindungs-Frame "
            #ifdef NO_symbolflags
            prin1(stream_,make_framepointer(FRAME)); # Frame-Pointer ausgeben
            write_sstring(stream_,OLS(showstack_string_binds)); # " bindet (~ = dynamisch):"
            pushSTACK(FRAME_(frame_next_env)); # weiteres Environment retten
            # Bindungen ausgeben:
            FRAME skipSTACKop frame_bindings;
            until (FRAME==FRAME_top) {
              if (!( (as_oint(FRAME_(varframe_binding_mark)) & wbit(active_bit_o)) ==0)) {
                # Bindung von Symbol FRAME_(1) an Wert FRAME_(2) ausgeben:
                write_sstring(stream_,O(showstack_string_bindung)); # "¿  | "
                if (!( (as_oint(FRAME_(varframe_binding_mark)) & wbit(dynam_bit_o)) ==0)) # Bindung dynamisch?
                  write_ascii_char(stream_,'~'); # ja -> '~' ausgeben
                write_ascii_char(stream_,' '); # ' ' ausgeben
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
            write_sstring(stream_,OLS(showstack_string_FUN_frame)); # "¿Funktionsbindungs-Frame "
            goto VARFUN_frame;
          VARFUN_frame:
            prin1(stream_,make_framepointer(FRAME)); # Frame-Pointer ausgeben
            write_sstring(stream_,OLS(showstack_string_binds)); # " bindet (~ = dynamisch):"
            pushSTACK(FRAME_(frame_next_env)); # weiteres Environment retten
            # Bindungen ausgeben:
            FRAME skipSTACKop frame_bindings;
            until (FRAME==FRAME_top) {
              if (!( (as_oint(FRAME_(0)) & wbit(active_bit_o)) ==0)) {
                # Bindung von Symbol FRAME_(0) an Wert FRAME_(1) ausgeben:
                write_sstring(stream_,O(showstack_string_bindung)); # "¿  | "
                if (!( (as_oint(FRAME_(0)) & wbit(dynam_bit_o)) ==0)) # Bindung dynamisch?
                  write_ascii_char(stream_,'~'); # ja -> '~' ausgeben
                write_ascii_char(stream_,' '); # ' ' ausgeben
                prin1(stream_,symbol_without_flags(FRAME_(0))); # Symbol ausgeben
                write_sstring(stream_,O(showstack_string_zuord)); # " <--> "
                prin1(stream_,FRAME_(1)); # Wert ausgeben
              }
              FRAME skipSTACKop 2;
            }
          VARFUN_frame_next:
            # Weiteres Environment ausgeben:
            write_sstring(stream_,OLS(showstack_string_next_env)); # "¿  Weiteres Environment: "
            {
              var object env = popSTACK(); # weiteres Environment
              if (!simple_vector_p(env)) {
                prin1(stream_,env);
              } else {
                # weiteres Environment ist ein Vektor, der Länge 2n+1
                do {
                  pushSTACK(env);
                  var uintL count = floor(Svector_length(env),2); # = n = Bindungszahl
                  var uintL index = 0;
                  dotimesL(count,count, {
                    write_sstring(stream_,O(showstack_string_bindung)); # "¿  | "
                    prin1(stream_,TheSvector(STACK_0)->data[index++]); # Symbol ausgeben
                    write_sstring(stream_,O(showstack_string_zuord)); # " <--> "
                    prin1(stream_,TheSvector(STACK_0)->data[index++]); # Symbol ausgeben
                  });
                  env = TheSvector(popSTACK())->data[index]; # letztes Vektor-Element
                } while (simple_vector_p(env));
              }
            }
            break;
          # Compilierte Block/Tagbody-Frames:
          case CBLOCK_CTAGBODY_frame_info:
            if (simple_vector_p(Car(FRAME_(frame_ctag)))) {
              # compilierte Tagbody-Frames:
              write_sstring(stream_,OLS(showstack_string_CTAGBODY_frame)); # "¿Tagbody-Frame (compiliert) für "
              prin1(stream_,Car(FRAME_(frame_ctag))); # Tag-Vektor
            } else {
              # compilierte Block-Frames:
              write_sstring(stream_,OLS(showstack_string_CBLOCK_frame)); # "¿Block-Frame (compiliert) für "
              prin1(stream_,Car(FRAME_(frame_ctag))); # Blockname
            }
            break;
          # Interpretierte Block-Frames:
          case IBLOCK_frame_info:
            write_sstring(stream_,OLS(showstack_string_IBLOCK_frame)); # "¿Block-Frame "
            goto IBLOCK_frame;
          case NESTED_IBLOCK_frame_info:
            write_sstring(stream_,OLS(showstack_string_NESTED_IBLOCK_frame)); # "¿Block-Frame (genestet) "
            goto IBLOCK_frame;
          IBLOCK_frame:
            pushSTACK(FRAME_(frame_next_env));
            prin1(stream_,make_framepointer(FRAME)); # Frame-Pointer ausgeben
            write_sstring(stream_,OLS(showstack_string_for1)); # " für "
            prin1(stream_,FRAME_(frame_name)); # Blockname
            goto NEXT_ENV;
          # Interpretierte Tagbody-Frames:
          case ITAGBODY_frame_info:
            write_sstring(stream_,OLS(showstack_string_ITAGBODY_frame)); # "¿Tagbody-Frame "
            goto ITAGBODY_frame;
          case NESTED_ITAGBODY_frame_info:
            write_sstring(stream_,OLS(showstack_string_NESTED_ITAGBODY_frame)); # "¿Tagbody-Frame (genestet) "
            goto ITAGBODY_frame;
          ITAGBODY_frame:
            pushSTACK(FRAME_(frame_next_env));
            prin1(stream_,make_framepointer(FRAME)); # Frame-Pointer ausgeben
            write_sstring(stream_,OLS(showstack_string_for2)); # " für"
            # Tags/Bodys ausgeben:
            FRAME skipSTACKop frame_bindings;
            until (FRAME==FRAME_top) {
              # Bindung von Tag FRAME_(0) an Body FRAME_(1) ausgeben:
              write_sstring(stream_,O(showstack_string_bindung)); # "¿  | "
              prin1(stream_,FRAME_(0)); # Tag ausgeben
              write_sstring(stream_,O(showstack_string_zuordtag)); # " --> "
              prin1(stream_,FRAME_(1)); # Body ausgeben
              FRAME skipSTACKop 2;
            }
            goto NEXT_ENV;
          NEXT_ENV: # Ausgeben eines Block- oder Tagbody-Environments STACK_0
            write_sstring(stream_,OLS(showstack_string_next_env)); # "¿  Weiteres Environment: "
            {
              var object env = popSTACK();
              if (!consp(env)) {
                prin1(stream_,env);
              } else {
                # weiteres Environment ist eine Aliste
                do {
                  pushSTACK(Cdr(env));
                  env = Car(env);
                  if (atomp(env)) {
                    pushSTACK(S(show_stack));
                    fehler(error,
                           GETTEXT("~: environment is not an alist")
                          );
                  }
                  pushSTACK(Cdr(env));
                  pushSTACK(Car(env));
                  write_sstring(stream_,O(showstack_string_bindung)); # "¿  | "
                  prin1(stream_,popSTACK());
                  write_sstring(stream_,O(showstack_string_zuordtag)); # " --> "
                  prin1(stream_,popSTACK());
                  env = popSTACK();
                } while (consp(env));
              }
            }
            break;
          case CATCH_frame_info:
            # Catch-Frames:
            write_sstring(stream_,OLS(showstack_string_CATCH_frame)); # "¿Catch-Frame für Tag "
            prin1(stream_,FRAME_(frame_tag)); # Tag
            break;
          case HANDLER_frame_info:
            # Handler-Frames:
            write_sstring(stream_,OLS(showstack_string_HANDLER_frame)); # "¿Handler-Frame für Conditions"
            {
              var uintL m2 = Svector_length(Car(FRAME_(frame_handlers))); # 2*m
              var uintL i = 0;
              do {
                write_ascii_char(stream_,' '); # ' ' ausgeben
                prin1(stream_,TheSvector(Car(FRAME_(frame_handlers)))->data[i]); # Typ i ausgeben
                i += 2;
              } while (i < m2);
            }
            break;
          case UNWIND_PROTECT_frame_info:
            # Unwind-Protect-Frames:
            write_sstring(stream_,OLS(showstack_string_UNWIND_PROTECT_frame)); # "¿Unwind-Protect-Frame"
            break;
          case DRIVER_frame_info:
            # Driver-Frames:
            write_sstring(stream_,OLS(showstack_string_DRIVER_frame)); # "¿¿Driver-Frame"
            break;
          # Environment-Frames:
          case ENV1V_frame_info:
            write_sstring(stream_,OLS(showstack_string_ENV_frame)); # "¿Environment-Bindungs-Frame"
            write_sstring(stream_,O(showstack_string_VENV_frame)); # "¿  VAR_ENV <--> "
            prin1(stream_,FRAME_(1));
            break;
          case ENV1F_frame_info:
            write_sstring(stream_,OLS(showstack_string_ENV_frame)); # "¿Environment-Bindungs-Frame"
            write_sstring(stream_,O(showstack_string_FENV_frame)); # "¿  FUN_ENV <--> "
            prin1(stream_,FRAME_(1));
            break;
          case ENV1B_frame_info:
            write_sstring(stream_,OLS(showstack_string_ENV_frame)); # "¿Environment-Bindungs-Frame"
            write_sstring(stream_,O(showstack_string_BENV_frame)); # "¿  BLOCK_ENV <--> "
            prin1(stream_,FRAME_(1));
            break;
          case ENV1G_frame_info:
            write_sstring(stream_,OLS(showstack_string_ENV_frame)); # "¿Environment-Bindungs-Frame"
            write_sstring(stream_,O(showstack_string_GENV_frame)); # "¿  GO_ENV <--> "
            prin1(stream_,FRAME_(1));
            break;
          case ENV1D_frame_info:
            write_sstring(stream_,OLS(showstack_string_ENV_frame)); # "¿Environment-Bindungs-Frame"
            write_sstring(stream_,O(showstack_string_DENV_frame)); # "¿  DECL_ENV <--> "
            prin1(stream_,FRAME_(1));
            break;
          case ENV2VD_frame_info:
            write_sstring(stream_,OLS(showstack_string_ENV_frame)); # "¿Environment-Bindungs-Frame"
            write_sstring(stream_,O(showstack_string_VENV_frame)); # "¿  VAR_ENV <--> "
            prin1(stream_,FRAME_(1));
            write_sstring(stream_,O(showstack_string_DENV_frame)); # "¿  DECL_ENV <--> "
            prin1(stream_,FRAME_(2));
            break;
          case ENV5_frame_info:
            write_sstring(stream_,OLS(showstack_string_ENV_frame)); # "¿Environment-Bindungs-Frame"
            write_sstring(stream_,O(showstack_string_VENV_frame)); # "¿  VAR_ENV <--> "
            prin1(stream_,FRAME_(1));
            write_sstring(stream_,O(showstack_string_FENV_frame)); # "¿  FUN_ENV <--> "
            prin1(stream_,FRAME_(2));
            write_sstring(stream_,O(showstack_string_BENV_frame)); # "¿  BLOCK_ENV <--> "
            prin1(stream_,FRAME_(3));
            write_sstring(stream_,O(showstack_string_GENV_frame)); # "¿  GO_ENV <--> "
            prin1(stream_,FRAME_(4));
            write_sstring(stream_,O(showstack_string_DENV_frame)); # "¿  DECL_ENV <--> "
            prin1(stream_,FRAME_(5));
            break;
          default:
            pushSTACK(S(show_stack));
            fehler(serious_condition,
                   GETTEXT("~: unknown frame type")
                  );
        }
        return FRAME_top; # Pointer übern Frame
      }
    }

LISPFUNN(describe_frame,2)
# (SYS::DESCRIBE-FRAME stream framepointer) gibt das Stackitem, auf das der
# Pointer zeigt, detailliert aus.
  {
    var object* FRAME = test_framepointer_arg(); # Pointer in den Stack
    if (!streamp(STACK_0))
      fehler_stream(STACK_0);
    print_stackitem(&STACK_0,FRAME); # Stack-Item ausgeben
    skipSTACK(1); value1 = NIL; mv_count=0; # keine Werte
  }

LISPFUNN(show_stack,0)
# (SHOW-STACK) zeigt den Inhalt des Stacks an.
  {
    var object* FRAME = STACK; # läuft durch den Stack nach oben
    pushSTACK(var_stream(S(standard_output),strmflags_wr_ch_B)); # Stream *STANDARD-OUTPUT*
    var object* stream_ = &STACK_0;
    var uintL count = 0;
    until (eq(FRAME_(0),nullobj)) { # Nullword = oberes Stackende
      FRAME = print_stackitem(stream_,FRAME); # Stack-Item ausgeben
      count++;
    }
    skipSTACK(1); value1 = UL_to_I(count); mv_count=1;
  }

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
# - für LISP-Objekte freier Platz
# - von LISP-Objekten statisch belegter Platz
# bei SPVW_PAGES ausführlicher machen??
  {
    var uintL n1 = used_space();
    var uintL n2 = free_space();
    var uintL n3 = static_space();
    pushSTACK(UL_to_I(n1));
    pushSTACK(UL_to_I(n2));
    pushSTACK(UL_to_I(n3));
    STACK_to_mv(3);
  }

LISPFUNN(gc,0)
# (GC) führt eine GC aus
# und liefert den für LISP-Objekte freien Platz (in Bytes)
  {
    gar_col(); # GC ausführen
    value1 = fixnum(free_space()); mv_count=1;
  }

# read-form neu schreiben, in Zusammenarbeit mit dem Terminal-Stream??

