# Error-Handling f�r CLISP
# Bruno Haible 26.6.1997
# Marcus Daniels 8.4.1994

#include "lispbibl.c"


# SYS::*RECURSIVE-ERROR-COUNT* = Rekursionstiefe der Ausgabe von Errormeldungen

# UP: Beginnt die Ausgabe einer Errormeldung.
# begin_error()
# < STACK_0: Stream (i.a. *ERROR-OUTPUT*)
# < STACK_1: Wert von *error-handler*
# < STACK_2: Argumentliste f�r *error-handler*
# < STACK_3: Condition-Typ (i.a. SIMPLE-ERROR) oder NIL
# erniedrigt STACK um 7
  local void begin_error (void);
  local void begin_error()
    { end_system_call(); # keine Betriebssystem-Operation l�uft mehr
      #ifdef PENDING_INTERRUPTS
        interrupt_pending = FALSE; # Ctrl-C-Wartezeit ist gleich beendet
        #ifndef WIN32_NATIVE
          begin_system_call();
          #ifdef HAVE_UALARM
            ualarm(0,0); # SIGALRM-Timer abbrechen
          #else
            alarm(0); # SIGALRM-Timer abbrechen
          #endif
          end_system_call();
        #endif
      #endif
      # Error-Count erh�hen, bei >3 Ausgabe-Abbruch:
      dynamic_bind(S(recursive_error_count),fixnum_inc(Symbol_value(S(recursive_error_count)),1));
      if (!posfixnump(Symbol_value(S(recursive_error_count)))) # sollte ein Fixnum >=0 sein
        { Symbol_value(S(recursive_error_count)) = Fixnum_0; } # sonst Notkorrektur
      if (posfixnum_to_L(Symbol_value(S(recursive_error_count))) > 3)
        { # Mehrfach verschachtelte Fehlermeldung.
          Symbol_value(S(recursive_error_count)) = Fixnum_0; # Error-Count l�schen
          # *PRINT-PRETTY* an NIL binden (um Speicher zu sparen):
          dynamic_bind(S(print_pretty),NIL);
          fehler(serious_condition,
                 DEUTSCH ? "Unausgebbare Fehlermeldung" :
                 ENGLISH ? "Unprintable error message" :
                 FRANCAIS ? "Message inimprimable" :
                 ""
                );
        }
     {var object error_handler = Symbol_value(S(error_handler)); # *ERROR-HANDLER*
      if (!nullp(error_handler))
        # *ERROR-HANDER* /= NIL
        { pushSTACK(NIL); pushSTACK(NIL); pushSTACK(error_handler);
          pushSTACK(make_string_output_stream()); # String-Output-Stream
        }
        else
        if (nullp(Symbol_value(S(use_clcs)))) # SYS::*USE-CLCS*
          # *ERROR-HANDER* = NIL, SYS::*USE-CLCS* = NIL
          { pushSTACK(NIL); pushSTACK(NIL); pushSTACK(NIL);
            pushSTACK(var_stream(S(error_output),strmflags_wr_ch_B)); # Stream *ERROR-OUTPUT*
            terpri(&STACK_0); # neue Zeile
            write_sstring(&STACK_0,O(error_string1)); # "*** - " ausgeben
          }
          else
          # *ERROR-HANDER* = NIL, SYS::*USE-CLCS* /= NIL
          { pushSTACK(S(simple_error)); pushSTACK(NIL); pushSTACK(unbound);
            pushSTACK(make_string_output_stream()); # String-Output-Stream
          }
    }}

# UP: Gibt ein Error-Objekt aus.
  local void write_errorobject (object obj);
  local void write_errorobject(obj)
    var object obj;
    { if (nullp(STACK_1))
        { dynamic_bind(S(prin_stream),unbound); # SYS::*PRIN-STREAM* an #<UNBOUND> binden
          dynamic_bind(S(print_escape),T); # *PRINT-ESCAPE* an T binden
          prin1(&STACK_(0+3+3),obj); # direkt ausgeben
          dynamic_unbind();
          dynamic_unbind();
        }
        else
        { # obj auf die Argumentliste schieben:
          pushSTACK(obj);
          obj = allocate_cons();
          Car(obj) = popSTACK();
          Cdr(obj) = STACK_2; STACK_2 = obj;
          # und "~S" in den Format-String schreiben:
          write_schar(&STACK_0,'~'); write_schar(&STACK_0,'S');
    }   }

# UP: Gibt ein Error-Character aus.
  local void write_errorchar (object obj);
  local void write_errorchar(obj)
    var object obj;
    { if (nullp(STACK_1))
        { write_char(&STACK_0,obj); } # direkt ausgeben
        else
        { # obj auf die Argumentliste schieben:
          pushSTACK(obj);
          obj = allocate_cons();
          Car(obj) = popSTACK();
          Cdr(obj) = STACK_2; STACK_2 = obj;
          # und "~A" in den Format-String schreiben:
          write_schar(&STACK_0,'~'); write_schar(&STACK_0,'A');
    }   }

# UP: Gibt einen Errorstring aus. Bei jeder Tilde '~' wird ein Objekt aus dem
# Stack ausgegeben, bei jedem '$' wird ein Character aus dem Stack ausgegeben.
# write_errorstring(errorstring)
# > STACK_0: Stream usw.
# > errorstring: Errorstring (ein unverschieblicher ASCIZ-String)
# > STACK_7, STACK_8, ...: Argumente (f�r jedes '~' bzw. '$' eines),
#   in umgekehrter Reihenfolge wie bei FUNCALL !
# < ergebnis: STACK-Wert oberhalb des Stream und der Argumente
  local object* write_errorstring (const char* errorstring);
  local object* write_errorstring(errorstring)
    var const char* errorstring;
    { var object* argptr = args_end_pointer STACKop 7; # Pointer �bern Stream und Frame
      loop
        { var uintB ch = *errorstring++; # n�chstes Zeichen
          if (ch==0) break; # String zu Ende?
          if (ch=='~') # Tilde?
            # ja -> ein Objekt vom Stack ausgeben:
            { write_errorobject(BEFORE(argptr)); }
          elif (ch=='$') # '$' ?
            # ja -> ein Character vom Stack ausgeben:
            { write_errorchar(BEFORE(argptr)); }
          else
            # nein -> Zeichen normal ausgeben:
            { write_char(&STACK_0,code_char(ch)); }
        }
      return argptr;
    }

# Beendet die Ausgabe einer Fehlermeldung und startet neuen Driver.
# end_error();
  nonreturning_function(local, end_error, (object* stackptr));
  local void end_error(stackptr)
    var object* stackptr;
    { if (nullp(STACK_1))
        # *ERROR-HANDER* = NIL, SYS::*USE-CLCS* = NIL
        { skipSTACK(4); # Fehlermeldung wurde schon ausgegeben
          dynamic_unbind(); # Bindungsframe f�r sys::*recursive-error-count* aufl�sen,
                            # da keine Fehlermeldungs-Ausgabe mehr aktiv
          set_args_end_pointer(stackptr);
          break_driver(NIL); # Break-Driver aufrufen (kehrt nicht zur�ck)
        }
        else
        { STACK_0 = get_output_stream_string(&STACK_0);
         {var object arguments = nreverse(STACK_2);
          # Stackaufbau: type, args, handler, errorstring.
          if (!eq(STACK_1,unbound))
            # *ERROR-HANDER* /= NIL
            { # Stackaufbau: nil, args, handler, errorstring.
              # (apply *error-handler* nil errorstring args) ausf�hren:
              check_SP(); check_STACK();
              {var object error_handler = STACK_1; STACK_1 = NIL;
               apply(error_handler,2,arguments);
               skipSTACK(2);
              }
              dynamic_unbind(); # Bindungsframe f�r sys::*recursive-error-count* aufl�sen,
                                # da keine Fehlermeldungs-Ausgabe mehr aktiv
              set_args_end_pointer(stackptr);
              break_driver(NIL); # Break-Driver aufrufen (kehrt nicht zur�ck)
            }
            else
            # *ERROR-HANDER* = NIL, SYS::*USE-CLCS* /= NIL
            { # Stackaufbau: type, args, --, errorstring.
              var object type = STACK_3;
              var object errorstring = STACK_0;
              skipSTACK(4);
              dynamic_unbind(); # Bindungsframe f�r sys::*recursive-error-count* aufl�sen
              # (APPLY #'coerce-to-condition errorstring args 'error type keyword-arguments)
              # ausf�hren:
              pushSTACK(errorstring); pushSTACK(arguments); pushSTACK(S(error)); pushSTACK(type);
             {var uintC argcount = 4;
              # arithmetic-error, division-by-zero, floating-point-overflow, floating-point-underflow
              #   --> erg�nze :operation :operands ??
              # cell-error, uncound-variable, undefined-function
              #   --> erg�nze :name
              if (eq(type,S(simple_cell_error))
                  || eq(type,S(simple_unbound_variable))
                  || eq(type,S(simple_undefined_function))
                 )
                { pushSTACK(S(Kname)); pushSTACK(BEFORE(stackptr)); # :name ...
                  argcount += 2;
                }
              # type-error, keyword-error --> erg�nze :datum, :expected-type
              if (eq(type,S(simple_type_error))
                  || eq(type,S(simple_keyword_error))
                 )
                { pushSTACK(S(Kexpected_type)); pushSTACK(BEFORE(stackptr)); # :expected-type ...
                  pushSTACK(S(Kdatum)); pushSTACK(BEFORE(stackptr)); # :datum ...
                  argcount += 4;
                }
              # package-error --> erg�nze :package
              if (eq(type,S(simple_package_error)))
                { pushSTACK(S(Kpackage)); pushSTACK(BEFORE(stackptr)); # :package ...
                  argcount += 2;
                }
              # print-not-readable --> erg�nze :object
              if (eq(type,S(simple_print_not_readable)))
                { pushSTACK(S(Kobject)); pushSTACK(BEFORE(stackptr)); # :object
                  argcount += 2;
                }
              # stream-error, end-of-file --> erg�nze :stream
              if (eq(type,S(simple_stream_error))
                  || eq(type,S(simple_end_of_file))
                 )
                { pushSTACK(S(Kstream)); pushSTACK(BEFORE(stackptr)); # :stream ...
                  argcount += 2;
                }
              # file-error --> erg�nze :pathname
              if (eq(type,S(simple_file_error)))
                { pushSTACK(S(Kpathname)); pushSTACK(BEFORE(stackptr)); # :pathname ...
                  argcount += 2;
                }
              funcall(S(coerce_to_condition),argcount); # (SYS::COERCE-TO-CONDITION ...)
              # set_args_end_pointer(stackptr); # wozu? macht das Debuggen nur schwieriger!
              pushSTACK(value1); # condition retten
              pushSTACK(value1); funcall(L(clcs_signal),1); # (SIGNAL condition)
              dynamic_bind(S(prin_stream),unbound); # SYS::*PRIN-STREAM* an #<UNBOUND> binden
              pushSTACK(STACK_(0+3)); # condition
              funcall(L(invoke_debugger),1); # (INVOKE-DEBUGGER condition)
            }}
        }}
      NOTREACHED
    }

# Fehlermeldung mit Errorstring. Kehrt nicht zur�ck.
# fehler(errortype,errorstring);
# > errortype: Condition-Typ
# > errorstring: Konstanter ASCIZ-String.
#   Bei jeder Tilde wird ein LISP-Objekt vom STACK genommen und statt der
#   Tilde ausgegeben.
# > auf dem STACK: Initialisierungswerte f�r die Condition, je nach errortype
  nonreturning_function(global, fehler, (conditiontype errortype, const char * errorstring));
  global void fehler(errortype,errorstring)
    var conditiontype errortype;
    var const char * errorstring;
    { begin_error(); # Fehlermeldung anfangen
      if (!nullp(STACK_3)) # *ERROR-HANDLER* = NIL, SYS::*USE-CLCS* /= NIL ?
        { # Error-Typ-Symbol zu errortype ausw�hlen:
          var object sym = S(simple_condition); # erster Error-Typ
          sym = objectplus(sym,
                           (soint)(sizeof(*TheSymbol(sym))<<(oint_addr_shift-addr_shift))
                           * (uintL)errortype
                          );
          STACK_3 = sym;
        }
      end_error(write_errorstring(errorstring)); # Fehlermeldung ausgeben, beenden
    }

#undef OS_error

#ifdef AMIGAOS
#include "erramiga.c"
#endif

#ifdef DJUNIX
#include "errdjgpp.c"
#endif

#if defined(UNIX) || defined(EMUNIX) || defined(WATCOM) || defined(RISCOS)
#include "errunix.c"
#endif # UNIX || EMUNIX || WATCOM || RISCOS

#ifdef WIN32_NATIVE
#include "errwin32.c"
#endif

LISPFUN(error,1,0,rest,nokey,0,NIL)
# (ERROR errorstring {expr})
# Kehrt nicht zur�ck.
# (defun error (errorstring &rest args)
#   (if (or *error-handler* (not *use-clcs*))
#     (progn
#       (if *error-handler*
#         (apply *error-handler* nil errorstring args)
#         (progn
#           (terpri *error-output*)
#           (write-string "*** - " *error-output*)
#           (apply #'format *error-output* errorstring args)
#       ) )
#       (funcall *break-driver* nil)
#     )
#     (let ((condition (coerce-to-condition errorstring args 'error 'simple-error)))
#       (signal condition)
#       (invoke-debugger condition)
#     )
# ) )
  { if (!nullp(Symbol_value(S(error_handler))) || nullp(Symbol_value(S(use_clcs))))
      { begin_error(); # Fehlermeldung anfangen
        rest_args_pointer skipSTACKop 1; # Pointer �ber die Argumente
        {var object fun;
         var object arg1;
         if (nullp(STACK_1))
           { fun = S(format); arg1 = STACK_0; } # (FORMAT *error-output* ...)
           else
           { fun = STACK_1; arg1 = NIL; } # (FUNCALL *error-handler* NIL ...)
         skipSTACK(4);
         # Errormeldung ausgeben:
         #   (FORMAT *ERROR-OUTPUT* errorstring {expr})
         # bzw. ({handler} nil errorstring {expr})
         pushSTACK(arg1);
         { var object* ptr = rest_args_pointer;
           var uintC count;
           dotimespC(count,1+argcount, { pushSTACK(NEXT(ptr)); } );
         }
         funcall(fun,2+argcount); # fun (= FORMAT bzw. handler) aufrufen
        }
        # Fehlermeldung beenden, vgl. end_error():
        dynamic_unbind(); # Keine Fehlermeldungs-Ausgabe mehr aktiv
        set_args_end_pointer(rest_args_pointer); # STACK aufr�umen
        break_driver(NIL); # Break-Driver aufrufen (kehrt nicht zur�ck)
      }
      else
      { {var object arguments = listof(argcount); pushSTACK(arguments); }
        pushSTACK(S(error));
        pushSTACK(S(simple_error));
        funcall(S(coerce_to_condition),4); # (SYS::COERCE-TO-CONDITION ...)
        pushSTACK(value1); # condition retten
        pushSTACK(value1); funcall(L(clcs_signal),1); # (SIGNAL condition)
        dynamic_bind(S(prin_stream),unbound); # SYS::*PRIN-STREAM* an #<UNBOUND> binden
        pushSTACK(STACK_(0+3)); # condition
        funcall(L(invoke_debugger),1); # (INVOKE-DEBUGGER condition)
      }
    NOTREACHED
  }

LISPFUNN(defclcs,1)
# (SYSTEM::%DEFCLCS error-types)
# setzt die f�r ERROR-OF-TYPE ben�tigten Daten.
  { O(error_types) = popSTACK();
    value1 = NIL; mv_count=0;
  }

# Konvertiert einen Condition-Typ zur entsprechenden Simple-Condition.
# convert_simple_condition(type)
  local object convert_simple_condition (object type);
  local object convert_simple_condition(type)
    var object type;
    { # Vektor O(error_types) wie eine Aliste durchlaufen:
      var object v = O(error_types);
      var object* ptr = &TheSvector(v)->data[0];
      var uintL count;
      dotimesL(count,Svector_length(v),
               { if (eq(type,Car(*ptr))) { return Cdr(*ptr); }
                 ptr++;
               });
      return type; # nicht gefunden -> Typ unver�ndert lassen
    }

LISPFUN(error_of_type,2,0,rest,nokey,0,NIL)
# (SYSTEM::ERROR-OF-TYPE type {keyword value}* errorstring {expr}*)
# Kehrt nicht zur�ck.
# (defun error-of-type (type &rest arguments)
#   ; Keyword-Argumente von den anderen Argumenten abspalten:
#   (let ((keyword-arguments '()))
#     (loop
#       (unless (and (consp arguments) (keywordp (car arguments))) (return))
#       (push (pop arguments) keyword-arguments)
#       (push (pop arguments) keyword-arguments)
#     )
#     (setq keyword-arguments (nreverse keyword-arguments))
#     (let ((errorstring (first arguments))
#           (args (rest arguments)))
#       ; Los geht's!
#       (if (or *error-handler* (not *use-clcs*))
#         (progn
#           (if *error-handler*
#             (apply *error-handler* nil errorstring args)
#             (progn
#               (terpri *error-output*)
#               (write-string "*** - " *error-output*)
#               (apply #'format *error-output* errorstring args)
#           ) )
#           (funcall *break-driver* nil)
#         )
#         (let ((condition
#                 (apply #'coerce-to-condition errorstring args
#                        'error (convert-simple-condition type) keyword-arguments
#              )) )
#           (signal condition)
#           (invoke-debugger condition)
#         )
# ) ) ) )
  { var uintC keyword_argcount = 0;
    rest_args_pointer skipSTACKop 1; # Pointer �ber die Argumente hinter type
    while (argcount>=2)
      { var object next_arg = Next(rest_args_pointer); # n�chstes Argument
        if (!(symbolp(next_arg) && keywordp(next_arg))) break; # Keyword?
        rest_args_pointer skipSTACKop -2; argcount -= 2; keyword_argcount += 2;
      }
    # N�chstes Argument hoffentlich ein String.
    if (!nullp(Symbol_value(S(error_handler))) || nullp(Symbol_value(S(use_clcs))))
      { # Der Typ und die Keyword-Argumente werden ignoriert.
        begin_error(); # Fehlermeldung anfangen
        {var object fun;
         var object arg1;
         if (nullp(STACK_1))
           { fun = S(format); arg1 = STACK_0; } # (FORMAT *error-output* ...)
           else
           { fun = STACK_1; arg1 = NIL; } # (FUNCALL *error-handler* NIL ...)
         skipSTACK(4);
         # Errormeldung ausgeben:
         #   (FORMAT *ERROR-OUTPUT* errorstring {expr})
         # bzw. ({handler} nil errorstring {expr})
         pushSTACK(arg1);
         { var object* ptr = rest_args_pointer;
           var uintC count;
           dotimespC(count,1+argcount, { pushSTACK(NEXT(ptr)); } );
         }
         funcall(fun,2+argcount); # fun (= FORMAT bzw. handler) aufrufen
        }
        # Fehlermeldung beenden, vgl. end_error():
        dynamic_unbind(); # Keine Fehlermeldungs-Ausgabe mehr aktiv
        set_args_end_pointer(rest_args_pointer); # STACK aufr�umen
        break_driver(NIL); # Break-Driver aufrufen (kehrt nicht zur�ck)
      }
      else
      { var object arguments = listof(argcount);
        # Stackaufbau: type, {keyword, value}*, errorstring.
        # Ein wenig im Stack umordnen:
        var object errorstring = STACK_0;
        pushSTACK(NIL); pushSTACK(NIL);
        { var object* ptr2 = args_end_pointer;
          var object* ptr1 = ptr2 STACKop 3;
          var uintC count;
          dotimesC(count,keyword_argcount, { BEFORE(ptr2) = BEFORE(ptr1); } );
          BEFORE(ptr2) = convert_simple_condition(BEFORE(ptr1));
          BEFORE(ptr2) = S(error);
          BEFORE(ptr2) = arguments;
          BEFORE(ptr2) = errorstring;
        }
        # Stackaufbau: errorstring, args, ERROR, type, {keyword, value}*.
        funcall(S(coerce_to_condition),4+keyword_argcount); # (SYS::COERCE-TO-CONDITION ...)
        pushSTACK(value1); # condition retten
        pushSTACK(value1); funcall(L(clcs_signal),1); # (SIGNAL condition)
        dynamic_bind(S(prin_stream),unbound); # SYS::*PRIN-STREAM* an #<UNBOUND> binden
        pushSTACK(STACK_(0+3)); # condition
        funcall(L(invoke_debugger),1); # (INVOKE-DEBUGGER condition)
      }
    NOTREACHED
  }

LISPFUNN(invoke_debugger,1)
# (INVOKE-DEBUGGER condition), CLtL2 S. 915
# Kehrt nicht zur�ck.
# (defun invoke-debugger (condition)
#   (when *debugger-hook*
#     (let ((debugger-hook *debugger-hook*)
#           (*debugger-hook* nil))
#       (funcall debugger-hook condition debugger-hook)
#   ) )
#   (funcall *break-driver* nil condition t)
# )
  { var object hook = Symbol_value(S(debugger_hook));
    if (!nullp(hook))
      { var object condition = STACK_0;
        dynamic_bind(S(debugger_hook),NIL); # *DEBUGGER-HOOK* an NIL binden
        pushSTACK(condition); pushSTACK(hook); funcall(hook,2); # Debugger-Hook aufrufen
        dynamic_unbind();
      }
    # *BREAK-DRIVER* kann hier als /= NIL angenommen werden.
    pushSTACK(NIL); pushSTACK(STACK_(0+1)); pushSTACK(T);
    funcall(Symbol_value(S(break_driver)),3); # Break-Driver aufrufen
    reset(); # kehrt wider Erwarten zur�ck -> zur n�chsten Schleife zur�ck
    NOTREACHED
  }

# UP: F�hrt eine Break-Schleife wegen Tastaturunterbrechung aus.
# > STACK_0 : aufrufende Funktion
# ver�ndert STACK, kann GC ausl�sen
  global void tast_break (void);
  global void tast_break()
    {
      #ifdef PENDING_INTERRUPTS
        interrupt_pending = FALSE; # Ctrl-C-Wartezeit ist gleich beendet
        #ifndef WIN32_NATIVE
          begin_system_call();
          #ifdef HAVE_UALARM
            ualarm(0,0); # SIGALRM-Timer abbrechen
          #else
            alarm(0); # SIGALRM-Timer abbrechen
          #endif
          end_system_call();
        #endif
      #endif
      # Simuliere begin_error(), 7 Elemente auf den STACK:
      pushSTACK(NIL); pushSTACK(NIL); pushSTACK(NIL);
      pushSTACK(NIL); pushSTACK(NIL); pushSTACK(NIL);
      pushSTACK(var_stream(S(debug_io),strmflags_wr_ch_B)); # Stream *DEBUG-IO*
      terpri(&STACK_0); # neue Zeile
      write_sstring(&STACK_0,O(error_string1)); # "*** - " ausgeben
      # String ausgeben, Aufrufernamen verbrauchen, STACK aufr�umen:
      set_args_end_pointer(
        write_errorstring(DEUTSCH ? "~: Tastatur-Interrupt" :
                          ENGLISH ? "~: User break" :
                          FRANCAIS ? "~ : Interruption clavier" :
                          "~"
                         ));
      break_driver(T); # Break-Driver aufrufen
    }

LISPFUN(clcs_signal,1,0,rest,nokey,0,NIL)
# (SIGNAL datum {arg}*), CLtL2 S. 888
# (defun signal (datum &rest arguments)
#   (let ((condition
#           (coerce-to-condition datum arguments 'signal
#                                'simple-condition ; CLtL2 p. 918 specifies this
#        )) )
#     (when (typep condition *break-on-signals*)
#       ; Enter the debugger prior to signalling the condition
#       (restart-case (invoke-debugger condition)
#         (continue ())
#     ) )
#     (invoke-handlers condition)
#     nil
# ) )
  { {var object arguments = listof(argcount); pushSTACK(arguments); }
    pushSTACK(S(clcs_signal));
    pushSTACK(S(simple_condition));
    funcall(S(coerce_to_condition),4); # (SYS::COERCE-TO-CONDITION ...)
    pushSTACK(value1); # condition retten
    pushSTACK(value1); pushSTACK(Symbol_value(S(break_on_signals)));
    funcall(S(safe_typep),2); # (SYS::SAFE-TYPEP condition *BREAK-ON-SIGNALS*)
    if (!nullp(value1))
      # Break-Driver aufrufen: (funcall *break-driver* t condition t)
      { # *BREAK-DRIVER* kann hier als /= NIL angenommen werden.
        pushSTACK(T); pushSTACK(STACK_(0+1)); pushSTACK(T);
        funcall(Symbol_value(S(break_driver)),3);
      }
   {var object condition = popSTACK(); # condition zur�ck
    invoke_handlers(condition); # Handler aufrufen
    value1 = NIL; mv_count=1; # Wert NIL
  }}

# Fehlermeldung, wenn ein Objekt keine Liste ist.
# fehler_list(obj);
# > obj: Nicht-Liste
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_list, (object obj));
  global void fehler_list(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(S(list)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist keine Liste." :
             ENGLISH ? "~: ~ is not a list" :
             FRANCAIS ? "~ : ~ n'est pas une liste." :
             ""
            );
    }

# Fehlermeldung, wenn ein Objekt keine echte Liste ist.
# fehler_proper_list(obj);
# > obj: Ende der Liste, Nicht-Liste
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_proper_list, (object obj));
  global void fehler_proper_list(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(S(list)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: Eine echte Liste darf nicht mit ~ aufh�ren." :
             ENGLISH ? "~: A true list must not end with ~" :
             FRANCAIS ? "~ : Une vraie liste ne peut pas se terminer en ~." :
             ""
            );
    }

# Fehlermeldung, wenn ein Objekt kein Symbol ist.
# fehler_kein_symbol(caller,obj);
# > caller: Aufrufer (ein Symbol)
# > obj: Nicht-Symbol
  nonreturning_function(global, fehler_kein_symbol, (object caller, object obj));
  global void fehler_kein_symbol(caller,obj)
    var object caller;
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(S(symbol)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj);
      pushSTACK(caller);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist kein Symbol." :
             ENGLISH ? "~: ~ is not a symbol" :
             FRANCAIS ? "~ : ~ n'est pas un symbole." :
             ""
            );
    }

# Fehlermeldung, wenn ein Objekt kein Symbol ist.
# fehler_symbol(obj);
# > subr_self: Aufrufer (ein SUBR oder FSUBR)
# > obj: Nicht-Symbol
  nonreturning_function(global, fehler_symbol, (object obj));
  global void fehler_symbol(obj)
    var object obj;
    { var object aufrufer = subr_self;
      aufrufer = (subrp(aufrufer) ? TheSubr(aufrufer)->name : TheFsubr(aufrufer)->name);
      fehler_kein_symbol(aufrufer,obj);
    }

# Fehlermeldung, wenn ein Objekt kein Simple-Vector ist.
# fehler_kein_svector(caller,obj);
# > caller: Aufrufer (ein Symbol)
# > obj: Nicht-Svector
  nonreturning_function(global, fehler_kein_svector, (object caller, object obj));
  global void fehler_kein_svector(caller,obj)
    var object caller;
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(S(simple_vector)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj);
      pushSTACK(caller);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist kein Simple-Vector." :
             ENGLISH ? "~: ~ is not a simple-vector" :
             FRANCAIS ? "~: ~ n'est pas de type SIMPLE-VECTOR." :
             ""
            );
    }

# Fehlermeldung, wenn ein Objekt kein Vektor ist.
# fehler_vector(obj);
# > subr_self: Aufrufer (ein SUBR)
# > obj: Nicht-Vektor
  nonreturning_function(global, fehler_vector, (object obj));
  global void fehler_vector(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(S(vector)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist kein Vektor." :
             ENGLISH ? "~: ~ is not a vector" :
             FRANCAIS ? "~: ~ n'est pas un vecteur." :
             ""
            );
    }

# Fehlermeldung, falls ein Argument kein Fixnum >=0 ist:
# fehler_posfixnum(obj);
# > obj: Das fehlerhafte Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_posfixnum, (object obj));
  global void fehler_posfixnum(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(O(type_posfixnum)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: Argument mu� ein Fixnum >=0 sein, nicht ~" :
             ENGLISH ? "~: argument ~ should be a nonnegative fixnum" :
             FRANCAIS ? "~ : L'argument doit �tre de type FIXNUM positif ou z�ro et non pas ~." :
             ""
            );
    }

# Fehlermeldung, falls ein Argument kein Character ist:
# fehler_char(obj);
# > obj: Das fehlerhafte Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_char, (object obj));
  global void fehler_char(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(S(character)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: Argument ~ ist kein Character." :
             ENGLISH ? "~: argument ~ is not a character" :
             FRANCAIS ? "~: L'argument ~ n'est pas un caract�re." :
             ""
            );
    }

# Fehler, wenn Argument kein String-Char ist.
# fehler_string_char(obj);
# > obj: fehlerhaftes Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_string_char, (object obj));
  global void fehler_string_char(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(S(string_char)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist kein String-Char." :
             ENGLISH ? "~: ~ is not a string-char" :
             FRANCAIS ? "~ : ~ n'est pas de type STRING-CHAR." :
             ""
            );
    }

# Fehlermeldung, falls ein Argument kein String ist:
# > obj: Das fehlerhafte Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_string, (object obj));
  global void fehler_string(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(S(string)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: Argument ~ ist kein String." :
             ENGLISH ? "~: argument ~ is not a string" :
             FRANCAIS ? "~: L'argument ~ n'est pas une cha�ne." :
             ""
            );
    }

# Fehlermeldung, falls ein Argument kein Simple-String ist:
# > obj: Das fehlerhafte Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_sstring, (object obj));
  global void fehler_sstring(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(S(simple_string)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: Argument ~ ist kein Simple-String." :
             ENGLISH ? "~: argument ~ is not a simple string" :
             FRANCAIS ? "~: L'argument ~ n'est pas de type SIMPLE-STRING." :
             ""
            );
    }

# Fehlermeldung, wenn ein Argument kein Stream ist:
# fehler_stream(obj);
# > obj: Das fehlerhafte Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_stream, (object obj));
  global void fehler_stream(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(S(stream)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: Argument mu� ein Stream sein, nicht ~" :
             ENGLISH ? "~: argument ~ should be a stream" :
             FRANCAIS ? "~ : L'argument doit �tre de type STREAM et non pas ~." :
             ""
            );
    }

# Fehlermeldung, wenn ein Argument kein Stream vom geforderten Stream-Typ ist:
# fehler_streamtype(obj,type);
# > obj: Das fehlerhafte Argument
# > type: geforderten Stream-Typ
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_streamtype, (object obj, object type));
  global void fehler_streamtype(obj,type)
    var object obj;
    var object type;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(type); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(type); pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: Argument ~ sollte ein Stream vom Typ ~ sein." :
             ENGLISH ? "~: argument ~ should be a stream of type ~" :
             FRANCAIS ? "~ : L'argument ~ devrait �tre de type ~." :
             ""
            );
    }

# Fehlermeldung, wenn ein Argument ein Lambda-Ausdruck statt einer Funktion ist:
# fehler_lambda_expression(obj);
# obj: Das fehlerhafte Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_lambda_expression, (object obj));
  global void fehler_lambda_expression(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(S(function)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: Argument ~ ist keine Funktion." NLstring "Um eine Funktion im aktuellen Environment zu bekommen, (FUNCTION ...) schreiben." NLstring "Um eine Funktion im globalen Environment zu bekommen, (COERCE '... 'FUNCTION) schreiben." :
             ENGLISH ? "~: argument ~ is not a function." NLstring "To get a function in the current environment, write (FUNCTION ...)." NLstring "To get a function in the global environment, write (COERCE '... 'FUNCTION)." :
             FRANCAIS ? "~ : L'argument ~ n'est pas une fonction." NLstring "Pour obtenir une fonction dans l'environnement courant, �crire (FUNCTION ...)." NLstring "Pour obtenir une fonction dans l'environnement global, �crire (COERCE '... 'FUNCTION)." :
             ""
            );
    }

#ifdef HAVE_FFI

# Fehler, wenn Argument kein Integer vom Typ `uint8' ist.
# fehler_uint8(obj);
# > obj: fehlerhaftes Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_uint8, (object obj));
  global void fehler_uint8(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(O(type_uint8)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist keine 8-bit-Zahl." :
             ENGLISH ? "~: ~ is not an 8-bit number" :
             FRANCAIS ? "~ : ~ n'est pas un nombre � 8 bits." :
             ""
            );
    }

# Fehler, wenn Argument kein Integer vom Typ `sint8' ist.
# fehler_sint8(obj);
# > obj: fehlerhaftes Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_sint8, (object obj));
  global void fehler_sint8(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(O(type_sint8)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist keine 8-bit-Zahl." :
             ENGLISH ? "~: ~ is not an 8-bit number" :
             FRANCAIS ? "~ : ~ n'est pas un nombre � 8 bits." :
             ""
            );
    }

# Fehler, wenn Argument kein Integer vom Typ `uint16' ist.
# fehler_uint16(obj);
# > obj: fehlerhaftes Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_uint16, (object obj));
  global void fehler_uint16(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(O(type_uint16)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist keine 16-bit-Zahl." :
             ENGLISH ? "~: ~ is not a 16-bit number" :
             FRANCAIS ? "~ : ~ n'est pas un nombre � 16 bits." :
             ""
            );
    }

# Fehler, wenn Argument kein Integer vom Typ `sint16' ist.
# fehler_sint16(obj);
# > obj: fehlerhaftes Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_sint16, (object obj));
  global void fehler_sint16(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(O(type_sint16)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist keine 16-bit-Zahl." :
             ENGLISH ? "~: ~ is not a 16-bit number" :
             FRANCAIS ? "~ : ~ n'est pas un nombre � 16 bits." :
             ""
            );
    }

# Fehler, wenn Argument kein Integer vom Typ `uint32' ist.
# fehler_uint32(obj);
# > obj: fehlerhaftes Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_uint32, (object obj));
  global void fehler_uint32(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(O(type_uint32)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist keine 32-bit-Zahl." :
             ENGLISH ? "~: ~ is not an 32-bit number" :
             FRANCAIS ? "~ : ~ n'est pas un nombre � 32 bits." :
             ""
            );
    }

# Fehler, wenn Argument kein Integer vom Typ `sint32' ist.
# fehler_sint32(obj);
# > obj: fehlerhaftes Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_sint32, (object obj));
  global void fehler_sint32(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(O(type_sint32)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist keine 32-bit-Zahl." :
             ENGLISH ? "~: ~ is not an 32-bit number" :
             FRANCAIS ? "~ : ~ n'est pas un nombre � 32 bits." :
             ""
            );
    }

# Fehler, wenn Argument kein Integer vom Typ `uint64' ist.
# fehler_uint64(obj);
# > obj: fehlerhaftes Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_uint64, (object obj));
  global void fehler_uint64(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(O(type_uint64)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist keine 64-bit-Zahl." :
             ENGLISH ? "~: ~ is not an 64-bit number" :
             FRANCAIS ? "~ : ~ n'est pas un nombre � 64 bits." :
             ""
            );
    }

# Fehler, wenn Argument kein Integer vom Typ `sint64' ist.
# fehler_sint64(obj);
# > obj: fehlerhaftes Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_sint64, (object obj));
  global void fehler_sint64(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(O(type_sint64)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist keine 64-bit-Zahl." :
             ENGLISH ? "~: ~ is not an 64-bit number" :
             FRANCAIS ? "~ : ~ n'est pas un nombre � 64 bits." :
             ""
            );
    }

# Fehler, wenn Argument kein Integer vom Typ `uint' ist.
# fehler_uint(obj);
# > obj: fehlerhaftes Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_uint, (object obj));
  global void fehler_uint(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      #if (int_bitsize==16)
      pushSTACK(O(type_uint16)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      #else # (int_bitsize==32)
      pushSTACK(O(type_uint32)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      #endif
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist keine `unsigned int'-Zahl." :
             ENGLISH ? "~: ~ is not an `unsigned int' number" :
             FRANCAIS ? "~ : ~ n'est pas un nombre �unsigned int�." :
             ""
            );
    }

# Fehler, wenn Argument kein Integer vom Typ `sint' ist.
# fehler_sint(obj);
# > obj: fehlerhaftes Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_sint, (object obj));
  global void fehler_sint(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      #if (int_bitsize==16)
      pushSTACK(O(type_sint16)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      #else # (int_bitsize==32)
      pushSTACK(O(type_sint32)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      #endif
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist keine `int'-Zahl." :
             ENGLISH ? "~: ~ is not an `int' number" :
             FRANCAIS ? "~ : ~ n'est pas un nombre �int�." :
             ""
            );
    }

# Fehler, wenn Argument kein Integer vom Typ `ulong' ist.
# fehler_ulong(obj);
# > obj: fehlerhaftes Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_ulong, (object obj));
  global void fehler_ulong(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      #if (long_bitsize==32)
      pushSTACK(O(type_uint32)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      #else # (long_bitsize==64)
      pushSTACK(O(type_uint64)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      #endif
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist keine `unsigned long'-Zahl." :
             ENGLISH ? "~: ~ is not a `unsigned long' number" :
             FRANCAIS ? "~ : ~ n'est pas un nombre �unsigned long�." :
             ""
            );
    }

# Fehler, wenn Argument kein Integer vom Typ `slong' ist.
# fehler_slong(obj);
# > obj: fehlerhaftes Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_slong, (object obj));
  global void fehler_slong(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      #if (long_bitsize==32)
      pushSTACK(O(type_sint32)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      #else # (long_bitsize==64)
      pushSTACK(O(type_sint64)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      #endif
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist keine `long'-Zahl." :
             ENGLISH ? "~: ~ is not a `long' number" :
             FRANCAIS ? "~ : ~ n'est pas un nombre �long�." :
             ""
            );
    }

# Fehler, wenn Argument kein Single-Float ist.
# fehler_ffloat(obj);
# > obj: fehlerhaftes Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_ffloat, (object obj));
  global void fehler_ffloat(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(S(single_float)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist kein Single-Float." :
             ENGLISH ? "~: ~ is not a single-float" :
             FRANCAIS ? "~ : ~ n'est pas de type SINGLE-FLOAT." :
             ""
            );
    }

# Fehler, wenn Argument kein Double-Float ist.
# fehler_dfloat(obj);
# > obj: fehlerhaftes Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(global, fehler_dfloat, (object obj));
  global void fehler_dfloat(obj)
    var object obj;
    { pushSTACK(obj); # Wert f�r Slot DATUM von TYPE-ERROR
      pushSTACK(S(double_float)); # Wert f�r Slot EXPECTED-TYPE von TYPE-ERROR
      pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,
             DEUTSCH ? "~: ~ ist kein Double-Float." :
             ENGLISH ? "~: ~ is not a double-float" :
             FRANCAIS ? "~ : ~ n'est pas de type DOUBLE-FLOAT." :
             ""
            );
    }

#endif

