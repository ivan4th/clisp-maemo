  # Behandlung von DJUNIX-(DOS-)Fehlern
  # OS_error();
  # > int errno: Fehlercode
    nonreturning_function(global, OS_error, (void));
    nonreturning_function(global, OS_file_error, (object pathname));
    local void OS_error_internal (uintC errcode);
    local void OS_error_internal(errcode)
      var uintC errcode;
      { # Meldungbeginn ausgeben:
        write_errorstring(DEUTSCH ? "DJDOS-Fehler " :
                          ENGLISH ? "DJDOS error " :
                          FRANCAIS ? "Erreur DJDOS " :
                          ""
                         );
        # Fehlernummer ausgeben:
        write_errorobject(fixnum(errcode));
        # nach M�glichkeit noch ausf�hrlicher:
        if (errcode < 36)
          {# Zu Fehlernummern <36 ist ein Text da.
           #ifdef LANGUAGE_STATIC
             #define lang3(english,deutsch,francais)  ENGLISH ? english : DEUTSCH ? deutsch : FRANCAIS ? francais : ""
             #define lang1(string)  string
             #define langcount  1
             #define language  0
             #define translate(string)  string
           #else
             #ifndef GNU_GETTEXT
               #define lang3(english,deutsch,francais)  english, deutsch, francais
               #define lang1(string)  string, string, string
               #define langcount  3
               #define translate(string)  string
             #else # GNU_GETTEXT
               #define lang3(english,deutsch,francais)  english
               #define lang1(string)  string
               #define langcount  1
               #define language  0
               #define translate(string)  clgettext(string)
             #endif
           #endif
           local const char* errormsg_table[36*(1+langcount)] = {
             /*  0 */ "", lang1(""),
             /*  1 */ "ENOSYS",
                      lang3( /* ENGLISH */ "Function not implemented" ,
                             /* DEUTSCH */ "Funktion ist nicht implementiert" ,
                             /* FRANCAIS */ "Fonction non impl�ment�e"),
             /*  2 */ "ENOENT",
                      lang3( /* ENGLISH */ "No such file or directory" ,
                             /* DEUTSCH */ "File oder Directory existiert nicht" ,
                             /* FRANCAIS */ "Fichier ou r�pertoire non existant"),
             /*  3 */ "ENOTDIR",
                      lang3( /* ENGLISH */ "Not a directory" ,
                             /* DEUTSCH */ "Das ist kein Directory" ,
                             /* FRANCAIS */ "N'est pas un r�pertoire"),
             /*  4 */ "EMFILE",
                      lang3( /* ENGLISH */ "Too many open files" ,
                             /* DEUTSCH */ "Zu viele offene Files" ,
                             /* FRANCAIS */ "Trop de fichiers ouverts"),
             /*  5 */ "EACCES",
                      lang3( /* ENGLISH */ "Permission denied" ,
                             /* DEUTSCH */ "Keine Berechtigung" ,
                             /* FRANCAIS */ "Permission refus�e"),
             /*  6 */ "EBADF",
                      lang3( /* ENGLISH */ "Bad file number" ,
                             /* DEUTSCH */ "File-Descriptor wurde nicht f�r diese Operation ge�ffnet" ,
                             /* FRANCAIS */ "Descripteur de fichier non allou�"),
             /*  7 */ "EARENA",
                      lang3( /* ENGLISH */ "Memory control blocks destroyed" ,
                             /* DEUTSCH */ "Speicherverwaltung ist durcheinander" ,
                             /* FRANCAIS */ "gestionnaire de m�moire perdu"),
             /*  8 */ "ENOMEM",
                      lang3( /* ENGLISH */ "Not enough memory" ,
                             /* DEUTSCH */ "Hauptspeicher oder Swapspace reicht nicht" ,
                             /* FRANCAIS */ "Pas assez de m�moire"),
             /*  9 */ "ESEGV",
                      lang3( /* ENGLISH */ "Invalid memory address" ,
                             /* DEUTSCH */ "Ung�ltige Speicher-Adresse" ,
                             /* FRANCAIS */ "adresse m�moire illicite"),
             /* 10 */ "EBADENV",
                      lang3( /* ENGLISH */ "Invalid environment" ,
                             /* DEUTSCH */ "Ung�ltiges Environment" ,
                             /* FRANCAIS */ "environnement incorrect"),
             /* 11 */ "", lang1(""),
             /* 12 */ "EACCODE",
                      lang3( /* ENGLISH */ "Invalid access code" ,
                             /* DEUTSCH */ "Ung�ltiger Zugriffsmodus" ,
                             /* FRANCAIS */ "mode d'acc�s ill�gal"),
             /* 13...14 */ "", lang1(""), "", lang1(""),
             /* 15 */ "ENODEV",
                      lang3( /* ENGLISH */ "No such device" ,
                             /* DEUTSCH */ "Ger�t nicht da oder unpassend" ,
                             /* FRANCAIS */ "P�riph�rique inexistant"),
             /* 16 */ "ECURDIR",
                      lang3( /* ENGLISH */ "Attempt to remove the current directory" ,
                             /* DEUTSCH */ "Das aktuelle Verzeichnis kann nicht entfernt werden" ,
                             /* FRANCAIS */ "Le r�pertoire courant ne peut pas �tre effac�"),
             /* 17 */ "ENOTSAME",
                      lang3( /* ENGLISH */ "Can't move to other than the same device" ,
                             /* DEUTSCH */ "Verschieben geht nicht �ber Laufwerksgrenzen hinweg" ,
                             /* FRANCAIS */ "ne peux pas d�placer au-del� de l'unit�"),
             /* 18 */ "ENOMORE",
                      lang3( /* ENGLISH */ "No more files" ,
                             /* DEUTSCH */ "Keine weiteren Dateien" ,
                             /* FRANCAIS */ "Pas plus de fichiers"),
             /* 19 */ "EINVAL",
                      lang3( /* ENGLISH */ "Invalid argument" ,
                             /* DEUTSCH */ "Ung�ltiger Parameter" ,
                             /* FRANCAIS */ "Param�tre illicite"),
             /* 20 */ "E2BIG",
                      lang3( /* ENGLISH */ "Arg list too long" ,
                             /* DEUTSCH */ "Zu lange Argumentliste" ,
                             /* FRANCAIS */ "Liste d'arguments trop longue"),
             /* 21 */ "ENOEXEC",
                      lang3( /* ENGLISH */ "Exec format error" ,
                             /* DEUTSCH */ "Kein ausf�hrbares Programm" ,
                             /* FRANCAIS */ "Programme non ex�cutable"),
             /* 22 */ "EXDEV",
                      lang3( /* ENGLISH */ "Cross-device link" ,
                             /* DEUTSCH */ "Links k�nnen nur aufs selbe Ger�t gehen" ,
                             /* FRANCAIS */ "Lien entre p�riph�riques diff�rents"),
             /* 23...27 */ "", lang1(""), "", lang1(""), "", lang1(""), "", lang1(""), "", lang1(""),
             /* 28...32 */ "", lang1(""), "", lang1(""), "", lang1(""), "", lang1(""), "", lang1(""),
             /* 33 */ "EDOM",
                      lang3( /* ENGLISH */ "Argument out of domain" ,
                             /* DEUTSCH */ "Argument zu mathematischer Funktion au�erhalb des Definitionsbereichs" ,
                             /* FRANCAIS */ "Argument math�matique en dehors du domaine de d�finition de la fonction"),
             /* 34 */ "ERANGE",
                      lang3( /* ENGLISH */ "Result too large" ,
                             /* DEUTSCH */ "Ergebnis mathematischer Funktion zu gro�" ,
                             /* FRANCAIS */ "R�sultat math�matique non repr�sentable"),
             /* 35 */ "EEXIST",
                      lang3( /* ENGLISH */ "File exists" ,
                             /* DEUTSCH */ "File existiert schon" ,
                             /* FRANCAIS */ "Le fichier existe d�j�"),
             };
           var const char* errorname = errormsg_table[errcode*(1+langcount)];
           var const char* errormsg = translate(errormsg_table[errcode*(1+langcount)+1+language]);
           if (!(errorname[0] == 0)) # bekannter Name?
             { write_errorstring(" (");
               write_errorstring(errorname);
               write_errorstring(")");
             }
           if (!(errormsg[0] == 0)) # nichtleere Meldung?
             { write_errorstring(": ");
               write_errorstring(errormsg);
             }
      }   }
    global void OS_error()
      { var uintC errcode; # positive Fehlernummer
        end_system_call(); # just in case
        begin_system_call();
        errcode = errno;
        end_system_call();
        clr_break_sem_4(); # keine DOS-Operation mehr aktiv
        begin_error(); # Fehlermeldung anfangen
        OS_error_internal(errcode);
        end_error(args_end_pointer STACKop 7); # Fehlermeldung beenden
      }
    global void OS_file_error(pathname)
      var object pathname;
      { var uintC errcode; # positive Fehlernummer
        begin_system_call();
        errcode = errno;
        end_system_call();
        clr_break_sem_4(); # keine DOS-Operation mehr aktiv
        pushSTACK(pathname); # Wert von PATHNAME f�r FILE-ERROR
        begin_error(); # Fehlermeldung anfangen
        if (!nullp(STACK_3)) # *ERROR-HANDLER* = NIL, SYS::*USE-CLCS* /= NIL ?
          { STACK_3 = S(simple_file_error); }
        OS_error_internal(errcode);
        end_error(args_end_pointer STACKop 7); # Fehlermeldung beenden
      }

  # Ausgabe eines Fehlers, direkt �bers Betriebssystem
  # errno_out(errorcode);
  # > int errorcode: Fehlercode
    global void errno_out (int errorcode);
    global void errno_out(errorcode)
      var int errorcode;
      { asciz_out(" errno = "); dez_out(errorcode); asciz_out("." NLstring); }

