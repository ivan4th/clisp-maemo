  # Behandlung von AMIGAOS-Fehlern
  # OS_error();
  # > IoErr(): Fehlercode
    nonreturning_function(global, OS_error, (void));
    global void OS_error ()
      { var uintC errcode; # Fehlernummer
        end_system_call(); # just in case
        begin_system_call();
        errcode = IoErr();
        end_system_call();
        clr_break_sem_4(); # keine AMIGAOS-Operation mehr aktiv
        begin_error(); # Fehlermeldung anfangen
        # Meldungbeginn ausgeben:
        write_errorstring(DEUTSCH ? "AmigaOS-Fehler " :
                          ENGLISH ? "Amiga OS error " :
                          FRANCAIS ? "Erreur S.E. Amiga " :
                          ""
                         );
        # Fehlernummer ausgeben:
        write_errorobject(fixnum(errcode));
        {
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
          local const char* error100_msg_table[23*(1+langcount)] = {
            /* 100 */ "", lang1(""),
            /* 101 */ "", lang1(""),
            /* 102 */ "", lang1(""),
            /* 103 */ "ERROR_NO_FREE_STORE",
                      lang3( /* ENGLISH */ "not enough memory available" ,
                             /* DEUTSCH */ "nicht gen�gend Speicher vorhanden" ,
                             /* FRANCAIS */ "Pas assez de m�moire"),
            /* 104 */ "", lang1(""),
            /* 105 */ "ERROR_TASK_TABLE_FULL",
                      lang3( /* ENGLISH */ "process table full" ,
                             /* DEUTSCH */ "keine weiteren CLI Prozesse mehr" ,
                             /* FRANCAIS */ "La table des processus est pleine"),
            /* 106 */ "", lang1(""),
            /* 107 */ "", lang1(""),
            /* 108 */ "", lang1(""),
            /* 109 */ "", lang1(""),
            /* 110 */ "", lang1(""),
            /* 111 */ "", lang1(""),
            /* 112 */ "", lang1(""),
            /* 113 */ "", lang1(""),
            /* 114 */ "ERROR_BAD_TEMPLATE",
                      lang3( /* ENGLISH */ "bad template" ,
                             /* DEUTSCH */ "ung�ltiges Muster" ,
                             /* FRANCAIS */ "mauvais sch�ma"),
            /* 115 */ "ERROR_BAD_NUMBER",
                      lang3( /* ENGLISH */ "bad number" ,
                             /* DEUTSCH */ "ung�ltige Zahl" ,
                             /* FRANCAIS */ "mauvais nombre"),
            /* 116 */ "ERROR_REQUIRED_ARG_MISSING",
                      lang3( /* ENGLISH */ "required argument missing" ,
                             /* DEUTSCH */ "ben�tigtes Schl�sselwort nicht vorhanden" ,
                             /* FRANCAIS */ "mot cl� manque"),
            /* 117 */ "ERROR_KEY_NEEDS_ARG",
                      lang3( /* ENGLISH */ "value after keyword missing" ,
                             /* DEUTSCH */ "kein Wert nach Schl�sselwort vorhanden" ,
                             /* FRANCAIS */ "mot cl� sans valeur"),
            /* 118 */ "ERROR_TOO_MANY_ARGS",
                      lang3( /* ENGLISH */ "wrong number of arguments" ,
                             /* DEUTSCH */ "falsche Anzahl Argumente" ,
                             /* FRANCAIS */ "mauvais nombre d'arguments"),
            /* 119 */ "ERROR_UNMATCHED_QUOTES",
                      lang3( /* ENGLISH */ "unmatched quotes" ,
                             /* DEUTSCH */ "ausstehende Anf�hrungszeichen" ,
                             /* FRANCAIS */ "guillemets non termin�s"),
            /* 120 */ "ERROR_LINE_TOO_LONG",
                      lang3( /* ENGLISH */ "argument line invalid or too long" ,
                             /* DEUTSCH */ "ung�ltige Zeile oder Zeile zu lang" ,
                             /* FRANCAIS */ "ligne est mauvaise ou trop longue"),
            /* 121 */ "ERROR_FILE_NOT_OBJECT",
                      lang3( /* ENGLISH */ "file is not executable" ,
                             /* DEUTSCH */ "Datei ist nicht ausf�hrbar" ,
                             /* FRANCAIS */ "fichier non ex�cutable"),
            /* 122 */ "ERROR_INVALID_RESIDENT_LIBRARY",
                      lang3( /* ENGLISH */ "invalid resident library" ,
                             /* DEUTSCH */ "ung�ltige residente Library" ,
                             /* FRANCAIS */ "Librarie r�sidente non valide"),
            };
          local const char* error200_msg_table[44*(1+langcount)] = {
            /* 200 */ "", lang1(""),
            /* 201 */ "ERROR_NO_DEFAULT_DIR",
                      lang3( "" ,
                             "" ,
                             ""),
            /* 202 */ "ERROR_OBJECT_IN_USE",
                      lang3( /* ENGLISH */ "object is in use" ,
                             /* DEUTSCH */ "Objekt wird schon benutzt" ,
                             /* FRANCAIS */ "l'objet est utilis�"),
            /* 203 */ "ERROR_OBJECT_EXISTS",
                      lang3( /* ENGLISH */ "object already exists" ,
                             /* DEUTSCH */ "Objekt existiert bereits" ,
                             /* FRANCAIS */ "l'objet existe d�j�"),
            /* 204 */ "ERROR_DIR_NOT_FOUND",
                      lang3( /* ENGLISH */ "directory not found" ,
                             /* DEUTSCH */ "Verzeichnis nicht gefunden" ,
                             /* FRANCAIS */ "r�pertoire non trouv�"),
            /* 205 */ "ERROR_OBJECT_NOT_FOUND",
                      lang3( /* ENGLISH */ "object not found" ,
                             /* DEUTSCH */ "Objekt nicht gefunden" ,
                             /* FRANCAIS */ "objet non trouv�"),
            /* 206 */ "ERROR_BAD_STREAM_NAME",
                      lang3( /* ENGLISH */ "invalid window description" ,
                             /* DEUTSCH */ "ung�ltige Fensterbeschreibung" ,
                             /* FRANCAIS */ "mauvais descripteur de fen�tre"),
            /* 207 */ "ERROR_OBJECT_TOO_LARGE",
                      lang3( /* ENGLISH */ "object too large" ,
                             /* DEUTSCH */ "Objekt zu gro�" ,
                             /* FRANCAIS */ "objet trop grand"),
            /* 208 */ "", lang1(""),
            /* 209 */ "ERROR_ACTION_NOT_KNOWN",
                      lang3( /* ENGLISH */ "packet request type unknown" ,
                             /* DEUTSCH */ "unbekannter Pakettyp" , # ??
                             /* FRANCAIS */ "Type de paquet inconnu"),
            /* 210 */ "ERROR_INVALID_COMPONENT_NAME",
                      lang3( /* ENGLISH */ "object name invalid" ,
                             /* DEUTSCH */ "ung�ltiger Objektname" ,
                             /* FRANCAIS */ "nom d'objet incorrect"),
            /* 211 */ "ERROR_INVALID_LOCK",
                      lang3( /* ENGLISH */ "invalid object lock" ,
                             /* DEUTSCH */ "ung�ltiger Objektlock" ,
                             /* FRANCAIS */ "�lock� invalide d'un objet"),
            /* 212 */ "ERROR_OBJECT_WRONG_TYPE",
                      lang3( /* ENGLISH */ "object is not of required type" ,
                             /* DEUTSCH */ "Objekt ist nicht von ben�tigten Typ" ,
                             /* FRANCAIS */ "objet de mauvais type"),
            /* 213 */ "ERROR_DISK_NOT_VALIDATED",
                      lang3( /* ENGLISH */ "disk not validated" ,
                             /* DEUTSCH */ "Datentr�ger ist nicht validiert" ,
                             /* FRANCAIS */ "volume non valid�"),
            /* 214 */ "ERROR_DISK_WRITE_PROTECTED",
                      lang3( /* ENGLISH */ "disk is write-protected" ,
                             /* DEUTSCH */ "Datentr�ger ist schreibgesch�tzt" ,
                             /* FRANCAIS */ "disquette prot�g�e contre l'�criture"),
            /* 215 */ "ERROR_RENAME_ACROSS_DEVICES",
                      lang3( /* ENGLISH */ "rename across devices attempted" ,
                             /* DEUTSCH */ "rename �ber Laufwerke versucht" ,
                             /* FRANCAIS */ "�rename� � travers des unit�s distinctes"),
            /* 216 */ "ERROR_DIRECTORY_NOT_EMPTY",
                      lang3( /* ENGLISH */ "directory not empty" ,
                             /* DEUTSCH */ "Verzeichnis ist nicht leer" ,
                             /* FRANCAIS */ "r�pertoire non vide"),
            /* 217 */ "ERROR_TOO_MANY_LEVELS",
                      lang3( /* ENGLISH */ "too many levels" ,
                             /* DEUTSCH */ "zu viele Verweise" ,
                             /* FRANCAIS */ "trop de niveaux"),
            /* 218 */ "ERROR_DEVICE_NOT_MOUNTED",
                      lang3( /* ENGLISH */ "device (or volume) is not mounted" ,
                             /* DEUTSCH */ "Datentr�ger ist in keinem Laufwerk" ,
                             /* FRANCAIS */ "l'unit� n'est dans aucun lecteur"),
            /* 219 */ "ERROR_SEEK_ERROR",
                      lang3( /* ENGLISH */ "seek failure" ,
                             /* DEUTSCH */ "seek schlug fehl" ,
                             /* FRANCAIS */ "erreur pendant un d�placement (seek)"),
            /* 220 */ "ERROR_COMMENT_TOO_BIG",
                      lang3( /* ENGLISH */ "comment is too long" ,
                             /* DEUTSCH */ "Kommentar ist zu lang" ,
                             /* FRANCAIS */ "Commentaire trop long"),
            /* 221 */ "ERROR_DISK_FULL",
                      lang3( /* ENGLISH */ "disk is full" ,
                             /* DEUTSCH */ "Datentr�ger ist voll" ,
                             /* FRANCAIS */ "support plein"),
            /* 222 */ "ERROR_DELETE_PROTECTED",
                      lang3( /* ENGLISH */ "object is protected from deletion" ,
                             /* DEUTSCH */ "Datei ist gegen L�schen gesch�tzt" ,
                             /* FRANCAIS */ "objet est prot�g� contre l'effacement"),
            /* 223 */ "ERROR_WRITE_PROTECTED",
                      lang3( /* ENGLISH */ "file is write protected" ,
                             /* DEUTSCH */ "Datei ist schreibgesch�tzt" ,
                             /* FRANCAIS */ "fichier prot�g� contre l'�criture"),
            /* 224 */ "ERROR_READ_PROTECTED",
                      lang3( /* ENGLISH */ "file is read protected" ,
                             /* DEUTSCH */ "Datei ist lesegesch�tzt" ,
                             /* FRANCAIS */ "fichier prot�g� contre la lecture"),
            /* 225 */ "ERROR_NOT_A_DOS_DISK",
                      lang3( /* ENGLISH */ "not a valid DOS disk" ,
                             /* DEUTSCH */ "kein g�ltiger DOS-Datentr�ger" ,
                             /* FRANCAIS */ "disque non DOS"),
            /* 226 */ "ERROR_NO_DISK",
                      lang3( /* ENGLISH */ "no disk in drive" ,
                             /* DEUTSCH */ "kein Datentr�ger im Laufwerk" ,
                             /* FRANCAIS */ "pas de disquette dans le lecteur"),
            /* 227 */ "", lang1(""),
            /* 228 */ "", lang1(""),
            /* 229 */ "", lang1(""),
            /* 230 */ "", lang1(""),
            /* 231 */ "", lang1(""),
            /* 232 */ "ERROR_NO_MORE_ENTRIES",
                      lang3( /* ENGLISH */ "no more entries in directory" ,
                             /* DEUTSCH */ "keine weiteren Verzeichniseintr�ge mehr" ,
                             /* FRANCAIS */ "pas plus d'entr�es dans le r�pertoire"),
            /* 233 */ "ERROR_IS_SOFT_LINK",
                      lang3( /* ENGLISH */ "object is soft link" ,
                             /* DEUTSCH */ "Objekt ist ein Softlink" ,
                             /* FRANCAIS */ "l'objet est un �soft link�"),
            /* 234 */ "ERROR_OBJECT_LINKED",
                      lang3( /* ENGLISH */ "object is linked" ,
                             /* DEUTSCH */ "Objekt ist gelinkt" ,
                             /* FRANCAIS */ "l'objet est li�"),
            /* 235 */ "ERROR_BAD_HUNK",
                      lang3( /* ENGLISH */ "bad loadfile hunk" ,
                             /* DEUTSCH */ "Datei teilweise nicht ladbar" ,
                             /* FRANCAIS */ "fichier pas enti�rement chargeable"),
            /* 236 */ "ERROR_NOT_IMPLEMENTED",
                      lang3( /* ENGLISH */ "function not implemented" ,
                             /* DEUTSCH */ "unimplementierte Funktion" ,
                             /* FRANCAIS */ "fonction non impl�ment�e"),
            /* 237 */ "", lang1(""),
            /* 238 */ "", lang1(""),
            /* 239 */ "", lang1(""),
            /* 240 */ "ERROR_RECORD_NOT_LOCKED",
                      lang3( /* ENGLISH */ "record not locked" ,
                             /* DEUTSCH */ "Datensatz nicht gesperrt" ,
                             /* FRANCAIS */ "enregistrement non verrouill�"),
            /* 241 */ "ERROR_LOCK_COLLISION",
                      lang3( /* ENGLISH */ "record lock collision" ,
                             /* DEUTSCH */ "Kollision bei Datensatzsperre" ,
                             /* FRANCAIS */ "conflit sur verrou d'enregistrement"),
            /* 242 */ "ERROR_LOCK_TIMEOUT",
                      lang3( /* ENGLISH */ "record lock timeout" ,
                             /* DEUTSCH */ "Zeit�berschreitung bei Datensatzsperre" ,
                             /* FRANCAIS */ "enregistrement verrouill�; d�lai d�pass�"),
            /* 243 */ "ERROR_UNLOCK_ERROR",
                      lang3( /* ENGLISH */ "record unlock error" ,
                             /* DEUTSCH */ "Fehler bei Datensatzfreigabe" ,
                             /* FRANCAIS */ "erreur lors du d�verrouillage de l'enregistrement"),
            };
          local const char* error300_msg_table[6*(1+langcount)] = {
            /* 300 */ "", lang1(""),
            /* 301 */ "", lang1(""),
            /* 302 */ "", lang1(""),
            /* 303 */ "ERROR_BUFFER_OVERFLOW",
                      lang3( /* ENGLISH */ "buffer overflow" ,
                             /* DEUTSCH */ "Puffer-�berlauf" ,
                             /* FRANCAIS */ "d�bordement de tampon"),
            /* 304 */ "ERROR_BREAK",
                      lang3( /* ENGLISH */ "break" ,
                             /* DEUTSCH */ "Unterbrechung" ,
                             /* FRANCAIS */ "interruption"),
            /* 305 */ "ERROR_NOT_EXECUTABLE",
                      lang3( /* ENGLISH */ "file not executable" ,
                             /* DEUTSCH */ "Datei ist nicht ausf�hrbar" ,
                             /* FRANCAIS */ "fichier non ex�cutable"),
            };
          var const char* errorname = "";
          var const char* errormsg = "";
          var uintC index;
          if (errcode == 0)
            { errorname = "";
              errormsg =
                /*  0 */ DEUTSCH ? "OK, kein Fehler" :
                         ENGLISH ? "Ok, No error" :
                         FRANCAIS ? "Ok, pas d'erreur" :
                         "";
            }
          elif ((index = errcode-100) < 23)
            { errorname = error100_msg_table[index*(1+langcount)];
              errormsg = translate(error100_msg_table[index*(1+langcount)+1+language]);
            }
          elif ((index = errcode-200) < 44)
            { errorname = error200_msg_table[index*(1+langcount)];
              errormsg = translate(error200_msg_table[index*(1+langcount)+1+language]);
            }
          elif ((index = errcode-300) < 6)
            { errorname = error300_msg_table[index*(1+langcount)];
              errormsg = translate(error300_msg_table[index*(1+langcount)+1+language]);
            }
          if (!(errorname[0] == 0)) # bekannter Name?
            { write_errorstring(" (");
              write_errorstring(errorname);
              write_errorstring(")");
            }
          if (!(errormsg[0] == 0)) # nichtleere Meldung?
            { write_errorstring(": ");
              write_errorstring(errormsg);
            }
        }
        SetIoErr(0L); # Fehlercode l�schen (f�rs n�chste Mal)
        end_error(args_end_pointer STACKop 7); # Fehlermeldung beenden
      }

  # Ausgabe eines Fehlers, direkt �bers Betriebssystem
  # errno_out(errorcode);
  # > LONG errorcode: Fehlercode
    global void errno_out (LONG errorcode);
    global void errno_out(errorcode)
      var LONG errorcode;
      { asciz_out(" IoErr() = "); dez_out(errorcode); asciz_out("." NLstring); }

