# Diverse Funktionen für CLISP
# Bruno Haible 1990-2000

#include "lispbibl.c"

# Eigenwissen:

LISPFUNN(lisp_implementation_type,0)
# (LISP-IMPLEMENTATION-TYPE), CLTL S. 447
  {
    VALUES1(O(lisp_implementation_type_string));
  }

LISPFUNN(lisp_implementation_version,0)
# (LISP-IMPLEMENTATION-VERSION), CLTL S. 447
  {
    value1 = O(lisp_implementation_version_string);
    if (nullp(value1)) { # noch unbekannt?
      var int count = 4;
      pushSTACK(O(lisp_implementation_version_number_string));
      pushSTACK(ascii_to_string(" (released "));
      pushSTACK(O(lisp_implementation_version_date_string));
      funcall(L(machine_instance),0);
      if (nullp(O(memory_image_host)) || equal(value1,O(memory_image_host))) {
        # the image was dumped on this machine - print time
        if (!nullp(O(lisp_implementation_version_built_string))) {
          # this is a gross and ugly hack!
          # I have no idea about how to get the executable link time,
          # let alone how to do this portably,
          # so I rely on __DATE__ and __TIME__ CPP macros.
          var uintL se,mi,ho,da,mo,ye;
          with_string_0(O(lisp_implementation_version_built_string),
                        O(misc_encoding),ztime,{
            # Mmm dd yyyyhh:mm:ss
            # 0   4  7   11 14 17
            ztime[13] = ztime[16] = 0;
            se = atol(ztime+17);
            mi = atol(ztime+14);
            ho = atol(ztime+11);
            da = atol(ztime+4);
            mo = (strncmp("Jan",ztime,3) == 0 ? 1 :
                  strncmp("Feb",ztime,3) == 0 ? 2 :
                  strncmp("Mar",ztime,3) == 0 ? 3 :
                  strncmp("Apr",ztime,3) == 0 ? 4 :
                  strncmp("May",ztime,3) == 0 ? 5 :
                  strncmp("Jun",ztime,3) == 0 ? 6 :
                  strncmp("Jul",ztime,3) == 0 ? 7 :
                  strncmp("Aug",ztime,3) == 0 ? 8 :
                  strncmp("Sep",ztime,3) == 0 ? 9 :
                  strncmp("Oct",ztime,3) == 0 ? 10 :
                  strncmp("Nov",ztime,3) == 0 ? 11 :
                  strncmp("Dec",ztime,3) == 0 ? 12 : 0);
            ztime[11]=0;
            ye = atol(ztime+7);
          });
          # no month ==> l_i_v_b_s must have been converted already
          if (mo != 0) {
            # YYYY-MM-DD HH:MM:SS
            var char build_time[4+1+2+1+2 +1+ 2+1+2+1+2+1];
            if (!boundp(Symbol_function(S(encode_universal_time)))) {
              sprintf(build_time,"%04u-%02u-%02u %02u:%02u:%02u",
                      (unsigned int) ye, (unsigned int) mo, (unsigned int) da,
                      (unsigned int) ho, (unsigned int) mi, (unsigned int) se);
            } else {
              pushSTACK(fixnum(se));
              pushSTACK(fixnum(mi));
              pushSTACK(fixnum(ho));
              pushSTACK(fixnum(da));
              pushSTACK(fixnum(mo));
              pushSTACK(fixnum(ye));
              funcall(S(encode_universal_time),6);
              sprintf(build_time,"%u", (unsigned int) I_to_UL(value1));
            }
            O(lisp_implementation_version_built_string) =
              ascii_to_string(build_time);
          }
          pushSTACK(ascii_to_string(") (built "));
          pushSTACK(O(lisp_implementation_version_built_string));
          count += 2;
        }
        if (!nullp(O(memory_image_timestamp))) {
          pushSTACK(ascii_to_string(") (memory "));
          pushSTACK(O(memory_image_timestamp));
          count += 2;
        }
      } else { # this image was built on a different machine
        pushSTACK(ascii_to_string(") (built on "));
        pushSTACK(O(memory_image_host));
        count += 2;
      }
      pushSTACK(ascii_to_string(")"));
      value1 = O(lisp_implementation_version_string) = string_concat(count);
    }
    mv_count=1;
  }

LISPFUN(version,0,1,norest,nokey,0,NIL)
# (SYSTEM::VERSION) liefert die Version des Runtime-Systems,
# (SYSTEM::VERSION version) überprüft (am Anfang eines FAS-Files),
# ob die Versionen des Runtime-Systems übereinstimmen.
  {
    var object arg = popSTACK();
    if (!boundp(arg)) {
      VALUES1(O(version));
    } else {
      if (equal(arg,O(version)) /* || equal(arg,O(oldversion)) */) {
        VALUES0;
      } else {
        fehler(error,
               GETTEXT("This file was produced by another lisp version, must be recompiled.")
              );
      }
    }
  }

#ifdef MACHINE_KNOWN

LISPFUNN(machinetype,0)
# (MACHINE-TYPE), CLTL S. 447
  {
    var object erg = O(machine_type_string);
    if (nullp(erg)) { # noch unbekannt?
      # ja -> holen
      #ifdef UNIX
        #ifdef HAVE_SYS_UTSNAME_H
          var struct utsname utsname;
          begin_system_call();
          if ( uname(&utsname) <0) { OS_error(); }
          end_system_call();
          pushSTACK(asciz_to_string(&!utsname.machine,O(misc_encoding)));
          funcall(L(nstring_upcase),1); # in Großbuchstaben umwandeln
          erg = value1;
        #else
          # Betriebssystem-Kommando 'uname -m' bzw. 'arch' ausführen und
          # dessen Output in einen String umleiten:
          # (string-upcase
          #   (with-open-stream (stream (make-pipe-input-stream "/bin/arch"))
          #     (read-line stream nil nil)
          # ) )
          #if defined(UNIX_SUNOS4)
            pushSTACK(ascii_to_string("/bin/arch"));
          #elif defined(UNIX_NEXTSTEP)
            pushSTACK(ascii_to_string("/usr/bin/arch"));
          #else
            pushSTACK(ascii_to_string("uname -m"));
          #endif
          funcall(L(make_pipe_input_stream),1); # (MAKE-PIPE-INPUT-STREAM "/bin/arch")
          pushSTACK(value1); # Stream retten
          pushSTACK(value1); pushSTACK(NIL); pushSTACK(NIL);
          funcall(L(read_line),3); # (READ-LINE stream NIL NIL)
          pushSTACK(value1); # Ergebnis (kann auch NIL sein) retten
          builtin_stream_close(&STACK_1); # Stream schließen
          if (!nullp(STACK_0))
            erg = string_upcase(STACK_0); # in Großbuchstaben umwandeln
          else
            erg = NIL;
          skipSTACK(2);
        #endif
      #endif
      #ifdef WIN32_NATIVE
        {
          var SYSTEM_INFO info;
          begin_system_call();
          GetSystemInfo(&info);
          end_system_call();
          if (info.wProcessorArchitecture==PROCESSOR_ARCHITECTURE_INTEL) {
            erg = ascii_to_string("PC/386");
          }
        }
      #endif
      # Das Ergebnis merken wir uns für's nächste Mal:
      O(machine_type_string) = erg;
    }
    VALUES1(erg);
  }

LISPFUNN(machine_version,0)
# (MACHINE-VERSION), CLTL S. 447
  {
    var object erg = O(machine_version_string);
    if (nullp(erg)) { # noch unbekannt?
      # ja -> holen
      #ifdef UNIX
        #ifdef HAVE_SYS_UTSNAME_H
          var struct utsname utsname;
          begin_system_call();
          if ( uname(&utsname) <0) { OS_error(); }
          end_system_call();
          pushSTACK(asciz_to_string(&!utsname.machine,O(misc_encoding)));
          funcall(L(nstring_upcase),1); # in Großbuchstaben umwandeln
        #else
          # Betriebssystem-Kommando 'uname -m' bzw. 'arch -k' ausführen und
          # dessen Output in einen String umleiten:
          # (string-upcase
          #   (with-open-stream (stream (make-pipe-input-stream "/bin/arch -k"))
          #     (read-line stream nil nil)
          # ) )
          #if defined(UNIX_SUNOS4)
            pushSTACK(ascii_to_string("/bin/arch -k"));
          #else
            pushSTACK(ascii_to_string("uname -m"));
          #endif
          funcall(L(make_pipe_input_stream),1); # (MAKE-PIPE-INPUT-STREAM "/bin/arch -k")
          pushSTACK(value1); # Stream retten
          pushSTACK(value1); pushSTACK(NIL); pushSTACK(NIL);
          funcall(L(read_line),3); # (READ-LINE stream NIL NIL)
          pushSTACK(value1); # Ergebnis (kann auch NIL sein) retten
          builtin_stream_close(&STACK_1); # Stream schließen
          funcall(L(string_upcase),1); skipSTACK(1); # in Großbuchstaben umwandeln
        #endif
        erg = value1;
      #endif
      #ifdef WIN32_NATIVE
        {
          var SYSTEM_INFO info;
          var OSVERSIONINFO v;
          begin_system_call();
          GetSystemInfo(&info);
          v.dwOSVersionInfoSize = sizeof(OSVERSIONINFO);
          if (!GetVersionEx(&v)) { OS_error(); }
          end_system_call();
          if (info.wProcessorArchitecture==PROCESSOR_ARCHITECTURE_INTEL) {
            erg = ascii_to_string("PC/386");
            # Check for Windows NT, since the info.wProcessorLevel is
            # garbage on Windows 95.
            if (v.dwPlatformId == VER_PLATFORM_WIN32_NT)
              TheS8string(erg)->data[3] = '0'+info.wProcessorLevel;
            else {
              if (info.dwProcessorType == PROCESSOR_INTEL_386)
                TheS8string(erg)->data[3] = '3';
              elif (info.dwProcessorType == PROCESSOR_INTEL_486)
                TheS8string(erg)->data[3] = '4';
              elif (info.dwProcessorType == PROCESSOR_INTEL_PENTIUM)
                TheS8string(erg)->data[3] = '5';
            }
          }
        }
      #endif
      # Das Ergebnis merken wir uns für's nächste Mal:
      O(machine_version_string) = erg;
    }
    VALUES1(erg);
  }

#endif # MACHINE_KNOWN

#ifdef HAVE_ENVIRONMENT

# (EXT:GETENV string) return the string associated with the given string
# in the OS Environment or NIL if no value
# if STRING is NIL, return all the environment as an alist
LISPFUN(get_env,0,1,norest,nokey,0,NIL) {
  var object arg = popSTACK();
  if (missingp(arg)) { /* return all the environment at once */
    extern char** environ;
    var char** epp;
    var char* ep;
    var uintL count = 0;
    for (epp = environ; (ep = *epp) != NULL; epp++, count++) {
      while ((*ep != 0) && (*ep != '=')) ep++;
      pushSTACK(allocate_cons());
      Car(STACK_0) = n_char_to_string(*epp,ep-*epp,O(misc_encoding));
      if (*ep == '=')
        Cdr(STACK_0) = asciz_to_string(ep+1,O(misc_encoding));
    }
    VALUES1(listof(count));
    return;
  }
  if (!stringp(arg))
    fehler_string(arg);
  var const char* found;
  with_string_0(arg,O(misc_encoding),envvar, {
    begin_system_call();
    found = getenv(envvar);
    end_system_call();
  });
  if (found != NULL)
    VALUES1(asciz_to_string(found,O(misc_encoding)));
  else
    VALUES1(NIL);
}

# Creates a string concatenating an environment variable and its value.
# Like sprintf(buffer, "%s=%s", name, value);
local char * cat_env_var (char * buffer, const char * name, uintL namelen,
                          const char * value, uintL valuelen) {
  memcpy(buffer,name,namelen);
  if (value != NULL) {
    buffer[namelen] = '=';
    memcpy(buffer+namelen+1,value,valuelen);
    buffer[namelen+1+valuelen] = 0;
  } else
    buffer[namelen] = 0;
  return buffer;
}

# Modify the environment variables. putenv() is POSIX, but some BSD systems
# only have setenv(). Therefore (and because it's simpler to use) we
# implement this interface, but without the third argument.
# clisp_setenv(name,value) sets the value of the environment variable `name'
# to `value' and returns 0. Returns -1 if not enough memory.
global int clisp_setenv (const char * name, const char * value) {
  var uintL namelen = asciz_length(name);
  var uintL valuelen = (value==NULL ? 0 : asciz_length(value));
#if defined(HAVE_PUTENV)
  var char* buffer = (char*)malloc(namelen+1+valuelen+1);
  if (!buffer)
    return -1; # no need to set errno = ENOMEM
  return putenv(cat_env_var(buffer,name,namelen,value,valuelen));
#elif defined(HAVE_SETENV)
  return setenv(name,value,1);
#else
  # Uh oh, neither putenv() nor setenv(), have to frob the environment
  # ourselves. Routine taken from glibc and fixed in several aspects.
  extern char** environ;
  var char** epp;
  var char* ep;
  var uintL envvar_count = 0;
  for (epp = environ; (ep = *epp) != NULL; epp++) {
    var const char * np = name;
    # Compare *epp and name:
    while (*np != '\0' && *np == *ep) { np++; ep++; }
    if (*np == '\0' && *ep == '=')
      break;
    envvar_count++;
  }
  ep = *epp;
  if (ep == NULL) {
    if (value != NULL) {
      # name not found in environ, add it.
      # if value is NULL - nothing is to be done!
      # Remember the environ, so that we can free it if we need
      # to reallocate it again next time.
      var static char** last_environ = NULL;
      var char** new_environ = (char**) malloc((envvar_count+2)*sizeof(char*));
      if (!new_environ)
        return -1; # no need to set errno = ENOMEM
      { # copy environ
        var uintL count;
        epp = environ;
        for (count = 0; count < envvar_count; count++)
          new_environ[count] = epp[count];
      }
      ep = (char*) malloc(namelen+1+valuelen+1);
      if (!ep) {
        free(new_environ); return -1; # no need to set errno = ENOMEM
      }
      new_environ[envvar_count] = cat_env_var(ep,name,namelen,value,valuelen);
      new_environ[envvar_count+1] = NULL;
      environ = new_environ;
      if (last_environ != NULL)
        free(last_environ);
      last_environ = new_environ;
    }
  } else {
    # name found, replace its value.
    # We could be tempted to overwrite name's value directly if
    # the new value is not longer than the old value. But that's
    # not a good idea - maybe someone still has a pointer to
    # this area around.
    # should we free() the old value?!
    ep = (char*) malloc(namelen+1+valuelen+1);
    if (!ep)
      return -1; # no need to set errno = ENOMEM
    *epp = cat_env_var(ep,name,namelen,value,valuelen);
  }
  return 0;
#endif
}

LISPFUNN(set_env,2)
# (SYS::SETENV name value)
# define the OS Environment variable NAME to have VALUE (string or NIL)
{
  if (!stringp(STACK_1)) fehler_string(STACK_1);
  if (!stringp(STACK_0) && !nullp(STACK_0)) fehler_string(STACK_0);
  var object value = popSTACK();
  var object name = popSTACK();
  var int ret;
  with_string_0(name,O(misc_encoding),namez, {
    begin_system_call();
    if (nullp(value)) {
      if (getenv(namez))
        ret = clisp_setenv(namez,NULL);
      else
        ret = 0;
    } else {
      with_string_0(value,O(misc_encoding),valuez, {
        ret = clisp_setenv(namez,valuez);
      });
    }
    end_system_call();
  });
  if (ret) {
    pushSTACK(value);
    pushSTACK(name);
    pushSTACK(TheSubr(subr_self)->name);
    fehler(error,
           GETTEXT("~ (~ ~): out of memory"));
  }
  VALUES1(value);
}

#endif

#ifdef WIN32_NATIVE

LISPFUNN(registry,2)
# (SYSTEM::REGISTRY path name) returns the value of path\\name in the registry.
# Used to implement SHORT-SITE-NAME and LONG-SITE-NAME.
  {
    if (!stringp(STACK_1))
      fehler_string(STACK_1);
    if (!stringp(STACK_0))
      fehler_string(STACK_0);
    with_string_0(STACK_1,O(misc_encoding),pathz, {
      with_string_0(STACK_0,O(misc_encoding),namez, {
        LONG err;
        HKEY key;
        DWORD type;
        DWORD size;
        begin_system_call();
        err = RegOpenKeyEx(HKEY_LOCAL_MACHINE,pathz,0,KEY_READ, &key);
        if (!(err == ERROR_SUCCESS)) {
          if (err == ERROR_FILE_NOT_FOUND) {
            VALUES1(NIL);
            goto none;
          }
          SetLastError(err); OS_error();
        }
        err = RegQueryValueEx(key,namez,NULL,&type, NULL,&size);
        if (!(err == ERROR_SUCCESS)) {
          if (err == ERROR_FILE_NOT_FOUND) {
            RegCloseKey(key);
            VALUES1(NIL);
            goto none;
          }
          SetLastError(err); OS_error();
        }
        switch (type) {
          case REG_SZ:
            {
              var char* buf = (char*)alloca(size);
              err = RegQueryValueEx(key,namez,NULL,&type, buf,&size);
              if (!(err == ERROR_SUCCESS)) { SetLastError(err); OS_error(); }
              err = RegCloseKey(key);
              if (!(err == ERROR_SUCCESS)) { SetLastError(err); OS_error(); }
              end_system_call();
              VALUES1(asciz_to_string(buf,O(misc_encoding)));
            }
            break;
          default:
            {
              var object path_name;
              pushSTACK(STACK_1); pushSTACK(O(backslash_string)); pushSTACK(STACK_(0+2));
              path_name = string_concat(3);
              pushSTACK(path_name);
              pushSTACK(TheSubr(subr_self)->name);
              fehler(error,
                     GETTEXT("~: type of attribute ~ is unsupported")
                    );
            }
        }
      });
    none:;
    });
    skipSTACK(2);
  }

#endif

LISPFUNN(software_type,0) { # (SOFTWARE-TYPE), CLTL p. 448
  VALUES1(CLSTEXT("ANSI C program"));
}

LISPFUNN(software_version,0) { # (SOFTWARE-VERSION), CLTL p. 448
#if defined(GNU)
 #if defined(__cplusplus)
  pushSTACK(CLSTEXT("GNU C++ "));
 #else
  pushSTACK(CLSTEXT("GNU C "));
 #endif
  pushSTACK(O(c_compiler_version));
  VALUES1(string_concat(2));
#else
 #if defined(__cplusplus)
  VALUES1(CLSTEXT("C++ compiler"));
 #else
  VALUES1(CLSTEXT("C compiler"));
 #endif
#endif
}

LISPFUNN(identity,1) { # (IDENTITY object), CLTL p. 448
  VALUES1(popSTACK());
}

LISPFUNN(address_of,1)
# (SYS::ADDRESS-OF object) liefert die Adresse von object
  {
    var object arg = popSTACK();
    #if defined(WIDE_HARD)
      VALUES1(UQ_to_I(untype(arg)));
    #elif defined(WIDE_SOFT)
      VALUES1(UL_to_I(untype(arg)));
    #else
      VALUES1(UL_to_I(as_oint(arg)));
    #endif
  }

#ifdef HAVE_DISASSEMBLER

LISPFUNN(code_address_of,1)
# (SYS::CODE-ADDRESS-OF object) liefert die Adresse des Maschinencodes von object
  {
    var object obj = popSTACK();
    if (ulong_p(obj)) # Zahl im Bereich eines aint == ulong -> Zahl selbst
      VALUES1(obj);
    elif (subrp(obj)) # SUBR -> seine Adresse
      VALUES1(ulong_to_I((aint)(TheSubr(obj)->function)));
    elif (fsubrp(obj)) # FSUBR -> seine Adresse
      VALUES1(ulong_to_I((aint)(TheFsubr(obj)->function)));
    #ifdef DYNAMIC_FFI
    elif (ffunctionp(obj))
      VALUES1(ulong_to_I((uintP)Faddress_value(TheFfunction(obj)->ff_address)));
    #endif
    else
      VALUES1(NIL);
  }

LISPFUNN(program_id,0)
# (SYS::PROGRAM-ID) returns the pid
  {
    begin_system_call();
    var int pid = getpid();
    end_system_call();
    VALUES1(L_to_I((sint32)pid));
  }

#endif

LISPFUNN(ansi,0)
# (SYS::ANSI)
  {
    VALUES1(O(ansi));
  }

LISPFUNN(set_ansi,1)
# (SYS::SET-ANSI ansi-p)
  {
    var object val = (nullp(popSTACK()) ? NIL : T);
    # (SETQ *ANSI* val)
    O(ansi) = val;
    # (SETQ *FLOATING-POINT-CONTAGION-ANSI* val)
    Symbol_value(S(floating_point_contagion_ansi)) = val;
    # (SETQ *MERGE-PATHNAMES-ANSI* val)
    Symbol_value(S(merge_pathnames_ansi)) = val;
    # (SETQ *PRINT-PATHNAMES-ANSI* val)
    Symbol_value(S(print_pathnames_ansi)) = val;
    # (SETQ *PARSE-NAMESTRING-ANSI* val)
    Symbol_value(S(parse_namestring_ansi)) = val;
    # (SETQ *SEQUENCE-COUNT-ANSI* val)
    Symbol_value(S(sequence_count_ansi)) = val;
    # (SETQ *COERCE-FIXNUM-CHAR-ANSI* val)
    Symbol_value(S(coerce_fixnum_char_ansi)) = val;
    VALUES1(val);
  }
