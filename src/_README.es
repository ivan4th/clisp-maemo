Esto es CLISP, una implementaci�n de Common Lisp.


� Qu� es LISP ?
---------------

LISP es un lenguaje de programaci�n inventado por J. McCarthy en
1959. Aunque ha habido muchos dialectos de �l, actualmente se ha
estandarizado y difundido ampliamente gracias al estandar industrial
COMMON LISP. Hay aplicaciones en los dominios del procesamiento del
conocimiento simb�lico (IA), c�lculo num�rico (MACLISP generaba c�digo
tan bueno como el de FORTRAN), y en programas ampliamente utilizados
como editores (EMACS) y CAD (AUTOCAD). Si lo desea, puede consultar la
introducci�n al lenguaje LISP:

  Sheila Hughes: Lisp. Pitman Publishing Limited, London 1986.
  107 pages.

Despu�s de un rato, necesitar� el texto estandar que contiene la
definici�n del lenguaje:

Guy L. Steele Jr.: Common Lisp - The Language. Digital Press.
  1. edition 1984, 465 pages.
  2. edition 1990, 1032 pages.

Este libro est� disponible en formato HTML via FTP en:
  ftp.cs.cmu.edu:/user/ai/lang/lisp/doc/cltl/cltl_ht.tgz

y puede consultarse a trav�s de WWW en:

  http://www.cs.cmu.edu:8001/Web/Groups/AI/html/cltl/cltl2.html o	
  http://www.cs.cmu.edu:8001/afs/cs/project/ai-repository/ai/html/cltl/cltl2.html .

Nota para los expertos: Este texto estandar se ha convertido en un
est�ndar ANSI, que puede obtenerse <<<exceptionally>>> sin cargo alguno en:

  http://www.lisp.org/HyperSpec/FrontMatter/

LISP se ejecuta en un entorno interactivo. Usted introduce formas, que
ser�n evaluadas de inmediato. Por lo tanto, puede inspeccionar
variables, invocar funciones con unos argumentos concretos o definir
sus propias funciones.


Contenidos:
-----------

Consta de los siguientes ficheros:

#ifdef UNIX
#ifndef UNIX_BINARY_DISTRIB
   base/lisp.a            programa principal, listo para ser enlazado
#endif
#ifdef UNIX_BINARY_DISTRIB
   base/lisp.run          programa principal
#endif
   base/lispinit.mem      imagen de memoria necesaria para la inicializaci�n
   doc/clisp.1            manual en formato man de Unix
   doc/clisp.man          manual
   doc/clisp.html         manual en format HTML
   doc/impnotes.html      notas de la implementaci�n
#ifdef GNU_READLINE
   doc/clreadline.3       manual de edici�n de l�nea en formato man de Unix
   doc/clreadline.man     manual de edici�n de l�nea
#endif
   doc/LISP-tutorial.txt  tutorial de LISP para aprendices
   doc/CLOS-guide.txt     breve gu�a de CLOS
   README                 este texto
   SUMMARY                peque�a descripci�n de CLISP
   ANNOUNCE               declaraci�n
   NEWS                   lista de modificaciones desde la �ltima versi�n
   COPYRIGHT              derechos de autor <<<copyright>>>
   GNU-GPL                licencia de software libre
#ifdef GNU_READLINE
   doc/readline.dvi       documentaci�n de la librer�a GNU readline
                          en formato DVI
#endif
   doc/editors.txt        Lista de editores que soportan Lisp
   emacs/*.el             personalizaci�n de Emacs, v�ase doc/editors.txt
#ifndef UNIX_BINARY_DISTRIB
   src/clisp.c            fuentes del programa
#endif
   src/config.lsp         configuraci�n dependiente del lugar

y - cuando le apetezca, si le gusta leer c�digo fuente -

   src/*.lsp              el c�digo fuente de lispinit.mem
   src/*.fas              los mismos ficheros, una vez compilados
#if !defined(UNIX_BINARY_DISTRIB) && defined(GNU_READLINE)

Para crear el ejecutable, tambi�n necesitar�:

   base/libreadline.a     librer�a GNU readline

o

   base/libnoreadline.a   sustituto ficticio de la librer�a GNU readline
#endif
#else /* !defined(UNIX) */
#ifdef AMIGAOS
      lisp.run           programa principal
#endif
#ifdef OS2
      lisp.exe           programa principal
#endif
#ifdef RISCOS
      lisp               programa principal
#endif
      lispinit.mem       imagen de memoria necesaria para la inicializaci�n
#ifdef GNU_GETTEXT
      locale/*/LC_MESSAGES/clisp.mo  <<<localized messages databases>>>
#endif
      clisp.1            manual en formato `man' de Unix
#ifdef AMIGAOS
      clisp.doc          manual
#else
      clisp.man          manual
#endif
      clisp.html         manual en format HTML
#ifdef OS2
      clisp.dvi          manual en formato DVI
#endif
      impnotes.html      notas de la implementaci�n
#ifdef GNU_READLINE
      clreadline.3       manual de edici�n de l�nea en formato `man' de Unix
      clreadline.man     manual de edici�n de l�nea
      clreadline.html    manual de edici�n de l�nea en format HTML
#ifdef OS2
      clreadline.dvi     manual de edici�n de l�nea en formato DVI
#endif
#endif
      LISP-tutorial.txt  tutorial de LISP para aprendices
      CLOS-guide.txt     breve gu�a de CLOS
      editors.txt        <<<some words about text editors for Lisp>>>
#ifdef EMUNIX
      emx.exe            extensor DOS rsx para ejecutar clisp bajo DOS o OS/2
      emx-user.doc       gu�a del usuario de aplicaciones emx
      emx-faq.doc        preguntas frecuentes sobre las aplicaciones emx
      emx.dll            librer�a de enlazamiento din�mico de OS/2 que contiene emx
      emxlibc.dll        librer�a de enlazamiento din�mico de OS/2 que contiene emx libc
      termcap.dat        base de datos del terminal 
#endif
#ifdef RISCOS
      !Run               fichero de ejecuci�n para CLISP
      !Sprites           icono de CLISP
#endif
      README             este texto
      SUMMARY            peque�a descripci�n de CLISP
      ANNOUNCE           declaraci�n
      NEWS               lista de modificaciones desde la �ltima versi�n
      COPYRIGHT          derechos de autor
      GNU-GPL            licencia de software libre
#ifdef GNU_READLINE
      readline.dvi	 documentaci�n de la librer�a GNU readline en formato DVI
#endif
      config.lsp         configuraci�n dependiente del lugar
#if !(defined(UNIX) || defined(WIN32))
      timezone.lsp       zona horaria dependiente del lugar
#endif

y - cuando le apetezca, si le gusta leer c�digo fuente -

      *.lsp              el c�digo fuente de lispinit.mem
#if !defined(OS2)
      *.fas              los mismos ficheros, una vez compilados
#endif
#endif

#ifdef OS2

Requisitos Hardware:
--------------------

La versi�n para OS/2 de CLISP necesita una CPU 80386 (SX o DX) o un 80486,
ejecutando OS/2 2.0.
Tambi�n se ejecuta en un Pentium; los resultados que produce CLISP no
est�n afectados por el error de divisi�n del Pentium de Intel.

#endif
#ifdef AMIGAOS

Requisitos Hardware:
--------------------

Esta versi�n para Amiga de CLISP requiere, al menos, 1.5 MB de RAM. La
versi�n denominada CLISP-LOW se ejecuta en m�quinas sin m�s memoria
que la que puede direccionarse en un rango de 24 bits: en el 68000,
A2620 y A2630. La versi�n denominada CLISP-HIGH se ejecuta en memorias
que se direccionan con 27 bits (en el rango de direcciones de
#x00000000 to #x07FFFFFF), pero s�lo en las CPUs 68020/030/040(/060?):
en A3000 y A4000 sin placas de memoria Zorro-III. La versi�n
denominada CLISP-00 se ejecuta �nicamente en una CPU 68000/010, pero
es m�s r�pida que CLISP-LOW. La versi�n denominada CLISP-WIDE utiliza
enteros de 64 bits y se ejecuta sobre cualquier memoria en un
procesador 68020 o superior: sobre A4000 con VMM. El esfuerzo
adicional para el tratamiento de n�meros enteros de 64 bits hace que
CLISP-WIDE sea m�s lento que CLISP-HIGH.

#endif
#ifdef RISCOS

Requisitos Hardware:
--------------------

Esta versi�n de CLISP requiere un PC Acorn Archimedes o Acorn RISC
con, al menos, 4 MB de Ram y RISC OS 3.0 o superior. M�s adelante se
explica como crear una versi�n de CLISP que se ejecute con solo 2 MB.

#endif
#if defined(SINGLEMAP_MEMORY) && (defined(UNIX_LINUX) || !defined(HAVE_MMAP_ANON))

Requisitos Software:
--------------------

#ifdef UNIX_LINUX
#ifdef GENERATIONAL_GC
#ifdef IMMUTABLE
Esta versi�n de CLISP necesita Linux 1.2.2 o m�s reciente.
#else
Esta versi�n de CLISP necesita Linux 1.1.52 o m�s reciente.
#endif
#else
Esta versi�n de CLISP necesita Linux 0.99.7 o m�s reciente.
#endif
#endif
#if !defined(HAVE_MACH_VM) && !defined(HAVE_MMAP_ANON) /* impliziert HAVE_MMAP_DEVZERO */
/dev/zero debe ser legible por cualquiera. Para ello, debe ejecutar el
comando "chmod a+r /dev/zero".
#endif

#endif
#ifdef AMIGAOS

Requisitos Software:
--------------------

Esta versi�n de CLISP necesita OS 2.04 (V37) o m�s reciente.

#endif

Instalaci�n:
------------

#ifdef OS2
Antes que nada, instale emx.dll y emxlibc.dll en un directorio aparte,
por ejemplo c:\emx\dll. A�ada c:\emx\dll (aseg�rese de colocar la
unidad de disco correcta) a la sentencia LIBPATH de su fichero
config.sys. Reinicie su ordenador, de modo que se active la nueva
instrucci�n LIBPATH y las nuevas variables de entorno.

#endif
#ifdef EMUNIX

Para que las l�neas de entrada demasiado largas puedan mostrarse de
una manera elegante, es necesario que tenga una linea del tipo:

    DEVICE=ANSI.SYS

en su fichero CONFIG.SYS. M�s a�n, la variable de entorno TERM debe
estar definida, y la variable de entorno TERMCAP debe contener el
nombre del fichero (con la ruta completa) de la base de datos
TERMCAP.DAT, con la definici�n de las capacidades del terminal. Es una
buena idea, a�adir estas instrucciones en el fichero CLISP.BAT que se
construye m�s adelante. Si lo desea, puede instalar el fichero
TERMCAP.DAT en un directorio aparte, por ejemplo c:\emx\etc.

#endif
#if defined(UNIX) || defined(WIN32)
#if defined(UNIX) && !defined(UNIX_BINARY_DISTRIB)
Teclee

         make

#if 0 /* def GNU_READLINE - man mu� Makefile ver�ndern */
Si desea renunciar a las capacidades de edici�n de lectura de la
librer�a GNU readline, deber�a haber reemplazado "libreadline.a" en la
l�nea LIBS del fichero BASE/MAKEVARS por "libnoreadline.a".

#endif
#endif
Cambie las cadenas en SRC/CONFIG.LSP, empleando para ello un editor de
textos.
#else
Edite el fichero CONFIG.LSP y modif�quelo adecuadamente para su
estaci�n, con especial atenci�n a las definiciones de short-site-name
y long-site-name. Si lo desea, tambi�n puede modificar la definici�n
de la zona horaria al final del fichero TIMEZONE.LSP.
#endif
Luego ejecute

#if defined(OS2) || defined(WIN32_NATIVE)
         lisp.exe -M lispinit.mem
#endif
#ifdef AMIGAOS
         lisp.run -M lispinit.mem
#endif
#ifdef UNIX
         base/lisp.run -M base/lispinit.mem
#endif
#ifdef RISCOS
         lisp -M mem.lispinit

o haga doble click sobre el directorio !Clisp.
#endif

Cuando aparezca el inductor de comandos

      > _

teclee

#ifdef RISCOS
        (cd "<clisp$path>.")

para asegurarse de que el directorio !Clisp es el que est� actualmente
seleccionado. Luego

#endif
#if defined(UNIX) || defined(WIN32)
        (compile-file "src/config.lsp")
        (load "src/config.fas")
#else
        (compile-file "config.lsp")
        (load "config.fas")

y - si modific� el fichero TIMEZONE.LSP -

        (compile-file "timezone.lsp")
        (load "timezone.fas")
#endif

y luego

#ifdef UNIX
        (cd "base/")
#endif
        (saveinitmem)

para sobreescribir el fichero LISPINIT.MEM con su configuraci�n. A
continuaci�n

        (exit)

#ifdef UNIX
El resto se hace simplemente con

        make install

En vez de esto, puede hacerlo usted mismo, paso por paso:

#endif
#ifndef RISCOS
Luego cree un directorio, y ponga en �l el ejecutable con la imagen de
memoria.
#endif
#ifdef UNIX
Le recomiendo /usr/local/lib/lisp :

   mkdir /usr/local/lib/lisp
   mv base/lisp.run /usr/local/lib/lisp
   mv base/lispinit.mem /usr/local/lib/lisp
#endif
#if defined(OS2) || defined(WIN32_NATIVE)
Suponiendo D:\LIB\LISP :

   mkdir d:\lib\lisp
   copy lisp.exe d:\lib\lisp
   copy lispinit.mem d:\lib\lisp
#endif

#if defined(MSDOS) || defined(WIN32_NATIVE)
Y cree un fichero de ejecuci�n por lotes que ejecute lisp:

#ifndef OS2
   copy con c:\bat\clisp.bat
#else
   copy con c:\cmd\clisp.cmd
#endif
#ifdef EMUNIX
   set TERM=ansi
   set TERMCAP=c:/emx/etc/termcap.dat
#endif
   d:\lib\lisp\lisp.exe -M d:\lib\lisp\lispinit.mem -B d:\lib\lisp\ %1 %2 %3 %4 %5 %6 %7 %8 %9
   [Ctrl-Z]
#endif
#ifdef UNIX
Y cree el programa que ejeute lisp:

#ifdef UNIX_BINARY_DISTRIB
   cc -O -DLISPLIBDIR='"/usr/local/lib/lisp"' \
         -DLOCALEDIR='"/usr/local/share/locale"' \
      src/clisp.c -o /usr/local/bin/clisp
#else
   ./hardcode -DLISPLIBDIR='/usr/local/lib/lisp' \
              -DLOCALEDIR='/usr/local/share/locale' \
              clisp /usr/local/bin/clisp
#endif

#ifdef GNU_READLINE
Ahora, instale las p�ginas de man.
#else
Ahora, instale la p�gina man.
#endif

   mv doc/clisp.1 /usr/local/man/man1/clisp.1
#ifdef GNU_READLINE
   mv doc/clreadline.3 /usr/local/man/man3/clreadline.3
#endif

and try

   man clisp
#endif

#ifdef AMIGAOS

Nota:
-----

Puede ejecutar CLISP desde Workbench(tm). Los siguientes Tooltypes son
reconocidos en el icono Tool:

   WINDOW=<ventana o especificaci�n de `pipe'>
   ARGS=<argumentos del tipo CLI>

Por ejemplo,

   WINDOW=CON:0/11/640/200/CLISP-Listener/CLOSE
   ARGS=-M lispinit.mem

#endif
#ifdef RISCOS

�Corto de memoria?
------------------

Si s�lo dispone de 2 MB de RAM, puede crear un CLISP "desmontado" que
requiere menos memoria, pero que no dispondr� de algunas partes
definidas en CLtL2, dpANS-LOOP, CLOS, Condiciones y flujos gen�ricos:
Reemplace DEFS2.FAS, LOOP.FAS, CLOS.FAS, CONDITIO.FAS, DEFS3.FAS,
GSTREAM.FAS por ficheros vac�os y ejecute:

   lisp
   > (load "init.fas")
   > (saveinitmem)
   > (exit)

Esto sobreescribir� el fichero LISPINIT.MEM por otro m�s peque�o.

#endif

Cuando encuentre problemas:
---------------------------

#ifdef EMUNIX
Si clisp no se ejecuta de ninguna manera, consulte
EMX-USER.DOC. LISP.EXE es una aplicaci�n EMX, de modo que todo lo que
se menciona ah�, se aplica a LISP.EXE.

#endif
Despu�s de un error, se encontrar� en el depurador:

     1. Break> _

En �l, usted puede evaluar formas como siempre. M�s a�n:

     Help
               invoca la ayuda
     Abort     o
     Unwind
               retrocede hasta el bucle de entrada m�s reciente
     Backtrace
               muestra los contenidos de la pila, �til para la depuraci�n

Y puede consultar el valor de las variables de las funciones donde se
produjo el error.

#ifdef UNIX
Cuando los problemas sean mayores, por ejemplo `core dumps', por favor
#endif
#ifdef AMIGAOS
Cuando los problemas sean mayor, por ejemplo "guru"s, por favor
#endif
#ifdef OS2
Cuando los problemas sean mayor, por ejemplo "register dumps", por favor
#endif
#ifdef RISCOS
Cuando los problemas sean mayores, por ejemplo, "stack dumps", por favor
#endif
env�e una descripci�n del error y una descripci�n de c�mo reproducir
el error a los autores o al "mantenedor". Por favor, acompa�e su mensaje
de la versi�n de CLISP que puede obtener invocando la funci�n
(lisp-implementation-version).


C�digo fuente:
--------------

El c�digo fuente de CLISP est� disponible en
     ftp://clisp.cons.org/pub/lisp/clisp/source/clispsrc*
#ifdef UNIX_LINUX
La �ltima distribuci�n binaria de CLISP para Linux tiene su propio
c�digo fuente en
     ftp://sunsite.unc.edu/pub/Linux/devel/lang/lisp/clisp-source.tar.gz
#endif


#if 0
<<<Mailing lists:>>>
#endif
Lista de correo:
----------------

#if 0
Hay una lista de correo para los usuarios de CLISP. �se es el foro
adecuado para cualquier cuesti�n relacionada con CLISP, problemas de
instalaci�n, errores, paquetes de aplicaciones, etc.
#endif
<<<There are three mailing lists for users of CLISP. You find subscription
information and archives on the homepage http://clisp.cons.org/.>>>


Agradecimientos:
----------------

Estamos muy agradecidos a 
  * Guy L. Steele y otros muchos por la especificaci�n de Common Lisp.
#ifdef UNIX
  * El proyecto GNU de Richard Stallman para el GCC, Autoconf y la librer�a
    readline.
#else
#ifdef GNU_READLINE
  * El proyecto GNU de Richard Stallman para el GCC y la librer�a readline.
#else
#ifdef GNU
  * El proyecto GNU de Richard Stallman para el GCC.
#endif
#endif
#endif
#ifdef EMUNIX
  * Eberhard Mattes por EMX.
#endif


Autores:
--------

        Bruno Haible
        Michael Stoll

Email: clisp-list@lists.sourceforge.net
#ifdef AMIGAOS

Migraci�n a Amiga por:
----------------------

        J�rg H�hle

Email: Joerg.Hoehle@gmd.de
#endif
#ifdef RISCOS

Migraci�n a Acorn RISC OS por:
------------------------------

        Peter Burwood

Email: clisp@arcangel.dircon.co.uk
#endif

"Mantenedor":
-------------

        Marcus Daniels

Email: marcus@sysc.pdx.edu
