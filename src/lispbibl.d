# Haupt-Include-File f�r CLISP
# Bruno Haible 21.9.1997
# Marcus Daniels 11.11.1994


# Flags intended to be set through CFLAGS:
#   Readline library:
#     NO_READLINE
#   Internationalization:
#     NO_GETTEXT
#   Foreign function interface:
#     DYNAMIC_FFI
#   Dynamic loading of modules:
#     DYNAMIC_MODULES
#   Safety level:
#     SAFETY={0,1,2,3}
# Flags that may be set through CFLAGS, in order to override the defaults:
#   Object representation (on 32-bit platforms only):
#     TYPECODES, NO_TYPECODES, WIDE
#   Advanced memory management:
#     NO_SINGLEMAP, NO_TRIVIALMAP, NO_MULTIMAP_FILE, NO_MULTIMAP_SHM,
#     NO_MORRIS_GC, NO_GENERATIONAL_GC


# Implementation ist auf folgende Rechner, Betriebssysteme und C-Compiler
# vorbereitet. (Nur ungef�hre Liste, Genaues siehe PLATFORMS.)
# Maschine     Hersteller         Betriebssystem                C-Compiler    erkennbar an
# AMIGA        Commodore          AMIGA-OS (AMIGADOS)           GNU           amiga oder AMIGA, __GNUC__, evtl. MC68000 oder AMIGA3000
# beliebig     beliebig           UNIX                          GNU           unix, __GNUC__, ...
# beliebig     beliebig           UNIX                          CC            unix, ...
# Amiga 3000   Commodore          Amiga UNIX 2.1 SVR4.0         GNU           unix, __unix__, AMIX, __AMIX__, __svr4__, m68k, __m68k__, __motorola__, __GNUC__
# SUN-3        Sun                SUN-OS3 (UNIX BSD 4.2)        GNU           sun, unix, mc68020, __GNUC__
# SUN-3        Sun                SUN-OS4 (UNIX SUNOS 4.1)      GNU           sun, unix, mc68020, __GNUC__
# SUN-386      Sun                SUN-OS4 (UNIX SUNOS 4.0)      GNU           sun, unix, sun386, i386, __GNUC__
# SUN-386      Sun                SUN-OS4 (UNIX SUNOS 4.0)      CC            sun, unix, sun386, i386
# SUN-4        Sun                SUN-OS4 (UNIX SUNOS 4.1)      GNU           sun, unix, sparc, __GNUC__
# SUN-4        Sun                SUN-OS4 (UNIX SUNOS 4.1)      CC            sun, unix, sparc
# SUN-4        Sun                SUN-OS5 (UNIX Solaris)        GCC           sun, unix, sparc, __GNUC__
# IBM-PC/386   beliebig           SUN-OS5 (UNIX Solaris)        GCC           sun, unix, __svr4__, i386, __GNUC__
# HP9000-300   Hewlett-Packard    NetBSD 0.9 (UNIX BSD 4.3)     GNU           unix, __NetBSD__, mc68000, __GNUC__
# HP9000-300   Hewlett-Packard    HP-UX 8.0 (UNIX SYS V)        GNU           [__]hpux, [__]unix, [__]hp9000s300, mc68000, __GNUC__
# HP9000-800   Hewlett-Packard    HP-UX 8.0 (UNIX SYS V)        GNU           [__]hpux, [__]unix, [__]hp9000s800
# IRIS         Silicon Graphics   IRIX (UNIX SYS V 3.2)         GNU           unix, SVR3, mips, sgi, __GNUC__
# IRIS         Silicon Graphics   IRIX (UNIX SYS V)             cc -ansi      [__]unix, [__]SVR3, [__]mips, [__]sgi
# IRIS         Silicon Graphics   IRIX 5 (UNIX SYS V 4)         GNU           [__]unix, [__]SYSTYPE_SVR4, [__]mips, [__]host_mips, [__]MIPSEB, [__]sgi, __DSO__, [__]_MODERN_C, __GNUC__
# DECstation 5000                 RISC/OS (Ultrix V4.2A)        GNU           unix, [__]mips, [__]ultrix
# DG-UX 88k    Data General       DG/UX                         GNU           unix, m88000, DGUX
# DEC Alpha    DEC                OSF/1 1.3                     cc            [unix,] __unix__, __osf__, __alpha
# DEC Alpha    DEC                OSF/1 1.3                     GNU           unix, __unix__, __osf__, __alpha, __alpha__, _LONGLONG
# Apple MacII  Apple              A/UX (UNIX SYS V 2)           GNU           [__]unix, [__]AUX, [__]macII, [__]m68k, mc68020, mc68881, __GNUC__
# NeXT         NeXT               NeXTstep 3.1 (UNIX)           cc            NeXT, m68k; NEXTAPP f�r NeXTstep-Applikation
# PowerPC      Apple              Mach 3.0 + MkLinux            GNU           unix, __powerpc__, __PPC__, _ARCH_PPC, _CALL_SYSV, __ELF__, __linux__
# Sequent      Sequent            PTX 3.2.0 V2.1.0 i386 (SYS V) GNU           unix, i386, _SEQUENT_, __GNUC__
# Sequent      Sequent            PTX V4.1.3                    GNU           unix, i386, _SEQUENT_, __svr4__, __GNUC__
# Convex C2    Convex             ConvexOS 10.1                 GNU           __convex__, __GNUC__
# IBM RS/6000  IBM                AIX 3.2                       GNU           _AIX, _AIX32, _IBMR2, __CHAR_UNSIGNED__, __GNUC__
# IBM-PC/386   beliebig           LINUX (freies UNIX)           GNU           unix, linux, i386, __GNUC__
# IBM-PC/386   beliebig           386BSD 0.1 (UNIX BSD 4.2)     GNU           unix, __386BSD__, i386, __GNUC__
# IBM-PC/386   beliebig           NetBSD 0.9 (UNIX BSD 4.3)     GNU           unix, __NetBSD__, i386, __GNUC__
# IBM-PC/386   beliebig           DJUNIX (UNIXlike auf MSDOS)   GNU           unix, i386, [__MSDOS__,] __GNUC__, __GO32__; __GO32__ muss man evtl. selbst definieren!
# IBM-PC/386   beliebig           EMX 0.9c (UNIXlike auf MSDOS) GNU           [unix,] i386, __GNUC__, __EMX__
# IBM-PC/386   beliebig           EMX 0.9c (UNIXlike auf OS/2)  GNU           [unix,] i386, __GNUC__, __EMX__, OS2; OS2 muss man selbst definieren!
# IBM-PC/386   beliebig           MSDOS                         WATCOM        MSDOS, __386__, M_I386, __WATCOMC__, __FLAT__
# IBM-PC/386   beliebig           Cygwin32 auf WinNT/Win95      GNU           _WIN32, __WINNT__, __CYGWIN32__, __POSIX__, _X86_, i386, __GNUC__
# IBM-PC/386   beliebig           Mingw32 auf WinNT/Win95       GNU           _WIN32, __WINNT__, __MINGW32__, _X86_, i386, __GNUC__
# IBM-PC/386   beliebig           WinNT/Win95                   MSVC4.0,5.0   _WIN32, _M_IX86, _MSC_VER
# IBM-PC/386   beliebig           WinNT/Win95                   Borland 5.0   __WIN32__, _M_IX86, __TURBOC__, __BORLANDC__
# IBM-PC/386   beliebig           WinNT/Win95 und Cygwin32      GNU           _WIN32, __WINNT__, __CYGWIN32__, __POSIX__, __i386__, _X86_, __GNUC__
# Alpha        DEC                WinNT                         ??
# RM400        Siemens-Nixdorf    SINIX-N 5.42                  c89           unix, mips, MIPSEB, host_mips, sinix, SNI, _XPG_IV
# Acorn        Risc PC            RISC OS 3.x                   GNU           [__]arm, [__]riscos, __GNUC__
# Acorn        Risc PC            RISC OS 3.x                   Norcroft      [__]arm, [__]riscos
# APPLE IIGS   Apple              ??                            ??
# F�r ANSI-C-Compiler: verwende Pr�prozessoren comment5, ansidecl
#   (und evtl. gcc-cpp, ccpaux).


# diese Maschine: AMIGA oder ACORN oder DOSPC oder WIN32 oder GENERIC_UNIX
#if (defined(__unix) || defined(__unix__) || defined(_AIX) || defined(sinix) || defined(__POSIX__)) && !defined(unix)
  #define unix
#endif
#if (defined(amiga) || defined(AMIGA))
  #undef AMIGA
  #define AMIGA
#endif
#if (defined(arm) || defined(__arm)) && (defined(riscos) || defined(__riscos))
  #define ACORN
#endif
#if (defined(i386) && defined(__EMX__)) || defined(__GO32__) || (defined(__386__) && defined(__WATCOMC__) && defined(MSDOS))
  #define DOSPC
#endif
#if (defined(_WIN32) && (defined(_MSC_VER) || defined(__MINGW32__))) || (defined(__WIN32__) && defined(__BORLANDC__))
  #undef WIN32  # wg. __MINGW32__
  #define WIN32
#endif
#if !(defined(AMIGA) || defined(ACORN) || defined(DOSPC) || defined(WIN32))
  #if defined(unix)
    #define GENERIC_UNIX
  #else
    #error "Unknown machine type -- Maschine neu einstellen!"
  #endif
#endif
# Zus�tzliche Spezifikation der Maschine:
#ifdef DOSPC
  #define PC386 # IBMPC-Kompatibler mit 80386/80486-Prozessor
#endif
#ifdef GENERIC_UNIX
  #if (defined(sun) && defined(unix) && defined(sun386))
    #define SUN386
  #endif
  #if (defined(unix) && defined(linux) && defined(i386))
    #define PC386
  #endif
  #if (defined(sun) && defined(unix) && defined(mc68020))
    #define SUN3
  #endif
  #if (defined(sun) && defined(unix) && defined(sparc))
    #define SUN4
  #endif
  #if defined(sparc)
    # evtl. SUN4_29 falls nur Adressen <2^29 unterst�tzt werden.
    #ifdef SUN4_29
      #define SUN4_29_1  # handling using PACKED_TYPECODES
      # define SUN4_29_2  # handling using SIXBIT_TYPECODES
    #endif
  #endif
  #if defined(hp9000s800) || defined(__hp9000s800)
    #define HP8XX
  #endif
#endif

# Auswahl des Prozessors:
# MC680X0 == alle Prozessoren der Motorola-68000-Serie
# MC680Y0 == alle Prozessoren der Motorola-68000-Serie ab MC68020
# SPARC == der Sun-SPARC-Prozessor
# HPPA == alle Prozessoren der HP-Precision-Architecture
# MIPS == der Mips-Prozessor
# M88000 == alle Prozessoren der Motorola-88000-Serie
# RS6000 == der IBM-RS/6000-Prozessor
# I80386 == alle Prozessoren der Intel-8086-Serie ab 80386
# VAX == der VAX-Prozessor
# CONVEX == der Convex-Prozessor
# ARM == der ARM-Prozessor
# DECALPHA == der DEC-Alpha-Chip
#ifdef AMIGA
  #define MC680X0
  #if defined(AMIGA3000) && !defined(MC680Y0)
    #define MC680Y0
  #endif
#endif
#ifdef DOSPC
  #define I80386
#endif
#if 0
  #define VAX
#endif
#if defined(arm) || defined(__arm)
  #define ARM
#endif
#ifdef WIN32
  #if defined(_M_IX86) || defined(_X86_)
    #define I80386
  #endif
#endif
#ifdef GENERIC_UNIX
  #if defined(m68k) || defined(mc68000)
    #define MC680X0
  #endif
  #if defined(mc68020) || (defined(m68k) && defined(NeXT))
    #define MC680X0
    #define MC680Y0
  #endif
  #if defined(i386) || defined(__i386) || defined(_I386)
    #define I80386
  #endif
  #ifdef sparc
    #define SPARC
  #endif
  #if defined(mips) || defined(__mips)
    #define MIPS
    #if defined(_MIPS_SZLONG)
      #if (_MIPS_SZLONG == 64)
        # We should also check for (_MIPS_SZPTR == 64), but gcc keeps this at 32.
        #define MIPS64
      #endif
    #endif
  #endif
  #if defined(HP8XX) || defined(hppa) || defined(__hppa)
    #define HPPA
  #endif
  #ifdef m88000
    #define M88000
  #endif
  #if defined(_IBMR2) || defined(__powerpc)
    #define RS6000
  #endif
  #ifdef __convex__
    #define CONVEX
  #endif
  #ifdef __alpha
    #define DECALPHA
  #endif
#endif


# Auswahl des Betriebssystems:
#ifdef AMIGA
  #define AMIGAOS
#endif
#if (defined(riscos) || defined(__riscos)) && !defined(unix)
  #define RISCOS  # Acorn RISC OS
  #ifndef __GNUC__
    #define RISCOS_CCBUG  # Bug in Norcrofts C-Compiler umgehen
  #endif
  #define ACORN_1  # Typcode "oben"
  # define ACORN_2  # Typcode "unten"
#endif
#ifdef WIN32
  # Windows NT, Windows 95
  #if 1
    #define WIN32_NATIVE  # native NT API, no DOS calls
  #endif
  #if 0
    #define WIN32_DOS  # native NT API plus DOS calls, runs in DOS box only
  #endif
#endif
#ifdef GENERIC_UNIX
  #define UNIX
  #ifdef linux
    #define UNIX_LINUX  # Linux (Linus Torvalds Unix)
  #endif
  #ifdef __GNU__
    #define UNIX_GNU  # the GNU system (Hurd + glibc)
  #endif
  #ifdef __NetBSD__
    #define UNIX_NETBSD
  #endif
  #ifdef __FreeBSD__
    #define UNIX_FREEBSD
  #endif
  #if defined(hpux) || defined(__hpux)
    #define UNIX_HPUX  # HP-UX
  #endif
  #if defined(SVR3) || defined(__SVR3) || defined(SVR4) || defined(__SVR4) || defined(SYSTYPE_SVR4) || defined(__SYSTYPE_SVR4) || defined(__svr4__) || defined(USG) || defined(UNIX_HPUX) # ??
    #define UNIX_SYSV  # UNIX System V
  #endif
  #if defined(UNIX_SYSV) && (defined(sgi) || defined(__sgi))
    #define UNIX_IRIX  # Irix
    #if defined(SYSTYPE_SVR4) || defined(__SYSTYPE_SVR4)
      #define UNIX_IRIX5  # Irix 5
    #endif
  #endif
  #if defined(MIPS) && (defined(ultrix) || defined(__ultrix))
    #define UNIX_DEC_ULTRIX  # DEC's (oder IBM's ?) RISC/OS Ultrix auf DEC MIPS
    #ifdef __GNUC__
      #define UNIX_DEC_ULTRIX_GCCBUG  # GCC 2.3.3 Bug umgehen
    #endif
  #endif
  #if defined(MIPS) && defined(sinix) # && defined(SNI)
    #define UNIX_SINIX # Siemens is nix
  #endif
  #if defined(USL) || (defined(__svr4__) && defined(I80386) && !(defined(sun) || defined(__sun__)))
    # Eine Reihe von 386er Unixen (alle unter verschiedenem Namen) stammen
    # von USL SysV R 4 ab:
    #   386 UHC UNIX System V release 4
    #   Consensys System V 4.2
    #   Onsite System V 4.2
    #   SINIX-Z
    #   DYNIX/ptx V4.1.3
    #   SunOS 5
    #define UNIX_SYSV_USL  # Unix System V R 4 von der AT&T-Tochter USL
    #define UNIX_SYSV_UHC_1 # Behandlung analog HPPA && UNIX_HPUX
    # define UNIX_SYSV_UHC_2 # Behandlung analog AMIGA3000 - langsamer
    #ifdef SNI
      #define UNIX_SINIX # Siemens is nix
    #endif
  #endif
  #if defined(_SEQUENT_) && !defined(__svr4__)
    #define UNIX_SYSV_PTX  # Dynix/ptx v. 2 or 3
  #endif
  #ifdef _AIX
    #define UNIX_AIX  # IBM AIX
  #endif
  #ifdef DGUX
    #define UNIX_DGUX  # Data General DG/UX
  #endif
  #ifdef __osf__
    #define UNIX_OSF  # OSF/1
  #endif
  #ifdef AUX
    #define UNIX_AUX  # Apple A/UX, ein aufgep�ppeltes SVR2
  #endif
  #ifdef NeXT
    #define UNIX_NEXTSTEP  # NeXTstep
    # define NEXTAPP       # Definiere dies, um eine NeXTstep-GUI-Applikation
                           # zu bekommen.
    #define MAYBE_NEXTAPP  # kleiner Hack, damit die .mem Files zwischen
                           # clisp mit NEXTAPP und ohne NEXTAPP kompatibel sind
  #endif
  #ifdef AMIX
    #define UNIX_AMIX  # Amiga UNIX
  #endif
  #ifdef __convex__
    #define UNIX_CONVEX  # ConvexOS
  #endif
  #ifdef __MINT__
    #define UNIX_MINT  # MiNT (UNIXlike auf Atari)
  #endif
  #ifdef __CYGWIN32__
    #define UNIX_CYGWIN32  # Cygwin32 (UNIXlike auf WinNT/Win95)
  #endif
#endif
#ifdef DOSPC
  #undef MSDOS  # wg. WATCOM
  #define MSDOS
  #ifdef __EMX__
    #define EMUNIX  # UNIX-Emulation auf MSDOS/OS2-Basis von Eberhard Mattes
    #ifdef OS2
      #define EMUNIX_PORTABEL # ob wir eine zwischen MSDOS und OS2 portable Version machen
    #endif
    # Nur noch emx >= 0.9c wird unterst�tzt.
  #endif
  #ifdef __GO32__
    #define DJUNIX  # UNIX-Emulation auf MSDOS-Basis von D.J. Delorie
  #endif
  #ifdef __WATCOMC__
    #define WATCOM  # Bibliotheksfunktionen von WATCOM C
  #endif
#endif


# Eigenschaften von Compiler und Umgebung abfragen:
#if defined(UNIX)
  #include "unixconf.h"  # von configure erzeugte Konfiguration
  #include "intparam.h"  # von machine erzeugte Integertyp-Charakteristika
#elif defined(AMIGA) || defined(ACORN) || defined(DOSPC) || defined(WIN32)
  #define char_bitsize 8
  #define short_bitsize 16
  #if defined(ACORN) || defined(DOSPC) || defined(WIN32)
    #define int_bitsize 32
  #else
    #define int_bitsize 0 # wird nicht ben�tigt
  #endif
  #if defined(AMIGA) || defined(ACORN) || defined(DOSPC) || (defined(WIN32) && defined(I80386))
    #define long_bitsize 32
  #elif (defined(WIN32) && defined(DECALPHA))
    #define long_bitsize 64
  #endif
  #ifdef __GNUC__
    #if (__GNUC__ >= 2) # GCC 2 hat inzwischen funktionierenden `long long' Typ
      #if !(defined(__m68k__) && (__GNUC_MINOR__ <= 7)) # au�er auf MC680X0
        #define HAVE_LONGLONG
        #define long_long_bitsize 64
      #endif
    #endif
  #endif
  #if defined(AMIGA) || defined(ACORN) || defined(DOSPC) || (defined(WIN32) && defined(I80386))
    #define pointer_bitsize 32
  #elif (defined(WIN32) && defined(DECALPHA))
    #define pointer_bitsize 64
  #endif
  #ifdef MC680X0
    #define alignment_long 2
  #else
    #define alignment_long 4
  #endif
  #ifdef MC680X0
    #define short_big_endian
    #define long_big_endian
  #endif
  #if defined(I80386) || defined(VAX) || defined(ARM) || defined(DECALPHA)
    #define short_little_endian
    #define long_little_endian
  #endif
  #define stack_grows_down
  #define CODE_ADDRESS_RANGE 0
  #define MALLOC_ADDRESS_RANGE 0
  #define SHLIB_ADDRESS_RANGE 0
#endif


# Genauere Klassifikation des Betriebssystems:
  #if defined(UNIX) && defined(SIGNALBLOCK_BSD) && !defined(SIGNALBLOCK_SYSV)
    #define UNIX_BSD  # BSD Unix
  #endif
  #if (defined(SUN3) || defined(SUN386) || defined(SUN4)) && defined(HAVE_MMAP) && defined(HAVE_VADVISE)
    #define UNIX_SUNOS4  # Sun OS Version 4
  #endif
  #if (defined(SUN4) || (defined(I80386) && defined(__svr4__) && (defined(sun) || defined(__sun__)))) && !defined(HAVE_VADVISE) # && !defined(HAVE_GETPAGESIZE)
    #define UNIX_SUNOS5  # Sun OS Version 5.[1-5] (Solaris 2)
  #endif


# Auswahl des Zeichensatzes:
#if defined(UNIX) || defined(AMIGA) || defined(ACORN) || defined(WIN32)
  #define ISOLATIN_CHS  # ISO 8859-1, siehe isolatin.chs
  # Most Unix systems today support the ISO Latin-1 character set, in
  # particular because they have X11 and the X11 fonts are in ISO Latin-1.
  # Exceptions below.
  # On Win32, the standard character set is ISOLATIN_CHS. Only the DOS box
  # displays IBMPC_CHS, but we convert from ISOLATIN_CHS to IBMPC_CHS in the
  # low-level output routine full_write().
#endif
#ifdef HP8XX
  #undef ISOLATIN_CHS
  #define HPROMAN8_CHS  # HP-Roman8, siehe hproman8.chs
  # unter X-Term aber: #define ISOLATIN_CHS ??
#endif
#ifdef UNIX_NEXTSTEP
  #undef ISOLATIN_CHS
  #define NEXTSTEP_CHS  # NeXTstep, siehe nextstep.chs
#endif
#ifdef DOSPC
  #define IBMPC_CHS  # IBM PC, siehe ibmpc.chs
#endif
#if !(defined(ISOLATIN_CHS) || defined(HPROMAN8_CHS) || defined(NEXTSTEP_CHS) || defined(IBMPC_CHS))
  #define ASCII_CHS  # Default: Nur Ascii-Zeichensatz ohne Sonderzeichen
#endif


# Auswahl des Compilers:
#if defined(__GNUC__)
  #define GNU
#endif
#if defined(__STDC__) || defined(__BORLANDC__) || defined(__cplusplus)
  # ANSI C compilers define __STDC__ (but some define __STDC__=0 !).
  # Borland C has an ANSI preprocessor and compiler, but fails to define
  # __STDC__.
  # HP aCC is an example of a C++ compiler which defines __cplusplus but
  # not __STDC__.
  #define ANSI
#endif
#if defined(_MSC_VER)
  #define MICROSOFT
#endif
#if defined(__BORLANDC__)
  #define BORLAND
#endif


# Auswahl der Floating-Point-F�higkeiten:
# FAST_DOUBLE sollte definiert werden, wenn ein Floating-Point-Coprozessor
# vorhanden ist, dessen 'double'-Typ IEEE-Floating-Points mit 64 Bits sind.
# FAST_FLOAT sollte definiert werden, wenn ein Floating-Point-Coprozessor
# vorhanden ist, dessen 'float'-Typ IEEE-Floating-Points mit 32 Bits sind,
# und der C-Compiler auch 'float'- und nicht 'double'-Operationen generiert.
#ifdef SPARC
  #define FAST_DOUBLE
  #define FAST_FLOAT
#endif
#ifdef HPPA
  #define FAST_DOUBLE
  #define FAST_FLOAT
#endif
#ifdef M88000
  #define FAST_DOUBLE
  #define FAST_FLOAT
#endif
#ifdef RS6000
  #define FAST_DOUBLE
  #define FAST_FLOAT
#endif
#if defined(I80386) && (defined(UNIX_LINUX) || defined(UNIX_NEXTSTEP) || defined(UNIX_GNU))
  # Linux hat einen funktionierenden Floating-Point-Coprozessor-Emulator.
  # NeXTstep l�uft sowieso nur mit Floating-Point-Coprozessor.
  # GNU l�uft sowieso nur ab i486, mit eingebautem Floating-Point-Coprozessor.
  # Aber auf Intel-Pentium-Prozessoren ist die FPU fehlerhaft.
  #define FAST_DOUBLE
  #define FAST_FLOAT
#endif
#ifdef ARM
  # Bei Integers ist der Prozessor Little-Endian, bei Double-Floats Big-Endian!
  #undef FAST_DOUBLE
#endif
#ifdef NO_FAST_DOUBLE
  #undef FAST_DOUBLE
#endif
#ifdef NO_FAST_FLOAT
  #undef FAST_FLOAT
#endif


# Auswahl der Sprache:
  #ifdef ENGLISH
    #undef ENGLISH
    #define ENGLISH 1
  #else
    #define ENGLISH 0
  #endif
  #ifdef DEUTSCH
    #undef DEUTSCH
    #define DEUTSCH 1
  #else
    #define DEUTSCH 0
  #endif
  #ifdef FRANCAIS
    #undef FRANCAIS
    #define FRANCAIS 1
  #else
    #define FRANCAIS 0
  #endif
  #if (DEUTSCH+ENGLISH+FRANCAIS > 1)
    #error "Ambiguous choice of language -- Sprache nicht eindeutig!!"
  #endif
  #if (DEUTSCH+ENGLISH+FRANCAIS > 0)
    #define LANGUAGE_STATIC
  #else # noch keine Sprache ausgew�hlt
    #undef ENGLISH
    #undef DEUTSCH
    #undef FRANCAIS
  #endif


# Auswahl der Sicherheitsstufe:
# SAFETY=0 : alle Optimierungen eingeschaltet
# SAFETY=1 : alle Optimierungen, aber noch STACKCHECKs
# SAFETY=2 : nur einfache Assembler-Unterst�tzung
# SAFETY=3 : keine Optimierungen
  #ifndef SAFETY
    #define SAFETY 0
  #endif
  #if SAFETY >= 3
    #define NO_ASM
    #define NO_FAST_DISPATCH
  #endif


# Name des Compilers: siehe constobj.d: software_version_string


# We don't support pre-ANSI-C compilers any more.
#if !defined(ANSI)
  #error "An ANSI C or C++ compiler is required to compile CLISP!"
#endif

# Der Acorn ANSI-C Compiler f�r ARM unter RISCOS hat "char" == "unsigned char".
  #if defined(ARM) && defined(RISCOS) && !defined(GNU)
    #define __CHAR_UNSIGNED__
  #endif

# gcc-2.7.2 has a bug: it interprets `const' as meaning `not modified by
# other parts of the program', and thus miscompiles at least justify_empty_2
# and pr_enter_1 in io.d.
  #if defined(GNU) && (__GNUC__ == 2) && (__GNUC_MINOR__ == 7)
    #undef const
    #define const
    #define __const
    #ifdef MULTITHREAD
      #warning "Multithreading will not be efficient because of a workaround to a gcc bug."
      #warning "Get a newer version of gcc."
    #endif
  #endif

# Eine Eigenschaft des Prozessors:
# Die Reihenfolge, in der Worte/Langworte in Bytes abgelegt werden.
  #if defined(short_little_endian) || defined(int_little_endian) || defined(long_little_endian)
    # Z80, VAX, I80386, DECALPHA, MIPSEL, ...:
    # Low Byte zuunterst, High Byte an h�herer Adresse
    #if defined(BIG_ENDIAN_P)
      #error "Bogus BIG_ENDIAN_P -- BIG_ENDIAN_P neu einstellen!"
    #endif
    #define BIG_ENDIAN_P  0
  #endif
  #if defined(short_big_endian) || defined(int_big_endian) || defined(long_big_endian)
    # MC680X0, SPARC, HPPA, MIPSEB, M88000, RS6000, ...:
    # High Byte zuunterst, Low Byte an h�herer Adresse (leichter zu lesen)
    #if defined(BIG_ENDIAN_P)
      #error "Bogus BIG_ENDIAN_P -- BIG_ENDIAN_P neu einstellen!"
    #endif
    #define BIG_ENDIAN_P  1
  #endif
  #if !defined(BIG_ENDIAN_P)
    #error "Bogus BIG_ENDIAN_P -- BIG_ENDIAN_P neu einstellen!"
  #endif

# A property of the processor (and C compiler): The alignment of C functions.
# (See gcc's machine descriptions, macro FUNCTION_BOUNDARY, for information.)
  #if defined(DECALPHA)
    #define C_CODE_ALIGNMENT  8
    #define log2_C_CODE_ALIGNMENT  3
  #endif
  #if (defined(I80386) && defined(GNU)) || defined(SPARC) || defined(MIPS) || defined(M88000) || defined(RS6000) || defined(ARM)
    # When using gcc on i386, this assumes that -malign-functions has not been
    # used to specify an alignment smaller than 4 bytes.
    #define C_CODE_ALIGNMENT  4
    #define log2_C_CODE_ALIGNMENT  2
  #endif
  #if defined(HPPA)
    # A function pointer on hppa is either
    #   - a code pointer == 0 mod 4, or
    #   - a pointer to a two-word structure (first word: a code pointer,
    #     second word: a value which will be put in register %r19),
    #     incremented by 2, hence == 2 mod 4.
    # The current compilers only emit the second kind of function pointers,
    # hence we can assume that all function pointers are == 2 mod 4.
    #define C_CODE_ALIGNMENT  2
    #define log2_C_CODE_ALIGNMENT  1
  #endif
  #if defined(MC680X0) || defined(CONVEX)
    #define C_CODE_ALIGNMENT  2
    #define log2_C_CODE_ALIGNMENT  1
  #endif
  #if !defined(C_CODE_ALIGNMENT) # e.g. (defined(I80386) && defined(MICROSOFT))
    #define C_CODE_ALIGNMENT  1
    #define log2_C_CODE_ALIGNMENT  0
  #endif


# Flags for the system's include files.
  #ifdef MULTITHREAD
    #if defined(UNIX_LINUX) || defined(UNIX_SUNOS5)
      #define _REENTRANT
    #endif
  #endif


# Width of object representation:
# WIDE means than an object (pointer) occupies 64 bits (instead of 32 bits).
# WIDE_HARD means on a 64-bit platform.
# WIDE_SOFT means on a 32-bit platform, each object pointer occupies 2 words.

#if defined(DECALPHA) || defined(MIPS64)
  #define WIDE_HARD
#endif

#if defined(WIDE) && !(defined(WIDE_HARD) || defined(WIDE_SOFT))
  #define WIDE_SOFT
#endif
#if (defined(WIDE_HARD) || defined(WIDE_SOFT)) && !defined(WIDE)
  #define WIDE
#endif
# Nun ist defined(WIDE) == defined(WIDE_HARD) || defined(WIDE_SOFT)


# Global register declarations.
# They must occur before any system include files define any inline function,
# which is the case on UNIX_DGUX and UNIX_LINUX.
  #if defined(GNU) && !defined(__cplusplus) && !defined(MULTITHREAD) && (SAFETY < 2)
    # Overview of use of registers in gcc terminology:
    # fixed: mentioned in FIXED_REGISTERS
    # used:  mentioned in CALL_USED_REGISTERS but not FIXED_REGISTERS (i.e. caller-saved)
    # save:  otherwise (i.e. call-preserved, callee-saved)
    #
    #               STACK    mv_count  value1   subr_self
    # MC680X0       used
    # I80386        save
    # SPARC         fixed    fixed     fixed    used
    # MIPS
    # HPPA          save     save      save     save
    # M88000        save     save      save
    # ARM           save
    # DECALPHA      save     save      save
    # CONVEX                 used      used     used     (??)
    #
    # Special notes:
    # - If STACK is in a "used"/"save" register, it needs to be saved into
    #   saved_STACK upon begin_call(), so that asynchronous interrupts will
    #   be able to restore it.
    # - All of the "used" registers need to be backuped upon begin_call()
    #   and restored during end_call().
    # - All of the "save" registers need to be backuped upon begin_callback()
    #   and restored during end_callback().
    # - When the interpreter does a longjmp(), the registers STACK, mv_count,
    #   value1 may need to be temporarily saved. This is highly machine
    #   dependent and is indicated by the NEED_temp_xxxx macros.
    # - CONVEX hasn't been tested for a long time.
    #
    # Register for STACK.
      #if defined(MC680X0)
        #define STACK_register  "a4"  # h�chstes Adressregister nach sp=A7,fp=A6/A5
      #endif
      #if defined(I80386) && !defined(DYNAMIC_MODULES)
        # Ist DYNAMIC_MODULES definiert, werden externe Module als PIC
        # compiliert, weswegen dann %ebx schon verbraucht ist.
        #if (__GNUC__ >= 2) # Die Namen der Register haben sich ver�ndert
          #define STACK_register  "%ebx"  # eines der call-saved Register ohne spezielle Hardware-Befehle
        #else
          #define STACK_register  "bx"
        #endif
      #endif
      #if defined(SPARC)
        #define STACK_register  "%g5"  # ein globales Register
      #endif
      #if defined(HPPA) && (__GNUC__*100 + __GNUC_MINOR__ >= 2*100+7) # earlier gcc versions than 2.7 had bugs
        #define STACK_register  "%r10"  # eines der allgemeinen Register %r5..%r18
      #endif
      #if defined(M88000)
        #define STACK_register  "%r14"  # eines der allgemeinen Register %r14..%r25
      #endif
      #if defined(ARM)
        #define STACK_register  "%r8"  # eines der allgemeinen Register %r4..%r8
      #endif
      #if defined(DECALPHA)
        #define STACK_register  "$9"  # eines der allgemeinen Register $9..$14
      #endif
      # What about NEED_temp_STACK ?? Needed if STACK is in a "used" register??
    # Register for mv_count.
      #if defined(SPARC)
        #define mv_count_register  "%g6"
      #endif
      #if defined(HPPA)
        #define mv_count_register  "%r11"  # eines der allgemeinen Register %r5..%r18
        #define NEED_temp_mv_count
      #endif
      #if defined(M88000)
        #define mv_count_register  "%r15"  # eines der allgemeinen Register %r14..%r25
        #define NEED_temp_mv_count
      #endif
      #if defined(DECALPHA)
        #define mv_count_register  "$10"  # eines der allgemeinen Register $9..$14
        #define NEED_temp_mv_count
      #endif
      #if defined(CONVEX)
        #define mv_count_register  "s5"
      #endif
    # Register for value1.
    #if !defined(WIDE_SOFT)
      #if defined(SPARC)
        #define value1_register  "%g7"
      #endif
      #if defined(HPPA)
        #define value1_register  "%r12"  # eines der allgemeinen Register %r5..%r18
        #define NEED_temp_value1
      #endif
      #if defined(M88000)
        #define value1_register  "%r16"  # eines der allgemeinen Register %r14..%r25
        #define NEED_temp_value1
      #endif
      #if defined(DECALPHA)
        #define value1_register  "$11"  # eines der allgemeinen Register $9..$14
        #define NEED_temp_value1
      #endif
      #if defined(CONVEX)
        #define value1_register  "s6"
      #endif
    #endif
    # Register for subr_self.
    #if !defined(WIDE_SOFT)
      #if defined(SPARC)
        #define subr_self_register  "%g4"  # ein globales Register
        # Neuerdings - bei gcc 2.3 - ist %g4 offenbar ein Scratch-Register.
        # Ab libc.so.1.6.1 (in getwd()) macht das Probleme.
        # Deswegen ist oben HAVE_SAVED_subr_self definiert.
      #endif
      #if defined(HPPA)
        #define subr_self_register  "%r13"  # eines der allgemeinen Register %r5..%r18
      #endif
      #if defined(CONVEX)
        #define subr_self_register  "s7"
      #endif
    #endif
    # Declare the registers now (before any system include file which could
    # contain some inline functions).
      #ifdef STACK_register
        register long STACK_reg __asm__(STACK_register);
      #endif
      #ifdef mv_count_register
        register long mv_count_reg __asm__(mv_count_register);
      #endif
      #ifdef value1_register
        register long value1_reg __asm__(value1_register);
      #endif
      #ifdef subr_self_register
        register long subr_self_reg __asm__(subr_self_register);
      #endif
    # Saving "save" registers.
    #if (defined(I80386) && !defined(DYNAMIC_MODULES)) || defined(HPPA) || defined(M88000) || defined(ARM) || defined(DECALPHA)
      #define HAVE_SAVED_REGISTERS
      struct registers
             {
               #ifdef STACK_register
                 long STACK_register_contents;
               #endif
               #ifdef mv_count_register
                 long mv_count_register_contents;
               #endif
               #ifdef value1_register
                 long value1_register_contents;
               #endif
               #ifdef subr_self_register
                 long subr_self_register_contents;
               #endif
             };
      #ifndef MULTITHREAD
        extern struct registers * callback_saved_registers;
      #else
        #define callback_saved_registers  (current_thread()->_callback_saved_registers)
      #endif
      #ifdef STACK_register
        #define SAVE_STACK_register(registers)     registers->STACK_register_contents = STACK_reg;
        #define RESTORE_STACK_register(registers)  STACK_reg = registers->STACK_register_contents;
      #else
        #define SAVE_STACK_register(registers)
        #define RESTORE_STACK_register(registers)
      #endif
      #ifdef mv_count_register
        #define SAVE_mv_count_register(registers)     registers->mv_count_register_contents = mv_count_reg;
        #define RESTORE_mv_count_register(registers)  mv_count_reg = registers->mv_count_register_contents;
      #else
        #define SAVE_mv_count_register(registers)
        #define RESTORE_mv_count_register(registers)
      #endif
      #ifdef value1_register
        #define SAVE_value1_register(registers)     registers->value1_register_contents = value1_reg;
        #define RESTORE_value1_register(registers)  value1_reg = registers->value1_register_contents;
      #else
        #define SAVE_value1_register(registers)
        #define RESTORE_value1_register(registers)
      #endif
      #ifdef subr_self_register
        #define SAVE_subr_self_register(registers)     registers->subr_self_register_contents = subr_self_reg;
        #define RESTORE_subr_self_register(registers)  subr_self_reg = registers->subr_self_register_contents;
      #else
        #define SAVE_subr_self_register(registers)
        #define RESTORE_subr_self_register(registers)
      #endif
      #define SAVE_REGISTERS(inner_statement)  \
        { struct registers * registers = alloca(sizeof(struct registers)); \
          SAVE_STACK_register(registers);                                  \
          SAVE_mv_count_register(registers);                               \
          SAVE_value1_register(registers);                                 \
          SAVE_subr_self_register(registers);                              \
          inner_statement;                                                 \
          { var object* top_of_frame = STACK;                              \
            pushSTACK(as_object((aint)callback_saved_registers));          \
            finish_frame(CALLBACK);                                        \
          }                                                                \
          callback_saved_registers = registers;                            \
        }
      #define RESTORE_REGISTERS(inner_statement)  \
        { struct registers * registers = callback_saved_registers;               \
          if (!(framecode(STACK_0) == CALLBACK_frame_info)) abort();             \
          callback_saved_registers = (struct registers *)(aint)as_oint(STACK_1); \
          skipSTACK(2);                                                          \
          inner_statement;                                                       \
          RESTORE_STACK_register(registers);                                     \
          RESTORE_mv_count_register(registers);                                  \
          RESTORE_value1_register(registers);                                    \
          RESTORE_subr_self_register(registers);                                 \
        }
    #endif
    # Saving the STACK (for asynchronous interrupts).
      # If STACK is a global variable or lies in a register which is left
      # untouched by operating system and library (this is the case on SUN4),
      # we don't need to worry about it.
      #if defined(STACK_register) && !defined(SUN4)
        #define HAVE_SAVED_STACK
      #endif
    # Saving "used" registers.
      #if defined(mv_count_register) && 0
        #define HAVE_SAVED_mv_count
      #endif
      #if defined(value1_register) && 0
        #define HAVE_SAVED_value1
      #endif
      #if defined(subr_self_register) && defined(SPARC)
        #define HAVE_SAVED_subr_self
      #endif
  #endif
  #ifndef HAVE_SAVED_REGISTERS
    #define SAVE_REGISTERS(inner_statement)
    #define RESTORE_REGISTERS(inner_statement)
  #endif


# ###################### Macros zu C ##################### #

#if !defined(UNIXCONF)
  # Um einen Typ vom Wert void weiterzureichen: return_void(...);
  #ifdef GNU
    #define return_void  return # 'return void;' ist zul�ssig
  #else
    # In general it is not legal to return `void' values.
    #define return_void  # Kein 'return' f�r Expressions vom Typ 'void' verwenden.
  #endif
#endif
#if defined(GNU) && defined(__GNUG__)
  # Although legal, g++ warns about 'return void;'. Shut up the warning.
  #undef return_void
  #define return_void
#endif
#if !defined(GNU) && !defined(UNIXCONF)
  #define inline      # inline foo() {...} --> foo() {...}
#endif

# Definitionen f�r C++-Compiler:
#ifdef __cplusplus
  #define BEGIN_DECLS  extern "C" {
  #define END_DECLS    }
#else
  #define BEGIN_DECLS
  #define END_DECLS
#endif

# Leere Macro-Argumente:
# Manche Compiler (z.B. der cc von HP-UX) interpretieren einen Macro-Aufruf
# foo(arg1,...,argn,) offenbar als �quivalent zu foo(arg1,...,argn), was einen
# Fehler ergibt. _EMA_ steht f�r "empty macro argument". Es wird durch
# CC_NEED_DEEMA eingef�gt, jeweils zwischen Komma und schlie�ende Klammer.
# Au�erdem ist es beim Durchreichen m�glicherweise leerer Argumente an andere
# Macros n�tig.
  #define _EMA_

# Zusammenh�ngen zweier macroexpandierter Tokens:
# Beispiel:
#   #undef x
#   #define y 16
#   CONCAT(x,y)        ==>  'x16' (nicht 'xy' !)
  #define CONCAT_(xxx,yyy)  xxx##yyy
  #define CONCAT3_(aaa,bbb,ccc)  aaa##bbb##ccc
  #define CONCAT4_(aaa,bbb,ccc,ddd)  aaa##bbb##ccc##ddd
  #define CONCAT5_(aaa,bbb,ccc,ddd,eee)  aaa##bbb##ccc##ddd##eee
  #define CONCAT6_(aaa,bbb,ccc,ddd,eee,fff)  aaa##bbb##ccc##ddd##eee##fff
  #define CONCAT7_(aaa,bbb,ccc,ddd,eee,fff,ggg)  aaa##bbb##ccc##ddd##eee##fff##ggg
  #define CONCAT(xxx,yyy)  CONCAT_(xxx,yyy)
  #define CONCAT3(aaa,bbb,ccc)  CONCAT3_(aaa,bbb,ccc)
  #define CONCAT4(aaa,bbb,ccc,ddd)  CONCAT4_(aaa,bbb,ccc,ddd)
  #define CONCAT5(aaa,bbb,ccc,ddd,eee)  CONCAT5_(aaa,bbb,ccc,ddd,eee)
  #define CONCAT6(aaa,bbb,ccc,ddd,eee,fff)  CONCAT6_(aaa,bbb,ccc,ddd,eee,fff)
  #define CONCAT7(aaa,bbb,ccc,ddd,eee,fff,ggg)  CONCAT7_(aaa,bbb,ccc,ddd,eee,fff,ggg)

# Generierung von Sprungzielen (goto-Marken) in Macros:
# GENTAG(end)  ==>  end116
# Damit kann ein Macro, der Marken definiert, mehr als einmal pro Funktion,
# aber immer noch nur einmal pro Source-Zeile benutzt werden.
  #define GENTAG(xxx)  CONCAT(xxx,__LINE__)

# Umwandlung von Tokens in Strings:
# STRING(token)  ==>  "token"
#define STRING(token) #token
#define STRINGIFY(token) STRING(token)

# Storage-Class-Specifier in Top-Level-Deklarationen:
# f�r Variablen:
#   global           �berall sichtbare Variable
#   local            nur im File (lokal) sichtbare Variable
#   extern           Verweis auf woanders definierte Variable
# f�r Funktionen:
#   global           �berall sichtbare Funktion
#   local            nur im File (lokal) sichtbare Funktion
#   extern           Verweis auf woanders definierte Funktion
#   extern_C         Verweis auf woanders definierte C-Funktion
#   nonreturning     Funktion, die nie zur�ckkommt
  #define global
  #define local  static
# #define extern extern
  #ifdef __cplusplus
    #define extern_C  extern "C"
  #else
    #define extern_C  extern
  #endif

# Deklaration einer Funktion, die nie zur�ckkommt:
# nonreturning_function(extern,abort,(void)); == extern void abort (void);
  #ifdef GNU
    #if (__GNUC__ == 2) && (__GNUC_MINOR__ >= 90)
      #define nonreturning_function(storclass,funname,arguments)  \
        storclass void funname arguments __attribute__((__noreturn__))
    #else
      #define nonreturning_function(storclass,funname,arguments)  \
        typedef void CONCAT3(funname,_function_,__LINE__) arguments; \
        storclass __volatile__ CONCAT3(funname,_function_,__LINE__) funname
    #endif
  #else
    #define nonreturning_function(storclass,funname,arguments)  \
      storclass void funname arguments
  #endif

# Storage-Class-Specifier in Deklarationen an Blockanf�ngen:
# var                       leitet Variablendeklarationen ein
  #define var

# Adresse des ersten Elements eines Arrays: &!array
# (Wenn klar werden soll, dass man die Adresse des ganzen Arrays �bergibt.
# Wenn man &array schreibt, ist das genau genommen ein Typfehler.)

# Verallgemeinerte if-Anweisung:
# if (cond1) ... {elif (condi) ...} [else ...]
  #define elif  else if

# Endlosschleife, nur mit  break;  oder  return...;  zu verlassen:
  #define loop  while (1)

# Umgekehrte Abbruchbedingung in Schleifen:
# Erlaubt   until (expression) statement
# und       do statement until (expression);
  #define until(expression)  while(!(expression))

# Fallunterscheidung �ber einen Wert >=0
# switchu (expression) ...
  #ifdef GNU # wird so besser optimiert
    #define switchu(expression)  switch ((unsigned int)(expression))
  #else
    #define switchu  switch
  #endif

# Ignorieren eines Wertes (statt einer Zuweisung an eine Variable)
# unused ...
  #ifdef GNU # um eine gcc-Warnung "statement with no effect" zu vermeiden
    #define unused  (void)
  #else
    #define unused
  #endif

# Vertauschen zweier Variableninhalte:  swap(register int, x1, x2);
  #define swap(swap_type,swap_var1,swap_var2)  \
    { var swap_type swap_temp;                                             \
      swap_temp = swap_var1; swap_var1 = swap_var2; swap_var2 = swap_temp; \
    }

# Kennzeichnung einer unerreichten Programmstelle: NOTREACHED
  #define NOTREACHED  fehler_notreached(__FILE__,__LINE__);

# �berpr�fung eines arithmetischen Ausdrucks: ASSERT(expr)
  #define ASSERT(expr)  { if (!(expr)) { NOTREACHED } }

# alloca()
  #if defined(GNU) && !defined(RISCOS) && !defined(CONVEX)
    #define alloca  __builtin_alloca
  #elif defined(MICROSOFT)
    #include <malloc.h>
    #define alloca _alloca
  #elif defined(HAVE_ALLOCA_H) || defined(RISCOS)
    #include <alloca.h>
    #ifndef alloca # Manche definieren 'alloca' als Macro...
      #if !(defined(UNIX_OSF) || defined(UNIX_DEC_ULTRIX) || defined(RISCOS))
        # OSF/1 V3 declares `alloca' as returning char*, but in OSF/1 V4
        # it returns void*. I don't know how to distinguish the two.
        extern_C void* alloca (int size); # siehe MALLOC(3V)
      #endif
    #endif
  #elif defined(_AIX)
    #pragma alloca /* AIX requires this to be the first thing in the file. */
  #elif defined(WATCOM) || defined(BORLAND)
    #include <malloc.h> # definiert 'alloca' als Macro
  #elif !defined(NO_ALLOCA)
    extern_C void* alloca (int size); # siehe MALLOC(3V)
  #endif

# Synonym f�r Byte, Word, Longword:
# SBYTE   = signed 8 bit integer
# UBYTE   = unsigned 8 bit int
# SWORD   = signed 16 bit int
# UWORD   = unsigned 16 bit int
# SLONG   = signed 32 bit int
# ULONG   = unsigned 32 bit int
# Hingegen wird "char" nur in der Bedeutung eines Elements eines Strings
# verwendet. Nie wird mit einem "char" wirklich gerechnet; das k�nnte von
# __CHAR_UNSIGNED__ abh�ngen!
  #if (char_bitsize==8)
    #ifdef __CHAR_UNSIGNED__
      typedef signed char  SBYTE;
    #else
      typedef char         SBYTE;
    #endif
    typedef unsigned char  UBYTE;
  #else
    #error "No 8 bit integer type? -- Welcher Integer-Typ hat 8 Bit?"
  #endif
  #if (short_bitsize==16)
    typedef short          SWORD;
    typedef unsigned short UWORD;
  #else
    #error "No 16 bit integer type? -- Welcher Integer-Typ hat 16 Bit?"
  #endif
  #if (long_bitsize==32)
    typedef long           SLONG;
    typedef unsigned long  ULONG;
  #elif (int_bitsize==32)
    typedef int            SLONG;
    typedef unsigned int   ULONG;
  #else
    #error "No 32 bit integer type? -- Welcher Integer-Typ hat 32 Bit?"
  #endif
  #if (long_bitsize==64)
    typedef long           SLONGLONG;
    typedef unsigned long  ULONGLONG;
    #undef HAVE_LONGLONG
    #define HAVE_LONGLONG
  #elif defined(HAVE_LONGLONG)
   #if defined(long_long_bitsize) && (long_long_bitsize==64)
    typedef long long           SLONGLONG;
    typedef unsigned long long  ULONGLONG;
   #else # unbrauchbarer Typ
    #undef HAVE_LONGLONG
   #endif
  #elif defined(MICROSOFT)
    typedef __int64           SLONGLONG;
    typedef unsigned __int64  ULONGLONG;
    #define HAVE_LONGLONG
  #endif
  #if defined(WIDE) && !defined(HAVE_LONGLONG)
    #error "No 64 bit integer type? -- Welcher Integer-Typ hat 64 Bit?"
  #endif

# Wahrheitswerte:
  #define TRUE   1
  #define FALSE  0
  typedef unsigned int  boolean;

# Typ f�r Vorzeichenwerte, Vergleichsergebnisse, dreiwertige enum's
# mit Werten +1, 0, -1
  typedef signed int  signean;
  #define signean_plus    1 # +1
  #define signean_null    0 #  0
  #define signean_minus  -1 # -1

# Nullpointer
  #undef NULL  # wg. WATCOM
  #ifdef __cplusplus
    #define NULL  0
  #else
    #define NULL  ((void*) 0L)
  #endif

# Den Offset einer Komponente 'ident' in einem Struct vom Typ 'type' bestimmen:
# 0 als Pointer auf 'type' auffassen, dorthin ein Struct 'type' legen und
# von dessen Komponente 'ident' die Adresse bestimmen und als Zahl liefern:
  #if !(defined(HAVE_OFFSETOF) || (defined(BORLAND) && defined(WIN32)))
    #undef offsetof
    #define offsetof(type,ident)  ((ULONG)&(((type*)0)->ident))
  #else
    #include <stddef.h>
  #endif
# Den Offset eines Arrays 'ident' in einem Struct vom Typ 'type' bestimmen:
  #define offsetofa(type,ident)  offsetof(type,ident[0])

# Unspezifizierte L�nge von Arrays in Structures:
# struct { ...; ...; type x[unspecified]; }
# Statt sizeof(..) muss man dann aber immer offsetof(..,x) schreiben.
  #if defined(GNU) # GNU-C kann Arrays der L�nge 0
    #define unspecified 0
  #elif 0
    # �blicherweise l�sst man die Arraygrenze weg:
    #define unspecified
  #else
    # Jedoch die HP-UX- und IRIX-Compiler lassen sich nur damit befriedigen:
    #define unspecified 1
  #endif

# Pointer-Arithmetik: einen gegebenen Offset (gemessen in Bytes)
# zu einem Pointer addieren.
  #if !(defined(GNU) || (pointer_bitsize > 32))
    # Billige Methode:
    #define pointerplus(pointer,offset)  ((void*)((ULONG)(pointer)+(offset)))
  #else
    # F�r GNU-C beim Initialisieren von static-Variablen unerl�sslich
    # (muss ein Bug in 'c-typeck.c' in 'initializer_constant_valid_p' sein):
    # Das einzig Richtige, falls sizeof(ULONG) < sizeof(void*):
    #define pointerplus(pointer,offset)  ((UBYTE*)(pointer)+(offset))
  #endif

# Bit Nummer n (0<=n<32)
  #define bit(n)  (1L<<(n))
# Bit Nummer n (0<n<=32) mod 2^32
  #define bitm(n)  (2L<<((n)-1))
# Bit-Test von Bit n in x, n konstant, x ein oint:
  #if !defined(SPARC)
    #define bit_test(x,n)  ((x) & bit(n))
  #else
    # Auf SPARC-Prozessoren sind lange Konstanten langsamer als Shifts.
    #if !defined(GNU)
      #define bit_test(x,n)  \
        ((n)<12 ? ((x) & bit(n)) : ((sint32)((uint32)(x) << (31-(n))) < 0))
    #else # der GNU-Compiler optimiert boolean-Expressions so besser:
      #define bit_test(x,n)  \
        (   ( ((n)<12) && ((x) & bit(n)) )                           \
         || ( ((n)>=12) && ((sint32)((uint32)(x) << (31-(n))) < 0) ) \
        )
    #endif
  #endif
# Minus Bit Nummer n (0<=n<32)
  #define minus_bit(n)  (-1L<<(n))
# Minus Bit Nummer n (0<n<=32) mod 2^32
  #define minus_bitm(n)  (-2L<<((n)-1))

# floor(a,b) liefert f�r a>=0, b>0  floor(a/b).
# b sollte eine 'constant expression' sein.
  #define floor(a_from_floor,b_from_floor)  ((a_from_floor) / (b_from_floor))

# ceiling(a,b) liefert f�r a>=0, b>0  ceiling(a/b) = floor((a+b-1)/b).
# b sollte eine 'constant expression' sein.
  #define ceiling(a_from_ceiling,b_from_ceiling)  \
    (((a_from_ceiling) + (b_from_ceiling) - 1) / (b_from_ceiling))

# round_down(a,b) rundet a>=0 so ab, dass es durch b>0 teilbar ist.
# b sollte eine 'constant expression' sein.
  #define round_down(a_from_round,b_from_round)  \
    (floor(a_from_round,b_from_round)*(b_from_round))

# round_up(a,b) rundet a>=0 so auf, dass es durch b>0 teilbar ist.
# b sollte eine 'constant expression' sein.
  #define round_up(a_from_round,b_from_round)  \
    (ceiling(a_from_round,b_from_round)*(b_from_round))

# nicht-lokale Ausg�nge
  #include <setjmp.h>
  #if defined(UNIX) && defined(HAVE__JMP) && !defined(UNIX_LINUX) && !defined(UNIX_GNU)
    # Folgende Routinen sind effizienter (hantieren nicht mit Signal-Masken):
    #undef setjmp
    #undef longjmp
    #define setjmp  _setjmp
    #define longjmp  _longjmp
    #ifdef LONGJMP_RETURNS
      # _longjmp(jmpbuf,value) kann zur�ckkehren, wenn jmpbuf ung�ltig ist.
      #undef longjmp
      #define longjmp(x,y)  (_longjmp(x,y), fehler_notreached(__FILE__,__LINE__))
    #endif
  #endif
# Mit longjmp() kann man nur ein `int' �bergeben.
# Wenn wir nun ein `long' �bergeben wollen und sizeof(int) < sizeof(long) ist,
# brauchen wir eine globale Variable:
  #if (int_bitsize == long_bitsize)
    #define setjmpl(x)  setjmp(x)
    #define longjmpl(x,y)  longjmp(x,y)
  #else # (int_bitsize < long_bitsize)
    extern long jmpl_value;
    #define setjmpl(x)  (setjmp(x) ? jmpl_value : 0)
    #define longjmpl(x,y)  (jmpl_value = (y), longjmp(x,1))
  #endif

# Dynamisch allozierte Arrays mit dynamic extent:
# Beispiel:
#     { var DYNAMIC_ARRAY(my_array,uintL,n);
#       ...
#       FREE_DYNAMIC_ARRAY(my_array);
#     }
# Vorsicht: Je nach Implementierung ist my_array entweder der Array selbst
# oder ein Pointer auf den Array! Immer nur my_array als Expression verwenden!
  #if defined(GNU)
    # verkraftet dynamisch allozierte Arrays im Maschinenstack
    # { var uintL my_array[n]; ... }
    #define DYNAMIC_ARRAY(arrayvar,arrayeltype,arraysize)  \
      arrayeltype arrayvar[arraysize]
    #define FREE_DYNAMIC_ARRAY(arrayvar)
    #ifdef DECALPHA # GCC 2.5.5 Bug umgehen
      #undef DYNAMIC_ARRAY
      #define DYNAMIC_ARRAY(arrayvar,arrayeltype,arraysize)  \
        arrayeltype arrayvar[(arraysize)+1]
    #endif
  #elif (defined(UNIX) && (defined(HAVE_ALLOCA_H) || defined(_AIX) || !defined(NO_ALLOCA))) || defined(WATCOM) || defined(BORLAND) || defined(MICROSOFT) || defined(RISCOS)
    # Platz im Maschinenstack reservieren.
    # { var uintL* my_array = (uintL*)alloca(n*sizeof(uintL)); ... }
    #define DYNAMIC_ARRAY(arrayvar,arrayeltype,arraysize)  \
      arrayeltype* arrayvar = (arrayeltype*)alloca((arraysize)*sizeof(arrayeltype))
    #define FREE_DYNAMIC_ARRAY(arrayvar)
    # kein Errorcheck??
  #else
    # Platz woanders reservieren und dann wieder freigeben.
    # { var uintL* my_array = (uintL*)malloc(n*sizeof(uintL)); ... free(my_array); }
    #ifdef HAVE_STDLIB_H
      #include <stdlib.h>
    #else
      #include <sys/types.h>
    #endif
    #ifndef malloc
      extern_C void* malloc (size_t size); # siehe MALLOC(3V)
    #endif
    #ifndef free
      extern_C void free (void* ptr); # siehe MALLOC(3V)
    #endif
    #define NEED_MALLOCA
    extern void* malloca (size_t size); # siehe SPVW.D
    extern void freea (void* ptr); # siehe SPVW.D
    #define DYNAMIC_ARRAY(arrayvar,arrayeltype,arraysize)  \
      arrayeltype* arrayvar = (arrayeltype*)malloca((arraysize)*sizeof(arrayeltype))
    #define FREE_DYNAMIC_ARRAY(arrayvar)  freea(arrayvar)
  #endif

# Signed/Unsigned-Integer-Typen mit vorgegebener Mindestgr��e:
  typedef UBYTE   uint1;   # unsigned 1 bit Integer
  typedef SBYTE   sint1;   # signed 1 bit Integer
  typedef UBYTE   uint2;   # unsigned 2 bit Integer
  typedef SBYTE   sint2;   # signed 2 bit Integer
  typedef UBYTE   uint3;   # unsigned 3 bit Integer
  typedef SBYTE   sint3;   # signed 3 bit Integer
  typedef UBYTE   uint4;   # unsigned 4 bit Integer
  typedef SBYTE   sint4;   # signed 4 bit Integer
  typedef UBYTE   uint5;   # unsigned 5 bit Integer
  typedef SBYTE   sint5;   # signed 5 bit Integer
  typedef UBYTE   uint6;   # unsigned 6 bit Integer
  typedef SBYTE   sint6;   # signed 6 bit Integer
  typedef UBYTE   uint7;   # unsigned 7 bit Integer
  typedef SBYTE   sint7;   # signed 7 bit Integer
  typedef UBYTE   uint8;   # unsigned 8 bit Integer
  typedef SBYTE   sint8;   # signed 8 bit Integer
  typedef UWORD   uint9;   # unsigned 9 bit Integer
  typedef SWORD   sint9;   # signed 9 bit Integer
  typedef UWORD   uint10;  # unsigned 10 bit Integer
  typedef SWORD   sint10;  # signed 10 bit Integer
  typedef UWORD   uint11;  # unsigned 11 bit Integer
  typedef SWORD   sint11;  # signed 11 bit Integer
  typedef UWORD   uint12;  # unsigned 12 bit Integer
  typedef SWORD   sint12;  # signed 12 bit Integer
  typedef UWORD   uint13;  # unsigned 13 bit Integer
  typedef SWORD   sint13;  # signed 13 bit Integer
  typedef UWORD   uint14;  # unsigned 14 bit Integer
  typedef SWORD   sint14;  # signed 14 bit Integer
  typedef UWORD   uint15;  # unsigned 15 bit Integer
  typedef SWORD   sint15;  # signed 15 bit Integer
  typedef UWORD   uint16;  # unsigned 16 bit Integer
  typedef SWORD   sint16;  # signed 16 bit Integer
  typedef ULONG   uint17;  # unsigned 17 bit Integer
  typedef SLONG   sint17;  # signed 17 bit Integer
  typedef ULONG   uint18;  # unsigned 18 bit Integer
  typedef SLONG   sint18;  # signed 18 bit Integer
  typedef ULONG   uint19;  # unsigned 19 bit Integer
  typedef SLONG   sint19;  # signed 19 bit Integer
  typedef ULONG   uint20;  # unsigned 20 bit Integer
  typedef SLONG   sint20;  # signed 20 bit Integer
  typedef ULONG   uint21;  # unsigned 21 bit Integer
  typedef SLONG   sint21;  # signed 21 bit Integer
  typedef ULONG   uint22;  # unsigned 22 bit Integer
  typedef SLONG   sint22;  # signed 22 bit Integer
  typedef ULONG   uint23;  # unsigned 23 bit Integer
  typedef SLONG   sint23;  # signed 23 bit Integer
  typedef ULONG   uint24;  # unsigned 24 bit Integer
  typedef SLONG   sint24;  # signed 24 bit Integer
  typedef ULONG   uint25;  # unsigned 25 bit Integer
  typedef SLONG   sint25;  # signed 25 bit Integer
  typedef ULONG   uint26;  # unsigned 26 bit Integer
  typedef SLONG   sint26;  # signed 26 bit Integer
  typedef ULONG   uint27;  # unsigned 27 bit Integer
  typedef SLONG   sint27;  # signed 27 bit Integer
  typedef ULONG   uint28;  # unsigned 28 bit Integer
  typedef SLONG   sint28;  # signed 28 bit Integer
  typedef ULONG   uint29;  # unsigned 29 bit Integer
  typedef SLONG   sint29;  # signed 29 bit Integer
  typedef ULONG   uint30;  # unsigned 30 bit Integer
  typedef SLONG   sint30;  # signed 30 bit Integer
  typedef ULONG   uint31;  # unsigned 31 bit Integer
  typedef SLONG   sint31;  # signed 31 bit Integer
  typedef ULONG   uint32;  # unsigned 32 bit Integer
  typedef SLONG   sint32;  # signed 32 bit Integer
  #ifdef HAVE_LONGLONG
  typedef ULONGLONG  uint33;  # unsigned 33 bit Integer
  typedef SLONGLONG  sint33;  # signed 33 bit Integer
  typedef ULONGLONG  uint48;  # unsigned 48 bit Integer
  typedef SLONGLONG  sint48;  # signed 48 bit Integer
  typedef ULONGLONG  uint64;  # unsigned 64 bit Integer
  typedef SLONGLONG  sint64;  # signed 64 bit Integer
  #endif
  #define exact_uint_size_p(n) (((n)==char_bitsize)||((n)==short_bitsize)||((n)==int_bitsize)||((n)==long_bitsize))
  #define signed_int_with_n_bits(n) CONCAT(sint,n)
  #define unsigned_int_with_n_bits(n) CONCAT(uint,n)
# Verwende 'uintn' und 'sintn' f�r Integers mit genau vorgegebener Breite.
# exact_uint_size_p(n) gibt an, ob der uint mit n Bits auch wirklich
# nur n Bits hat.

# Ab hier bedeuten 'uintX' und 'sintX' unsigned bzw. signed integer -
# Typen der Wortbreite X (X=B,W,L,Q).
  #define intBsize 8
  typedef signed_int_with_n_bits(intBsize)    sintB;
  typedef unsigned_int_with_n_bits(intBsize)  uintB;
  #define intWsize 16
  typedef signed_int_with_n_bits(intWsize)    sintW;
  typedef unsigned_int_with_n_bits(intWsize)  uintW;
  #define intLsize 32
  typedef signed_int_with_n_bits(intLsize)    sintL;
  typedef unsigned_int_with_n_bits(intLsize)  uintL;
  #if defined(DECALPHA) || defined(MIPS64)
    # Maschine hat echte 64-Bit-Zahlen in Hardware.
    #define intQsize 64
    typedef signed_int_with_n_bits(intQsize)    sintQ;
    typedef unsigned_int_with_n_bits(intQsize)  uintQ;
    typedef sintQ  sintL2;
    typedef uintQ  uintL2;
  #else
    # Emuliere 64-Bit-Zahlen mit Hilfe von zwei 32-Bit-Zahlen.
    typedef struct { sintL hi; uintL lo; } sintL2; # signed integer mit 64 Bit
    typedef struct { uintL hi; uintL lo; } uintL2; # unsigned integer mit 64 Bit
  #endif
# Verwende 'uintX' und 'sintX' f�r Integers mit ungef�hr vorgegebener Breite
# und m�glichst geringem Speicherplatz.

# Ab hier bedeuten 'uintP' und 'sintP' unsigned bzw. signed integer - Typen,
# die so breit sind wie ein void* - Pointer.
  typedef signed_int_with_n_bits(pointer_bitsize)    sintP;
  typedef unsigned_int_with_n_bits(pointer_bitsize)  uintP;

# Ab hier bedeuten 'uintXY' und 'sintXY' unsigned bzw. signed integer -
# Typen der Wortbreite X oder Y (X,Y=B,W,L).
  #if (defined(MC680X0) && !defined(HPUX_ASSEMBLER)) || defined(VAX)
    # Der 68000 hat gute uintB-, uintW-, uintL-Verarbeitung, insbesondere
    # DBRA-Befehle f�r uintW.
    #define intBWsize intBsize
    #define intWLsize intWsize
    #define intBWLsize intBsize
  #elif (defined(MC680X0) && defined(HPUX_ASSEMBLER)) || defined(SPARC) || defined(HPPA) || defined(MIPS) || defined(M88000) || defined(RS6000) || defined(CONVEX)
    # Der Sparc-Prozessor kann mit uintB und uintW schlecht rechnen.
    # Anderen 32-Bit-Prozessoren geht es genauso.
    #define intBWsize intWsize
    #define intWLsize intLsize
    #define intBWLsize intLsize
  #elif defined(I80386)
    # Wird auf einem 80386 mit uintB und uintW gerechnet, so gibt das viele
    # Zero-Extends, die - da es zu wenig Register gibt - andere Variablen
    # unn�tigerweise in den Speicher schieben.
    #define intBWsize intWsize
    #define intWLsize intLsize
    #define intBWLsize intLsize
  #elif defined(ARM)
    # Der ARM kann mit uintB und uintW sehr schlecht rechnen.
    #define intBWsize intBsize
    #define intWLsize intLsize
    #define intBWLsize intLsize
  #elif defined(DECALPHA)
    # Auch 64-Bit-Prozessoren k�nnen mit uintB und uintW schlecht rechnen.
    #define intBWsize intWsize
    #define intWLsize intLsize
    #define intBWLsize intLsize
  #else
    #error "Preferred integer sizes depend on CPU -- Gr��en intBWsize, intWLsize, intBWLsize neu einstellen!"
  #endif
  typedef signed_int_with_n_bits(intBWsize)    sintBW;
  typedef unsigned_int_with_n_bits(intBWsize)  uintBW;
  typedef signed_int_with_n_bits(intWLsize)    sintWL;
  typedef unsigned_int_with_n_bits(intWLsize)  uintWL;
  typedef signed_int_with_n_bits(intBWLsize)    sintBWL;
  typedef unsigned_int_with_n_bits(intBWLsize)  uintBWL;
# Verwende 'uintXY' und 'sintXY' f�r Integers mit vorgegebener Mindestbreite,
# mit denen sich leicht rechnen l�sst.

# Schleife, die ein Statement eine gewisse Anzahl mal ausf�hrt:
# dotimesW(countvar,count,statement);  falls count in ein uintW passt,
# dotimesL(countvar,count,statement);  falls count nur in ein uintL passt,
# dotimespW(countvar,count,statement);  falls count in ein uintW passt und >0 ist,
# dotimespL(countvar,count,statement);  falls count nur in ein uintL passt und >0 ist.
# Die Variable countvar muss bereits deklariert sein, vom Typ uintW bzw. uintL
# und wird durch diese Anweisung ver�ndert!
# Sie darf in statement nicht verwendet werden!
# Die Expression count wird nur einmal (zu Beginn) ausgewertet.
  #if defined(GNU) && defined(MC680X0) && !defined(HPUX_ASSEMBLER)
    # GNU-C auf einem 680X0 l�sst sich dazu �berreden, den DBRA-Befehl zu verwenden:
    #define fast_dotimesW
    # Um zu entscheiden, wie man GNU-C am besten dazu �berredet, betrachte man
    # den Code, der f�r spvw.d:gc_markphase() produziert wird.
    # Oder ein kleines Testprogramm (dbratest.c), das mit
    # "gcc -O6 -da -S dbratest.c" compiliert wird, und betrachte dbratest.s
    # und dbratest.c.flow sowie dbratest.c.combine.
    #if (__GNUC__<2) # GNU C Version 1
      #define dotimesW_(countvar_from_dotimesW,count_from_dotimesW,statement_from_dotimesW)  \
        { countvar_from_dotimesW = (count_from_dotimesW);     \
          if (!(countvar_from_dotimesW==0))                   \
            { countvar_from_dotimesW--;                       \
              do {statement_from_dotimesW}                    \
                 until ((sintW)--countvar_from_dotimesW==-1); \
        }   }
      #define dotimespW_(countvar_from_dotimespW,count_from_dotimespW,statement_from_dotimespW)  \
        { countvar_from_dotimespW = (count_from_dotimespW)-1;                         \
          do {statement_from_dotimespW} until ((sintW)--countvar_from_dotimespW==-1); \
        }
    #else
      #define dotimesW_(countvar_from_dotimesW,count_from_dotimesW,statement_from_dotimesW)  \
        { countvar_from_dotimesW = (count_from_dotimesW);        \
          if (!(countvar_from_dotimesW==0))                      \
            { countvar_from_dotimesW--;                          \
              do {statement_from_dotimesW}                       \
                 until ((sintW)(--countvar_from_dotimesW)+1==0); \
        }   }
      #define dotimespW_(countvar_from_dotimespW,count_from_dotimespW,statement_from_dotimespW)  \
        { countvar_from_dotimespW = (count_from_dotimespW)-1;                            \
          do {statement_from_dotimespW} until ((sintW)(--countvar_from_dotimespW)+1==0); \
        }
    #endif
  #else
    #define dotimesW_(countvar_from_dotimesW,count_from_dotimesW,statement_from_dotimesW)  \
      { countvar_from_dotimesW = (count_from_dotimesW);         \
        until (countvar_from_dotimesW==0)                       \
          {statement_from_dotimesW; countvar_from_dotimesW--; } \
      }
    #define dotimespW_(countvar_from_dotimespW,count_from_dotimespW,statement_from_dotimespW)  \
      { countvar_from_dotimespW = (count_from_dotimespW);                   \
        do {statement_from_dotimespW} until (--countvar_from_dotimespW==0); \
      }
  #endif
  #if defined(GNU) && defined(MC680X0) && !defined(HPUX_ASSEMBLER)
    # GNU-C auf einem 680X0 l�sst sich dazu �berreden, den DBRA-Befehl
    # auf intelligente Weise zu verwenden:
    #define fast_dotimesL
    #define dotimesL_(countvar_from_dotimesL,count_from_dotimesL,statement_from_dotimesL)  \
      { countvar_from_dotimesL = (count_from_dotimesL);           \
        if (!(countvar_from_dotimesL==0))                         \
          { countvar_from_dotimesL--;                             \
            do {statement_from_dotimesL}                          \
               until ((sintL)(--countvar_from_dotimesL) == -1);   \
      }   }
    #define dotimespL_(countvar_from_dotimespL,count_from_dotimespL,statement_from_dotimespL)  \
      { countvar_from_dotimespL = (count_from_dotimespL)-1;                             \
        do {statement_from_dotimespL} until ((sintL)(--countvar_from_dotimespL) == -1); \
      }
  #endif
  #ifndef dotimesL_
    #define dotimesL_(countvar_from_dotimesL,count_from_dotimesL,statement_from_dotimesL)  \
      { countvar_from_dotimesL = (count_from_dotimesL);         \
        until (countvar_from_dotimesL==0)                       \
          {statement_from_dotimesL; countvar_from_dotimesL--; } \
      }
    #define dotimespL_(countvar_from_dotimespL,count_from_dotimespL,statement_from_dotimespL)  \
      { countvar_from_dotimespL = (count_from_dotimespL);                   \
        do {statement_from_dotimespL} until (--countvar_from_dotimespL==0); \
      }
  #endif
  #if defined(GNU) && defined(__OPTIMIZE__)
    # Es ist mir nun schon zweimal passiert, dass ich dotimesL auf eine
    # Variable vom Typ uintC angewandt habe. Damit J�rg und Marcus nicht
    # mehr suchen m�ssen, �berpr�fe ich das jetzt.
    # Der Dummy-Aufruf wird, wenn's gut geht, von gcc wegoptimiert.
    # Ansonsten bekommt man einen Fehler beim Linken.
    #define dotimes_check_sizeof(countvar,type)  \
      if (!(sizeof(countvar)==sizeof(type))) { dotimes_called_with_count_of_wrong_size(); }
    extern void dotimes_called_with_count_of_wrong_size (void); # nicht existente Funktion
  #else
    #define dotimes_check_sizeof(countvar,type)
  #endif
  #define dotimesW(countvar_from_dotimesW,count_from_dotimesW,statement_from_dotimesW) \
    { dotimes_check_sizeof(countvar_from_dotimesW,uintW); \
      dotimesW_(countvar_from_dotimesW,count_from_dotimesW,statement_from_dotimesW); \
    }
  #define dotimespW(countvar_from_dotimespW,count_from_dotimespW,statement_from_dotimespW) \
    { dotimes_check_sizeof(countvar_from_dotimespW,uintW); \
      dotimespW_(countvar_from_dotimespW,count_from_dotimespW,statement_from_dotimespW); \
    }
  #define dotimesL(countvar_from_dotimesL,count_from_dotimesL,statement_from_dotimesL) \
    { dotimes_check_sizeof(countvar_from_dotimesL,uintL); \
      dotimesL_(countvar_from_dotimesL,count_from_dotimesL,statement_from_dotimesL); \
    }
  #define dotimespL(countvar_from_dotimespL,count_from_dotimespL,statement_from_dotimespL) \
    { dotimes_check_sizeof(countvar_from_dotimespL,uintL); \
      dotimespL_(countvar_from_dotimespL,count_from_dotimespL,statement_from_dotimespL); \
    }
# doconsttimes(count,statement);
# f�hrt statement count mal aus (count mal der Code!),
# wobei count eine constant-expression >=0, <=8 ist.
  #define doconsttimes(count_from_doconsttimes,statement_from_doconsttimes)  \
    { if (0 < (count_from_doconsttimes)) { statement_from_doconsttimes; } \
      if (1 < (count_from_doconsttimes)) { statement_from_doconsttimes; } \
      if (2 < (count_from_doconsttimes)) { statement_from_doconsttimes; } \
      if (3 < (count_from_doconsttimes)) { statement_from_doconsttimes; } \
      if (4 < (count_from_doconsttimes)) { statement_from_doconsttimes; } \
      if (5 < (count_from_doconsttimes)) { statement_from_doconsttimes; } \
      if (6 < (count_from_doconsttimes)) { statement_from_doconsttimes; } \
      if (7 < (count_from_doconsttimes)) { statement_from_doconsttimes; } \
    }
# DOCONSTTIMES(count,macroname);
# ruft count mal den Macro macroname auf (count mal der Code!),
# wobei count eine constant-expression >=0, <=8 ist.
# Dabei bekommt macroname der Reihe nach die Werte 0,...,count-1 �bergeben.
  #define DOCONSTTIMES(count_from_DOCONSTTIMES,macroname_from_DOCONSTTIMES)  \
    { if (0 < (count_from_DOCONSTTIMES)) { macroname_from_DOCONSTTIMES((0 < (count_from_DOCONSTTIMES) ? 0 : 0)); } \
      if (1 < (count_from_DOCONSTTIMES)) { macroname_from_DOCONSTTIMES((1 < (count_from_DOCONSTTIMES) ? 1 : 0)); } \
      if (2 < (count_from_DOCONSTTIMES)) { macroname_from_DOCONSTTIMES((2 < (count_from_DOCONSTTIMES) ? 2 : 0)); } \
      if (3 < (count_from_DOCONSTTIMES)) { macroname_from_DOCONSTTIMES((3 < (count_from_DOCONSTTIMES) ? 3 : 0)); } \
      if (4 < (count_from_DOCONSTTIMES)) { macroname_from_DOCONSTTIMES((4 < (count_from_DOCONSTTIMES) ? 4 : 0)); } \
      if (5 < (count_from_DOCONSTTIMES)) { macroname_from_DOCONSTTIMES((5 < (count_from_DOCONSTTIMES) ? 5 : 0)); } \
      if (6 < (count_from_DOCONSTTIMES)) { macroname_from_DOCONSTTIMES((6 < (count_from_DOCONSTTIMES) ? 6 : 0)); } \
      if (7 < (count_from_DOCONSTTIMES)) { macroname_from_DOCONSTTIMES((7 < (count_from_DOCONSTTIMES) ? 7 : 0)); } \
    }

# Ab hier bedeutet uintC einen unsigned-Integer-Typ, mit dem sich besonders
# leicht z�hlen l�sst. Teilmengenrelation: uintW <= uintC <= uintL.
  #define intCsize intWLsize
  #define uintC uintWL
  #define sintC sintWL
  #if (intCsize==intWsize)
    #define dotimesC dotimesW
    #define dotimespC dotimespW
  #endif
  #if (intCsize==intLsize)
    #define dotimesC dotimesL
    #define dotimespC dotimespL
  #endif
# Verwende 'uintC' f�r Z�hler, die meist klein sind.

# Die Arithmetik benutzt "Digit Sequences" aus "Digits".
# Das sind unsigned ints mit intDsize Bits (sollte =8 oder =16 oder =32 sein).
# Falls HAVE_DD: "Doppel-Digits" sind unsigned ints mit 2*intDsize<=32 Bits.
  #if defined(MC680X0) && !defined(MC680Y0)
    #define intDsize 16
    #define intDDsize 32  # = 2*intDsize
    #define log2_intDsize  4  # = log2(intDsize)
  #elif defined(MC680Y0) || defined(I80386) || defined(SPARC) || defined(HPPA) || defined(MIPS) || defined(M88000) || defined(RS6000) || defined(VAX) || defined(CONVEX) || defined(ARM) || defined(DECALPHA)
    #define intDsize 32
    #define intDDsize 64  # = 2*intDsize
    #define log2_intDsize  5  # = log2(intDsize)
  #else
    #error "Preferred digit size depends on CPU -- Gr��e intDsize neu einstellen!"
  #endif
  typedef unsigned_int_with_n_bits(intDsize)  uintD;
  typedef signed_int_with_n_bits(intDsize)    sintD;
  #if (intDDsize<=32) || ((intDDsize<=64) && (defined(DECALPHA) || defined(MIPS64)))
    #define HAVE_DD 1
    typedef unsigned_int_with_n_bits(intDDsize)  uintDD;
    typedef signed_int_with_n_bits(intDDsize)    sintDD;
  #else
    #define HAVE_DD 0
  #endif

# Auch einige andere K�rzel wie 'oint', 'tint', 'aint', 'cint' werden noch
# f�r entsprechende Integer-Typen verwendet werden:
#   Integertyp     enth�lt Information �quivalent zu
#      oint           LISP-Objekt
#      tint           Typcode eines LISP-Objekts
#      aint           Adresse eines LISP-Objekts
#      cint           LISP-Character

# �blicherweise ist sizeof(oint) = sizeof(aint) = sizeof(uintL) = 32 Bit.
# Bei Modell WIDE ist sizeof(oint) > sizeof(uintL).
# Modell WIDE_HARD steht f�r sizeof(aint) > sizeof(uintL).
#   Dieses Modell muss dann gew�hlt werden, wenn
#   sizeof(void*) > sizeof(uintL) = 32 Bit ist. Es setzt
#   sizeof(long) = sizeof(void*) = 64 Bit voraus, denn einige 64-Bit-Zahlen
#   tauchen als Pr�prozessor-Konstanten auf.
# Modell WIDE_SOFT steht f�r sizeof(oint) = 64 Bit und sizeof(aint) = 32 Bit.
#   Dieses Modell kann auf jeder 32-Bit-Maschine gew�hlt werden, wenn der
#   Compiler (soft- oder hardwarem��ige) 64-Bit-Zahlen hat. Es muss dann
#   gew�hlt werden, wenn ansonsten nicht genug Platz f�r die Typbits in einem
#   32-Bit-Pointer w�re.
# Model NO_TYPECODES stands for sizeof(oint) = sizeof(aint), and only minimal
#   type information is stored in a pointer. All heap allocated objects
#   (except conses) must contain the complete type and a length field in the
#   first word. The heap gets somewhat bigger by this, and type tests require
#   more memory accesses on average. But this model is portable even to
#   systems whose memory map looks like Swiss Cheese.

#if defined(WIDE_SOFT) && defined(NO_TYPECODES)
  #error "WIDE and NO_TYPECODES make no sense together, no need for WIDE"
#endif

#if !(defined(TYPECODES) || defined(NO_TYPECODES))
  # Choose typecodes on 64-bit machines (because there's enough room for type
  # bits), but not on 32-bit machines (because a 16 MB limit is ridiculous
  # today), except if the CPU cannot address more than 16 MB anyway.
  # NO_TYPECODES will normally not work if alignof(subr_) = alignof(long) < 4.
  #if defined(WIDE) || defined(MC68000) || (alignment_long < 4)
    #define TYPECODES
  #else
    #define NO_TYPECODES
  #endif
#endif

#ifdef WIDE_SOFT
  #ifdef GNU
    # Benutze die GNU-C-Erweiterungen, um die breiten oints als structs aufzufassen.
    #define WIDE_STRUCT
  #endif
  # Bestimmt die Anordnung der Teile eines oints:
  #define WIDE_ENDIANNESS TRUE  # so ist's effizienter
#endif

#if defined(GNU) && (SAFETY >= 3)
  #if (__GNUC__ >= 2)
    #if (__GNUC_MINOR__ >= 7) # gcc-2.6.3 Bug umgehen
      # Typ�berpr�fungen durch den C-Compiler
      #define OBJECT_STRUCT
      #define CHART_STRUCT
    #endif
  #endif
#endif


# ###################### Betriebssystem-Routinen ##################### #

# allgemein standardisierte Konstanten f�r Steuerzeichen:
  #define BS    8  #  #\Backspace     Backspace
  #define TAB   9  #  #\Tab           Tabulator
  #define LF   10  #  #\Linefeed      Zeilenvorschub
  #define CR   13  #  #\Return        Carriage return, zum Zeilenanfang
  #define PG   12  #  #\Page          Form Feed, neue Seite

#ifdef AMIGAOS

#include "amiga.c"

# statement im Unterbrechungsfalle (Ctrl-C gedr�ckt) ausf�hren:
# interruptp(statement);
  #define interruptp(statement) \
    { # Ctrl-C-Signal abfragen und l�schen:                             \
      if (SetSignal(0L,(ULONG)(SIGBREAKF_CTRL_C)) & (SIGBREAKF_CTRL_C)) \
        { statement }                                                   \
    }
  # vgl. AMIGA.D und exec.library/SetSignal
# wird verwendet von EVAL, IO, SPVW, STREAM

#endif # AMIGAOS

#ifdef RISCOS

#include "acorn.c"

# Unterbrechungen noch nicht implementiert.
  #define interruptp(statement)

#endif # RISCOS

#if defined(UNIX) || defined(DJUNIX) || defined(EMUNIX) || defined(WATCOM) || defined(WIN32)

#ifdef UNIX
#include "unix.c"
#endif
#ifdef MSDOS
#include "msdos.c"
#endif
#ifdef WIN32_NATIVE
#include "win32.c"
#endif

# statement im Unterbrechungsfalle ausf�hren:
# interruptp(statement);
 #if defined(UNIX) || defined(EMUNIX) || defined(WIN32_NATIVE)
  # Eine Tastatur-Unterbrechung (Signal SIGINT, erzeugt durch Ctrl-C)
  # wird eine Sekunde lang aufgehoben. In dieser Zeit kann sie mittels
  # 'interruptp' auf fortsetzbare Art behandelt werden. Nach Ablauf dieser
  # Zeit wird das Programm nichtfortsetzbar unterbrochen.
  #define PENDING_INTERRUPTS
  extern uintB interrupt_pending;
  #define interruptp(statement)  if (interrupt_pending) { statement; }
 #endif
 #if defined(DJUNIX)
  # DJUNIX kennt keine Signale, nicht mal Ctrl-C.
  # Hat auch kein alarm() oder ualarm().
  #define interruptp(statement)  if (_go32_was_ctrl_break_hit()) { statement; }
 #endif
 #if defined(WATCOM)
  # WATCOM hat kein alarm() oder ualarm().
  #define interruptp(statement)  FALSE
 #endif
# wird verwendet von EVAL, IO, SPVW, STREAM

# Consensys macht "#define DS 3". Grr...
  #undef DS
# 386BSD macht "#define CBLOCK 64". Grr...
  #undef CBLOCK

#endif # UNIX || DJUNIX || EMUNIX || WATCOM || WIN32

#if defined(UNIX) || defined(WIN32_NATIVE)
  # Support for fault handling.
  #include "sigsegv.h"
#endif

#ifdef AMIGAOS
  # Behandlung von AMIGAOS-Fehlern
  # OS_error();
  # > IoErr(): Fehlercode
    nonreturning_function(extern, OS_error, (void));
  # wird verwendet von SPVW, STREAM, PATHNAME
#endif
#if defined(UNIX) || defined(DJUNIX) || defined(EMUNIX) || defined(WATCOM) || defined(RISCOS)
  # Behandlung von UNIX-Fehlern
  # OS_error();
  # > int errno: Fehlercode
    nonreturning_function(extern, OS_error, (void));
  # wird verwendet von SPVW, STREAM, PATHNAME, GRAPH
#endif
#if defined(WIN32_NATIVE)
  # Behandlung von Win32-Fehlern
  # OS_error();
  # > GetLastError(): Fehlercode
    nonreturning_function(extern, OS_error, (void));
  # Behandlung von Winsock-Fehlern
  # SOCK_error();
  # > WSAGetLastError(): Fehlercode
    nonreturning_function(extern, SOCK_error, (void));
#endif
#if defined(UNIX) || defined(EMUNIX) || defined(WATCOM) || defined(RISCOS)
  # Initialisierung der Fehlertabelle:
    extern int init_errormsg_table (void);
#else
  # Nichts zu initialisieren.
    #define init_errormsg_table()  0
#endif
#if defined(DEBUG_OS_ERROR)
  # Show the file and line number of the caller of OS_error(). For debugging.
  #define OS_error()  \
    (asciz_out_s("\n[%s:",__FILE__), asciz_out_1("%d] ",__LINE__), (OS_error)())
#endif

#ifdef MULTITHREAD

#include "xthread.c"

#if !(defined(HAVE_MMAP_ANON) || defined(HAVE_MMAP_DEVZERO) || defined(HAVE_MACH_VM) || defined(HAVE_WIN32_VM))
  #error "Multithreading requires memory mapping facilities!"
#endif

#endif

# ##################### Weitere System-Abh�ngigkeiten ##################### #

# Erst solche, die bis auf die Lisp-Ebene hin sichtbar sind:

# Einstellung der Tabelle von Zeichennamen:
  #ifdef AMIGA
    #define AMIGA_CHARNAMES
  #endif
  #ifdef MSDOS
    #define MSDOS_CHARNAMES
  #endif
  #ifdef WIN32
    #define WIN32_CHARNAMES
  #endif
  #if defined(UNIX) || defined(RISCOS)
    #define UNIX_CHARNAMES
  #endif
# Bei Erweiterung: CONSTOBJ, CHARSTRG, FORMAT.LSP erweitern.

# Ob wir die GNU gettext-Library f�r Internationalisierung benutzen:
  #if !defined(LANGUAGE_STATIC) && !defined(__cplusplus) && (defined(ISOLATIN_CHS) || defined(IBMPC_CHS)) && !defined(NO_GETTEXT)
    # Wenn nur eine Sprache gew�nscht ist, brauchen wir kein gettext.
    # Mit einem C++-Compiler ist die gettext-Library nicht compilierbar.
    # Ist der Zeichensatz nicht ISOLATIN oder IBMPC, l�sst sich spanish.lsp
    # weder laden noch compilieren.
    #define GNU_GETTEXT
  #endif
# Bei Erweiterung: Nichts weiter zu tun.

# Ob ein Stream *KEYBOARD-INPUT* gebildet wird,
# und ob er f�r den Stream *TERMINAL-IO* verwendet wird:
  #if defined(MSDOS) || (defined(UNIX) && !defined(NEXTAPP) || defined(MAYBE_NEXTAPP)) || defined(RISCOS) || defined(WIN32_NATIVE)
    #define KEYBOARD
    #if 0
      #define TERMINAL_USES_KEYBOARD
    #endif
  #endif
# Bei Erweiterung: STREAM, USER1.LSP erweitern.

# Ob wir die GNU Readline-Library f�r *TERMINAL-IO* benutzen:
  #if ((defined(UNIX) && !defined(NEXTAPP)) || (defined(MSDOS) && !defined(WATCOM))) && !defined(__cplusplus) && !defined(NO_READLINE)
    # Auf WATCOM ist die Readline-Library noch nicht portiert.
    # Mit einem C++-Compiler ist die Readline-Library nicht compilierbar.
    #define GNU_READLINE
  #endif
# Bei Erweiterung: READLINE erweitern.

# Ob es Window-Streams und eine Package SCREEN gibt:
  #if defined(MSDOS) || (defined(UNIX) && !defined(NEXTAPP) || defined(MAYBE_NEXTAPP))
    #define SCREEN
  #endif
# Bei Erweiterung: STREAM erweitern (viel Arbeit!).

# Ob es Pipe-Streams gibt:
  #if defined(UNIX) || defined(EMUNIX_PORTABEL) || defined(WIN32_NATIVE)
    #define PIPES
    #if defined(UNIX) || defined(EMUNIX_PORTABEL) || defined(WIN32_NATIVE)
      #define PIPES2  # bidirektionale Pipes
    #endif
  #endif
# Bei Erweiterung: STREAM und USER2.LSP erweitern.

# Ob es Socket-Streams gibt:
  #if (defined(UNIX) || defined(WIN32_NATIVE)) && defined(HAVE_GETHOSTBYNAME)
    # Damit Socket-Streams sinnvoll sind, muss socket.d compilierbar sein.
    # Dazu muss netdb.h oder sun/netdb.h existieren, was zuf�llig auch der
    # Existenz von gethostbyname() entspricht.
    #define X11SOCKETS
    #if defined(HAVE_NETINET_IN_H) || defined(WIN32_NATIVE) # see socket.d
      #define SOCKET_STREAMS
    #endif
  #endif
# Bei Erweiterung: STREAM erweitern.

# Whether there are generic streams:
  #if 1
    #define GENERIC_STREAMS
  #endif
# Bei Erweiterung: Nichts weiter zu tun.

# Ob die f�r die Funktionen MACHINE-TYPE, MACHINE-VERSION, MACHINE-INSTANCE
# ben�tigte Information vom Betriebssystem geholt werden kann:
  #if defined(UNIX) || defined(WIN32_NATIVE)
    #define MACHINE_KNOWN
  #endif
# Bei Erweiterung: MISC erweitern.

# Ob es LOGICAL-PATHNAMEs gibt:
  #if 1
    #define LOGICAL_PATHNAMES
  #endif
# Bei Erweiterung: Nichts weiter zu tun.

# Ob die Funktion USER-HOMEDIR-PATHNAME existiert:
  #if defined(UNIX) || defined(RISCOS) || defined(WIN32)
    #define USER_HOMEDIR
  #endif
# Bei Erweiterung: PATHNAME erweitern.

# Ob ein Stream *PRINTER-OUTPUT* bzw. eine Funktion MAKE-PRINTER-STREAM
# zur Verf�gung gestellt werden:
  #ifdef AMIGAOS
    #define PRINTER_AMIGAOS
  #endif
# Ob es Printer-Streams gibt:
  #ifdef PRINTER_AMIGAOS
    #define PRINTER
  #endif
# Bei Erweiterung: STREAM erweitern.

# Ob externe Kommunikation via Rexx unterst�tzt wird.
  #ifdef AMIGAOS
    #define REXX
    # define REXX_SERVER  # noch nicht ?JCH?
  #endif
# Bei Erweiterung: REXX erweitern.

# Ob Graphik-Operationen unterst�tzt werden.
  #if defined(EMUNIX) || (defined(UNIX_LINUX) && defined(PC386))
    #define GRAPHICS
    #define GRAPHICS_SWITCH  # Umschalten zwischen Text-Modus und Grafik-Modus
  #endif
# Bei Erweiterung: GRAPH erweitern.

# Ob das Betriebssystem ein Environment verwaltet, das Strings zu Strings
# assoziiert:
  #if defined(UNIX) || defined(MSDOS) || defined(AMIGAOS) || defined(RISCOS) || defined(WIN32)
    #define HAVE_ENVIRONMENT
  #endif
# Bei Erweiterung: Nichts weiter zu tun.

# Ob das Betriebssystem einen bevorzugten Kommando-Interpreter hat:
  #if defined(UNIX) || defined(MSDOS) || defined(AMIGAOS) || defined(RISCOS) || defined(WIN32_NATIVE)
    #define HAVE_SHELL
  #endif
# Bei Erweiterung: PATHNAME erweitern.

# Ob ein Foreign Function Interface zur Verf�gung gestellt wird:
  #if (defined(UNIX) && !defined(UNIX_BINARY_DISTRIB)) || defined(DYNAMIC_FFI)
    #define HAVE_FFI
  #endif
  #if defined(AMIGAOS)
    #define HAVE_AFFI # Amiga specific FFI
  #endif
# Bei Erweiterung: ??

# Ob ein externer Disassembler zur Verf�gung steht:
  #if defined(UNIX)
    #define HAVE_DISASSEMBLER
  #endif
# Bei Erweiterung: PATHNAME erweitern.

# Dann die, die nur intern bedeutsam sind:

# Ob die GC nicht mehr referenzierte Files schlie�t:
  #if defined(UNIX) || defined(AMIGAOS) || defined(RISCOS) || defined(WIN32)
    #define GC_CLOSES_FILES
  #endif
# Bei Erweiterung: nichts zu tun.

# Wie die Zeitmessungen durchgef�hrt werden:
  #ifdef MSDOS
    #define TIME_MSDOS
  #endif
  #ifdef AMIGAOS
    #define TIME_AMIGAOS
  #endif
  #ifdef RISCOS
    #define TIME_RISCOS
  #endif
  #ifdef UNIX
    #if defined(HAVE_GETTIMEOFDAY) || defined(HAVE_FTIME)
      #define TIME_UNIX
    #elif defined(HAVE_TIMES_CLOCK)
      #define TIME_UNIX_TIMES
    #endif
  #endif
  #ifdef WIN32_NATIVE
    #define TIME_WIN32
  #endif
  #if defined(TIME_MSDOS) || defined(TIME_AMIGAOS) || defined(TIME_UNIX_TIMES) || defined(TIME_RISCOS)
    # Die Zeitaufl�sung ist nur mittel, so dass man f�r Zeitdifferenz-Messungen
    # ohne weiteres eine 32-Bit-Zahl nehmen kann.
    #define TIME_1
    # Wir holen die Uhrzeit einmal beim System-Start. Alle weiteren
    # Uhrzeiten werden relativ zu dieser genommen.
    #define TIME_RELATIVE
  #endif
  #if defined(TIME_UNIX) || defined(TIME_WIN32)
    # Die Zeitaufl�sung ist so hoch, dass man f�r Zeitdifferenz-Messungen gleich
    # zwei 32-Bit-Zahlen braucht: Sekunden und Sekundenbruchteile.
    #define TIME_2
    # In diesem Fall k�nnen wir auch gleich immer mit absoluten und genauen
    # Uhrzeiten rechnen.
    #define TIME_ABSOLUTE
  #endif
# Bei Erweiterung: TIME erweitern.

# Ob die Funktion SYS::%SLEEP ein oder zwei Argumente �bergeben bekommt:
  #if defined(TIME_MSDOS) || defined(TIME_AMIGAOS) || defined(TIME_RISCOS)
    #define SLEEP_1
  #endif
  #if defined(TIME_UNIX) || defined(TIME_WIN32) || defined(TIME_UNIX_TIMES)
    #define SLEEP_2
  #endif
# Bei Erweiterung: TIME, DEFS1.LSP erweitern.

# Ob das Betriebssystem uns die Run-Time liefern kann, oder ob wir sie
# selber akkumulieren m�ssen (was bei Multitasking-Betriebssystemen ein wenig
# verf�lschend ist: AMIGAOS kann diese Information nicht liefern, RISCOS??):
  #if defined(UNIX) || defined(WIN32_NATIVE)
    #define HAVE_RUN_TIME
  #endif
# Bei Erweiterung: TIME erweitern.

# Ob das Betriebssystem Virtual Memory zur Verf�gung stellt.
  #if defined(UNIX) || defined(EMUNIX) || defined(DJUNIX) || defined(WIN32)
    #define VIRTUAL_MEMORY
  #endif
# Bei Erweiterung: nichts zu tun.

# Ob das Betriebssystem Unterbrechungen (Ctrl-C o.�.) als Signal auszuliefern
# in der Lage ist:
  #if defined(UNIX) || defined(EMUNIX) || defined(WATCOM) || defined(RISCOS)
    #define HAVE_SIGNALS
  #endif
# Ob wir auf asynchrone Signale auch reagieren k�nnen:
# (Bei WIDE_SOFT ist das Schreiben eines Pointers i.a. keine Elementar-Operation mehr!)
  #if defined(WIDE_SOFT) && !(defined(GNU) && defined(SPARC))
    #define NO_ASYNC_INTERRUPTS
  #endif
  #if defined(NO_ASYNC_INTERRUPTS) && defined(MULTITHREAD)
    #error "No multithreading possible with this memory model!"
  #endif
# Bei Erweiterung: SPVW erweitern, interruptp() schreiben.

# Arten der Pathname-Verwaltung:
  #ifdef AMIGAOS
    #define PATHNAME_AMIGAOS
  #endif
  #ifdef MSDOS
   #ifdef OS2
    #define PATHNAME_OS2
   #else
    #define PATHNAME_MSDOS
   #endif
  #endif
  #ifdef RISCOS
    #define PATHNAME_RISCOS
  #endif
  #ifdef UNIX
    #define PATHNAME_UNIX
  #endif
  #ifdef WIN32
    #define PATHNAME_WIN32
  #endif
# Die Komponenten von Pathnames:
  #if defined(PATHNAME_AMIGAOS) || defined(PATHNAME_MSDOS) || defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
    #define HAS_HOST      0
    #define HAS_DEVICE    1
    #define HAS_VERSION   0
  #endif
  #ifdef PATHNAME_UNIX
    #define HAS_HOST      0
    #define HAS_DEVICE    0
    #define HAS_VERSION   0
  #endif
  #ifdef PATHNAME_RISCOS
    #define HAS_HOST      1
    #define HAS_DEVICE    1
    #define HAS_VERSION   0
    #define FLIP_NAME_TYPE # Name und Type zum Betriebssystem hin vertauschen
  #endif
# Handhabung der File "Extension" (pathname-type):
  #if defined(PATHNAME_MSDOS)
    #define PATHNAME_EXT83  # Name und Type getrennt, Abschneiden nach 8 bzw. 3 Zeichen
  #endif
  #if defined(PATHNAME_RISCOS)
    #define PATHNAME_EXT  # Name und Type getrennt, aber keine L�ngenbegrenzung
  #endif
  #if defined(PATHNAME_UNIX) || defined(PATHNAME_AMIGAOS) || defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
    #define PATHNAME_NOEXT  # Keine explizite Extension.
  #endif
# Ob "//" am Anfang eines Pathname erhalten bleiben muss (nicht zu "/" verk�rzen):
  #ifdef UNIX_CYGWIN32
    #define PATHNAME_UNIX_UNC
  #endif
# Bei Erweiterung: PATHNAME erweitern.

# Ob es einen Typ FOREIGN gibt (eine Verpackung f�r diverse Pointer):
  #if defined(UNIX) || defined(DYNAMIC_FFI) || defined(AMIGAOS)
    # (Wird benutzt vom FFI und von CLX.)
    #define FOREIGN  void*
  #endif
# Bei Erweiterung: Nichts weiter zu tun.

# Ob an diversen Schl�sselstellen der STACK �berpr�ft wird:
  #define STACKCHECKS  (SAFETY >= 1) # beim Aufruf von SUBRs und FSUBRs
  #define STACKCHECKC  (SAFETY >= 1) # beim Abinterpretieren compilierter Closures
  #define STACKCHECKR  (SAFETY >= 1) # im Reader
  #define STACKCHECKP  (SAFETY >= 1) # im Printer
# Bei Ver�nderung: Nichts weiter zu tun.

# Ob subr_tab statisch zu initialisieren versucht wird.
  #if !(defined(WIDE_SOFT) && !defined(WIDE_STRUCT)) && !defined(WATCOM)
    #define INIT_SUBR_TAB
  #endif
# NB: Das muss definiert sein, damit externe Module funktionieren.
# Bei Ver�nderung: Nichts weiter zu tun.

# Ob symbol_tab statisch zu initialisieren versucht wird.
# (Es macht die Initialisierung einfacher, aber bei GNU-C auf einem Amiga
# reicht der Platz zum Compilieren von SPVWTABS nicht.
# WATCOM st�rzt ab mit "Abnormal program termination: Page fault".
# EMX 0.9c (gcc-2.7.2.1) meldet "Virtual memory exhausted".)
  #if !(defined(WIDE_SOFT) && !defined(WIDE_STRUCT)) && !(defined(AMIGA) || defined(WATCOM) || defined(EMUNIX))
    #define INIT_SYMBOL_TAB
  #endif
# Bei Ver�nderung: Nichts weiter zu tun.

# Ob object_tab statisch zu initialisieren versucht wird.
  #if !(defined(WIDE_SOFT) && !defined(WIDE_STRUCT)) && !defined(WATCOM)
    #define INIT_OBJECT_TAB
  #endif
# Bei Ver�nderung: Nichts weiter zu tun.


# ############### Liste von implementierten CLtL2-Features ################ #

#undef  X3J13_003
#define X3J13_005  # 18.5.1993
#define X3J13_014  # 22.1.1995
#define X3J13_149  # 22.7.1993
#define X3J13_161  # 20.5.1993
#define X3J13_175  # 25.7.1993


# ##################### Speicherstruktur von Objekten ##################### #

/*

Memory Representation and the Type Code of the various data types
=================================================================

1. The type code
----------------

An object consists of - in the same word - some type information and, for
immediate types, a couple of data bits, or, for heap allocated types,
a pointer to memory. There are many models of mixing type and pointer.
In the standard model, 6 to 8 bits (the word's high bits) are used for the
type. In the WIDE model, type and pointer are each 32 bits. In the CLEAN
model, there are only 2 to 6 bits.

One bit (normally bit 31) is used as mark bit by the garbage collector.
Outside of GC, it is always cleared. (Except for the get_circularities and
subst_circ routines, and in the STACK, the GC bit is used for marking frames.)

2. Memory formats
-----------------

2.1. Immediate objects

2.1.1. Machine pointers

Machine pointers are immediate objects. They may point to the code area
(.text segment), to data areas (.bss, .data segments, malloc'ed areas).
Other values (e.g. pointers to text/data in shared libraries) are not
allowed, because they may contain bits which are interpreted as a type code.
To use such machine addresses, you must wrap them in foreign-pointers or
simple-bit-vectors.

2.1.2. Other immediate objects

Character, Fixnum, Short-Float, and, if WIDE, Single-Float.
Furthermore: Frame-Pointer, Read-Label, System. (System means some
finite number of special values, such as #<UNBOUND>.)

2.2. SUBRs

They are immediate in the sense that they don't move (they don't need to,
because they are allocated statically), but they have to traversed by GC.

2.3. Pairs

These are heap objects containing just two pointers: Cons and, if SPVW_PURE,
Ratio and Complex.

2.4. Varobjects

These are heap objects of varying size. GC needs a header word at the
beginning of the object.

2.4.1. Records

These are varobjects which have additional type information and flags
in the second header word. Closure, Structure, Stream, Instance are always
records. Depending on the memory model, arrays, symbols etc. may or may
not be records.

2.4.2. Arrays

Simple-Bit-Vector, Simple-String, Simple-Vector are the "simple" arrays.
The non-simple ones are represented by a Iarray, yet the type code gives
some information about the rank, the representation and the element type:

                                |   "simple"    | "not simple" |
                                |   Sarray      |    Iarray    |
  ------------------------------+---------------+--------------+
   (vector bit/[un]signed-byte) | sbvector_type | bvector_type |
  ------------------------------+---------------+--------------+
   (vector character)           | sstring_type  | string_type  |
  ------------------------------+---------------+--------------+
   (vector t)                   | svector_type  | vector_type  |
  ------------------------------+---------------+--------------+
   array of dimension /= 1      |     --        | mdarray_type |
  ------------------------------+---------------+--------------+

2.4.3. Other varobjects

Symbol has some special flags (keyword, constant, special) in the header,
if possible.

FSUBR, Bignum, Single-Float (unless WIDE), Double-Float, Long-Float,
Ratio and Complex (only if SPVW_MIXED).

*/

# ######################## LISP-Objekte allgemein ######################### #

#if !defined(WIDE)

# Ein Objektpointer ist erst einmal ein leerer Pointer (damit man in C nichts
# Unbeabsichtigtes mit ihm machen kann):
  #ifdef OBJECT_STRUCT
    typedef struct { uintL one; } object;
  #else
    typedef  void *  object;
  #endif
# Aber in der Repr�sentation steckt eine Adresse und Typbits.

# Ein (unsigned) Integer von der Gr��e eines Objekts:
  typedef  uintL  oint;
  typedef  sintL  soint;

#else # defined(WIDE)

# Ein Objekt besteht aus getrennten 32 Bit Adresse und 32 Bit Typinfo.
  typedef  uint64  oint;
  typedef  sint64  soint;
  #ifdef WIDE_STRUCT
    #if BIG_ENDIAN_P==WIDE_ENDIANNESS
      #define TYPEDEF_OBJECT  \
        typedef  union { struct { /* tint */ uintL type; /* aint */ uintL addr; } both; \
                         oint one _attribute_aligned_object_;                           \
                       }                                                                \
                 object;
    #else
      #define TYPEDEF_OBJECT  \
        typedef  union { struct { /* aint */ uintL addr; /* tint */ uintL type; } both; \
                         oint one _attribute_aligned_object_;                           \
                       }                                                                \
                 object;
    #endif
  #else
    typedef  oint  object;
  #endif

#endif

# Es muss sizeof(object) = sizeof(oint) gelten!

# Umwandlungen zwischen object und oint:
# as_oint(expr)   object --> oint
# as_object(x)    oint --> object
  #if defined(WIDE_STRUCT) || defined(OBJECT_STRUCT)
    #define as_oint(expr)  ((expr).one)
    #if 1
      #define as_object(o)  ((object){one:(o)})
    #else
      extern __inline__ object as_object (register oint o)
        { register object obj; obj.one = o; return obj; }
    #endif
  #else
    #define as_oint(expr)  (oint)(expr)
    #define as_object(o)  (object)(o)
  #endif

# Aufteilung eines oint in Typbits und Adresse:
# Stets ist  oint_type_mask  subset  (2^oint_type_len-1)<<oint_type_shift
# und        oint_addr_mask superset (2^oint_addr_len-1)<<oint_addr_shift .
#if !defined(TYPECODES)
  #if defined(WIDE_HARD)
    # This is probably not really useful...
    #define oint_type_shift 0
    #define oint_type_len 16
    #define oint_type_mask 0x000000000000FFFFUL
    #define oint_addr_shift 0
    #define oint_addr_len 64
    #define oint_addr_mask 0xFFFFFFFFFFFFFFFFUL
    #define oint_data_shift 16
    #define oint_data_len 32
    #define oint_data_mask 0x0000FFFFFFFF0000UL
  #else
    # For pointers, the address takes the full word (with type info in the
    # lowest two bits). For immediate objects, we use 24 bits for the data
    # (but exclude the highest bit, which is the garcol_bit).
    #define oint_type_shift 0
    #define oint_type_len 8
    #define oint_type_mask 0x0000007FUL
    #define oint_addr_shift 0
    #define oint_addr_len 32
    #define oint_addr_mask 0xFFFFFFFFUL
    #define oint_data_shift 7
    #define oint_data_len 24
    #define oint_data_mask 0x7FFFFF80UL
  #endif
#elif defined(WIDE_HARD)
  #if defined(DECALPHA) && (defined(UNIX_OSF) || defined(UNIX_LINUX))
    # UNIX_OSF:
    #   Gew�hnliche Pointer liegen im Bereich 1*2^32..2*2^32.
    # UNIX_LINUX:
    #   Code address range:    0x000000012xxxxxxx
    #   Malloc address range:  0x000000012xxxxxxx
    #                    and:  0x0000015555xxxxxx
    #   Shared libraries:      0x0000015555xxxxxx
    #   Virtual address limit: 0x0000040000000000
    #if defined(NO_SINGLEMAP)
      # Wenn MAP_MEMORY nicht gefordert ist, ist das das sicherste.
      # Bits 63..48 = Typcode, Bits 47..0 = Adresse
      #define oint_type_shift 48
      #define oint_type_len 16
      #define oint_type_mask 0xFFFF000000000000UL
      #define oint_addr_shift 0
      #define oint_addr_len 48
      #define oint_addr_mask 0x0000FFFFFFFFFFFFUL
      #define oint_data_shift 0
      #define oint_data_len 32
      #define oint_data_mask 0x00000000FFFFFFFFUL
    #else
      # Bits 63..33 = Typcode, Bits 32..0 = Adresse
      #if 1 # Was ist besser??
        #define oint_type_shift 32
        #define oint_type_len 32
      #else
        #define oint_type_shift 33
        #define oint_type_len 31
      #endif
      #define oint_type_mask 0xFFFFFFFE00000000UL
      #define oint_addr_shift 0
      #define oint_addr_len 33
      #define oint_addr_mask 0x00000001FFFFFFFFUL
      #define oint_data_shift 0
      #define oint_data_len 32
      #define oint_data_mask 0x00000000FFFFFFFFUL
    #endif
  #endif
  #if defined(MIPS64)
    # Bits 63..32 = Typcode, Bits 31..0 = Adresse
    #define oint_type_shift 32
    #define oint_type_len 32
    #define oint_type_mask 0xFFFFFFFF00000000UL
    #define oint_addr_shift 0
    #define oint_addr_len 64
    #define oint_addr_mask 0x00000000FFFFFFFFUL
    #define oint_data_shift 0
    #define oint_data_len 32
    #define oint_data_mask 0x00000000FFFFFFFFUL
  #endif
#elif defined(WIDE_SOFT)
  # Getrennte 32-Bit-W�rter f�r Typcode und Adresse.
  #if WIDE_ENDIANNESS
    # Bits 63..32 = Typcode, Bits 31..0 = Adresse
    #define oint_type_shift 32
    #define oint_type_len 32
    #define oint_type_mask 0xFFFFFFFF00000000ULL
    #define oint_addr_shift 0
    #define oint_addr_len 32
    #define oint_addr_mask 0x00000000FFFFFFFFULL
  #else # umgekehrt ist es etwas langsamer:
    # Bits 63..32 = Adresse, Bits 31..0 = Typcode
    #define oint_type_shift 0
    #define oint_type_len 32
    #define oint_type_mask 0x00000000FFFFFFFFULL
    #define oint_addr_shift 32
    #define oint_addr_len 32
    #define oint_addr_mask 0xFFFFFFFF00000000ULL
  #endif
#elif (defined(MC680X0) && !defined(AMIGA3000) && !defined(UNIX_AMIX) && !defined(UNIX_NEXTSTEP)) || (defined(I80386) && !defined(WATCOM_BLAKE) && !defined(UNIX_SYSV_UHC_2) && !defined(UNIX_SYSV_UHC_1) && !(defined(UNIX_LINUX) && CODE_ADDRESS_RANGE) && !defined(UNIX_GNU) && !defined(UNIX_NEXTSTEP) && !defined(UNIX_SYSV_PTX) && !defined(UNIX_SUNOS5) && !defined(UNIX_CYGWIN32) && !defined(WIN32_NATIVE)) || (defined(SPARC) && !defined(SUN4_29_2)) || (defined(MIPS) && !defined(UNIX_IRIX) && !defined(UNIX_DEC_ULTRIX)) || defined(M88000) || (defined(RS6000) && !defined(UNIX_AIX) && !defined(UNIX_LINUX)) || defined(VAX) || (defined(CONVEX) && !defined(UNIX_CONVEX)) || defined(ACORN_1)
  # Bits 31..24 = Typcode, Bits 23..0 = Adresse
  #define oint_type_shift 24
  #define oint_type_len 8
  #define oint_type_mask 0xFF000000UL
  #define oint_addr_shift 0
  #define oint_addr_len 24
  #define oint_addr_mask 0x00FFFFFFUL
#elif defined(ACORN_2)
  # Bits 31..8 = Adresse, Bits 7..0 = Typcode
  #define oint_type_shift 0
  #define oint_type_len 8
  #define oint_type_mask 0x000000FFUL
  #define oint_addr_shift 8
  #define oint_addr_len 24
  #define oint_addr_mask 0xFFFFFF00UL
#elif defined(ACORN_3) || (defined(I80386) && defined(WIN32_NATIVE))
  # Bits 31..26 = Typcode, Bits 25..0 = Adresse
  #define oint_type_shift 26
  #define oint_type_len 6
  #define oint_type_mask 0xFC000000UL
  #define oint_addr_shift 0
  #define oint_addr_len 26
  #define oint_addr_mask 0x03FFFFFFUL
#elif defined(ACORN_4)
  # Bits 31..6 = Adresse, Bits 5..0 = Typcode
  #define oint_type_shift 0
  #define oint_type_len 6
  #define oint_type_mask 0x0000003FUL
  #define oint_addr_shift 6
  #define oint_addr_len 26
  #define oint_addr_mask 0xFFFFFFC0UL
#elif defined(AMIGA3000)
  # Bits 31..6 = Adresse/2, Bits 5..0 = Typcode
  #define oint_type_shift 0
  #define oint_type_len 6
  #define oint_type_mask 0x0000003FUL
  #define oint_addr_shift 6
  #define oint_addr_len 26
  #define oint_addr_mask 0xFFFFFFC0UL
  #define addr_shift 1
#elif defined(UNIX_SYSV_UHC_2)
  # Bits 31..6 = Adresse/4, Bits 5..0 = Typcode
  #define oint_type_shift 0
  #define oint_type_len 6
  #define oint_type_mask 0x0000003FUL
  #define oint_addr_shift 6
  #define oint_addr_len 26
  #define oint_addr_mask 0xFFFFFFC0UL
  #define addr_shift 2  # funktioniert nicht wegen STACK_alignment ??
#elif defined(I80386) && defined(UNIX_CYGWIN32)
  # Bits 31..7 = Adresse/4, Bits 6..0 = Typcode
  #define oint_type_shift 0
  #define oint_type_len 7
  #define oint_type_mask 0x0000007FUL
  #define oint_addr_shift 7
  #define oint_addr_len 25
  #define oint_addr_mask 0xFFFFFF80UL
  #define addr_shift 2
#elif (defined(HPPA) && defined(UNIX_HPUX)) || (defined(MC680X0) && defined(UNIX_AMIX))
  # Bits 29..24 = Typcode, Bits 31..30,23..0 = Adresse
  #define oint_type_shift 24
  #define oint_type_len 6
  #define oint_type_mask 0x3F000000UL
  #define oint_addr_shift 0
  #define oint_addr_len 24 # vern�nftig nutzbar sind nur die unteren 24 Bit
  #define oint_addr_mask 0xC0FFFFFFUL
  # Beachte: unten wird aint = uint24 = uint32 sein.
#elif defined(I80386) && defined(UNIX_CYGWIN32) && defined(WINDOWS_NT)
  # Bits 31..26,24 = Typcode, Bits 25,23..0 = Adresse
  #define oint_type_shift 24
  #define oint_type_len 8
  #define oint_type_mask 0xFD000000UL
  #define oint_addr_shift 0
  #define oint_addr_len 24
  #define oint_addr_mask 0x02FFFFFFUL
  # Malloc address range: starting at 0x02000000.
  # Shared libraries: cygwin32.dll is at 0x10000000, other libraries are
  # at 0x7Fxxxxxx.
  #define vm_addr_mask 0xEFFFFFFFUL
#elif defined(I80386) && defined(UNIX_CYGWIN32) && defined(WINDOWS_95)
  # Bits 31..27,25 = Typcode, Bits 26,24..0 = Adresse
  #define oint_type_shift 24
  #define oint_type_len 8
  #define oint_type_mask 0xFA000000UL
  #define oint_addr_shift 0
  #define oint_addr_len 24
  #define oint_addr_mask 0x05FFFFFFUL
  # Malloc address range: starting at 0x04800000 or 0x05000000.
  # Shared libraries: cygwin32.dll is at 0x10000000.
#elif defined(UNIX_SYSV_UHC_1)
  # Bits 31..28,26..24 = Typcode, Bits 23..0 = Adresse
  #define oint_type_shift 24
  #define oint_type_len 8
  #define oint_type_mask 0xF7000000UL
  #define oint_addr_shift 0
  #define oint_addr_len 24
  #define oint_addr_mask 0x08FFFFFFUL
#elif defined(I80386) && ((defined(UNIX_LINUX) && (CODE_ADDRESS_RANGE != 0)) || defined(UNIX_GNU)) && ((defined(DYNAMIC_MODULES) && !defined(NO_MORRIS_GC)) || defined(EFENCE)) # Linux with ELF binary format (or GNU, with ELF as well)
  # Dynamic loading of modules gives &module_xxx_object_tab = 0x40xxxxxx,
  # which yields to problems in the Morris GC (the 0x40000000 being masked out).
  # Use of libefence causes malloc to return addresses = 0x40xxxxxx.
  # Bits 31,29..28,26..24 = Typcode, Bits 30,27,23..0 = Adresse
  #define oint_type_shift 24
  #define oint_type_len 8
  #define oint_type_mask 0xB7000000UL
  #define oint_addr_shift 0
  #define oint_addr_len 24
  #define oint_addr_mask 0x48FFFFFFUL
#elif defined(I80386) && ((defined(UNIX_LINUX) && (CODE_ADDRESS_RANGE != 0)) || defined(UNIX_GNU)) # Linux with ELF binary format (or GNU, with ELF as well)
  # Bits 31..28,26..24 = Typcode, Bits 23..0 = Adresse
  #define oint_type_shift 24
  #define oint_type_len 8
  #define oint_type_mask 0xF7000000UL
  #define oint_addr_shift 0
  #define oint_addr_len 24
  #define oint_addr_mask 0x08FFFFFFUL
  # Shared libraries are mapped in at 0x50000000 or 0x40000000, via mmap().
  #define vm_addr_mask 0xBFFFFFFFUL
#elif defined(MIPS) && (defined(UNIX_IRIX) || defined(UNIX_DEC_ULTRIX))
  # Bits 31..29,27..24 = Typcode, Bits 23..0 = Adresse
  #define oint_type_shift 24
  #define oint_type_len 8
  #define oint_type_mask 0xEF000000UL
  #define oint_addr_shift 0
  #define oint_addr_len 24
  #define oint_addr_mask 0x10FFFFFFUL
#elif defined(RS6000) && defined(UNIX_AIX)
  # Bits 31..30,28..24 = Typcode, Bits 23..0 = Adresse
  #define oint_type_shift 24
  #define oint_type_len 8
  #define oint_type_mask 0xDF000000UL
  #define oint_addr_shift 0
  #define oint_addr_len 24
  #define oint_addr_mask 0x20FFFFFFUL
#elif defined(RS6000) && defined(UNIX_LINUX)
  # Bits 31..25 = Typcode, Bits 24..0 = Adresse
  #define oint_type_shift 24
  #define oint_type_len 8
  #define oint_type_mask 0xFE000000UL
  #define oint_addr_shift 0
  #define oint_addr_len 24
  #define oint_addr_mask 0x01FFFFFFUL
  # Virtual address range is only 2 GB, and moreover libc-1.99 mmap() is
  # broken, thinks that addresses >= 0x80000000 are errors.
  # Shared libraries are mapped in at 0x2AAAA000, via mmap(). We risk to
  # overwrite them only if someone uses several megabytes of negative bignums.
  #define vm_addr_mask 0x7FFFFFFFUL
#elif defined(SPARC) && defined(SUN4_29_2)
  # Bits 31,28..24 = Typcode, Bits 23..0 = Adresse
  #define oint_type_shift 24
  #define oint_type_len 8
  #define oint_type_mask 0x9F000000UL
  #define oint_addr_shift 0
  #define oint_addr_len 24
  #define oint_addr_mask 0x60FFFFFFUL
#elif defined(WATCOM_BLAKE)
  # Bits 30..25 = Typcode, Bits 31,24..0 = Adresse
  #define oint_type_shift 25
  #define oint_type_len 6
  #define oint_type_mask 0x7E000000UL
  #define oint_addr_shift 0
  #define oint_addr_len 25
  #define oint_addr_mask 0x81FFFFFFUL
#elif defined(UNIX_NEXTSTEP)
  # Bits 31..24 = Typcode, Bits 23..0 = Adresse
  #define oint_type_shift 24
  #define oint_type_len 8
  #define oint_type_mask 0xFF000000UL
  #define oint_addr_shift 0
  #define oint_addr_len 24
  #define oint_addr_mask 0x00FFFFFFUL
  # UNIX_NEXTSTEP has shared libraries at 0x05000000, related storage at
  # 0x04000000, a stack from 0x03F80000..0x04000000. We avoid this address
  # range of VM addresses by not using bits 26 and 24 in our typecode
  # bit encoding scheme.
  #define vm_addr_mask 0xFAFFFFFFUL
#elif defined(UNIX_SYSV_PTX)
  # Bits 31..24 = Typcode, Bits 23..0 = Adresse
  #define oint_type_shift 24
  #define oint_type_len 8
  #define oint_type_mask 0xFF000000UL
  #define oint_addr_shift 0
  #define oint_addr_len 24
  #define oint_addr_mask 0x00FFFFFFUL
  # UNIX_SYSV_PTX has its stack above 0x40000000. We avoid this address range
  # of VM addresses by not using bit 30 in our typecode bit encoding scheme.
  #define vm_addr_mask 0xBFFFFFFFUL
#elif defined(I80386) && defined(UNIX_SUNOS5)
  # Bits 31..28,26..24 = Typcode, Bits 23..0 = Adresse
  #define oint_type_shift 24
  #define oint_type_len 8
  #define oint_type_mask 0xF7000000UL
  #define oint_addr_shift 0
  #define oint_addr_len 24
  #define oint_addr_mask 0x08FFFFFFUL
  # UNIX_SUNOS5 has shared libraries at 0x80000000. We avoid this
  # address range of VM addresses by not using bit 31 in our typecode bit
  # encoding scheme.
  #define vm_addr_mask 0x7FFFFFFFUL
#elif defined(UNIX_NETBSD) # experimentell??
  # Bits 31..24 = Typcode, Bits 23..0 = Adresse
  #define oint_type_shift 24
  #define oint_type_len 8
  #define oint_type_mask 0xFF000000UL
  #define oint_addr_shift 0
  #define oint_addr_len 24
  #define oint_addr_mask 0x00FFFFFFUL
  # NetBSD 1.0 has its shared libraries above 0x10000000. We avoid this
  # address range of VM addresses by not using bit 28 in our typecode bit
  # encoding scheme.
  #define vm_addr_mask 0xEFFFFFFFUL
#elif defined(CONVEX) && defined(UNIX_CONVEX)
  # Bits 30..24 = Typcode, Bits 31,23..0 = Adresse
  #define oint_type_shift 24
  #define oint_type_len 8
  #define oint_type_mask 0x7F000000UL
  #define oint_addr_shift 0
  #define oint_addr_len 24
  #define oint_addr_mask 0x80FFFFFFUL
  # UNIX_CONVEX user space addresses are in the range 0x80000000..0xFFFFFFFF.
  # Memory mapping works in the range 0x80000000..0xBFFFFFFFUL.
  #define vm_addr_mask 0xBFFFFFFFUL
#else
  #error "How to split a pointer into type and address? -- Gr��en oint_type_shift, oint_addr_shift neu einstellen!"
#endif

# Meist nutzen wir den ganzen Platz einer Adresse f�r die Daten von Fixnums etc.
# Stets ist  [oint_data_shift..oint_data_shift+oint_data_len-1] subset
#            [oint_addr_shift..oint_addr_shift+oint_addr_len-1],
# also       oint_data_len <= oint_addr_len,
# aber auch  oint_data_len <= intLsize = 32 .
#ifndef oint_data_len
  #define oint_data_shift oint_addr_shift
  #define oint_data_len oint_addr_len
  #define oint_data_mask oint_addr_mask
#endif

# Integertyp f�r Typbits:
  typedef unsigned_int_with_n_bits(oint_type_len)  tint;

# Integertyp f�r Adressen:
  typedef unsigned_int_with_n_bits(oint_addr_len)  aint;
  typedef signed_int_with_n_bits(oint_addr_len)  saint;

# Anzahl der Bits, um die eine Adresse zuletzt noch geshiftet wird:
  #ifndef addr_shift
    #define addr_shift 0
  #endif

# Verify the values w.r.t. the autoconfigured CODE_ADDRESS_RANGE and
# MALLOC_ADDRESS_RANGE values.
#if !defined(WIDE_SOFT)
  #if (CODE_ADDRESS_RANGE >> addr_shift) & ~(oint_addr_mask >> oint_addr_shift)
     #error "oint_addr_mask doesn't cover CODE_ADDRESS_RANGE !!"
  #endif
  #if (MALLOC_ADDRESS_RANGE >> addr_shift) & ~(oint_addr_mask >> oint_addr_shift)
     #error "oint_addr_mask doesn't cover MALLOC_ADDRESS_RANGE !!"
  #endif
#endif

# Maske der Bits eines tint, die wirklich zum Typ geh�ren:
# tint_type_mask = oint_type_mask >> oint_type_shift
# (eine Constant Expression, in der keine 'long long's vorkommen!)
  #ifdef WIDE_SOFT
    #define tint_type_mask  (bitm(oint_type_len)-1)
  #else
    #define tint_type_mask  (oint_type_mask >> oint_type_shift)
  #endif

# Um zu einem object/oint etwas zu addieren:
# objectplus(obj,offset)
  #if !(defined(WIDE_SOFT) || defined(OBJECT_STRUCT))
    #define objectplus(obj,offset)  ((object)pointerplus(obj,offset))
  #else # defined(WIDE_SOFT) || defined(OBJECT_STRUCT)
    #define objectplus(obj,offset)  as_object(as_oint(obj)+(soint)(offset))
  #endif

# Bitoperationen auf Gr��en vom Typ oint:
# ...wbit... statt ...bit..., "w" = "wide".
  #if !defined(WIDE_SOFT)
    #define wbit  bit
    #define wbitm  bitm
    #define wbit_test  bit_test
    #define minus_wbit  minus_bit
  #else
    #define wbit(n)  (1LL<<(n))
    #define wbitm(n)  (2LL<<((n)-1))
    #define wbit_test(x,n)  ((x) & wbit(n))
    #define minus_wbit(n)  (-1LL<<(n))
  #endif

#ifdef TYPECODES

# Typinfo:
# typecode(object) und mtypecode(object) liefern den Typcode eines
# Objektes obj. Bei mtypecode muss er dazu im Speicher liegen.
  #if !(exact_uint_size_p(oint_type_len) && (tint_type_mask == bit(oint_type_len)-1))
    #define typecode(expr)  \
      ((tint)(as_oint(expr) >> oint_type_shift) & (oint_type_mask >> oint_type_shift))
    #define mtypecode(expr)  typecode(expr)
  #else
    # Der Typ 'tint' hat genau oint_type_len Bits, und tint_type_mask = 2^oint_type_len-1.
    # Also kann man sich das ANDen sparen.
    # Allerdings ist auf einem 68000 ein ROL.L #8 schneller, auf einer SPARC ein Shift.
      #define typecode(expr)  \
        ((tint)(as_oint(expr) >> oint_type_shift))
      #if defined(MC68000) && defined(GNU) && !defined(NO_ASM) && (oint_type_shift==24) && (oint_type_len==8)
        # GNU C auf einem 68000, ersetze LSR.L #24 durch ROL.L #8 :
        #undef typecode
        #define typecode(expr)  \
          ({var tint __typecode;                                               \
            __asm__ ("roll #8,%0" : "=d" (__typecode) : "0" (as_oint(expr)) ); \
            __typecode;                                                        \
           })
      #elif defined(SPARC) && !defined(WIDE)
        #undef typecode
        #define typecode(expr)  \
          ((as_oint(expr) << (32-oint_type_len-oint_type_shift)) >> (32-oint_type_len))
      #elif defined(WIDE) && defined(WIDE_STRUCT)
        #undef typecode
        #define typecode(expr)  ((expr).both.type)
      #endif
    # Au�erdem kann man Zugriffe im Speicher auch ohne Shift machen:
      #if !defined(WIDE) && (((oint_type_shift==24) && BIG_ENDIAN_P) || ((oint_type_shift==0) && !BIG_ENDIAN_P))
        #define mtypecode(expr)  (*(tint*)&(expr))
        #define fast_mtypecode
      #elif !defined(WIDE) && (((oint_type_shift==24) && !BIG_ENDIAN_P) || ((oint_type_shift==0) && BIG_ENDIAN_P))
        #define mtypecode(expr)  (*((tint*)&(expr)+3))
        #define fast_mtypecode
      #elif defined(WIDE)
        #ifdef WIDE_STRUCT
          #define mtypecode(expr)  ((expr).both.type)
        #elif (oint_type_len==16)
          #if (oint_type_shift==0) == BIG_ENDIAN_P
            #define mtypecode(expr)  (*((tint*)&(expr)+3))
          #else # (oint_type_shift==48) == BIG_ENDIAN_P
            #define mtypecode(expr)  (*(tint*)&(expr))
          #endif
        #elif (oint_type_len==32)
          #if (oint_type_shift==0) == BIG_ENDIAN_P
            #define mtypecode(expr)  (*((tint*)&(expr)+1))
          #else # (oint_type_shift==32) == BIG_ENDIAN_P
            #define mtypecode(expr)  (*(tint*)&(expr))
          #endif
        #endif
        #define fast_mtypecode
      #else # keine Optimierung m�glich
        #define mtypecode(expr)  typecode(expr)
      #endif
  #endif

# Extraktion des Adressfelds ohne Typinfo:
# untype(obj)
  #if defined(WIDE) && defined(WIDE_STRUCT)
    #define untype(expr)  ((expr).both.addr)
  #elif !(defined(SPARC) && (oint_addr_len+oint_addr_shift<32))
    #define untype(expr)    \
      ((aint)(as_oint(expr) >> oint_addr_shift) & (aint)(oint_addr_mask >> oint_addr_shift))
  #else
    # Auf einem SPARC-Prozessor sind lange Konstanten langsamer als Shifts:
    # Evtl. kann man sich ein ANDen sparen.
    #define untype(expr)  \
      ((aint)((as_oint(expr) << (32-oint_addr_len-oint_addr_shift)) >> (32-oint_addr_len)))
  #endif

# Objekt aus Typinfo und Adressfeld:
# type_untype_object(type,address)
  #if defined(WIDE) && defined(WIDE_STRUCT)
    #if BIG_ENDIAN_P==WIDE_ENDIANNESS
      #define type_untype_object(type,address)  ((object){{(tint)(type),(aint)(address)}})
    #else
      #define type_untype_object(type,address)  ((object){{(aint)(address),(tint)(type)}})
    #endif
  #elif !(oint_addr_shift==0)
    #define type_untype_object(type,address)  \
      (as_object(  ((oint)(tint)(type) << oint_type_shift) + \
                   ((oint)(aint)(address) << oint_addr_shift) ))
  #else # bei oint_addr_shift=0 braucht man nicht zu schieben:
    #if defined(WIDE_SOFT)
      # Vorsicht: Konversion von address zum oint durch Zero-Extend!
      #define type_untype_object(type,address)              \
        objectplus((oint)(aint)(address),(oint)(tint)(type)<<oint_type_shift)
    #elif defined(OBJECT_STRUCT)
      #define type_untype_object(type,address)              \
        as_object((oint)pointerplus((address),(oint)(tint)(type)<<oint_type_shift))
    #else # Normalfall
      # Damit das f�r gcc-2.5.8 ein g�ltiger Initialisierer ist (NIL_IS_CONSTANT),
      # darf man nicht vom Pointer zum oint und dann wieder zum Pointer casten,
      # sondern muss im Bereich der Pointer bleiben.
      #define type_untype_object(type,address)              \
        as_object(pointerplus((address),(oint)(tint)(type)<<oint_type_shift))
    #endif
  #endif

# Objekt aus Typinfo und direkten Daten (als "Adresse"):
# type_data_object(type,data)
  #if defined(WIDE) && defined(WIDE_STRUCT)
    #if BIG_ENDIAN_P==WIDE_ENDIANNESS
      #define type_data_object(type,data)  ((object){{(tint)(type),(aint)(data)}})
    #else
      #define type_data_object(type,data)  ((object){{(aint)(data),(tint)(type)}})
    #endif
  #elif !(oint_addr_shift==0)
    #define type_data_object(type,data)  \
      (as_object(  ((oint)(tint)(type) << oint_type_shift) + \
                   ((oint)(aint)(data) << oint_addr_shift) ))
  #else # bei oint_addr_shift=0 braucht man nicht zu schieben:
    #define type_data_object(type,data)  \
      (as_object( ((oint)(tint)(type) << oint_type_shift) + (oint)(aint)(data) ))
  #endif

# Extraktion der Adresse ohne Typinfo:
# upointer(obj)
# (upointer steht f�r "untyped pointer".)
  #if (addr_shift==0)
    #define upointer  untype
  #else
    #define optimized_upointer(obj)  \
      ((aint)((as_oint(obj) << (32-oint_addr_len-oint_addr_shift)) >> (32-oint_addr_len-addr_shift)))
    #define upointer(obj)  (untype(obj)<<addr_shift)
  #endif

# Objekt aus Typinfo und Adresse:
# type_pointer_object(type,address)
  #if (addr_shift==0)
    # (Kein Cast auf aint, damit NIL als Initializer zu gebrauchen ist.)
    #define type_pointer_object(type,address)  \
      type_untype_object(type,address)
  #elif defined(WIDE_SOFT) && !defined(WIDE_STRUCT)
    #define type_pointer_object(type,address)  \
      type_untype_object(type,(aint)(address)>>addr_shift)
  #else # effizienter,
    # setzt aber voraus, dass address durch 2^addr_shift teilbar ist:
    #define type_pointer_object(type,address)  \
      (as_object(  ((oint)(tint)(type) << oint_type_shift) + \
                   ((oint)(aint)(address) << (oint_addr_shift-addr_shift)) ))
  #endif

# Objekt aus konstanter Typinfo und konstanter Adresse:
# type_constpointer_object(type,address)
  #define type_constpointer_object(type,address)  type_pointer_object(type,address)

# oint aus konstanter Typinfo und Adresse = 0:
# type_zero_oint(type)
  #if defined(WIDE_SOFT) && defined(WIDE_STRUCT)
    #define type_zero_oint(type)  as_oint(type_untype_object(type,0))
  #else
    #define type_zero_oint(type)  ((oint)(tint)(type) << oint_type_shift)
  #endif

#else # no TYPECODES

# We can assume a general alignment of 4 bytes, and thus have the low 2 bits
# for encoding type. Here's how we divide the address space:
#   machine, frame_pointer  1/4
#   subr                    1/4
#   cons                    1/8
#   varobject               1/4 (not 1/8 because symbol_tab is not 8-aligned)
#   immediate               > 0 (anything >= 7/256 does it).
# Note that cons and varobject cannot have the same encoding mod 8
# (otherwise gc_mark:up wouldn't work).
# So, here are the encodings.
#   machine         ......00   encodes pointers, offset 0
#   subr            ......10   encodes pointers, offset 2
#   varobject       ......01   offset 1, the pointers are == 0 mod 4
#   cons            .....011   offset 3, the pointers are == 0 mod 8
#   immediate       .....111
#     fixnum        ..00s111   s = sign bit
#     sfloat        ..01s111   s = sign bit
#     char          ..100111
#     read-label    ..110111
#     system        ..111111
# Varobjects all start with a word containing the type (1 byte) and a length
# field (up to 24 bits).

# These are the biases, mod 8.
  #define machine_bias    0  # mod 4
  #define subr_bias       2  # mod 4
  #define varobject_bias  1  # mod 4
  #define cons_bias       3  # mod 8
  #define immediate_bias  7  # mod 8

# The types of immediate objects.
  #define fixnum_type      ((0 << 3) + immediate_bias)
  #define sfloat_type      ((2 << 3) + immediate_bias)
  #define char_type        ((4 << 3) + immediate_bias)
  #define read_label_type  ((6 << 3) + immediate_bias)
  #define system_type      ((7 << 3) + immediate_bias)

# The sign bit, for immediate numbers only.
  #define sign_bit_t  3
  #define sign_bit_o  (sign_bit_t+oint_type_shift)
# Distinction between fixnums and bignums.
  #define bignum_bit_o  1
  #define NUMBER_BITS_INVERTED

# For masking out the nonimmediate biases.
# This must be 3, not 7, otherwise gc_mark won't work.
  #define nonimmediate_bias_mask  3

# Combine an object from type info and immediate data.
# type_data_object(type,data)
  #define type_data_object(type,data)  \
      (as_object(  ((oint)(tint)(type) << oint_type_shift) + \
                   ((oint)(aint)(data) << oint_data_shift) ))

# An oint made up with a given type info, and address = 0.
# type_zero_oint(type)
  #define type_zero_oint(type)  ((oint)(tint)(type) << oint_type_shift)

# The GC bit. Addresses may not have this bit set.
  #define garcol_bit_o  (oint_addr_len-1)  # only set during garbage collection

# Test for immediate object.
# immediate_object_p(obj)
  #define immediate_object_p(obj)  ((7 & ~as_oint(obj)) == 0)

# Test for gc-invariant object. (This includes immediate, machine, subr.)
# gcinvariant_object_p(obj)
  #define gcinvariant_object_p(obj)  \
    (((as_oint(obj) & 1) == 0) || immediate_object_p(obj))

#endif


#if (oint_addr_shift == 0) && (addr_shift == 0) && defined(TYPECODES) && !defined(WIDE_SOFT) && !(defined(SUN3) && !defined(UNIX_SUNOS4) && !defined(WIDE_SOFT))
# Falls die Adressbits die unteren sind und nicht WIDE_SOFT,
# ist evtl. Memory-Mapping m�glich.

  #if (defined(HAVE_MMAP_ANON) || defined(HAVE_MMAP_DEVZERO) || defined(HAVE_MACH_VM) || defined(HAVE_WIN32_VM)) && !defined(MULTIMAP_MEMORY) && !(defined(UNIX_SINIX) || defined(UNIX_AIX)) && !defined(NO_SINGLEMAP)
    # Zugriff auf Lisp-Objekte wird vereinfacht dadurch, dass jedes Lisp-Objekt
    # an eine Adresse gelegt wird, das seine Typinformation bereits enth�lt.
    # Funktioniert aber nicht auf SINIX und AIX.
      #define SINGLEMAP_MEMORY
  #endif

  #if defined(UNIX_SUNOS4) && !defined(MULTIMAP_MEMORY) && !defined(SINGLEMAP_MEMORY) && !defined(NO_MULTIMAP_FILE)
    # Zugriff auf Lisp-Objekte geschieht mittels Memory-Mapping: Jede Speicher-
    # seite ist unter mehreren Adressen zugreifbar.
      #define MULTIMAP_MEMORY
      #define MULTIMAP_MEMORY_VIA_FILE
  #endif

  #if defined(HAVE_SHM) && !defined(MULTIMAP_MEMORY) && !defined(SINGLEMAP_MEMORY) && !defined(NO_MULTIMAP_SHM)
    # Zugriff auf Lisp-Objekte geschieht mittels Memory-Mapping: Jede Speicher-
    # seite ist unter mehreren Adressen zugreifbar.
      #define MULTIMAP_MEMORY
      #define MULTIMAP_MEMORY_VIA_SHM
  #endif

  #if defined(UNIX_LINUX) && !defined(MULTIMAP_MEMORY) && !defined(SINGLEMAP_MEMORY) && !defined(NO_MULTIMAP_FILE)
    # Zugriff auf Lisp-Objekte geschieht mittels Memory-Mapping: Jede Speicher-
    # seite ist unter mehreren Adressen zugreifbar.
      #define MULTIMAP_MEMORY
      #define MULTIMAP_MEMORY_VIA_FILE
  #endif

#endif

#if defined(MULTIMAP_MEMORY) || defined(SINGLEMAP_MEMORY)
  #define MAP_MEMORY
#endif

#if (defined(HAVE_MMAP_ANON) || defined(HAVE_MMAP_DEVZERO) || defined(HAVE_MACH_VM) || defined(HAVE_WIN32_VM)) && !defined(MAP_MEMORY) && !(defined(UNIX_HPUX) || defined(UNIX_AIX)) && !defined(NO_TRIVIALMAP)
  # mmap() erlaubt eine flexiblere Art der Speicherverwaltung als malloc().
  # Es ist kein wirkliches Memory-Mapping, sondern nur eine bequemere Art,
  # zwei gro�e Speicherbl�cke zu verwalten.
  # Funktioniert aber nicht auf HP-UX 9 und AIX.
  #define TRIVIALMAP_MEMORY
#endif


# Art des Einlesens des .mem-Files.
#if defined(VIRTUAL_MEMORY) && (defined(SINGLEMAP_MEMORY) /* || defined(TRIVIALMAP_MEMORY) */) && !defined(HAVE_MMAP) && defined(HAVE_SIGSEGV_RECOVERY) && (SAFETY < 3) && !defined(NO_SELFMADE_MMAP)
  # Zwischen Programmstart und der ersten vollen GC wird das .mem-File
  # seitenweise, nach Bedarf, eingelesen. Ohne mmap() geht das, wenn man
  # SIGSEGV selber abf�ngt.
  # Das funktioniert mit SINGLEMAP_MEMORY || TRIVIALMAP_MEMORY, bringt aber
  # nur bei SINGLEMAP_MEMORY etwas. (Bei TRIVIALMAP_MEMORY muss loadmem
  # das ganze mem-File einlesen, um alle Pointer zu relozieren.)
  #define SELFMADE_MMAP
#endif


# Art der Garbage Collection: normal oder generational.
#if defined(VIRTUAL_MEMORY) && (defined(SINGLEMAP_MEMORY) || defined(TRIVIALMAP_MEMORY) || (defined(MULTIMAP_MEMORY) && defined(UNIX_LINUX))) && defined(HAVE_WORKING_MPROTECT) && defined(HAVE_SIGSEGV_RECOVERY) && (SAFETY < 3) && !defined(NO_GENERATIONAL_GC)
  # F�r "generational garbage collection" sind einige Voraussetzungen n�tig.
  # Unter Linux geht es erst ab Linux 1.1.52, das wird in makemake �berpr�ft.
  #define GENERATIONAL_GC
#endif


#ifdef MAP_MEMORY
  # Evtl. sind einige Typbit-Kombinationen nicht erlaubt.
  #ifdef vm_addr_mask
    #define tint_allowed_type_mask  ((oint_type_mask & vm_addr_mask) >> oint_type_shift)
  #endif
#endif


# Der Typ `object' liegt nun vollst�ndig fest.
#ifdef WIDE_STRUCT
  #ifdef GENERATIONAL_GC
    # Die Generational GC kann es nicht brauchen, dass ein einzelner
    # Objektpointer sich auf zwei Seiten erstreckt.
    # Erzwinge daher  alignof(object) = sizeof(object).
    #define _attribute_aligned_object_  __attribute__ ((aligned(8)))
  #else
    #define _attribute_aligned_object_
  #endif
  TYPEDEF_OBJECT
#endif


# Objekte variabler L�nge m�ssen an durch 2 (o.�.) teilbaren Adressen liegen:
#if defined(VAX) # ?? gcc/config/vax/vax.h sagt: Alignment = 4
  #define varobject_alignment  1
#endif
#if defined(MC680X0)
  #if !(addr_shift==0)
    #define varobject_alignment  bit(addr_shift)  # wegen der gedr�ngten Typcodeverteilung
  #else
    #define varobject_alignment  2
  #endif
#endif
#if defined(I80386) || defined(RS6000) || defined(CONVEX) || defined(ARM)
  #define varobject_alignment  4
#endif
#if defined(SPARC) || defined(HPPA) || defined(MIPS) || defined(M88000) || defined(DECALPHA)
  #define varobject_alignment  8
#endif
#if (!defined(TYPECODES) || defined(GENERATIONAL_GC)) && (varobject_alignment < 4)
  #undef varobject_alignment
  #define varobject_alignment  4
#endif
#if (defined(GENERATIONAL_GC) && defined(WIDE)) && (varobject_alignment < 8)
  #undef varobject_alignment
  #define varobject_alignment  8
#endif
# varobject_alignment sollte definiert sein:
#ifndef varobject_alignment
  #error "varobject_alignment depends on CPU -- varobject_alignment neu einstellen!!"
#endif
# varobject_alignment sollte eine Zweierpotenz sein:
#if !((varobject_alignment & (varobject_alignment-1)) ==0)
  #error "Bogus varobject_alignment -- varobject_alignment neu einstellen!!"
#endif
# varobject_alignment sollte ein Vielfaches von 2^addr_shift sein:
#if (varobject_alignment % bit(addr_shift))
  #error "Bogus varobject_alignment -- varobject_alignment neu einstellen!!"
#endif


#ifdef TYPECODES

# Es folgt die Festlegung der einzelnen Typbits und Typcodes.

# Feststellen, ob ein Typ bei GC keine Ver�nderung erf�hrt
# (z.B. weil er keinen Pointer darstellt):
  #if 0 && defined(GNU)
    #define gcinvariant_type_p(type)  \
      ({var boolean _erg;                      \
        switch (type)                          \
          { case_machine:                      \
            case_char: case_subr: case_system: \
            case_fixnum: case_sfloat:          \
            /* bei WIDE auch: case_ffloat: */  \
              _erg = TRUE; break;              \
            default: _erg = FALSE; break;      \
          }                                    \
        _erg;                                  \
       })
  #endif

#ifndef tint_allowed_type_mask
  #define tint_allowed_type_mask  tint_type_mask
#endif

# Wir haben 6 bis 8 Typbits zur Verf�gung: TB7, [TB6,] [TB5,] TB4, ..., TB0.
# Alle m�ssen in tint_allowed_type_mask und damit auch in tint_type_mask
# gesetzt sein. Wir verteilen sie unter der Annahme, dass in tint_type_mask
# h�chstens ein Bit fehlt. TB6 und TB5 werden, falls nicht benutzbar,
# auf -1 gesetzt.
#if ((0xFF & ~tint_allowed_type_mask) == 0)
  #define TB7 7
  #define TB6 6
  #define TB5 5
  #define TB4 4
  #define TB3 3
  #define TB2 2
  #define TB1 1
  #define TB0 0
#elif (oint_type_len==7)
  #define TB7 6
  #define TB6 -1
  #define TB5 5
  #define TB4 4
  #define TB3 3
  #define TB2 2
  #define TB1 1
  #define TB0 0
#elif (oint_type_len==6)
  #define TB7 5
  #define TB6 -1
  #define TB5 -1
  #define TB4 4
  #define TB3 3
  #define TB2 2
  #define TB1 1
  #define TB0 0
#elif (oint_type_len>=8) && !((0xFF & ~tint_allowed_type_mask) == 0)
  # Manchem Bit m�ssen wir aus dem Weg gehen:
  #define tint_avoid  (0xFF & ~tint_allowed_type_mask)
  #if ((tint_avoid & (tint_avoid-1)) == 0)
    # tint_avoid besteht aus genau einem Bit, das es zu vermeiden gilt.
    #if (tint_avoid > bit(0))
      #define TB0 0
    #else
      #define TB0 1
    #endif
    #if (tint_avoid > bit(1))
      #define TB1 1
    #else
      #define TB1 2
    #endif
    #if (tint_avoid > bit(2))
      #define TB2 2
    #else
      #define TB2 3
    #endif
    #if (tint_avoid > bit(3))
      #define TB3 3
    #else
      #define TB3 4
    #endif
    #if (tint_avoid > bit(4))
      #define TB4 4
    #else
      #define TB4 5
    #endif
    #if (tint_avoid > bit(5))
      #define TB5 5
    #else
      #define TB5 6
    #endif
    #define TB6 -1
    #if (tint_avoid > bit(6))
      #define TB7 6
    #else
      #define TB7 7
    #endif
  #else
    # tint_avoid darf h�chstens zwei Bits enthalten:
    #if ((tint_avoid & (tint_avoid-1)) & ((tint_avoid & (tint_avoid-1)) - 1))
      #error "Bogus oint_type_mask -- oint_type_mask neu einstellen!"
    #endif
    # Das eine verbotene Bit k�nnen wir immer noch als GC-Bit nutzen,
    # vorausgesetzt, es ist in tint_type_mask enthalten:
    #define tint_maybegc_type_mask  (0xFF & tint_type_mask & ~tint_allowed_type_mask)
    #if (tint_maybegc_type_mask!=0)
      # Davon nehmen wir das kleinere Bit als GC-Bit:
      #define tint_avoid1  (tint_maybegc_type_mask & -tint_maybegc_type_mask)
      #if (tint_avoid1 == bit(0))
        #define TB7 0
      #elif (tint_avoid1 == bit(1))
        #define TB7 1
      #elif (tint_avoid1 == bit(2))
        #define TB7 2
      #elif (tint_avoid1 == bit(3))
        #define TB7 3
      #elif (tint_avoid1 == bit(4))
        #define TB7 4
      #elif (tint_avoid1 == bit(5))
        #define TB7 5
      #elif (tint_avoid1 == bit(6))
        #define TB7 6
      #elif (tint_avoid1 == bit(7))
        #define TB7 7
      #else
        #error "Bogus tint_avoid1!"
      #endif
      #define TB6 -1
      # Und das gr��ere Bit gilt es noch zu vermeiden:
      #define tint_avoid2  (tint_avoid & ~tint_avoid1)
      #if (TB7 > 0) && (tint_avoid2 > bit(0))
        #define TB0 0
      #elif (TB7 > 1) || (tint_avoid2 > bit(1))
        #define TB0 1
      #else
        #define TB0 2
      #endif
      #if (TB7 > 1) && (tint_avoid2 > bit(1))
        #define TB1 1
      #elif (TB7 > 2) || (tint_avoid2 > bit(2))
        #define TB1 2
      #else
        #define TB1 3
      #endif
      #if (TB7 > 2) && (tint_avoid2 > bit(2))
        #define TB2 2
      #elif (TB7 > 3) || (tint_avoid2 > bit(3))
        #define TB2 3
      #else
        #define TB2 4
      #endif
      #if (TB7 > 3) && (tint_avoid2 > bit(3))
        #define TB3 3
      #elif (TB7 > 4) || (tint_avoid2 > bit(4))
        #define TB3 4
      #else
        #define TB3 5
      #endif
      #if (TB7 > 4) && (tint_avoid2 > bit(4))
        #define TB4 4
      #elif (TB7 > 5) || (tint_avoid2 > bit(5))
        #define TB4 5
      #else
        #define TB4 6
      #endif
      #if (TB7 > 5) && (tint_avoid2 > bit(5))
        #define TB5 5
      #elif (TB7 > 6) || (tint_avoid2 > bit(6))
        #define TB5 6
      #else
        #define TB5 7
      #endif
    #else
      # Wir m�ssen beiden Bits vollst�ndig aus dem Weg gehen.
      #define tint_avoid1  (tint_avoid & -tint_avoid)     # das kleinere der Bits
      #define tint_avoid2  (tint_avoid & (tint_avoid-1))  # das gr��ere der Bits
      #if (tint_avoid1 > bit(0))
        #define TB0 0
      #elif (tint_avoid2 > bit(1))
        #define TB0 1
      #else
        #define TB0 2
      #endif
      #if (tint_avoid1 > bit(1))
        #define TB1 1
      #elif (tint_avoid2 > bit(2))
        #define TB1 2
      #else
        #define TB1 3
      #endif
      #if (tint_avoid1 > bit(2))
        #define TB2 2
      #elif (tint_avoid2 > bit(3))
        #define TB2 3
      #else
        #define TB2 4
      #endif
      #if (tint_avoid1 > bit(3))
        #define TB3 3
      #elif (tint_avoid2 > bit(4))
        #define TB3 4
      #else
        #define TB3 5
      #endif
      #if (tint_avoid1 > bit(4))
        #define TB4 4
      #elif (tint_avoid2 > bit(5))
        #define TB4 5
      #else
        #define TB4 6
      #endif
      #define TB5 -1
      #define TB6 -1
      #if (tint_avoid1 > bit(5))
        #define TB7 5
      #elif (tint_avoid2 > bit(6))
        #define TB7 6
      #else
        #define TB7 7
      #endif
    #endif
  #endif
#else
  #error "Bogus TB7..TB0 -- TB7..TB0 neu einstellen!"
#endif

#if (TB7==7)&&(TB6==6)&&(TB5==5)&&(TB4==4)&&(TB3==3)&&(TB2==2)&&(TB1==1)&&(TB0==0)
  #if defined(SUN3) && !defined(UNIX_SUNOS4) && !defined(WIDE_SOFT)
    #define SUN3_TYPECODES
  #elif defined(SUN4_29_1) && defined(MAP_MEMORY) && !defined(WIDE_SOFT)
    #define PACKED_TYPECODES
  #elif defined(DECALPHA) && defined(UNIX_OSF) && defined(MAP_MEMORY)
    #define PACKED_TYPECODES
  #else
    #define STANDARD_TYPECODES
  #endif
#endif
#if (oint_type_len>=8) && (TB6==-1)
  #if (TB5==-1)
    #define SIXBIT_TYPECODES
  #elif defined(DECALPHA) && defined(UNIX_OSF) && defined(MAP_MEMORY)
    #define PACKED_TYPECODES
  #else
    #define SEVENBIT_TYPECODES
  #endif
#endif
#if (oint_type_len==7)
  #define SEVENBIT_TYPECODES
#endif
#if (oint_type_len==6)
  #define SIXBIT_TYPECODES
#endif

#ifdef STANDARD_TYPECODES

#if defined(I80386) && defined(UNIX_LINUX) && (CODE_ADDRESS_RANGE == 0)
  # Bei 0x60000000 sitzen die Shared-Libraries.
  # Bei 0x50000000 (Linux 1.2) bzw. 0x40000000 (Linux 2.0) sitzen diverse
  # mmap-Seiten, z.B. von setlocale() oder gettext() alloziert.
  # Deswegen brauchen wir die Typcode-Verteilung nur ein wenig zu �ndern.
#endif

#if (defined(MC680X0) || (defined(SPARC) && !defined(SUN4_29))) && defined(UNIX_LINUX)
  # Bei 0x50000000 sitzen die Shared Libraries.
  # Deswegen brauchen wir die Typcode-Verteilung aber nicht zu �ndern.
#endif

#if (defined(MIPS) || defined(RS6000)) && defined(UNIX_LINUX)
  # Bei 0x2AAAB000 sitzen die Shared Libraries.
  # Deswegen brauchen wir die Typcode-Verteilung aber nicht zu �ndern.
#endif

#if defined(SPARC64) && defined(UNIX_LINUX)
  # Bei 0x70000000 sitzen die Shared Libraries.
  # Deswegen brauchen wir die Typcode-Verteilung aber nicht zu �ndern.
#endif

# Typbits:
# in Typcodes (tint):
  #define garcol_bit_t     7  # gesetzt nur w�hrend der Garbage Collection!
  #define cons_bit_t       6  # gesetzt nur bei CONS
  #define symbol_bit_t     5  # gesetzt nur bei SYMBOL
  #define number_bit_t     4  # gesetzt nur bei Zahlen
  #define notsimple_bit_t  2  # bei Arrays: gel�scht bei Simple-Arrays
  #define sign_bit_t       0  # Vorzeichen bei reellen Zahlen (gesetzt <==> Zahl <0)
  #define float_bit_t      1
  #define float1_bit_t     3
  #define float2_bit_t     2
  #define ratio_bit_t      3
  #define bignum_bit_t     2
# in Objekten (oint):
  #define garcol_bit_o     (garcol_bit_t+oint_type_shift)    # gesetzt nur w�hrend der Garbage Collection!
  #define cons_bit_o       (cons_bit_t+oint_type_shift)      # gesetzt nur bei CONS
  #define symbol_bit_o     (symbol_bit_t+oint_type_shift)    # gesetzt nur bei SYMBOL
  #define number_bit_o     (number_bit_t+oint_type_shift)    # gesetzt nur bei Zahlen
  #define notsimple_bit_o  (notsimple_bit_t+oint_type_shift) # bei Arrays: gel�scht bei Simple-Arrays
  #define sign_bit_o       (sign_bit_t+oint_type_shift)      # Vorzeichen bei reellen Zahlen
  #define float_bit_o      (float_bit_t+oint_type_shift)
  #define float1_bit_o     (float1_bit_t+oint_type_shift)
  #define float2_bit_o     (float2_bit_t+oint_type_shift)
  #define ratio_bit_o      (ratio_bit_t+oint_type_shift)
  #define bignum_bit_o     (bignum_bit_t+oint_type_shift)

# konstante Typcodes:
  #define machine_type   0x00  # %00000000  ; Maschinenpointer
  #define sbvector_type  0x01  # %00000001  ; Simple-Bit-Vector
  #define sstring_type   0x02  # %00000010  ; Simple-String
  #define svector_type   0x03  # %00000011  ; Simple-Vector
  #define mdarray_type   0x04  # %00000100  ; sonstiger Array (Rang /=1 oder
                               #            ; - sp�ter vielleicht - anderer Elementtyp)
  #define bvector_type   0x05  # %00000101  ; sonstiger Bit-Vector oder Byte-Vector
  #define string_type    0x06  # %00000110  ; sonstiger String
  #define vector_type    0x07  # %00000111  ; sonstiger (VECTOR T)
  #define closure_type   0x08  # %00001000  ; Closure
  #define structure_type 0x09  # %00001001  ; Structure
  #define stream_type    0x0A  # %00001010  ; Stream
  #define orecord_type   0x0B  # %00001011  ; OtherRecord (Package, Byte, ...)
  #define instance_type  0x0C  # %00001100  ; CLOS-Instanz
  #define char_type      0x0D  # %00001101  ; Character
  #define subr_type      0x0E  # %00001110  ; SUBR
  #define system_type    0x0F  # %00001111  ; Frame-Pointer, Read-Label, SYSTEM
  #define fixnum_type    0x10  # %00010000  ; Fixnum
  #define sfloat_type    0x12  # %00010010  ; Short-Float
  #define bignum_type    0x14  # %00010100  ; Bignum
  #define ffloat_type    0x16  # %00010110  ; Single-Float
  #define ratio_type     0x18  # %00011000  ; Ratio
  #define dfloat_type    0x1A  # %00011010  ; Double-float
  #define complex_type   0x1C  # %00011100  ; Complex
  #define lfloat_type    0x1E  # %00011110  ; Long-Float
  #define symbol_type    0x20  # %00100000  ; Symbol
          # Bits f�r Symbole in VAR/FUN-Frames (im LISP-Stack):
          #define active_bit  1  # gesetzt: Bindung ist aktiv
          #define dynam_bit   2  # gesetzt: Bindung ist dynamisch
          #define svar_bit    3  # gesetzt: n�chster Parameter ist supplied-p-Parameter f�r diesen
          #define oint_symbolflags_shift  oint_type_shift
          # Bits f�r Symbole im Selbstpointer:
          #define constant_bit_t  1  # zeigt an, ob das Symbol eine Konstante ist
          #define special_bit_t   2  # zeigt an, ob das Symbol SPECIAL-proklamiert ist
  #if defined(I80386) && defined(UNIX_LINUX)
  #define cons_type      0x44  # %01000100  ; Cons
  #else
  #define cons_type      0x40  # %01000000  ; Cons
  #endif

#ifndef WIDE
  # Typ ist GC-invariant, wenn
  # Typinfobyte=0 oder char_type <= Typinfobyte < bignum_type.
    #define gcinvariant_type_p(type)  \
      (((type)==0) || ((char_type<=(type)) && ((type)<bignum_type)))
#else
  # Typ ist GC-invariant, wenn
  # Typinfobyte eines von 0x00,0x0D..0x13,0x16..0x17 ist.
    #define gcinvariant_type_p(type)  \
      (((type)<0x18) && ((bit(type) & 0xFF301FFEUL) == 0))
#endif

#endif # STANDARD_TYPECODES

#ifdef PACKED_TYPECODES

#ifdef SUN4_29_1
# Zugriffe sind nur auf Pointer >=0, <2^29 erlaubt.
# Daher eine etwas gedr�ngte Typcode-Verteilung.
#endif

#if defined(DECALPHA) && defined(UNIX_OSF) && !(defined(NO_SINGLEMAP) || defined(NO_TRIVIALMAP))
# mmap() geht nur mit Adressen >=0, <2^38, aber da gew�hnliche Pointer im
# Bereich 1*2^32..2*2^32 liegen, bleiben uns nur die Bits 37..33 als Typbits.
#endif

# Typbits:
# in Typcodes (tint):
  #define garcol_bit_t     TB7  # gesetzt nur w�hrend der Garbage Collection!
  #define number_bit_t     TB4  # gesetzt nur bei Zahlen
  #define notsimple_bit_t  TB2  # bei Arrays: gel�scht bei Simple-Arrays
  #define sign_bit_t       TB0  # Vorzeichen bei reellen Zahlen (gesetzt <==> Zahl <0)
  #define float_bit_t      TB1
  #define float1_bit_t     TB3
  #define float2_bit_t     TB2
  #define ratio_bit_t      TB3
  #define bignum_bit_t     TB2
# in Objekten (oint):
  #define garcol_bit_o     (garcol_bit_t+oint_type_shift)    # gesetzt nur w�hrend der Garbage Collection!
  #define number_bit_o     (number_bit_t+oint_type_shift)    # gesetzt nur bei Zahlen
  #define notsimple_bit_o  (notsimple_bit_t+oint_type_shift) # bei Arrays: gel�scht bei Simple-Arrays
  #define sign_bit_o       (sign_bit_t+oint_type_shift)      # Vorzeichen bei reellen Zahlen
  #define float_bit_o      (float_bit_t+oint_type_shift)
  #define float1_bit_o     (float1_bit_t+oint_type_shift)
  #define float2_bit_o     (float2_bit_t+oint_type_shift)
  #define ratio_bit_o      (ratio_bit_t+oint_type_shift)
  #define bignum_bit_o     (bignum_bit_t+oint_type_shift)

# konstante Typcodes:
  #define machine_type   (0)                                            # 0x00  # %00000000  ; Maschinenpointer
  #define sbvector_type  (                                    bit(TB0)) # 0x01  # %00000001  ; Simple-Bit-Vector
  #define sstring_type   (                           bit(TB1)         ) # 0x02  # %00000010  ; Simple-String
  #define svector_type   (                           bit(TB1)|bit(TB0)) # 0x03  # %00000011  ; Simple-Vector
  #define mdarray_type   (                  bit(TB2)                  ) # 0x04  # %00000100  ; sonstiger Array (Rang /=1 oder
                                                                                #            ; - sp�ter vielleicht - anderer Elementtyp)
  #define bvector_type   (                  bit(TB2)         |bit(TB0)) # 0x05  # %00000101  ; sonstiger Bit-Vector oder Byte-Vector
  #define string_type    (                  bit(TB2)|bit(TB1)         ) # 0x06  # %00000110  ; sonstiger String
  #define vector_type    (                  bit(TB2)|bit(TB1)|bit(TB0)) # 0x07  # %00000111  ; sonstiger (VECTOR T)
  #define closure_type   (         bit(TB3)                           ) # 0x08  # %00001000  ; Closure
  #define structure_type (         bit(TB3)                  |bit(TB0)) # 0x09  # %00001001  ; Structure
  #define stream_type    (         bit(TB3)         |bit(TB1)         ) # 0x0A  # %00001010  ; Stream
  #define orecord_type   (         bit(TB3)         |bit(TB1)|bit(TB0)) # 0x0B  # %00001011  ; OtherRecord (Package, Byte, ...)
  #define instance_type  (         bit(TB3)|bit(TB2)                  ) # 0x0C  # %00001100  ; CLOS-Instanz
  #define symbol_type    (         bit(TB3)|bit(TB2)         |bit(TB0)) # 0x0D  # %00001101  ; Symbol
          # Bits f�r Symbole in VAR/FUN-Frames (im LISP-Stack):
          # sitzen nicht im oint_type-Teil, sondern im oint_addr-Teil.
          #define active_bit  0  # gesetzt: Bindung ist aktiv
          #define dynam_bit   1  # gesetzt: Bindung ist dynamisch
          #define svar_bit    2  # gesetzt: n�chster Parameter ist supplied-p-Parameter f�r diesen
          #if (varobject_alignment >= bit(3))
            #define oint_symbolflags_shift  oint_addr_shift
          #else
            #define NO_symbolflags # active_bit, dynam_bit, svar_bit haben im Symbol keinen Platz
          #endif
          # Bits f�r Symbole im Selbstpointer:
          #if !((TB3+3==TB7) || (TB3+2==TB7) || (TB3+1==TB7))
            #define constant_bit_t  (TB3+3)  # zeigt an, ob das Symbol eine Konstante ist
            #define special_bit_t   (TB3+2)  # zeigt an, ob das Symbol SPECIAL-proklamiert ist
          #else
            #define constant_bit_t  (TB7+3)  # zeigt an, ob das Symbol eine Konstante ist
            #define special_bit_t   (TB7+2)  # zeigt an, ob das Symbol SPECIAL-proklamiert ist
          #endif
  #define cons_type      (         bit(TB3)|bit(TB2)|bit(TB1)         ) # 0x0E  # %00001110  ; Cons
  #define subr_type      (         bit(TB3)|bit(TB2)|bit(TB1)|bit(TB0)) # 0x0F  # %00001111  ; SUBR
  #define fixnum_type    (bit(TB4)                                    ) # 0x10  # %00010000  ; Fixnum
  #define sfloat_type    (bit(TB4)                  |bit(TB1)         ) # 0x12  # %00010010  ; Short-Float
  #define bignum_type    (bit(TB4)         |bit(TB2)                  ) # 0x14  # %00010100  ; Bignum
  #define ffloat_type    (bit(TB4)         |bit(TB2)|bit(TB1)         ) # 0x16  # %00010110  ; Single-Float
  #define ratio_type     (bit(TB4)|bit(TB3)                           ) # 0x18  # %00011000  ; Ratio
  #define dfloat_type    (bit(TB4)|bit(TB3)         |bit(TB1)         ) # 0x1A  # %00011010  ; Double-float
  #define complex_type   (bit(TB4)|bit(TB3)|bit(TB2)                  ) # 0x1C  # %00011100  ; Complex
  #define lfloat_type    (bit(TB4)|bit(TB3)|bit(TB2)|bit(TB1)         ) # 0x1E  # %00011110  ; Long-Float
  #define system_type    (bit(TB5)                                    ) # 0x20  # %00100000  ; Frame-Pointer, Read-Label, SYSTEM
  #define char_type      (bit(TB5)|bit(TB0)                           ) # 0x21  # %00100001  ; Character

# Typ ist GC-invariant, wenn
  #if (TB5==5)&&(TB4==4)&&(TB3==3)&&(TB2==2)&&(TB1==1)&&(TB0==0) && !defined(WIDE)
    # Typinfobyte eines von 0x00,0x0F,0x10,0x11,0x12,0x13,0x20,0x21 ist.
    #define gcinvariant_type_p(type)  \
      (((type)>=32) || ((bit(type) & 0xFFF07FFEUL) == 0))
  #elif (TB5==6)&&(TB4==5)&&(TB3==4)&&(TB2==3)&&(TB1==2)&&(TB0==1) && defined(WIDE)
    # Typinfobyte/2 eines von 0x00,0x0F,0x10,0x11,0x12,0x13,0x16,0x17,0x20,0x21 ist.
    #define gcinvariant_type_p(type)  \
      (((type)>=64) || ((bit((type)>>1) & 0xFF307FFEUL) == 0))
  #elif !defined(WIDE)
    # Typinfobyte = 0 oder subr_type <= Typinfobyte < bignum_type oder Typinfobyte >= system_type ist.
    #define gcinvariant_type_p(type)  \
      (((type) == 0) || ((subr_type <= (type)) && ((type) < bignum_type)) || (system_type <= (type)))
  #else
    #error "gcinvariant_type_p() implementieren!"
  #endif

#endif # PACKED_TYPECODES

#ifdef SEVENBIT_TYPECODES

#if defined(UNIX_SYSV_UHC_1) || (defined(I80386) && ((defined(UNIX_LINUX) && (CODE_ADDRESS_RANGE != 0)) || defined(UNIX_GNU)))
# Mallozierter Speicher belegt den Bereich ab 0x08000000.
# F�r die Typinformation stehen nur 7 Bit zur Verf�gung, und die f�r den
# Typcode zur Verf�gung stehenden Bits liegen nicht am St�ck.
# Wir m�ssen Bit 3 aus dem Weg gehen.
#if defined(I80386) && defined(UNIX_LINUX) && (CODE_ADDRESS_RANGE != 0)
# Shared Libraries belegen den Bereich ab 0x40000000 oder 0x50000000.
# Nehme daher Bit 6 als GC-Bit.
#endif
#endif

#if defined(UNIX_IRIX) || defined(UNIX_DEC_ULTRIX)
# Mallozierter Speicher belegt den Bereich ab 0x10000000.
# F�r die Typinformation stehen nur 7 Bit zur Verf�gung, und die f�r den
# Typcode zur Verf�gung stehenden Bits liegen nicht am St�ck.
# Wir m�ssen Bit 4 aus dem Weg gehen.
#endif

#ifdef UNIX_AIX
# Mallozierter Speicher belegt den Bereich ab 0x20000000.
# F�r die Typinformation stehen nur 7 Bit zur Verf�gung, und die f�r den
# Typcode zur Verf�gung stehenden Bits liegen nicht am St�ck.
# Wir m�ssen Bit 5 aus dem Weg gehen.
#endif

#if defined(UNIX_NEXTSTEP) && defined(MAP_MEMORY)
# UNIX_NEXTSTEP verbietet uns die Benutzung von Adressen im Bereich von
# unterhalb 0x04000000 bis oberhalb 0x05000000. Wir vermeiden daher als
# Typbits Bit 0 und Bit 2 (ausgenommen GC-Bit, das ja vor jedem Speicherzugriff
# wegmaskiert wird).
#endif

#if defined(UNIX_CONVEX) && defined(MAP_MEMORY)
# Bei UNIX_CONVEX liegt der Adressraum der Prozesse ab 0x80000000.
# mmap() funktioniert allerdings nur unterhalb von 0xC000000. Daher
# geh�rt Bit 31 zur Adresse, und Bit 30 m�ssen wir aus dem Weg gehen.
#endif

#if defined(I80386) && defined(UNIX_CYGWIN32)
# Mallozierter Speicher belegt den Bereich ab 0x02000000 unter WinNT, aber
# den Bereich ab 0x04800000 oder 0x05000000 unter Win95. Wenn man dieselben
# Binaries und dieselben mem-Files f�r beides verwenden will, bleiben nur
# noch die Bits 31..27 und 1..0 f�r Typinformation �brig. Alignment = 4 kann
# man voraussetzen.
#endif

#if defined(DECALPHA) && defined(UNIX_LINUX) && !(defined(NO_SINGLEMAP) || defined(NO_TRIVIALMAP))
# Mallozierter Speicher belegt den Bereich ab 0x120000000.
# Wir m�ssen Bit 32 aus dem Weg gehen.
#endif

#if defined(RS6000) && defined(UNIX_LINUX)
# On MkLinux, code and mallocated memory starts at 0x01000000. Avoid bit 24.
# Moreover, bit 31 cannot be used in addresses.
# Shared libraries are at 0x2AAAA000, but we won't probably hit them.
#endif

# Typbits:
# in Typcodes (tint):
  #define garcol_bit_t     TB7  # gesetzt nur w�hrend der Garbage Collection!
  #define number_bit_t     TB4  # gesetzt nur bei Zahlen
  #define notsimple_bit_t  TB2  # bei Arrays: gel�scht bei Simple-Arrays
  #define sign_bit_t       TB0  # Vorzeichen bei reellen Zahlen (gesetzt <==> Zahl <0)
  #define float_bit_t      TB1
  #define float1_bit_t     TB3
  #define float2_bit_t     TB2
  #define ratio_bit_t      TB3
  #define bignum_bit_t     TB2
# in Objekten (oint):
  #define garcol_bit_o     (garcol_bit_t+oint_type_shift)    # gesetzt nur w�hrend der Garbage Collection!
  #define number_bit_o     (number_bit_t+oint_type_shift)    # gesetzt nur bei Zahlen
  #define notsimple_bit_o  (notsimple_bit_t+oint_type_shift) # bei Arrays: gel�scht bei Simple-Arrays
  #define sign_bit_o       (sign_bit_t+oint_type_shift)      # Vorzeichen bei reellen Zahlen
  #define float_bit_o      (float_bit_t+oint_type_shift)
  #define float1_bit_o     (float1_bit_t+oint_type_shift)
  #define float2_bit_o     (float2_bit_t+oint_type_shift)
  #define ratio_bit_o      (ratio_bit_t+oint_type_shift)
  #define bignum_bit_o     (bignum_bit_t+oint_type_shift)

# konstante Typcodes:
  #define machine_type   (0)                                             # %000000  ; Maschinenpointer
  #define sbvector_type  (                                    bit(TB0))  # %000001  ; Simple-Bit-Vector
  #define sstring_type   (                           bit(TB1)         )  # %000010  ; Simple-String
  #define svector_type   (                           bit(TB1)|bit(TB0))  # %000011  ; Simple-Vector
  #define mdarray_type   (                  bit(TB2)                  )  # %000100  ; sonstiger Array (Rang /=1 oder
                                                                         #          ; - sp�ter vielleicht - anderer Elementtyp)
  #define bvector_type   (                  bit(TB2)         |bit(TB0))  # %000101  ; sonstiger Bit-Vector oder Byte-Vector
  #define string_type    (                  bit(TB2)|bit(TB1)         )  # %000110  ; sonstiger String
  #define vector_type    (                  bit(TB2)|bit(TB1)|bit(TB0))  # %000111  ; sonstiger (VECTOR T)
  #define closure_type   (         bit(TB3)                           )  # %001000  ; Closure
  #define structure_type (         bit(TB3)                  |bit(TB0))  # %001001  ; Structure
  #define stream_type    (         bit(TB3)         |bit(TB1)         )  # %001010  ; Stream
  #define orecord_type   (         bit(TB3)         |bit(TB1)|bit(TB0))  # %001011  ; OtherRecord (Package, Byte, ...)
  #define instance_type  (         bit(TB3)|bit(TB2)                  )  # %001100  ; CLOS-Instanz
  #define char_type      (         bit(TB3)|bit(TB2)         |bit(TB0))  # %001101  ; Character
  #define subr_type      (         bit(TB3)|bit(TB2)|bit(TB1)         )  # %001110  ; SUBR
  #define system_type    (         bit(TB3)|bit(TB2)|bit(TB1)|bit(TB0))  # %001111  ; Frame-Pointer, Read-Label, SYSTEM
  #define fixnum_type    (bit(TB4)                                    )  # %010000  ; Fixnum
  #define sfloat_type    (bit(TB4)                  |bit(TB1)         )  # %010010  ; Short-Float
  #define bignum_type    (bit(TB4)         |bit(TB2)                  )  # %010100  ; Bignum
  #define ffloat_type    (bit(TB4)         |bit(TB2)|bit(TB1)         )  # %010110  ; Single-Float
  #define ratio_type     (bit(TB4)|bit(TB3)                           )  # %011000  ; Ratio
  #define dfloat_type    (bit(TB4)|bit(TB3)         |bit(TB1)         )  # %011010  ; Double-float
  #define complex_type   (bit(TB4)|bit(TB3)|bit(TB2)                  )  # %011100  ; Complex
  #define lfloat_type    (bit(TB4)|bit(TB3)|bit(TB2)|bit(TB1)         )  # %011110  ; Long-Float
  #define symbol_type    (bit(TB5)                                    )  # %100000  ; Symbol
          # Bits f�r Symbole in VAR/FUN-Frames (im LISP-Stack):
          #define active_bit  TB0  # gesetzt: Bindung ist aktiv
          #define dynam_bit   TB1  # gesetzt: Bindung ist dynamisch
          #define svar_bit    TB2  # gesetzt: n�chster Parameter ist supplied-p-Parameter f�r diesen
          #define oint_symbolflags_shift  oint_type_shift
          # Bits f�r Symbole im Selbstpointer:
          #define constant_bit_t  TB0  # zeigt an, ob das Symbol eine Konstante ist
          #define special_bit_t   TB1  # zeigt an, ob das Symbol SPECIAL-proklamiert ist
  #define cons_type      (bit(TB5)|bit(TB3)|bit(TB2)                  )  # %101000  ; Cons

#ifndef WIDE
  # Typ ist GC-invariant, wenn
  # Typinfobyte=0 oder char_type <= Typinfobyte < bignum_type.
    #define gcinvariant_type_p(type)  \
      (((type)==0) || ((char_type<=(type)) && ((type)<bignum_type)))
#elif (TB5==6)&&(TB4==5)&&(TB3==4)&&(TB2==3)&&(TB1==2)&&(TB0==1) && defined(WIDE)
  # Typinfobyte/2 eines von 0x00,0x0D,0x0E,0x0F,0x10,0x11,0x12,0x13,0x16,0x17 ist.
  #define gcinvariant_type_p(type)  \
    (((type)<64) && ((bit((type)>>1) & 0xFF301FFEUL) == 0))
#else
  #error "gcinvariant_type_p() implementieren!"
#endif

#endif # SEVENBIT_TYPECODES

#ifdef PACKED_SEVENBIT_TYPECODES

# Typbits:
# in Typcodes (tint):
  #define garcol_bit_t     TB7  # gesetzt nur w�hrend der Garbage Collection!
  #define number_bit_t     TB4  # gesetzt nur bei Zahlen
  #define notsimple_bit_t  TB2  # bei Arrays: gel�scht bei Simple-Arrays
  #define sign_bit_t       TB0  # Vorzeichen bei reellen Zahlen (gesetzt <==> Zahl <0)
  #define float_bit_t      TB1
  #define float1_bit_t     TB3
  #define float2_bit_t     TB2
  #define ratio_bit_t      TB3
  #define bignum_bit_t     TB2
# in Objekten (oint):
  #define garcol_bit_o     (garcol_bit_t+oint_type_shift)    # gesetzt nur w�hrend der Garbage Collection!
  #define number_bit_o     (number_bit_t+oint_type_shift)    # gesetzt nur bei Zahlen
  #define notsimple_bit_o  (notsimple_bit_t+oint_type_shift) # bei Arrays: gel�scht bei Simple-Arrays
  #define sign_bit_o       (sign_bit_t+oint_type_shift)      # Vorzeichen bei reellen Zahlen
  #define float_bit_o      (float_bit_t+oint_type_shift)
  #define float1_bit_o     (float1_bit_t+oint_type_shift)
  #define float2_bit_o     (float2_bit_t+oint_type_shift)
  #define ratio_bit_o      (ratio_bit_t+oint_type_shift)
  #define bignum_bit_o     (bignum_bit_t+oint_type_shift)

# konstante Typcodes:
  #define machine_type   (0)                                             # %000000  ; Maschinenpointer
  #define sbvector_type  (                                    bit(TB0))  # %000001  ; Simple-Bit-Vector
  #define sstring_type   (                           bit(TB1)         )  # %000010  ; Simple-String
  #define svector_type   (                           bit(TB1)|bit(TB0))  # %000011  ; Simple-Vector
  #define mdarray_type   (                  bit(TB2)                  )  # %000100  ; sonstiger Array (Rang /=1 oder
                                                                         #          ; - sp�ter vielleicht - anderer Elementtyp)
  #define bvector_type   (                  bit(TB2)         |bit(TB0))  # %000101  ; sonstiger Bit-Vector oder Byte-Vector
  #define string_type    (                  bit(TB2)|bit(TB1)         )  # %000110  ; sonstiger String
  #define vector_type    (                  bit(TB2)|bit(TB1)|bit(TB0))  # %000111  ; sonstiger (VECTOR T)
  #define symbol_type    (         bit(TB3)                           )  # %001000  ; Symbol
          # Bits f�r Symbole in VAR/FUN-Frames (im LISP-Stack):
          #define active_bit  0  # gesetzt: Bindung ist aktiv
          #define dynam_bit   1  # gesetzt: Bindung ist dynamisch
          #define svar_bit    2  # gesetzt: n�chster Parameter ist supplied-p-Parameter f�r diesen
          #if (varobject_alignment >= bit(3))
            #define oint_symbolflags_shift  oint_addr_shift
          #else
            #define NO_symbolflags # active_bit, dynam_bit, svar_bit haben im Symbol keinen Platz
          #endif
          # Bits f�r Symbole im Selbstpointer:
          #define constant_bit_t  TB0  # zeigt an, ob das Symbol eine Konstante ist
          #define special_bit_t   TB4  # zeigt an, ob das Symbol SPECIAL-proklamiert ist
  #define cons_type      (         bit(TB3)                  |bit(TB0))  # %001001  ; Cons
  #define closure_type   (         bit(TB3)         |bit(TB1)         )  # %001010  ; Closure
  #define structure_type (         bit(TB3)         |bit(TB1)|bit(TB0))  # %001011  ; Structure
  #define orecord_type   (         bit(TB3)|bit(TB2)                  )  # %001100  ; OtherRecord (Stream, Package, Byte, ...)
  #define instance_type  (         bit(TB3)|bit(TB2)         |bit(TB0))  # %001101  ; CLOS-Instanz
  #define subr_type      (         bit(TB3)|bit(TB2)|bit(TB1)         )  # %001110  ; SUBR
  #define system_type    (         bit(TB3)|bit(TB2)|bit(TB1)|bit(TB0))  # %001111  ; Frame-Pointer, Read-Label, SYSTEM
  #define fixnum_type    (bit(TB4)                                    )  # %010000  ; Fixnum
  #define sfloat_type    (bit(TB4)                  |bit(TB1)         )  # %010010  ; Short-Float
  #define bignum_type    (bit(TB4)         |bit(TB2)                  )  # %010100  ; Bignum
  #define ffloat_type    (bit(TB4)         |bit(TB2)|bit(TB1)         )  # %010110  ; Single-Float
  #define ratio_type     (bit(TB4)|bit(TB3)                           )  # %011000  ; Ratio
  #define dfloat_type    (bit(TB4)|bit(TB3)         |bit(TB1)         )  # %011010  ; Double-float
  #define complex_type   (bit(TB4)|bit(TB3)|bit(TB2)                  )  # %011100  ; Complex
  #define lfloat_type    (bit(TB4)|bit(TB3)|bit(TB2)|bit(TB1)         )  # %011110  ; Long-Float
  #define char_type      (bit(TB5)|bit(TB3)         |bit(TB1)         )  # %101010  ; Character

#ifndef WIDE
  # Typ ist GC-invariant, wenn
  # Typinfobyte=0 oder subr_type <= Typinfobyte < bignum_type oder Typinfobyte >= char_type.
    #define gcinvariant_type_p(type)  \
      (((type)==0) || ((subr_type<=(type)) && ((type)<bignum_type)) || (char_type<=(type)))
#else
  #error "gcinvariant_type_p() implementieren!"
#endif

#endif # PACKED_SEVENBIT_TYPECODES

#ifdef SIXBIT_TYPECODES

#if defined(ACORN_3) || defined(ACORN_4)
# Speicher kann den Bereich von 0x00000000 bis 0x03FFFFFF umfassen.
# F�r die Typinformation stehen nur 6 Bit zur Verf�gung.
#endif

#ifdef AMIGA3000
# Speicher kann den Bereich von 0x07000000 bis 0x0FFFFFFF umfassen.
# F�r die Typinformation stehen nur 6 Bit zur Verf�gung, und dies auch nur,
# wenn wir Alignment = 4 voraussetzen.
# Das k�nnen wir aber nicht, da der C-Compiler bzw. der Linker im Text-Segment
# nur Alignment = 2 hat. Somit k�nnen wir nur den Bereich von 0x07000000 bis
# 0x07FFFFFF nutzen.
#endif

#if defined(I80386) && defined(WIN32_NATIVE)
# The memory map looks like this:
#   0x00000000 - 0x00400000  stack, executable
#   0x00400000 - 0x00E00000  (WinNT 4.0 only) something
#   then free
#   0x75xxxxxx               DLLs
#   0x77xxxxxx               DLLs
#   0x78xxxxxx               DLLs
#   0x7Fxxxxxx               DLLs
#   0x80000000 - 0xFFFFFFFF  not present
# Therefore we put the type bits into bits 31..26 (bit 31 being the GC bit),
# and let the base address range extend from 0x00000000 to 0x03FFFFFF. This
# should be enough for up to 50 MB memory use.
# Also, we avoid to map memory to addresses 0x70000000 - 0x7FFFFFFF.
#define NUMBER_BITS_INVERTED
#endif

#if defined(HPPA) && defined(UNIX_HPUX)
# Mallozierter Speicher belegt den Bereich ab 0x40000000.
# F�r die Typinformation stehen die Bits 29..24 zur Verf�gung.
#endif

#ifdef UNIX_AMIX
# Bits 31..30 werden vom Betriebssystem belegt.
# F�r die Typinformation stehen die Bits 29..24 zur Verf�gung.
#endif

#ifdef UNIX_SYSV_UHC_2
# Mallozierter Speicher belegt den Bereich ab 0x08000000.
# F�r die Typinformation stehen nur 6 Bit zur Verf�gung, und dies auch nur,
# wenn wir Alignment = 4 voraussetzen.
#endif

#ifdef WATCOM_BLAKE
# When run with virtual memory or in the DOS box, the DOS4GW extender returns
# malloc'ed memory in the range beginning at 0x80000000.
# The type information can use the bits 30..25.
#endif

#ifdef SUN4_29_2
# Zugriffe sind nur auf Pointer >=0, <2^29 erlaubt.
#endif

# F�r die Typinformation stehen nur 6 Bit zur Verf�gung.
# Daher eine etwas gedr�ngte Typcode-Verteilung.

# Typbits:
# in Typcodes (tint):
  #define garcol_bit_t     TB7  # gesetzt nur w�hrend der Garbage Collection!
  #define number_bit_t     TB4  # gesetzt nur bei Zahlen
  #define notsimple_bit_t  TB2  # bei Arrays: gel�scht bei Simple-Arrays
  #define sign_bit_t       TB0  # Vorzeichen bei reellen Zahlen (gesetzt <==> Zahl <0)
  #define float_bit_t      TB1
  #define float1_bit_t     TB3
  #define float2_bit_t     TB2
  #define ratio_bit_t      TB3
  #define bignum_bit_t     TB2
# in Objekten (oint):
  #define garcol_bit_o     (garcol_bit_t+oint_type_shift)    # gesetzt nur w�hrend der Garbage Collection!
  #define number_bit_o     (number_bit_t+oint_type_shift)    # gesetzt nur bei Zahlen
  #define notsimple_bit_o  (notsimple_bit_t+oint_type_shift) # bei Arrays: gel�scht bei Simple-Arrays
  #define sign_bit_o       (sign_bit_t+oint_type_shift)      # Vorzeichen bei reellen Zahlen
  #define float_bit_o      (float_bit_t+oint_type_shift)
  #define float1_bit_o     (float1_bit_t+oint_type_shift)
  #define float2_bit_o     (float2_bit_t+oint_type_shift)
  #define ratio_bit_o      (ratio_bit_t+oint_type_shift)
  #define bignum_bit_o     (bignum_bit_t+oint_type_shift)

# konstante Typcodes:
  #define machine_type   (0)                                             # %000000  ; Maschinenpointer
  #define sbvector_type  (                                    bit(TB0))  # %000001  ; Simple-Bit-Vector
  #define sstring_type   (                           bit(TB1)         )  # %000010  ; Simple-String
  #define svector_type   (                           bit(TB1)|bit(TB0))  # %000011  ; Simple-Vector
  #define mdarray_type   (                  bit(TB2)                  )  # %000100  ; sonstiger Array (Rang /=1 oder
                                                                         #          ; - sp�ter vielleicht - anderer Elementtyp)
  #define bvector_type   (                  bit(TB2)         |bit(TB0))  # %000101  ; sonstiger Bit-Vector oder Byte-Vector
  #define string_type    (                  bit(TB2)|bit(TB1)         )  # %000110  ; sonstiger String
  #define vector_type    (                  bit(TB2)|bit(TB1)|bit(TB0))  # %000111  ; sonstiger (VECTOR T)
  #define orecord_type   (         bit(TB3)                           )  # %001000  ; OtherRecord (Structure, Stream, Package, Byte, ...)
  #define instance_type  (         bit(TB3)                  |bit(TB0))  # %001001  ; CLOS-Instanz
  #define closure_type   (         bit(TB3)         |bit(TB1)         )  # %001010  ; Closure
  #define cons_type      (         bit(TB3)         |bit(TB1)|bit(TB0))  # %001011  ; Cons
  #define symbol_type    (         bit(TB3)|bit(TB2)                  )  # %001100  ; Symbol
          # Bits f�r Symbole in VAR/FUN-Frames (im LISP-Stack):
          #define active_bit  0  # gesetzt: Bindung ist aktiv
          #define dynam_bit   1  # gesetzt: Bindung ist dynamisch
          #define svar_bit    2  # gesetzt: n�chster Parameter ist supplied-p-Parameter f�r diesen
          #if (varobject_alignment >= 8)
            # sitzen nicht im oint_type-Teil, sondern im oint_addr-Teil.
            #define oint_symbolflags_shift  oint_addr_shift
          #else
            #define NO_symbolflags # active_bit, dynam_bit, svar_bit haben im Symbol keinen Platz
          #endif
          # Bits f�r Symbole im Selbstpointer:
          #define constant_bit_t  TB1  # zeigt an, ob das Symbol eine Konstante ist
          #define special_bit_t   TB0  # zeigt an, ob das Symbol SPECIAL-proklamiert ist
  #define subr_type      (         bit(TB3)|bit(TB2)         |bit(TB0))  # %001101  ; SUBR
  #define system_type    (         bit(TB3)|bit(TB2)|bit(TB1)         )  # %001110  ; Frame-Pointer, Read-Label, SYSTEM
  #define char_type      (         bit(TB3)|bit(TB2)|bit(TB1)|bit(TB0))  # %001111  ; Character
 #ifndef NUMBER_BITS_INVERTED
  #define fixnum_type    (bit(TB4)                                    )  # %010000  ; Fixnum
  #define sfloat_type    (bit(TB4)                  |bit(TB1)         )  # %010010  ; Short-Float
  #define bignum_type    (bit(TB4)         |bit(TB2)                  )  # %010100  ; Bignum
  #define ffloat_type    (bit(TB4)         |bit(TB2)|bit(TB1)         )  # %010110  ; Single-Float
  #define ratio_type     (bit(TB4)|bit(TB3)                           )  # %011000  ; Ratio
  #define dfloat_type    (bit(TB4)|bit(TB3)         |bit(TB1)         )  # %011010  ; Double-float
  #define complex_type   (bit(TB4)|bit(TB3)|bit(TB2)                  )  # %011100  ; Complex
  #define lfloat_type    (bit(TB4)|bit(TB3)|bit(TB2)|bit(TB1)         )  # %011110  ; Long-Float
 #else # NUMBER_BITS_INVERTED inverts TB2 and TB3 and also TB1 (so that N_integerp remains fast)
  #define lfloat_type    (bit(TB4)                                    )  # %011100  ; Long-Float
  #define complex_type   (bit(TB4)                  |bit(TB1)         )  # %011110  ; Complex
  #define dfloat_type    (bit(TB4)         |bit(TB2)                  )  # %010100  ; Double-float
  #define ratio_type     (bit(TB4)         |bit(TB2)|bit(TB1)         )  # %010110  ; Ratio
  #define ffloat_type    (bit(TB4)|bit(TB3)                           )  # %011000  ; Single-Float
  #define bignum_type    (bit(TB4)|bit(TB3)         |bit(TB1)         )  # %011010  ; Bignum
  #define sfloat_type    (bit(TB4)|bit(TB3)|bit(TB2)                  )  # %011100  ; Short-Float
  #define fixnum_type    (bit(TB4)|bit(TB3)|bit(TB2)|bit(TB1)         )  # %011110  ; Fixnum
 #endif

# Typ ist GC-invariant, wenn
# Typinfobyte eines von 0x00,0x0D,0x0E,0x0F,0x10,0x11,0x12,0x13 ist.
  #if (TB4==4)&&(TB3==3)&&(TB2==2)&&(TB1==1)&&(TB0==0) && !defined(WIDE)
    #ifndef NUMBER_BITS_INVERTED
      #define gcinvariant_type_p(type)  \
        ((bit(type) & 0xFFF01FFEUL) == 0)
    #else
      #define gcinvariant_type_p(type)  \
        ((bit(type) & 0x0FFF1FFEUL) == 0)
    #endif
  #elif !defined(WIDE)
    #ifndef NUMBER_BITS_INVERTED
      #define gcinvariant_type_p(type)  \
        (((type)==0) || ((subr_type<=(type)) && ((type)<bignum_type)))
    #else
      #define gcinvariant_type_p(type)  \
        (((type)==0) || ((subr_type<=(type)) && ((type)<lfloat_type)) || (sfloat_type<=(type)))
    #endif
  #else
    #error "gcinvariant_type_p() implementieren!"
  #endif

#endif # SIXBIT_TYPECODES

#ifdef SUN3_TYPECODES

# Typbits:
# in Typcodes (tint):
  #define garcol_bit_t     1  # gesetzt nur w�hrend der Garbage Collection!
  #define cons_bit_t       7  # gesetzt nur bei CONS
  #define symbol_bit_t     6  # gesetzt nur bei SYMBOL
  #define number_bit_t     2  # gesetzt nur bei Zahlen
  #define notsimple_bit_t  0  # bei Arrays: gel�scht bei Simple-Arrays
  #define sign_bit_t       0  # Vorzeichen bei reellen Zahlen (gesetzt <==> Zahl <0)
  #define float_bit_t      5
  #define float1_bit_t     3
  #define float2_bit_t     4
  #define ratio_bit_t      3
  #define bignum_bit_t     4
# in Objekten (oint):
  #define garcol_bit_o     (garcol_bit_t+oint_type_shift)    # gesetzt nur w�hrend der Garbage Collection!
  #define cons_bit_o       (cons_bit_t+oint_type_shift)      # gesetzt nur bei CONS
  #define symbol_bit_o     (symbol_bit_t+oint_type_shift)    # gesetzt nur bei SYMBOL
  #define number_bit_o     (number_bit_t+oint_type_shift)    # gesetzt nur bei Zahlen
  #define notsimple_bit_o  (notsimple_bit_t+oint_type_shift) # bei Arrays: gel�scht bei Simple-Arrays
  #define sign_bit_o       (sign_bit_t+oint_type_shift)      # Vorzeichen bei reellen Zahlen
  #define float_bit_o      (float_bit_t+oint_type_shift)
  #define float1_bit_o     (float1_bit_t+oint_type_shift)
  #define float2_bit_o     (float2_bit_t+oint_type_shift)
  #define ratio_bit_o      (ratio_bit_t+oint_type_shift)
  #define bignum_bit_o     (bignum_bit_t+oint_type_shift)

# konstante Typcodes:
  #define machine_type   0x00  # %00000000  ; Maschinenpointer
  #define sbvector_type  0x10  # %00010000  ; Simple-Bit-Vector
  #define sstring_type   0x08  # %00001000  ; Simple-String
  #define svector_type   0x18  # %00011000  ; Simple-Vector
  #define mdarray_type   0x01  # %00000001  ; sonstiger Array (Rang /=1 oder
                               #            ; - sp�ter vielleicht - anderer Elementtyp)
  #define bvector_type   0x11  # %00010001  ; sonstiger Bit-Vector oder Byte-Vector
  #define string_type    0x09  # %00001001  ; sonstiger String
  #define vector_type    0x19  # %00011001  ; sonstiger (VECTOR T)
  #define closure_type   0x20  # %00100000  ; Closure
  #define structure_type 0x21  # %00100001  ; Structure
  #define stream_type    0x28  # %00101000  ; Stream
  #define orecord_type   0x29  # %00101001  ; OtherRecord (Package, Byte, ...)
  #define instance_type  0x39  # %00111001  ; CLOS-Instanz
  #define char_type      0x31  # %00110001  ; Character
  #define subr_type      0x30  # %00110000  ; SUBR
  #define system_type    0x38  # %00111000  ; Frame-Pointer, Read-Label, SYSTEM
  #define fixnum_type    0x04  # %00000100  ; Fixnum
  #define sfloat_type    0x24  # %00100100  ; Short-Float
  #define bignum_type    0x14  # %00010100  ; Bignum
  #define ffloat_type    0x34  # %00110100  ; Single-Float
  #define ratio_type     0x0C  # %00001100  ; Ratio
  #define dfloat_type    0x2C  # %00101100  ; Double-float
  #define complex_type   0x1C  # %00011100  ; Complex
  #define lfloat_type    0x3C  # %00111100  ; Long-Float
  #define symbol_type    0x40  # %01000000  ; Symbol
          # Bits f�r Symbole in VAR/FUN-Frames (im LISP-Stack):
          #define active_bit  3  # gesetzt: Bindung ist aktiv
          #define dynam_bit   4  # gesetzt: Bindung ist dynamisch
          #define svar_bit    5  # gesetzt: n�chster Parameter ist supplied-p-Parameter f�r diesen
          #define oint_symbolflags_shift  oint_type_shift
          # Bits f�r Symbole im Selbstpointer:
          #define constant_bit_t  3  # zeigt an, ob das Symbol eine Konstante ist
          #define special_bit_t   4  # zeigt an, ob das Symbol SPECIAL-proklamiert ist
  #define cons_type      0x80  # %10000000  ; Cons

# Typ ist GC-invariant, wenn
# Typinfobyte eines von 0x00,0x04,0x05,0x24,0x25,0x30,0x31,0x38 ist.
  #define gcinvariant_type_p(type)  \
    (((type)<0x39) && (((type)==0) || !((bit((type)>>1) & 0x11040004) == 0)))

#endif # SUN3_TYPECODES

#if !(gcinvariant_type_p(ffloat_type) == defined(WIDE))
  #error "gcinvariant_type_p() fehlerhaft implementiert!"
#endif

# Test for gc-invariant object. (This includes immediate, machine, subr.)
# gcinvariant_object_p(obj)
  #define gcinvariant_object_p(obj)  \
    gcinvariant_type_p(typecode(obj))

#else # no TYPECODES

# Bits f�r Symbole in VAR/FUN-Frames (im LISP-Stack):
# sitzen nicht im oint_type-Teil, sondern im oint_data-Teil.
  #define active_bit  0  # gesetzt: Bindung ist aktiv
  #define dynam_bit   1  # gesetzt: Bindung ist dynamisch
  #define svar_bit    2  # gesetzt: n�chster Parameter ist supplied-p-Parameter f�r diesen
#define NO_symbolflags # active_bit, dynam_bit, svar_bit haben im Symbol keinen Platz

# Bits f�r Symbole in den Flags:
  #define constant_bit_f  0  # zeigt an, ob das Symbol eine Konstante ist
  #define special_bit_f   1  # zeigt an, ob das Symbol SPECIAL-proklamiert ist

#endif


# Was von einer Adresse auch wirklich auf den Adressbus geschickt wird:
#if defined(MC68000)
  #define hardware_addressbus_mask  0x00FFFFFFUL  # 68000 wirft 8 Bits weg
#elif defined(SUN3) && !defined(UNIX_SUNOS4)
  #define hardware_addressbus_mask  0x0FFFFFFFUL  # SUN3 unter SunOS 3.5 wirft 4 Bits weg
#else
  #define hardware_addressbus_mask  ~0UL  # Default: nichts wird weggeworfen
#endif
# Durch geschicktes Memory-Mapping braucht man bestimmte Bits
# nicht mehr auszumaskieren, bevor man auf die Adresse zugreift:
#define addressbus_mask  hardware_addressbus_mask
#ifdef MAP_MEMORY
  #if defined(SUN4_29_1)
    # Durchs Memory-Mapping sind jetzt die Bits 28..24 einer Adresse redundant.
    #undef addressbus_mask
    #define addressbus_mask  0xE0FFFFFFUL
  #elif defined(DECALPHA) && defined(UNIX_OSF)
    # Durchs Memory-Mapping sind jetzt die Bits 37..33 einer Adresse redundant.
    #undef addressbus_mask
    #define addressbus_mask  0xFFFFFFC1FFFFFFFFUL
  #elif !defined(WIDE_SOFT)
    # Durchs Memory-Mapping sind jetzt die Bits 31..24 einer Adresse redundant.
    #undef addressbus_mask
    #define addressbus_mask  oint_addr_mask  # meist = 0x00FFFFFFUL
  #endif
#endif


#if defined(SINGLEMAP_MEMORY) && (((system_type*1UL << oint_type_shift) & addressbus_mask) == 0)
  # Auch der STACK liegt in einem Singlemap-Bereich, Typinfo system_type.
  #define SINGLEMAP_MEMORY_STACK
#endif


#ifdef oint_symbolflags_shift
  #if defined(SINGLEMAP_MEMORY) && (oint_symbolflags_shift==oint_type_shift)
    # Da wir die symbol_tab nicht multimappen k�nnen, m�ssen wir auf extra Bits
    # im Typcode von Symbolen verzichten.
    #undef oint_symbolflags_shift
    #define NO_symbolflags
  #endif
#endif
#ifdef NO_symbolflags
  #define oint_symbolflags_shift  -1 # ung�ltiger Wert
#endif


# ################### Methode der Speicherverwaltung ###################### #

# SPVW_BLOCKS : Speicherverwaltung mit wenigen Speicherbl�cken
# SPVW_PAGES  : Speicherverwaltung mit vielen Speicherseiten
# SPVW_MIXED  : Objekte verschiedenen Typs in derselben Seite/demselben Block
#               m�glich
# SPVW_PURE   : Jeder Speicherblock/jede Speicherseite enth�lt nur Objekte
#               ein und desselben Typs
#if defined(WATCOM) || defined(MAP_MEMORY) || defined(TRIVIALMAP_MEMORY)
  # Auf der DOSe mit dem WATCOM-Extender steht nur endlich viel Speicher
  # zur Verf�gung.
  # Multimapping einzelner Pages ist noch nicht implementiert.??
  # Singlemapping einzelner Pages ist noch nicht implementiert.??
  # Verwendet man mmap() als malloc()-Ersatz, braucht man keine einzelnen Pages.
  #define SPVW_BLOCKS
#elif defined(AMIGA) || defined(VIRTUAL_MEMORY)
  # Auf dem Amiga sollte man nicht zu viel Speicher auf einmal holen.
  # Auf Unix-Systemen kann man nachtr�glich immer noch Speicher holen,
  # man sollte aber die Daten wenn m�glich in wenigen Pages konzentrieren.
  #define SPVW_PAGES
#else
  #define SPVW_BLOCKS
#endif
#if defined(MULTIMAP_MEMORY)
  # MULTIMAP_MEMORY -> Mixed Pages dienen besserer Speicher-Ausnutzung.
  #define SPVW_MIXED
#elif defined(SINGLEMAP_MEMORY)
  # SINGLEMAP_MEMORY -> Nur Pure Pages/Blocks sinnvoll, denn
  # die Adresse einer Page bestimmt den Typ der Objekte, die sie enth�lt.
  #define SPVW_PURE
#elif !defined(TYPECODES) || defined(MC68000) || defined(SUN3) || defined(AMIGA) || defined(SPVW_BLOCKS) || defined(TRIVIALMAP_MEMORY)
  # !TYPECODES -> es gibt keine wirklichen typecodes, nur Cons und Varobject.
  # MC68000 oder SUN3 -> type_pointable(...) kostet nichts oder nur wenig.
  # AMIGA -> nur endlich viel Speicher, Mixed Pages nutzen ihn besser.
  # SPVW_BLOCKS -> SPVW_PURE_BLOCKS nur f�r SINGLEMAP_MEMORY implementiert.
  # TRIVIALMAP_MEMORY -> Nicht viele Bl�cke m�glich, da wenig Adressraum.
  #define SPVW_MIXED
#elif 1 # vorl�ufig! ??
  #define SPVW_MIXED
#endif
#if !(defined(SPVW_BLOCKS) || defined(SPVW_PAGES))
  #error "SPVW_BLOCKS/SPVW_PAGES neu einstellen!"
#endif
#if !(defined(SPVW_MIXED) || defined(SPVW_PURE))
  #error "SPVW_MIXED/SPVW_PURE neu einstellen!"
#endif
#if (defined(SPVW_BLOCKS) && defined(SPVW_PURE)) != defined(SINGLEMAP_MEMORY)
  #error "SINGLEMAP_MEMORY impliziert SPVW_PURE_BLOCKS und umgekehrt!"
#endif
#if (defined(SPVW_BLOCKS) && defined(SPVW_MIXED)) < defined(TRIVIALMAP_MEMORY)
  #error "TRIVIALMAP_MEMORY impliziert SPVW_MIXED_BLOCKS!"
#endif
#if (defined(SPVW_BLOCKS) && (defined(SPVW_PURE) || defined(SPVW_MIXED))) < defined(GENERATIONAL_GC)
  #error "GENERATIONAL_GC impliziert SPVW_PURE_BLOCKS oder SPVW_MIXED_BLOCKS_STAGGERED oder SPVW_MIXED_BLOCKS_OPPOSITE!"
#endif
#if (defined(SPVW_BLOCKS) && (defined(SPVW_PURE) || defined(SPVW_MIXED))) < defined(SELFMADE_MMAP)
  #error "SELFMADE_MMAP impliziert SPVW_PURE_BLOCKS oder SPVW_MIXED_BLOCKS_STAGGERED!"
#endif

# Algorithmus nach Morris, der die Conses kompaktiert, ohne sie dabei
# durcheinanderzuw�rfeln:
#if defined(SPVW_BLOCKS) && defined(VIRTUAL_MEMORY) && !defined(NO_MORRIS_GC)
  # Morris-GC ist zu empfehlen, weil es die Lokalit�t erh�lt.
  #define MORRIS_GC
#endif

# Lege subr_tab und symbol_tab per Memory-Mapping an vorgegebene Adressen.
# (Die Morris-GC verwendet bei MULTIMAP_MEMORY den Macro upointer(). Bei
# &symbol_tab = 0x20000000 w�re upointer(NIL)=0. Mist!)
#if defined(MAP_MEMORY) && !defined(WIDE_SOFT) && !(defined(MULTIMAP_MEMORY) && defined(MORRIS_GC))
  #define MAP_MEMORY_TABLES
#endif


# ################# Fallunterscheidungen nach Typcodes #################### #

#ifdef TYPECODES

# Einzuleiten durch switch (typecode(obj)), danach wie in einer
# switch-Anweisung beliebig viele case-Labels.
# Beispiel:  switch (typecode(arg)) { case_string: ...; break; ... }
  #define case_machine    case machine_type   # Maschinenpointer
  #define case_sstring    case sstring_type   # Simple-String
  #define case_ostring    case string_type    # Other String
  #define case_sbvector   case sbvector_type  # Simple-Bit-Vector
  #define case_obvector   case bvector_type   # Other Bit/Byte-Vector
  #define case_svector    case svector_type   # Simple-(General-)Vector
  #define case_ovector    case vector_type    # Other (General-)Vector
  #define case_mdarray    case mdarray_type   # sonstiger Array
  #define case_string     case_sstring: case_ostring # String allgemein
  #define case_bvector    case_sbvector: case_obvector # Bit-Vector allgemein
  #define case_vector     case_svector: case_ovector # (General-)Vector allgemein
  #define case_array      case_string: case_bvector: case_vector: case_mdarray # Array allgemein
  #define case_closure    case closure_type   # Closure
  #ifdef structure_type
  #define case_structure  case structure_type # Structure
  #define _case_structure case_structure:
  #else
  #define structure_type  orecord_type        # Structures sind OtherRecords
  #define _case_structure
  #endif
  #ifdef stream_type
  #define case_stream     case stream_type    # Stream
  #define _case_stream    case_stream:
  #else
  #define stream_type     orecord_type        # Streams sind OtherRecords
  #define _case_stream
  #endif
  #define case_orecord    case orecord_type   # Other Record
  #define case_instance   case instance_type  # CLOS-Instanz
  #define case_char       case char_type      # Character
  #define case_subr       case subr_type      # SUBR
  #define case_system     case system_type    # Frame-Pointer, Read-Label, System
  #define case_posfixnum  case fixnum_type    # Fixnum >=0
  #define case_negfixnum  case fixnum_type|bit(sign_bit_t) # Fixnum <0
  #define case_fixnum     case_posfixnum: case_negfixnum # Fixnum
  #define case_posbignum  case bignum_type    # Bignum >0
  #define case_negbignum  case bignum_type|bit(sign_bit_t) # Bignum <0
  #define case_bignum     case_posbignum: case_negbignum # Bignum
  #define case_integer    case_fixnum: case_bignum # Integer
  #define case_ratio      case ratio_type: case ratio_type|bit(sign_bit_t) # Ratio
  #ifdef SPVW_MIXED
  #define _case_ratio     case_ratio:
  #else
  #define _case_ratio
  #endif
  #define case_rational   case_integer: case_ratio # Rational
  #define case_sfloat     case sfloat_type: case sfloat_type|bit(sign_bit_t) # Short-Float
  #define case_ffloat     case ffloat_type: case ffloat_type|bit(sign_bit_t) # Single-Float
  #define case_dfloat     case dfloat_type: case dfloat_type|bit(sign_bit_t) # Double-Float
  #define case_lfloat     case lfloat_type: case lfloat_type|bit(sign_bit_t) # Long-Float
  #define case_float      case_sfloat: case_ffloat: case_dfloat: case_lfloat # Float
  #define case_real       case_rational: case_float # Real
  #define case_complex    case complex_type # Complex
  #ifdef SPVW_MIXED
  #define _case_complex   case_complex:
  #else
  #define _case_complex
  #endif
  #define case_number     case_real: case_complex # Number
  #define case_symbol     case symbol_type # Symbol
  #define case_record     case_closure: _case_structure _case_stream _case_ratio _case_complex case_orecord: case_instance # Record allgemein
  #if /* !defined(NO_symbolflags) && */ (oint_symbolflags_shift==oint_type_shift)
  #define case_symbolflagged  # Symbol mit Flags \
                          case symbol_type: \
                          case symbol_type|bit(active_bit): \
                          case symbol_type|bit(dynam_bit): \
                          case symbol_type|bit(dynam_bit)|bit(active_bit): \
                          case symbol_type|bit(svar_bit): \
                          case symbol_type|bit(svar_bit)|bit(active_bit): \
                          case symbol_type|bit(svar_bit)|bit(dynam_bit): \
                          case symbol_type|bit(svar_bit)|bit(dynam_bit)|bit(active_bit)
  #else
  #define case_symbolflagged  case_symbol # Symbol mit Flags
  #endif
  #define case_cons       case cons_type # Cons

#else

  #define _case_structure
  #define _case_stream

#endif


# ################## Speicheraufbau von LISP-Objekten ##################### #

# uintWC ist der Integer-Typ f�r die L�ngen von Bignum, Lfloat, Iarray.
# Teilmengenrelation: uintW <= uintWC <= uintC.
  #ifdef TYPECODES
    #define intWCsize intCsize
    typedef uintC uintWC;
    typedef sintC sintWC;
  #else
    # Type and sign are stored in the heap - only 16 bits for the length.
    #define intWCsize intWsize
    typedef uintW uintWC;
    typedef sintW sintWC;
  #endif
# uintWCoverflow(x) stellt fest, ob nach Ausf�hren eines x++ ein Overflow
# eingetreten ist.
  #define uintWCoverflow(x)  ((intWCsize<intLsize) && ((uintWC)(x)==0))

# ---------------------- Objects with two pointers ---------------------- #
# They contain just the two pointers, no header. The type must already be
# known when the object is accessed.

# Normally, Cons, Ratio, Complex can all be considered as pairs. But if
# SPVW_MIXED, the heap statistics are a little unspecific if we mix the
# three types; therefore in that case we let Ratio and Complex be Varobjects.
#ifdef SPVW_MIXED
  #define case_pair  case_cons
#else
  #define case_pair  case_cons: case_ratio: case_complex
#endif

# ---------------------- Objects of varying length ---------------------- #
# The first word is reserved for garbage collection. Outside of garbage
# collection, it contains a pointer to the object itself. Note that the
# GC, when it moves an object, takes care not to modify the typecode of
# this first word (except the GC bit, which it temporarily uses).

# Typ der Header-Flags:
  #if (oint_type_len<=8) && !defined(ARM) && !defined(DECALPHA)
    # Zugriff auf ein einzelnes Byte m�glich
    #define hfintsize  intBsize
    typedef uintB  hfint;
  #else
    # Zugriff auf ein ganzes Wort
    #define hfintsize  intLsize
    typedef uintL  hfint;
  #endif

# Objekt variabler L�nge
#ifdef TYPECODES
  #define VAROBJECT_HEADER  \
               union { object _GCself;  # Selbstpointer f�r GC            \
                       hfint flags[sizeof(object)/sizeof(hfint)]; # Flags \
                     } header;
#else
  #define VAROBJECT_HEADER  \
               object GCself;  # Selbstpointer f�r GC \
               uintL tfl;      # Type, Flags, L�nge
#endif
typedef struct { VAROBJECT_HEADER }
        varobject_;
typedef varobject_ *  Varobject;
#ifdef TYPECODES
  #define GCself  header._GCself
  # Der Typcode ist im Byte ((Varobject)p)->header_flags enthalten.
    #if !(oint_type_len>=hfintsize ? oint_type_shift%hfintsize==0 : floor(oint_type_shift,hfintsize)==floor(oint_type_shift+oint_type_len-1,hfintsize))
      #error "Bogus header_flags -- header_flags neu definieren!"
    #endif
    #if BIG_ENDIAN_P
      #define header_flags  header.flags[sizeof(object)/sizeof(hfint)-1-floor(oint_type_shift,hfintsize)]
    #else
      #define header_flags  header.flags[floor(oint_type_shift,hfintsize)]
    #endif
    # Es gilt  mtypecode(((Varobject)p)->GCself) =
    # (((Varobject)p)->header_flags >> (oint_type_shift%hfintsize)) & tint_type_mask
    # Bits f�r Symbole im Selbstpointer (siehe oben):
    # define constant_bit_t  ...  # zeigt an, ob das Symbol eine Konstante ist
    # define special_bit_t   ...  # zeigt an, ob das Symbol SPECIAL-proklamiert ist
    #define constant_bit_hf  (constant_bit_t+(oint_type_shift%hfintsize))
    #define special_bit_hf  (special_bit_t+(oint_type_shift%hfintsize))
#else
  # Three possible layouts of type, flags, length:
  #   8 bits type, 24 bits length [Lrecord]
  #   8 bits type, 8 bits flags, 16 bits length [Srecord]
  #   8 bits type, 8 bits flags, 8 bits length, 8 bits xlength [Xrecord]
    #define lrecord_tfl(type,length)  \
      ((uintL)(uintB)(type)+((uintL)(length)<<8))
    #define srecord_tfl(type,flags,length)  \
      ((uintL)(uintB)(type)+((uintL)(uintB)(flags)<<8)+((uintL)(length)<<16))
    #define xrecord_tfl(type,flags,length,xlength)  \
      ((uintL)(uintB)(type)+((uintL)(uintB)(flags)<<8)+((uintL)(uintB)(length)<<16)+((uintL)(uintB)(xlength)<<24))
  #define varobject_type(ptr) ((sintB)((ptr)->tfl & 0xFF))
  #if defined(__GNUC__) && (__GNUC__ == 2) && ((__GNUC_MINOR__ == 8) || (__GNUC_MINOR__ == 90))
    # Work around a gcc bug present (at least) in gcc-2.8.1 on hppa and
    # egcs-1.0.3a on i386. It miscompiles xpathnamep.
    #undef varobject_type
    #define varobject_type(ptr) ((sintB)((sintL)((ptr)->tfl) & 0xFF))
  #endif
  # Bits for symbols in the flags:
    #define header_flags  tfl
    #define constant_bit_hf  (constant_bit_f+8)
    #define special_bit_hf  (special_bit_f+8)
#endif

# Records
# These are varobjects with a one-byte type field in memory.
# There are three types of records:
#   Long-Records can have up to 16777215 elements, but have no flags.
#   Simple-Records can have up to 65535 elements,
#   Extended-Records have room for up to 255 elements and 255 extra (non-Lisp)
#   elements.
# Long-Records are recognized by their type field:
#   rectype == Rectype_Sbvector, Rectype_Sstring, Rectype_Svector.
# The others are partitioned into:
#   - Simple-Records, if rectype < rectype_limit.
#   - Extended-Records, if rectype >= rectype_limit.

typedef struct { VAROBJECT_HEADER # Selbstpointer f�r GC
                 #ifdef TYPECODES
                 uintB recflags;  # bei OtherRecord: Flags
                 sintB rectype;   # bei OtherRecord: Untertyp
                 uintW recfiller; # L�nge u.a.
                 #endif
                 object recdata[unspecified]; # Elemente
               }
        record_;
typedef record_ *  Record;
# Zugriff auf type, flags:
  #ifdef TYPECODES
    #define record_type(ptr)  ((ptr)->rectype)
  #else
    #define record_type(ptr)  varobject_type(ptr)
  #endif
  #define Record_type(obj)  record_type(TheRecord(obj))
  #ifdef TYPECODES
    #define record_flags(ptr)  ((ptr)->recflags)
  #else
    #define record_flags(ptr)  (((ptr)->tfl >> 8) & 0xFF)
  #endif
  #define Record_flags(obj)  record_flags(TheRecord(obj))
  #ifdef TYPECODES
    #define record_flags_clr(ptr,bits)  ((ptr)->recflags &= ~(bits))
    #define record_flags_set(ptr,bits)  ((ptr)->recflags |= (bits))
    #define record_flags_replace(ptr,newflags)  ((ptr)->recflags = (newflags))
  #else
    #define record_flags_clr(ptr,bits)  ((ptr)->tfl &= ~((uintL)(bits) << 8))
    #define record_flags_set(ptr,bits)  ((ptr)->tfl |= ((uintL)(bits) << 8))
    #define record_flags_replace(ptr,newflags)  \
      ((ptr)->tfl ^= (((ptr)->tfl ^ (uintL)(newflags)<<8) & 0xFF00))
  #endif

#ifdef TYPECODES
  #define LRECORD_HEADER  \
                 VAROBJECT_HEADER # Selbstpointer f�r GC \
                 uintL length;    # L�nge
#else
  #define LRECORD_HEADER  \
                 VAROBJECT_HEADER # Selbstpointer f�r GC, tfl
#endif
typedef struct { LRECORD_HEADER }
        lrecord_;
typedef lrecord_ *  Lrecord;
#ifdef TYPECODES
  #define lrecord_length(ptr)  ((ptr)->length)
#else
  #define lrecord_length(ptr)  ((ptr)->tfl >> 8)
#endif

#ifdef TYPECODES
  #define SRECORD_HEADER  \
                 VAROBJECT_HEADER # Selbstpointer f�r GC      \
                 uintB recflags;  # Flags                     \
                 sintB rectype;   # Untertyp, < rectype_limit \
                 uintW reclength; # L�nge in Objekten
#else
  #define SRECORD_HEADER  \
                 VAROBJECT_HEADER # Selbstpointer f�r GC, tfl
#endif
typedef struct { SRECORD_HEADER
                 object recdata[unspecified]; # Elemente, reclength St�ck
               }
        srecord_;
typedef srecord_ *  Srecord;
#ifdef TYPECODES
  #define srecord_length(ptr)  ((ptr)->reclength)
#else
  #define srecord_length(ptr)  ((ptr)->tfl >> 16)
#endif
#define Srecord_length(obj)  srecord_length(TheSrecord(obj))

#ifdef TYPECODES
  #define XRECORD_HEADER  \
                 VAROBJECT_HEADER  # Selbstpointer f�r GC       \
                 uintB recflags;   # Flags                      \
                 sintB rectype;    # Untertyp, >= rectype_limit \
                 uintB reclength;  # L�nge in Objekten          \
                 uintB recxlength; # L�nge der Extra-Elemente
#else
  #define XRECORD_HEADER  \
                 VAROBJECT_HEADER  # Selbstpointer f�r GC, tfl
#endif
typedef struct { XRECORD_HEADER
                 object recdata[unspecified];  # Elemente, reclength St�ck
               # uintB  recxdata[unspecified]; # Extra-Elemente, recxlength St�ck
               }
        xrecord_;
typedef xrecord_ *  Xrecord;
#ifdef TYPECODES
  #define xrecord_length(ptr)  ((ptr)->reclength)
  #define xrecord_xlength(ptr)  ((ptr)->recxlength)
#else
  #define xrecord_length(ptr)  (((ptr)->tfl >> 16) & 0xFF)
  #define xrecord_xlength(ptr)  ((ptr)->tfl >> 24)
#endif
#define Xrecord_length(obj)  xrecord_length(TheXrecord(obj))
#define Xrecord_xlength(obj)  xrecord_xlength(TheXrecord(obj))

# Possible rectype values for records.
  enum {
           enum_rectype_first = -4,     # Try to keep rectype_limit = 0.
         Rectype_Closure,
         Rectype_Structure,             # only used #ifndef case_structure
         Rectype_Instance,
           rectype_limit, # Here is the limit between Srecord and Xrecord.
         Rectype_Hashtable = rectype_limit,
         #ifndef TYPECODES
                          # Here the arrays start.
         Rectype_Sbvector,      /* 1 */ # Sbvector, not Srecord/Xrecord
         Rectype_Sstring,       /* 2 */ # Sstring, not Srecord/Xrecord
         Rectype_Svector,       /* 3 */ # Svector, not Srecord/Xrecord
         Rectype_mdarray,       /* 4 */ # Iarray, not Srecord/Xrecord
         Rectype_bvector,       /* 5 */ # Iarray, not Srecord/Xrecord
         Rectype_string,        /* 6 */ # Iarray, not Srecord/Xrecord
         Rectype_vector,        /* 7 */ # Iarray, not Srecord/Xrecord
                          # Here the arrays end.
                          # Here the numbers start.
         Rectype_Bignum,                # Bignum, not Srecord/Xrecord
         Rectype_Lfloat,                # Lfloat, not Srecord/Xrecord
         Rectype_Dfloat,
         Rectype_Ffloat,
         #endif
         #ifdef SPVW_MIXED
         Rectype_Ratio,
         Rectype_Complex,
         #endif
                          # Here the numbers end.
         #ifndef TYPECODES
         Rectype_Symbol,
         #endif
         Rectype_Package,
         Rectype_Readtable,
         Rectype_Pathname,
         #ifdef LOGICAL_PATHNAMES
         Rectype_Logpathname,
         #endif
         Rectype_Random_State,
         #ifndef case_stream
         Rectype_Stream,
         #endif
         Rectype_Byte,
         Rectype_Fsubr,
         Rectype_Loadtimeeval,
         Rectype_Symbolmacro,
         Rectype_Fpointer,              # only used #ifdef FOREIGN
         #ifdef DYNAMIC_FFI
         Rectype_Faddress,
         Rectype_Fvariable,
         Rectype_Ffunction,
         #endif
         Rectype_Weakpointer,
         Rectype_Finalizer,
         #ifdef SOCKET_STREAMS
         Rectype_Socket_Server,
         #endif
         #ifdef YET_ANOTHER_RECORD
         Rectype_Yetanother,
         #endif
         rectype_for_broken_compilers_that_dont_like_trailing_commas
       };

# -------------------------- the various types -------------------------- #

# Cons
typedef struct { object cdr; # CDR
                 object car; # CAR
               }
        cons_;
typedef cons_ *  Cons;

# Ratio
typedef struct {
                 #ifdef SPVW_MIXED
                 XRECORD_HEADER
                 #endif
                 object rt_num; # Z�hler, Integer
                 object rt_den; # Nenner, Integer >0
               }
        ratio_;
typedef ratio_ *  Ratio;

# Complex
typedef struct {
                 #ifdef SPVW_MIXED
                 XRECORD_HEADER
                 #endif
                 object c_real; # Realteil, reelle Zahl
                 object c_imag; # Imagin�rteil, reelle Zahl
               }
        complex_;
typedef complex_ *  Complex;

# Symbol
typedef struct { VAROBJECT_HEADER
                 object symvalue;    # Wertzelle
                 object symfunction; # Funktiondefinitionszelle
                 object proplist;    # Property-Liste
                 object pname;       # Printname
                 object homepackage; # Home-Package oder NIL
               }
        symbol_;
typedef symbol_ *  Symbol;
#define symbol_objects_offset  offsetof(symbol_,symvalue)

# Jedes Keyword ist eine Konstante.

# Test, ob ein Symbol ein Keyword ist:
  #define keywordp(sym)  \
    (eq(TheSymbol(sym)->homepackage,O(keyword_package)))

# Bei Konstanten ist das Special-Bit bedeutungslos (denn Konstanten
# k�nnen bei uns weder lexikalisch noch dynamisch gebunden werden).

# Test, ob ein Symbol eine Konstante ist:
  #define constantp(sym)  \
    (((sym)->header_flags) & bit(constant_bit_hf))

# Test, ob ein Symbol eine SPECIAL-proklamierte Variable ist:
  #define special_var_p(sym)  \
    (((sym)->header_flags) & bit(special_bit_hf))

# Constant-Flag eines Symbols setzen:
  #define set_const_flag(sym)  \
    (((sym)->header_flags) |= bit(constant_bit_hf))

# Constant-Flag eines Symbols l�schen:
# (Symbol darf kein Keyword sein, vgl. spvw.d:case_symbolwithflags)
  #define clear_const_flag(sym)  \
    (((sym)->header_flags) &= ~bit(constant_bit_hf))

# Special-Flag eines Symbols setzen:
  #define set_special_flag(sym)  \
    (((sym)->header_flags) |= bit(special_bit_hf))

# Special-Flag eines Symbols l�schen:
  #define clear_special_flag(sym)  \
    (((sym)->header_flags) &= ~bit(special_bit_hf))

# Symbol als Konstante mit gegebenem Wert val definieren.
# val darf keine GC ausl�sen!
  #define define_constant(sym,val)  \
    {var Symbol sym_from_define_constant = TheSymbol(sym); \
     set_const_flag(sym_from_define_constant);             \
     sym_from_define_constant->symvalue = (val);           \
    }

# Symbol als Variable mit gegebenem Initialisierungswert val definieren.
# val darf keine GC ausl�sen!
  #define define_variable(sym,val)  \
    {var Symbol sym_from_define_variable = TheSymbol(sym); \
     set_special_flag(sym_from_define_variable);           \
     sym_from_define_variable->symvalue = (val);           \
    }

# Flagbits in einem Symbol entfernen:
  #if defined(NO_symbolflags)
    #define symbol_without_flags(symbol)  symbol
  #elif (oint_symbolflags_shift==oint_type_shift)
    #define symbol_without_flags(symbol)  \
      as_object(as_oint(symbol) & (type_zero_oint(symbol_type) | oint_addr_mask))
  #else
    #define symbol_without_flags(symbol)  \
      as_object(as_oint(symbol) & ~((wbit(active_bit)|wbit(dynam_bit)|wbit(svar_bit))<<oint_symbolflags_shift))
  #endif

# Characters

# Integer type holding the data of a character:
  #define char_int_len 8
  #define char_int_limit  (1UL<<char_int_len)
  typedef unsigned_int_with_n_bits(char_int_len)  cint;
  #define char_code_limit  char_int_limit
# Converting an integral code to a character:
  #define int_char(int_from_int_char)  \
    type_data_object(char_type,(aint)(cint)(int_from_int_char))
# Converting a character to an integral code:
  #if !((oint_data_shift==0) && (char_int_len<=oint_data_len) && (exact_uint_size_p(char_int_len)))
    #ifdef TYPECODES
      #define char_int(char_from_char_int)  \
        ((cint)(untype(char_from_char_int)))
    #else
      #define char_int(char_from_char_int)  \
        ((cint)(as_oint(char_from_char_int)>>oint_data_shift))
    #endif
  #else
    # If oint_data_shift=0, untype needs not to shift. If also
    # char_int_len<=oint_data_len, and if a cint has exactly char_int_len
    # bits, untype needs not to AND.
    #define char_int(char_from_char_int)  \
      ((cint)as_oint(char_from_char_int))
  #endif
# Characters can therefore be compared for equality using EQ, this is an
# oint comparison, among the characters a comparison of their integral code.

# A standalone character. Prefer `chart' to `cint' wherever possible because
# it is typesafe. sizeof(chart) = sizeof(cint).
  #ifdef CHART_STRUCT
    typedef struct { cint one; } chart;
  #else
    typedef cint chart;
  #endif
# Conversions between both:
# as_cint(ch)   chart --> cint
# as_chart(c)   cint --> chart
  #ifdef CHART_STRUCT
    #define as_cint(ch)  ((ch).one)
    #if 1
      #define as_chart(c)  ((chart){one:(c)})
    #else
      extern __inline__ chart as_chart (register cint c)
        { register chart ch; ch.one = c; return ch; }
    #endif
  #else
    #define as_cint(ch)  (ch)
    #define as_chart(c)  (c)
  #endif
# Conversion chart --> object.
  #define code_char(ch)  int_char(as_cint(ch))
# Conversion object --> chart.
  #define char_code(obj)  as_chart(char_int(obj))
# Comparison operations.
  #define chareq(ch1,ch2)  (as_cint(ch1) == as_cint(ch2))
  #define charlt(ch1,ch2)  (as_cint(ch1) < as_cint(ch2))
  #define chargt(ch1,ch2)  (as_cint(ch1) > as_cint(ch2))

# Conversion standard char (in ASCII encoding) --> chart.
  #define ascii(x)  as_chart((uintB)(x))
# Conversion standard char (in ASCII encoding) --> object.
  #define ascii_char(x)  code_char(ascii(x))

# Base characters are those whose code is < base_char_code_limit.
  #define base_char_int_len 8
  #define base_char_int_limit  (1UL<<base_char_int_len)
  typedef unsigned_int_with_n_bits(base_char_int_len)  bcint;
  #define base_char_code_limit  base_char_int_limit

# Fixnums

# fixnum(x) ist ein Fixnum mit Wert x>=0.
# x eine Expression mit 0 <= x < 2^oint_data_len.
# (Sollte eigentlich posfixnum(x) hei�en.)
  #define fixnum(x)  type_data_object(fixnum_type,x)

# Fixnum_0 ist die Zahl 0, Fixnum_1 ist die Zahl 1,
# Fixnum_minus1 ist die Zahl -1
  #define Fixnum_0  fixnum(0)
  #define Fixnum_1  fixnum(1)
  #define Fixnum_minus1  type_data_object( fixnum_type | bit(sign_bit_t), bitm(oint_data_len)-1 )

# Wert eines nichtnegativen Fixnum:
# posfixnum_to_L(obj)
# Ergebnis ist >= 0, < 2^oint_data_len.
  #if !(defined(SPARC) && (oint_data_len+oint_data_shift<32))
    #define posfixnum_to_L(obj)  \
      ((uintL)((as_oint(obj)&((oint)wbitm(oint_data_len+oint_data_shift)-1))>>oint_data_shift))
  #else
    # Auf einem SPARC-Prozessor sind lange Konstanten langsamer als Shifts:
    #define posfixnum_to_L(obj)  \
      ((uintL)((as_oint(obj) << (32-oint_data_len-oint_data_shift)) >> (32-oint_data_len)))
  #endif

# Wert eines negativen Fixnum:
# negfixnum_to_L(obj)
# Ergebnis ist >= - 2^oint_data_len, < 0.
  #define negfixnum_to_L(obj)  (posfixnum_to_L(obj) | (-bitm(oint_data_len)))

# Betrag eines negativen Fixnum:
# negfixnum_abs_L(obj)
# Ergebnis ist > 0, <= 2^oint_data_len.
# Vorsicht: Wraparound bei oint_data_len=intLsize m�glich!
  #define negfixnum_abs_L(obj)  \
    ((uintL)((as_oint(fixnum_inc(Fixnum_minus1,1))-as_oint(obj))>>oint_data_shift))

# Wert eines Fixnum, obj sollte eine Variable sein:
# fixnum_to_L(obj)
# Ergebnis ist >= - 2^oint_data_len, < 2^oint_data_len und vom Typ sintL.
# Die Verwendung dieses Macros ist nur bei oint_data_len+1 <= intLsize sinnvoll!
  #if (oint_data_len>=intLsize)
    # Kein Platz mehr f�rs Vorzeichenbit, daher fixnum_to_L = posfixnum_to_L = negfixnum_to_L !
    #define fixnum_to_L(obj)  (sintL)posfixnum_to_L(obj)
  #elif (sign_bit_o == oint_data_len+oint_data_shift)
    #define fixnum_to_L(obj)  \
      (((sintL)as_oint(obj) << (intLsize-1-sign_bit_o)) >> (intLsize-1-sign_bit_o+oint_data_shift))
  #else
    #if !defined(SPARC)
      #define fixnum_to_L(obj)  \
        (sintL)( ((((sintL)as_oint(obj) >> sign_bit_o) << (intLsize-1)) >> (intLsize-1-oint_data_len)) \
                |((uintL)((as_oint(obj) & ((oint)wbitm(oint_data_len+oint_data_shift)-1)) >> oint_data_shift)) \
               )
    #else
      # Auf einem SPARC-Prozessor sind lange Konstanten langsamer als Shifts:
      #define fixnum_to_L(obj)  \
        (sintL)( ((((sintL)as_oint(obj) >> sign_bit_o) << (intLsize-1)) >> (intLsize-1-oint_data_len)) \
                |(((uintL)as_oint(obj) << (intLsize-oint_data_len-oint_data_shift)) >> (intLsize-oint_data_len)) \
               )
    #endif
  #endif

#ifdef intQsize
# Wert eines Fixnum, obj sollte eine Variable sein:
# fixnum_to_Q(obj)
# Ergebnis ist >= - 2^oint_data_len, < 2^oint_data_len.
  #if (sign_bit_o == oint_data_len+oint_data_shift)
    #define fixnum_to_Q(obj)  \
      (((sintQ)as_oint(obj) << (intQsize-1-sign_bit_o)) >> (intQsize-1-sign_bit_o+oint_data_shift))
  #else
    #define fixnum_to_Q(obj)  \
      ( ((((sintQ)as_oint(obj) >> sign_bit_o) << (intQsize-1)) >> (intQsize-1-oint_data_len)) \
       |((uintQ)((as_oint(obj) & (wbitm(oint_data_len+oint_data_shift)-1)) >> oint_data_shift)) \
      )
  #endif
#endif

# Zu einem nichtnegativen Fixnum eine Konstante addieren, vorausgesetzt,
# das Ergebnis ist wieder ein nichtnegatives Fixnum:
# fixnum_inc(obj,delta)
# > obj: ein Fixnum
# > delta: eine Konstante
# < ergebnis: erh�htes Fixnum
  #define fixnum_inc(obj,delta)  \
    objectplus(obj, (soint)(delta) << oint_data_shift)

# posfixnum(x) ist ein Fixnum mit Wert x>=0.
  #define posfixnum(x)  fixnum_inc(Fixnum_0,x)

# negfixnum(x) ist ein Fixnum mit Wert x<0.
# (Vorsicht, wenn x unsigned ist!)
  #define negfixnum(x)  fixnum_inc(fixnum_inc(Fixnum_minus1,1),x)

# sfixnum(x) ist ein Fixnum mit Wert x,
# x eine Constant-Expression mit -2^oint_data_len <= x < 2^oint_data_len.
  #define sfixnum(x) ((x)>=0 ? posfixnum(x) : negfixnum(x))

# Aus einem Character ein Fixnum >=0 machen (wie bei char-int):
  #ifdef WIDE_STRUCT
    #define char_to_fixnum(obj)  \
      type_data_object(fixnum_type,untype(obj))
  #else
    #define char_to_fixnum(obj)  \
      objectplus(obj,type_zero_oint(fixnum_type)-type_zero_oint(char_type))
  #endif

# Aus einem passenden Fixnum >=0 ein Character machen (wie bei int-char):
  #ifdef WIDE_STRUCT
    #define fixnum_to_char(obj)  \
      type_data_object(char_type,untype(obj))
  #else
    #define fixnum_to_char(obj)  \
      objectplus(obj,type_zero_oint(char_type)-type_zero_oint(fixnum_type))
  #endif

# Bignums
typedef struct { VAROBJECT_HEADER  # Selbstpointer f�r GC
                 #ifdef TYPECODES
                 uintC length;     # L�nge in Digits
                 #endif
                 uintD data[unspecified]; # Zahl in Zweierkomplementdarstellung
               }
        bignum_;
typedef bignum_ *  Bignum;
# The length is actually an uintWC.
#ifdef TYPECODES
  #define bignum_length(ptr)  ((ptr)->length)
#else
  #define bignum_length(ptr)  srecord_length(ptr)
#endif
#define Bignum_length(obj)  bignum_length(TheBignum(obj))

# Single-Floats
typedef uint32 ffloat; # 32-Bit-Float im IEEE-Format
typedef union { ffloat eksplicit;    # Wert, explizit
                #ifdef FAST_FLOAT
                float machine_float; # Wert, als C-'float'
                #endif
              }
        ffloatjanus;
#ifndef WIDE
typedef struct { VAROBJECT_HEADER            # Selbstpointer f�r GC
                 ffloatjanus representation; # Wert
               }
        ffloat_;
typedef ffloat_ *  Ffloat;
#define ffloat_value(obj)  (TheFfloat(obj)->float_value)
#else
# Der Float-Wert wird im Pointer selbst untergebracht, wie bei Short-Floats.
#define ffloat_value(obj)  ((ffloat)untype(obj))
#endif

# Double-Floats
typedef # 64-Bit-Float im IEEE-Format:
        #ifdef intQsize
          # Sign/Exponent/Mantisse
          uint64
        #else
          # Sign/Exponent/MantisseHigh und MantisseLow
          #if BIG_ENDIAN_P
            struct {uint32 semhi,mlo;}
          #else
            struct {uint32 mlo,semhi;}
          #endif
        #endif
        dfloat;
typedef union { dfloat eksplicit;      # Wert, explizit
                #ifdef FAST_DOUBLE
                double machine_double; # Wert, als C-'double'
                #endif
              }
        dfloatjanus;
typedef struct { VAROBJECT_HEADER            # Selbstpointer f�r GC
                 dfloatjanus representation; # Wert
               }
        dfloat_;
typedef dfloat_ *  Dfloat;

# Single- und Double-Floats
  #define float_value  representation.eksplicit

# Long-Floats
typedef struct { VAROBJECT_HEADER   # Selbstpointer f�r GC
                 #ifdef TYPECODES
                 uintC  len;        # L�nge der Mantisse in Digits
                 #endif
                 uint32 expo;       # Exponent
                 uintD  data[unspecified]; # Mantisse
               }
        lfloat_;
typedef lfloat_ *  Lfloat;
# The length is actually an uintWC.
#ifdef TYPECODES
  #define lfloat_length(ptr)  ((ptr)->len)
#else
  #define lfloat_length(ptr)  srecord_length(ptr)
#endif
#define Lfloat_length(obj)  lfloat_length(TheLfloat(obj))

# Simple-Array (umfasst einfache eindimensionale Arrays:
# Simple-Bit-Vector, Simple-String, Simple-Vector)
typedef struct { LRECORD_HEADER } # Selbstpointer f�r GC, L�nge in Elementen
        sarray_;
typedef sarray_ *  Sarray;
#define sarray_length(ptr)  lrecord_length(ptr)
#define Sarray_length(obj)  sarray_length(TheSarray(obj))

# Simple-Bit-Vektor
typedef struct { LRECORD_HEADER # Selbstpointer f�r GC, L�nge in Bits
                 uint8  data[unspecified]; # Bits, in Bytes unterteilt
               }
        sbvector_;
typedef sbvector_ *  Sbvector;
#define sbvector_length(ptr)  sarray_length(ptr)
#define Sbvector_length(obj)  sbvector_length(TheSbvector(obj))

# Simple-String
typedef struct { LRECORD_HEADER # Selbstpointer f�r GC, L�nge in Bytes
                 chart  data[unspecified]; # Characters
               }
        sstring_;
typedef sstring_ *  Sstring;
#define sstring_length(ptr)  sarray_length(ptr)
#define Sstring_length(obj)  sstring_length(TheSstring(obj))

# Simple-Vector
typedef struct { LRECORD_HEADER # Selbstpointer f�r GC, L�nge in Objekten
                 object data[unspecified]; # Elemente
               }
        svector_;
typedef svector_ *  Svector;
#define svector_length(ptr)  sarray_length(ptr)
#define Svector_length(obj)  svector_length(TheSvector(obj))

# nicht-simpler, indirekter Array
typedef struct { VAROBJECT_HEADER  # Selbstpointer f�r GC
                 #ifdef TYPECODES
                 uintB flags;      # Flags
                                   # dann ein Byte unbenutzt
                 uintC rank;       # Rang n
                 #endif
                 object data;      # Datenvektor
                 uintL totalsize;  # Totalsize = Produkt der n Dimensionen
                 uintL dims[unspecified]; # evtl. displaced-offset,
                                   # n Dimensionen,
                                   # evtl. Fill-Pointer
               }
        iarray_;
typedef iarray_ *  Iarray;
#define iarray_data_offset  offsetof(iarray_,data)
# The rank is actually an uintWC.
# Zugriff auf Rang, Flags:
  #ifdef TYPECODES
    #define iarray_rank(ptr)  ((ptr)->rank)
  #else
    #define iarray_rank(ptr)  srecord_length(ptr)
  #endif
  #define Iarray_rank(obj)  iarray_rank(TheIarray(obj))
  #ifdef TYPECODES
    #define iarray_flags(ptr)  ((ptr)->flags)
  #else
    #define iarray_flags(ptr)  record_flags(ptr)
  #endif
  #define Iarray_flags(obj)  iarray_flags(TheIarray(obj))
  #ifdef TYPECODES
    #define iarray_flags_clr(ptr,bits)  ((ptr)->flags &= ~(bits))
    #define iarray_flags_set(ptr,bits)  ((ptr)->flags |= (bits))
    #define iarray_flags_replace(ptr,newflags)  ((ptr)->flags = (newflags))
  #else
    #define iarray_flags_clr(ptr,bits)  record_flags_clr(ptr,bits)
    #define iarray_flags_set(ptr,bits)  record_flags_set(ptr,bits)
    #define iarray_flags_replace(ptr,newflags)  record_flags_replace(ptr,newflags)
  #endif
# Bits in den Flags:
  #define arrayflags_adjustable_bit  7 # gesetzt, wenn Array adjustable
  #define arrayflags_fillp_bit       6 # gesetzt, wenn Fill-Pointer vorhanden (nur bei n=1 m�glich)
  #define arrayflags_displaced_bit   5 # gesetzt, wenn Array displaced
  #define arrayflags_dispoffset_bit  4 # gesetzt, wenn Platz f�r den
                                       # Displaced-Offset vorhanden ist
                                       # (<==> Array adjustable oder displaced)
  #define arrayflags_notbytep_bit    3 # gel�scht bei Byte-Vektoren
  #define arrayflags_atype_mask  0x07  # Maske f�r Elementtyp
# Elementtypen von Arrays in Bits 2..0 der flags:
  # Die ersten sind so gew�hlt, dass 2^Atype_nBit = n ist.
  #define Atype_Bit    0         # arrayflags_notbytep_bit gesetzt!
  #define Atype_2Bit   1
  #define Atype_4Bit   2
  #define Atype_8Bit   3
  #define Atype_16Bit  4
  #define Atype_32Bit  5
  #define Atype_T      6         # arrayflags_notbytep_bit gesetzt!
  #define Atype_Char   7         # arrayflags_notbytep_bit gesetzt!

# Typ von Arrays:
  #ifdef TYPECODES
    #define Array_type(obj)  typecode(obj)
    #define Array_type_bvector   bvector_type      # Iarray
    #define Array_type_string    string_type       # Iarray
    #define Array_type_vector    vector_type       # Iarray
    #define Array_type_mdarray   mdarray_type      # Iarray
    #define Array_type_sbvector  sbvector_type     # Sbvector
    #define Array_type_sstring   sstring_type      # Sstring
    #define Array_type_svector   svector_type      # Svector
  #else
    #define Array_type(obj)  Record_type(obj)
    #define Array_type_bvector   Rectype_bvector   # Iarray
    #define Array_type_string    Rectype_string    # Iarray
    #define Array_type_vector    Rectype_vector    # Iarray
    #define Array_type_mdarray   Rectype_mdarray   # Iarray
    #define Array_type_sbvector  Rectype_Sbvector  # Sbvector
    #define Array_type_sstring   Rectype_Sstring   # Sstring
    #define Array_type_svector   Rectype_Svector   # Svector
  #endif

# Packages
typedef struct { XRECORD_HEADER
                 object pack_external_symbols;
                 object pack_internal_symbols;
                 object pack_shadowing_symbols;
                 object pack_use_list;
                 object pack_used_by_list;
                 object pack_name;
                 object pack_nicknames;
               }
        *  Package;
#define package_length  ((sizeof(*(Package)0)-offsetofa(record_,recdata))/sizeof(object))
# Manche Packages sind case-sensitive.
  #define mark_pack_casesensitive(obj)  record_flags_set(ThePackage(obj),bit(0))
  #define pack_casesensitivep(obj)  (!((record_flags(ThePackage(obj)) & bit(0)) == 0))
# Mit gel�schten Packages darf man nichts anstellen.
  #define mark_pack_deleted(obj)  record_flags_set(ThePackage(obj),bit(7))
  #define pack_deletedp(obj)  (!((record_flags(ThePackage(obj)) & bit(7)) == 0))

# Hash-Tables
typedef struct { XRECORD_HEADER
                 #ifdef GENERATIONAL_GC
                 object ht_lastrehash;
                 #endif
                 object ht_size;
                 object ht_maxcount;
                 object ht_itable;
                 object ht_ntable;
                 object ht_kvtable;
                 object ht_freelist;
                 object ht_count;
                 object ht_rehash_size;
                 object ht_mincount_threshold;
                 object ht_mincount;
               }
        *  Hashtable;
#define hashtable_length  ((sizeof(*(Hashtable)0)-offsetofa(record_,recdata))/sizeof(object))
# Markiere eine Hash-Table als neu zu reorganisieren:
# mark_ht_invalid(TheHashtable(ht));
  #ifdef GENERATIONAL_GC
    #define mark_ht_invalid(ptr)  (ptr)->ht_lastrehash = unbound
    #define mark_ht_valid(ptr)  (ptr)->ht_lastrehash = O(gc_count)
    #define ht_validp(ptr)  eq((ptr)->ht_lastrehash,O(gc_count))
  #else
    #define mark_ht_invalid(ptr)  record_flags_set(ptr,bit(7))
    #define mark_ht_valid(ptr)  record_flags_clr(ptr,bit(7))
    #define ht_validp(ptr)  ((record_flags(ptr) & bit(7)) == 0)
  #endif

# Readtables
typedef struct { XRECORD_HEADER
                 object readtable_syntax_table;
                 object readtable_macro_table;
                 object readtable_case;
               }
        *  Readtable;
#define readtable_length  ((sizeof(*(Readtable)0)-offsetofa(record_,recdata))/sizeof(object))

# Pathnames
typedef struct { XRECORD_HEADER
                 #if HAS_HOST
                   object pathname_host;
                 #endif
                 #if HAS_DEVICE
                   object pathname_device;
                 #endif
                 #if 1
                   object pathname_directory;
                   object pathname_name;
                   object pathname_type;
                 #endif
                 #if HAS_VERSION
                   object pathname_version;
                 #endif
               }
        *  Pathname;
#define pathname_length  ((sizeof(*(Pathname)0)-offsetofa(record_,recdata))/sizeof(object))

#ifdef LOGICAL_PATHNAMES
# Logical Pathnames
typedef struct { XRECORD_HEADER
                 object pathname_host;
                 object pathname_directory;
                 object pathname_name;
                 object pathname_type;
                 object pathname_version;
               }
        *  Logpathname;
#define logpathname_length  ((sizeof(*(Logpathname)0)-offsetofa(record_,recdata))/sizeof(object))
#endif

# Random-States
typedef struct { XRECORD_HEADER
                 object random_state_seed;
               }
        *  Random_state;
#define random_state_length  ((sizeof(*(Random_state)0)-offsetofa(record_,recdata))/sizeof(object))

# Bytes
typedef struct { XRECORD_HEADER
                 object byte_size;
                 object byte_position;
               }
        *  Byte;
#define byte_length  ((sizeof(*(Byte)0)-offsetofa(record_,recdata))/sizeof(object))

# Fsubrs
typedef struct { XRECORD_HEADER
                 object name;
                 object argtype;
                 void* function; # actually a fsubr_function*
               }
        *  Fsubr;
#define fsubr_length  2
#define fsubr_xlength  (sizeof(*(Fsubr)0)-offsetofa(record_,recdata)-fsubr_length*sizeof(object))

# Load-time-evals
typedef struct { XRECORD_HEADER
                 object loadtimeeval_form;
               }
        *  Loadtimeeval;
#define loadtimeeval_length  ((sizeof(*(Loadtimeeval)0)-offsetofa(record_,recdata))/sizeof(object))

# Symbol-macros
typedef struct { XRECORD_HEADER
                 object symbolmacro_expansion;
               }
        *  Symbolmacro;
#define symbolmacro_length  ((sizeof(*(Symbolmacro)0)-offsetofa(record_,recdata))/sizeof(object))

#ifdef FOREIGN
# Foreign-Pointer-Verpackung
typedef struct { XRECORD_HEADER
                 void* fp_pointer;
               }
        *  Fpointer;
#define fpointer_length  0
#define fpointer_xlength  (sizeof(*(Fpointer)0)-offsetofa(record_,recdata)-fpointer_length*sizeof(object))
#define mark_fp_invalid(ptr)  record_flags_set(ptr,bit(7))
#define mark_fp_valid(ptr)  record_flags_clr(ptr,bit(7))
#define fp_validp(ptr)  ((record_flags(ptr) & bit(7)) == 0)
#else
#define mark_fp_invalid(ptr)
#endif

#ifdef DYNAMIC_FFI

# Foreign-Adressen
typedef struct { XRECORD_HEADER
                 object fa_base;
                 uintP fa_offset;
               }
        * Faddress;
#define faddress_length  1
#define faddress_xlength  (sizeof(*(Faddress)0)-offsetofa(record_,recdata)-faddress_length*sizeof(object))

# Foreign-Variables
typedef struct { XRECORD_HEADER
                 object fv_name;
                 object fv_address;
                 object fv_size;
                 object fv_type;
               }
        * Fvariable;
#define fvariable_length  ((sizeof(*(Fvariable)0)-offsetofa(record_,recdata))/sizeof(object))

# Foreign-Functions
typedef struct { XRECORD_HEADER
                 object ff_name;
                 object ff_address;
                 object ff_resulttype;
                 object ff_argtypes;
                 object ff_flags;
               }
        * Ffunction;
#define ffunction_length  ((sizeof(*(Ffunction)0)-offsetofa(record_,recdata))/sizeof(object))

#endif

# Weak-Pointer
typedef struct { XRECORD_HEADER
                 object wp_cdr;   # active weak-pointers form a chained list
                 object wp_value; # the referenced object
               }
        * Weakpointer;
# Both wp_cdr and wp_value are invisible to gc_mark routines.
# When the weak-pointer becomes inactive, both fields are turned to unbound.
#define weakpointer_length  0
#define weakpointer_xlength  (sizeof(*(Weakpointer)0)-offsetofa(record_,recdata)-weakpointer_length*sizeof(object))

# Finalisierer
typedef struct { XRECORD_HEADER
                 object fin_alive;    # nur solange dieses Objekt lebt
                 object fin_trigger;  # der Tod dieses Objekts wird abgewartet
                 object fin_function; # dann wird diese Funktion aufgerufen
                 object fin_cdr;
               }
        * Finalizer;
#define finalizer_length  ((sizeof(*(Finalizer)0)-offsetofa(record_,recdata))/sizeof(object))

#ifdef SOCKET_STREAMS
# Socket-Server
typedef struct { XRECORD_HEADER
                 object socket_handle; # socket handle
                 object host; # host string
                 object port; # port number
               }
        * Socket_server;
#define socket_server_length  ((sizeof(*(Socket_server)0)-offsetofa(record_,recdata))/sizeof(object))

# Information about any of the two ends of a socket connection.
typedef struct host_data {
  unsigned long host;    # IP address
  char hostname[20];     # IP address in aaa.bbb.ccc.ddd notation
  const char * truename; # hostname, with or without domain name
  unsigned int port;
} host_data;
#endif

#ifdef YET_ANOTHER_RECORD

# Yet another record
typedef struct { XRECORD_HEADER
                 object yetanother_x;
                 object yetanother_y;
                 object yetanother_z;
               }
        * Yetanother;
#define yetanother_length  ((sizeof(*(Yetanother)0)-offsetofa(record_,recdata))/sizeof(object))

#endif

# Streams
typedef struct {
                 #ifdef case_stream
                 VAROBJECT_HEADER # Selbstpointer f�r GC
                 uintB strmflags; # Flags
                 uintB strmtype;  # Untertyp (als sintB >=0 !)
                 uintB reclength; # L�nge in Objekten
                 uintB recxlength; # L�nge der Extra-Elemente
                 #else
                 # Muss strmflags und strmtype aus Platzgr�nden in einem Fixnum
                 # in recdata[0] unterbringen.
                 #if !((oint_addr_len+oint_addr_shift>=24) && (8>=oint_addr_shift))
                 #error "No room for stream flags -- Stream-Flags neu unterbringen!!"
                 #endif
                 XRECORD_HEADER
                 uintB strmfiller1;
                 uintB strmflags; # Flags
                 uintB strmtype;  # Untertyp
                 uintB strmfiller2;
                 #endif
                 object strm_rd_by;
                 object strm_rd_by_array;
                 object strm_wr_by;
                 object strm_wr_by_array;
                 object strm_rd_ch;
                 object strm_pk_ch;
                 object strm_rd_ch_array;
                 object strm_rd_ch_last;
                 object strm_wr_ch;
                 object strm_wr_ch_array;
                 object strm_wr_ch_lpos;
                 object strm_wr_ss;
                 object strm_other[unspecified]; # typspezifische Komponenten
               }
        *  Stream;
#define strm_len  ((sizeof(*(Stream)0)-offsetofa(record_,recdata))/sizeof(object)-unspecified)
#define stream_length(ptr)  xrecord_length(ptr)
#define stream_xlength(ptr)  xrecord_xlength(ptr)
#define Stream_length(obj)  stream_length(TheStream(obj))
#define Stream_xlength(obj)  stream_xlength(TheStream(obj))
# Bitmaske in den Flags:
  #define strmflags_open_B   0xF0  # gibt an, ob der Stream offen ist
  #define strmflags_reval_bit_B  2  # gesetzt, falls Read-Eval erlaubt ist
  #define strmflags_rd_ch_bit_B  6  # gesetzt, falls READ-CHAR m�glich ist
  #define strmflags_wr_ch_bit_B  7  # gesetzt, falls WRITE-CHAR m�glich ist
  #define strmflags_rd_ch_B  bit(strmflags_rd_ch_bit_B)
  #define strmflags_wr_ch_B  bit(strmflags_wr_ch_bit_B)
# N�here Typinfo:
  enum { # Die Werte dieser Aufz�hlung sind der Reihe nach 0,1,2,...
  # First the OS independent streams.
                              enum_strmtype_synonym,
  #define strmtype_synonym    (uintB)enum_strmtype_synonym
                              enum_strmtype_broad,
  #define strmtype_broad      (uintB)enum_strmtype_broad
                              enum_strmtype_concat,
  #define strmtype_concat     (uintB)enum_strmtype_concat
                              enum_strmtype_twoway,
  #define strmtype_twoway     (uintB)enum_strmtype_twoway
                              enum_strmtype_echo,
  #define strmtype_echo       (uintB)enum_strmtype_echo
                              enum_strmtype_str_in,
  #define strmtype_str_in     (uintB)enum_strmtype_str_in
                              enum_strmtype_str_out,
  #define strmtype_str_out    (uintB)enum_strmtype_str_out
                              enum_strmtype_str_push,
  #define strmtype_str_push   (uintB)enum_strmtype_str_push
                              enum_strmtype_pphelp,
  #define strmtype_pphelp     (uintB)enum_strmtype_pphelp
                              enum_strmtype_buff_in,
  #define strmtype_buff_in    (uintB)enum_strmtype_buff_in
                              enum_strmtype_buff_out,
  #define strmtype_buff_out   (uintB)enum_strmtype_buff_out
  #ifdef GENERIC_STREAMS
                              enum_strmtype_generic,
  #define strmtype_generic    (uintB)enum_strmtype_generic
  #endif
  # Then the OS dependent streams.
                              enum_strmtype_file,
  #define strmtype_file       (uintB)enum_strmtype_file
  #ifdef KEYBOARD
                              enum_strmtype_keyboard,
  #define strmtype_keyboard   (uintB)enum_strmtype_keyboard
  #endif
                              enum_strmtype_terminal,
  #define strmtype_terminal   (uintB)enum_strmtype_terminal
  #ifdef SCREEN
                              enum_strmtype_window,
  #define strmtype_window     (uintB)enum_strmtype_window
  #endif
  #ifdef PRINTER
                              enum_strmtype_printer,
  #define strmtype_printer    (uintB)enum_strmtype_printer
  #endif
  #ifdef PIPES
                              enum_strmtype_pipe_in,
  #define strmtype_pipe_in    (uintB)enum_strmtype_pipe_in
                              enum_strmtype_pipe_out,
  #define strmtype_pipe_out   (uintB)enum_strmtype_pipe_out
  #endif
  #ifdef X11SOCKETS
                              enum_strmtype_x11socket,
  #define strmtype_x11socket  (uintB)enum_strmtype_x11socket
  #endif
  #ifdef SOCKET_STREAMS
                              enum_strmtype_socket,
  #define strmtype_socket     (uintB)enum_strmtype_socket
                              enum_strmtype_twoway_socket,
  #define strmtype_twoway_socket (uintB)enum_strmtype_twoway_socket
  #endif
                              enum_strmtype_dummy
  };
  # Bei �nderung dieser Tabelle auch
  # - die acht Sprungtabellen bei STREAM-ELEMENT-TYPE, INTERACTIVE-STREAM-P,
  #   CLOSE, LISTEN, CLEAR_INPUT, FINISH_OUTPUT, FORCE_OUTPUT, CLEAR_OUTPUT
  #   in STREAM.D und
  # - die Namenstabelle in CONSTOBJ.D und
  # - die Sprungtabelle bei PR_STREAM in IO.D und
  # - die Pseudofunktionentabelle in PSEUDOFUN.D
  # anpassen!
# weitere typspezifische Komponenten:
  #define strm_eltype          strm_other[0] # CHARACTER or ([UN]SIGNED-BYTE n)
  #define strm_file_name       strm_other[5] # Filename, ein Pathname oder NIL
  #define strm_file_truename   strm_other[6] # Truename, ein nicht-Logical Pathname oder NIL
  #define strm_file_handle     strm_other[4] # eingepacktes Handle
  #define strm_synonym_symbol  strm_other[0]
  #define strm_broad_list      strm_other[0] # Liste von Streams
  #define strm_concat_list     strm_other[0] # Liste von Streams
  #define strm_pphelp_lpos     strm_wr_ch_lpos # Line Position (Fixnum>=0)
  #define strm_pphelp_strings  strm_other[0]   # Semi-Simple-Strings f�r Output
  #define strm_pphelp_modus    strm_other[1]   # Modus (NIL=Einzeiler, T=Mehrzeiler)
  #define strm_buff_in_fun     strm_other[0] # Lesefunktion
  #define strm_buff_out_fun    strm_other[0] # Ausgabefunktion
  #ifdef PIPES
  #define strm_pipe_pid        strm_other[5] # Prozess-Id, ein Fixnum >=0
  #endif
  #ifdef X11SOCKETS
  #define strm_x11socket_connect  strm_other[5] # Liste (host display)
  #endif
  #ifdef SOCKET_STREAMS
  #define strm_socket_port     strm_other[5] # port, a fixnum >=0
  #define strm_socket_host     strm_other[6] # host, NIL or a string
  #define strm_twoway_socket_input  strm_other[0] # input side, a socket stream
  #endif
  #ifdef GENERIC_STREAMS
  #define strm_controller_object strm_other[0] # Controller (meist CLOS-Instanz)
  #endif
# wird verwendet von STREAM, PATHNAME, IO

# Structures
typedef Srecord  Structure;
  #define structure_types   recdata[0]
#define structure_length(ptr)  srecord_length(ptr)
#define Structure_length(obj)  structure_length(TheStructure(obj))

# CLOS-Klassen (= Instanzen von <class>), siehe clos.lsp
typedef struct { SRECORD_HEADER
                 object structure_types_2;   # Liste (metaclass <class>)
                 object metaclass;           # eine Subklasse von <class>
                 object classname;           # ein Symbol
                 object direct_superclasses; # direkte Oberklassen
                 object all_superclasses;    # alle Oberklassen inkl. sich selbst
                 object precedence_list;     # angeordnete Liste aller Oberklassen
                 object slot_location_table; # Hashtabelle Slotname -> wo der Slot sitzt
                 # ab hier nur bei metaclass = <standard-class> oder metaclass = <structure-class>
                 object slots;
                 object default_initargs;
                 object valid_initargs;
                 object instance_size;
                 # ab hier nur bei metaclass = <standard-class>
                 object shared_slots;
                 object direct_slots;
                 object direct_default_initargs;
                 object other[unspecified];
               }
        *  Class;

# CLOS-Instanzen
typedef struct { SRECORD_HEADER
                 object inst_class; # eine CLOS-Klasse
                 object other[unspecified];
               }
        *  Instance;

# Closures
typedef struct { SRECORD_HEADER
                 object clos_name;
                 object clos_codevec;
                 object other[unspecified];
               }
        *  Closure;
# interpretierte Closure:
typedef struct { SRECORD_HEADER
                 object clos_name;
                 object clos_form;
                 object clos_docstring;
                 object clos_body;
                 object clos_var_env;
                 object clos_fun_env;
                 object clos_block_env;
                 object clos_go_env;
                 object clos_decl_env;
                 object clos_vars;
                 object clos_varflags;
                 object clos_spec_anz;
                 object clos_req_anz;
                 object clos_opt_anz;
                 object clos_opt_inits;
                 object clos_key_anz;
                 object clos_keywords;
                 object clos_key_inits;
                 object clos_allow_flag;
                 object clos_rest_flag;
                 object clos_aux_anz;
                 object clos_aux_inits;
               }
        *  Iclosure;
#define iclos_length  ((sizeof(*(Iclosure)0)-offsetofa(record_,recdata))/sizeof(object))
# compilierte Closure:
typedef struct { SRECORD_HEADER
                 object clos_name;
                 object clos_codevec;
                 object clos_consts[unspecified]; # Closure-Konstanten
               }
        *  Cclosure;
#define cclosure_length(ptr)  srecord_length(ptr)
#define Cclosure_length(obj)  cclosure_length(TheCclosure(obj))
#define clos_venv  clos_consts[0]
typedef struct { LRECORD_HEADER # Selbstpointer f�r GC, L�nge in Bits
                 # Ab hier der Inhalt des Bitvektors.
                 uintW  ccv_spdepth_1;          # maximale SP-Tiefe, 1-Anteil
                 uintW  ccv_spdepth_jmpbufsize; # maximale SP-Tiefe, jmpbufsize-Anteil
                 uintW  ccv_numreq;    # Anzahl der required parameter
                 uintW  ccv_numopt;    # Anzahl der optionalen Parameter
                 uintB  ccv_flags;     # Flags. Bit 0: ob &REST - Parameter angegeben
                                       #        Bit 7: ob Keyword-Parameter angegeben
                                       #        Bit 6: &ALLOW-OTHER-KEYS-Flag
                                       #        Bit 4: ob generische Funktion
                                       #        Bit 3: ob generische Funktion mit Aufrufhemmung
                 uintB  ccv_signature; # K�rzel f�r den Argumenttyp, f�r schnelleres FUNCALL
                 # Falls Keyword-Parameter angegeben:
                 uintW  ccv_numkey;    # Anzahl der Keyword-Parameter
                 uintW  ccv_keyconsts; # Offset in FUNC der Keywords
               }
        *  Codevec;
#define CCV_SPDEPTH_1           0
#define CCV_SPDEPTH_JMPBUFSIZE  2
#define CCV_NUMREQ              4
#define CCV_NUMOPT              6
#define CCV_FLAGS               8
#define CCV_SIGNATURE           9
#define CCV_NUMKEY             10
#define CCV_KEYCONSTS          12
#define CCV_START_NONKEY       10
#define CCV_START_KEY          14
# Compilierte Closures, bei denen Bit 4 in den Flags von clos_codevec
# gesetzt ist, sind generische Funktionen.

# Eine compilierte LISP-Funktion bekommt ihre Argumente auf dem STACK
# und liefert ihre Werte im MULTIPLE_VALUE_SPACE. Als C-Funktion liefert
# sie keinen Wert.
  # R�ckgabe von Multiple Values geschieht vollst�ndig �ber den
  # MULTIPLE_VALUE_SPACE. Als C-Funktion: Ergebnistyp Values.
    #ifndef Values
    typedef void Values;
    #endif
  # Um einen Typ vom Wert Values weiterzureichen: return_Values(...);
    #define return_Values  return_void
  # Eine Lisp-Funktion ist ein Pointer auf eine C-Funktion ohne R�ckgabewert
    typedef Values (*lisp_function)();
# Sollte dies ge�ndert werden, so ist jeder Aufruf einer C-Funktion vom
# Ergebnistyp 'Values' (insbesondere 'funcall', 'apply', 'eval') zu �berpr�fen.

# FSUBRs
# Als C-Funktionen: vom Typ fsubr_function (keine Argumente, kein Wert):
  typedef Values fsubr_function (void);
# Die Adressen dieser C-Funktionen werden direkt angesprungen.
# F�r SAVEMEM/LOADMEM gibt es eine Tabelle aller FSUBRs.
  typedef fsubr_function * fsubr_;
# Signatur von FSUBRs im Lisp-Sinne:
#         argtype          K�rzel f�r den Argumente-Typ     fsubr_argtype_t
#         req_anz          Anzahl required Parameter        uintW
#         opt_anz          Anzahl optionaler Parameter      uintW
#         body_flag        Body-Flag                        fsubr_body_t
# Die Komponente body_flag enth�lt ein uintW, gemeint ist aber:
  typedef enum { fsubr_nobody, fsubr_body } fsubr_body_t;
# Die Komponente argtype enth�lt ein Fixnum, gemeint ist aber:
  typedef enum {
                fsubr_argtype_1_0_nobody,
                fsubr_argtype_2_0_nobody,
                fsubr_argtype_1_1_nobody,
                fsubr_argtype_2_1_nobody,
                fsubr_argtype_0_body,
                fsubr_argtype_1_body,
                fsubr_argtype_2_body
               }
          fsubr_argtype_t;
# Umwandlung siehe SPVW:
# extern fsubr_argtype_t fsubr_argtype (uintW req_anz, uintW opt_anz, fsubr_body_t body_flag);

# SUBRs
# SUBR-Tabellen-Eintrag:
  typedef struct { lisp_function function; # Funktion
                   object name;            # Name
                   object keywords;        # NIL oder Vektor mit den Keywords
                   uintW argtype;          # K�rzel f�r den Argumente-Typ
                   uintW req_anz;          # Anzahl required Parameter
                   uintW opt_anz;          # Anzahl optionaler Parameter
                   uintB rest_flag;        # Flag f�r beliebig viele Argumente
                   uintB key_flag;         # Flag f�r Keywords
                   uintW key_anz;          # Anzahl Keywordparameter
                 }
          subr_;
  typedef subr_ *  Subr;
# GC ben�tigt Information, wo hierin Objekte stehen:
  #define subr_const_offset  offsetof(subr_,name)
  #define subr_const_anz     2
# Die Komponente rest_flag enth�lt ein uintB, gemeint ist aber:
  typedef enum { subr_norest, subr_rest } subr_rest_t;
# Die Komponente key_flag enth�lt ein uintB, gemeint ist aber:
  typedef enum { subr_nokey, subr_key, subr_key_allow } subr_key_t;
# Die Komponente argtype enth�lt ein uintW, gemeint ist aber:
  typedef enum {
                subr_argtype_0_0,
                subr_argtype_1_0,
                subr_argtype_2_0,
                subr_argtype_3_0,
                subr_argtype_4_0,
                subr_argtype_5_0,
                subr_argtype_6_0,
                subr_argtype_0_1,
                subr_argtype_1_1,
                subr_argtype_2_1,
                subr_argtype_3_1,
                subr_argtype_4_1,
                subr_argtype_0_2,
                subr_argtype_1_2,
                subr_argtype_2_2,
                subr_argtype_0_3,
                subr_argtype_0_4,
                subr_argtype_0_5,
                subr_argtype_0_0_rest,
                subr_argtype_1_0_rest,
                subr_argtype_2_0_rest,
                subr_argtype_3_0_rest,
                subr_argtype_0_0_key,
                subr_argtype_1_0_key,
                subr_argtype_2_0_key,
                subr_argtype_3_0_key,
                subr_argtype_4_0_key,
                subr_argtype_0_1_key,
                subr_argtype_1_1_key,
                subr_argtype_1_2_key
               }
          subr_argtype_t;
# Umwandlung siehe SPVW:
# extern subr_argtype_t subr_argtype (uintW req_anz, uintW opt_anz, subr_rest_t rest_flag, subr_key_t key_flag);

# Read-Label
  #ifdef TYPECODES
    #define make_read_label(n)  \
      type_data_object(system_type, ((uintL)(n)<<1) + bit(0))
    #define read_label_integer_p(obj)  \
      (posfixnump(obj) && (posfixnum_to_L(obj) < bit(oint_data_len-2)))
  #else
    #define make_read_label(n)  \
      type_data_object(read_label_type, (uintL)(n))
    #define read_label_integer_p(obj)  posfixnump(obj)
  #endif

# Maschinen-Pointer
# make_machine(ptr)
  #ifdef TYPECODES
    #define make_machine(ptr)  type_pointer_object(machine_type,ptr)
  #else
    #define make_machine(ptr)  as_object((oint)(ptr)+machine_bias)
  #endif

# Pointer to machine code
# make_machine_code(ptr)
  #if defined(TYPECODES) || (log2_C_CODE_ALIGNMENT >= 2)
    #define make_machine_code(ptr)  make_machine(ptr)
  #elif defined(HPPA)
    #define make_machine_code(ptr)  make_machine((uintP)(ptr)&~(uintP)3)
  #else
    #define make_machine_code(ptr)  make_machine((uintP)(ptr)<<(2-log2_C_CODE_ALIGNMENT))
  #endif

# System-Pointer
  #define make_system(data)  \
    type_data_object(system_type, bit(oint_data_len-1) | bit(0) | ((bitm(oint_data_len)-1) & (data)))
# Alle solchen m�ssen in io.d:pr_system() eine spezielle print-Routine bekommen.

# Indikator f�r nicht vorhandenen Wert:
  #define unbound  make_system(0xFFFFFFUL)

# Indikator f�r nicht vorhandenes Objekt (nur intern verwendet):
  #define nullobj  make_machine(0)  # = as_object((oint)0)


#ifdef TYPECODES

# Um auf die Komponenten eines Objekts zugreifen zu k�nnen, muss man erst
# die Typbits entfernen:
  #if !((oint_addr_shift==0) && (addr_shift==0))
    #define pointable(obj)  ((void*)upointer(obj))
  #else
    # Ist oint_addr_shift=0 und addr_shift=0, so braucht man nicht zu shiften.
    #if !(((tint_type_mask<<oint_type_shift) & addressbus_mask) == 0)
      #define pointable(obj)  \
        ((void*)((aint)as_oint(obj) & ((aint)oint_addr_mask | ~addressbus_mask)))
    #else
      # Ist ferner oint_type_mask von addressbus_mask disjunkt, so werden
      # sowieso keine Typbits auf den Adressbus geschickt.
      # Also ist gar nichts zu tun:
      #define pointable(obj)  ((void*)(aint)as_oint(obj))
    #endif
  #endif

# Wenn man auf ein Objekt zugreifen will, das eine bekannte Typinfo hat,
# dessen gesetzte Typbits vom Adressbus verschluckt werden (auf die
# Typbits, die =0 sind, kommt es nicht an), so kann man auf das 'untype'
# verzichten:
  #if defined(WIDE_STRUCT)
    #define type_pointable(type,obj)  ((void*)((obj).both.addr))
  #elif !((oint_addr_shift==0) && (addr_shift==0) && (((tint_type_mask<<oint_type_shift) & addressbus_mask) == 0))
    #if (addr_shift==0)
      #define type_pointable(type,obj)  \
        ((oint_addr_shift==0) && ((type_zero_oint(type) & addressbus_mask) == 0) \
         ? (void*)(aint)as_oint(obj)                                             \
         : (void*)(aint)pointable(obj)                                           \
        )
    #elif !(addr_shift==0)
      # Analog, nur dass der Macro 'optimized_upointer' die Rolle des Adressbus �bernimmt:
      #define type_pointable(type,obj)  \
        ((optimized_upointer(type_data_object(type,0)) == 0) \
         ? (void*)(aint)optimized_upointer(obj)              \
         : (void*)(aint)pointable(obj)                       \
        )
    #endif
  #else
    # Wenn pointable(obj) = obj, braucht auch type_pointable() nichts zu tun:
    #define type_pointable(type,obj)  ((void*)(aint)as_oint(obj))
  #endif

# Wenn man auf ein Objekt zugreifen will, das eine von mehreren bekannten
# Typinfos hat, kann man evtl. auf das 'untype' verzichten. Ma�geblich
# ist das OR der Typinfos.
  #define types_pointable(ORed_types,obj)  type_pointable(ORed_types,obj)

#endif

# TheCons(object) liefert das zu object �quivalente Cons.
# Die Information, dass es Cons darstellt, muss hineingesteckt werden.
# Analog die anderen Typumwandlungen.
#ifdef TYPECODES
  #define TheCons(obj)  ((Cons)(types_pointable(cons_type,obj)))
  #define TheRatio(obj)  ((Ratio)(types_pointable(ratio_type|bit(sign_bit_t),obj)))
  #define TheComplex(obj)  ((Complex)(type_pointable(complex_type,obj)))
  #define TheSymbol(obj)  ((Symbol)(type_pointable(symbol_type,obj)))
  #if (oint_symbolflags_shift==oint_type_shift)
  #define TheSymbolflagged(obj)  ((Symbol)(types_pointable(symbol_type|bit(active_bit)|bit(dynam_bit)|bit(svar_bit),obj)))
  #else
  #define TheSymbolflagged(obj)  TheSymbol(symbol_without_flags(obj))
  #endif
  #define TheBignum(obj)  ((Bignum)(types_pointable(bignum_type|bit(sign_bit_t),obj)))
  #ifndef WIDE
  #define TheFfloat(obj)  ((Ffloat)(types_pointable(ffloat_type|bit(sign_bit_t),obj)))
  #endif
  #define TheDfloat(obj)  ((Dfloat)(types_pointable(dfloat_type|bit(sign_bit_t),obj)))
  #define TheLfloat(obj)  ((Lfloat)(types_pointable(lfloat_type|bit(sign_bit_t),obj)))
  #define TheSarray(obj)  ((Sarray)(types_pointable(sbvector_type|sstring_type|svector_type,obj)))
  #define TheSbvector(obj)  ((Sbvector)(types_pointable(sbvector_type,obj)))
  #define TheCodevec(obj)  ((Codevec)TheSbvector(obj))
  #define TheSstring(obj)  ((Sstring)(types_pointable(sstring_type,obj)))
  #define TheSvector(obj)  ((Svector)(types_pointable(svector_type,obj)))
  #define TheIarray(obj)  ((Iarray)(types_pointable(mdarray_type|bvector_type|string_type|vector_type,obj)))
  #define TheRecord(obj)  ((Record)(types_pointable(closure_type|structure_type|stream_type|orecord_type|instance_type,obj)))
  #define TheSrecord(obj)  ((Srecord)(types_pointable(closure_type|structure_type|orecord_type|instance_type,obj)))
  #define TheXrecord(obj)  ((Xrecord)(types_pointable(stream_type|orecord_type,obj)))
  #define ThePackage(obj)  ((Package)(type_pointable(orecord_type,obj)))
  #define TheHashtable(obj)  ((Hashtable)(type_pointable(orecord_type,obj)))
  #define TheReadtable(obj)  ((Readtable)(type_pointable(orecord_type,obj)))
  #define ThePathname(obj)  ((Pathname)(type_pointable(orecord_type,obj)))
  #ifdef LOGICAL_PATHNAMES
  #define TheLogpathname(obj)  ((Logpathname)(type_pointable(orecord_type,obj)))
  #endif
  #define The_Random_state(obj)  ((Random_state)(type_pointable(orecord_type,obj)))
  #define TheByte(obj)  ((Byte)(type_pointable(orecord_type,obj)))
  #define TheFsubr(obj)  ((Fsubr)(type_pointable(orecord_type,obj)))
  #define TheLoadtimeeval(obj)  ((Loadtimeeval)(type_pointable(orecord_type,obj)))
  #define TheSymbolmacro(obj)  ((Symbolmacro)(type_pointable(orecord_type,obj)))
  #ifdef FOREIGN
  #define TheFpointer(obj)  ((Fpointer)(type_pointable(orecord_type,obj)))
  #endif
  #ifdef DYNAMIC_FFI
  #define TheFaddress(obj)  ((Faddress)(type_pointable(orecord_type,obj)))
  #define TheFvariable(obj)  ((Fvariable)(type_pointable(orecord_type,obj)))
  #define TheFfunction(obj)  ((Ffunction)(type_pointable(orecord_type,obj)))
  #endif
  #define TheWeakpointer(obj)  ((Weakpointer)(type_pointable(orecord_type,obj)))
  #define TheFinalizer(obj)  ((Finalizer)(type_pointable(orecord_type,obj)))
  #ifdef SOCKET_STREAMS
  #define TheSocketServer(obj) ((Socket_server)(type_pointable(orecord_type,obj)))
  #endif
  #ifdef YET_ANOTHER_RECORD
  #define TheYetanother(obj)  ((Yetanother)(type_pointable(orecord_type,obj)))
  #endif
  #define TheStream(obj)  ((Stream)(type_pointable(stream_type,obj)))
  #define TheStructure(obj)  ((Structure)(type_pointable(structure_type,obj)))
  #define TheClass(obj)  ((Class)(type_pointable(structure_type,obj)))
  #define TheClosure(obj)  ((Closure)(type_pointable(closure_type,obj)))
  #define TheIclosure(obj)  ((Iclosure)(type_pointable(closure_type,obj)))
  #define TheCclosure(obj)  ((Cclosure)(type_pointable(closure_type,obj)))
  #define TheInstance(obj)  ((Instance)(type_pointable(instance_type,obj)))
  #define TheSubr(obj)  ((Subr)(type_pointable(subr_type,obj)))
  #define TheFramepointer(obj)  ((object*)(type_pointable(system_type,obj)))
  #define TheMachine(obj)  ((void*)(type_pointable(machine_type,obj)))
  #define TheMachineCode(obj)  TheMachine(obj)
  #define ThePseudofun(obj)  ((Pseudofun)TheMachineCode(obj))
  #ifdef FOREIGN_HANDLE
  # Handle in Sbvector verpackt
  #define TheHandle(obj)  (*(Handle*)(&TheSbvector(obj)->data[0]))
  #else
  # Handle in Fixnum>=0 verpackt
  #define TheHandle(obj)  ((Handle)posfixnum_to_L(obj))
  #endif
  # Objekt variabler L�nge:
  #define TheVarobject(obj)  \
    ((Varobject)                                                                                 \
     (types_pointable                                                                            \
      (sbvector_type|sstring_type|svector_type|mdarray_type|bvector_type|string_type|vector_type \
       |closure_type|structure_type|stream_type|orecord_type|symbol_type                         \
       |bignum_type|ffloat_type|dfloat_type|lfloat_type|bit(sign_bit_t),                         \
       obj                                                                                       \
    )))
  # Objekt, das einen Pointer in den Speicher darstellt:
  #define ThePointer(obj)  \
    (types_pointable                                                                            \
     (sbvector_type|sstring_type|svector_type|mdarray_type|bvector_type|string_type|vector_type \
      |closure_type|structure_type|stream_type|orecord_type|symbol_type|cons_type               \
      |bignum_type|ffloat_type|dfloat_type|lfloat_type|ratio_type|complex_type|bit(sign_bit_t), \
      obj                                                                                       \
    ))
#else # no TYPECODES
  #define TheCons(obj)  ((Cons)(as_oint(obj)-cons_bias))
  #define TheRatio(obj)  ((Ratio)(as_oint(obj)-varobject_bias))
  #define TheComplex(obj)  ((Complex)(as_oint(obj)-varobject_bias))
  #define TheSymbol(obj)  ((Symbol)(as_oint(obj)-varobject_bias))
  #define TheSymbolflagged(obj)  TheSymbol(symbol_without_flags(obj))
  #define TheBignum(obj)  ((Bignum)(as_oint(obj)-varobject_bias))
  #define TheFfloat(obj)  ((Ffloat)(as_oint(obj)-varobject_bias))
  #define TheDfloat(obj)  ((Dfloat)(as_oint(obj)-varobject_bias))
  #define TheLfloat(obj)  ((Lfloat)(as_oint(obj)-varobject_bias))
  #define TheSarray(obj)  ((Sarray)(as_oint(obj)-varobject_bias))
  #define TheSbvector(obj)  ((Sbvector)(as_oint(obj)-varobject_bias))
  #define TheCodevec(obj)  ((Codevec)TheSbvector(obj))
  #define TheSstring(obj)  ((Sstring)(as_oint(obj)-varobject_bias))
  #define TheSvector(obj)  ((Svector)(as_oint(obj)-varobject_bias))
  #define TheIarray(obj)  ((Iarray)(as_oint(obj)-varobject_bias))
  #define TheRecord(obj)  ((Record)(as_oint(obj)-varobject_bias))
  #define TheSrecord(obj)  ((Srecord)(as_oint(obj)-varobject_bias))
  #define TheXrecord(obj)  ((Xrecord)(as_oint(obj)-varobject_bias))
  #define ThePackage(obj)  ((Package)(as_oint(obj)-varobject_bias))
  #define TheHashtable(obj)  ((Hashtable)(as_oint(obj)-varobject_bias))
  #define TheReadtable(obj)  ((Readtable)(as_oint(obj)-varobject_bias))
  #define ThePathname(obj)  ((Pathname)(as_oint(obj)-varobject_bias))
  #ifdef LOGICAL_PATHNAMES
  #define TheLogpathname(obj)  ((Logpathname)(as_oint(obj)-varobject_bias))
  #endif
  #define The_Random_state(obj)  ((Random_state)(as_oint(obj)-varobject_bias))
  #define TheByte(obj)  ((Byte)(as_oint(obj)-varobject_bias))
  #define TheFsubr(obj)  ((Fsubr)(as_oint(obj)-varobject_bias))
  #define TheLoadtimeeval(obj)  ((Loadtimeeval)(as_oint(obj)-varobject_bias))
  #define TheSymbolmacro(obj)  ((Symbolmacro)(as_oint(obj)-varobject_bias))
  #ifdef FOREIGN
  #define TheFpointer(obj)  ((Fpointer)(as_oint(obj)-varobject_bias))
  #endif
  #ifdef DYNAMIC_FFI
  #define TheFaddress(obj)  ((Faddress)(as_oint(obj)-varobject_bias))
  #define TheFvariable(obj)  ((Fvariable)(as_oint(obj)-varobject_bias))
  #define TheFfunction(obj)  ((Ffunction)(as_oint(obj)-varobject_bias))
  #endif
  #define TheWeakpointer(obj)  ((Weakpointer)(as_oint(obj)-varobject_bias))
  #define TheFinalizer(obj)  ((Finalizer)(as_oint(obj)-varobject_bias))
  #ifdef SOCKET_STREAMS
  #define TheSocketServer(obj) ((Socket_server)(as_oint(obj)-varobject_bias))
  #endif
  #ifdef YET_ANOTHER_RECORD
  #define TheYetanother(obj)  ((Yetanother)(as_oint(obj)-varobject_bias))
  #endif
  #define TheStream(obj)  ((Stream)(as_oint(obj)-varobject_bias))
  #define TheStructure(obj)  ((Structure)(as_oint(obj)-varobject_bias))
  #define TheClass(obj)  ((Class)(as_oint(obj)-varobject_bias))
  #define TheClosure(obj)  ((Closure)(as_oint(obj)-varobject_bias))
  #define TheIclosure(obj)  ((Iclosure)(as_oint(obj)-varobject_bias))
  #define TheCclosure(obj)  ((Cclosure)(as_oint(obj)-varobject_bias))
  #define TheInstance(obj)  ((Instance)(as_oint(obj)-varobject_bias))
  #define TheSubr(obj)  ((Subr)(as_oint(obj)-subr_bias))
  #define TheFramepointer(obj)  ((object*)(as_oint(obj)-machine_bias))
  #define TheMachine(obj)  ((void*)(as_oint(obj)-machine_bias))
  #if (log2_C_CODE_ALIGNMENT >= 2)
    #define TheMachineCode(obj)  TheMachine(obj)
  #elif defined(HPPA)
    #define TheMachineCode(obj)  ((void*)((uintP)TheMachine(obj)+2))
  #else
    #define TheMachineCode(obj)  ((void*)((uintP)TheMachine(obj)>>(2-log2_C_CODE_ALIGNMENT)))
  #endif
  #define ThePseudofun(obj)  ((Pseudofun)TheMachineCode(obj))
  #ifdef FOREIGN_HANDLE
  # Handle in Sbvector verpackt
  #define TheHandle(obj)  (*(Handle*)(&TheSbvector(obj)->data[0]))
  #else
  # Handle in Fixnum>=0 verpackt
  #define TheHandle(obj)  ((Handle)posfixnum_to_L(obj))
  #endif
  # Objekt variabler L�nge:
  #define TheVarobject(obj)  ((Varobject)(as_oint(obj)-varobject_bias))
  # Objekt, das einen Pointer in den Speicher darstellt:
  #define ThePointer(obj)  ((void*)(as_oint(obj) & ~(oint)nonimmediate_bias_mask))
#endif

# Ein paar Abk�rzungen:
  # Zugriff auf Objekte, die Conses sind:
    #define Car(obj)  (TheCons(obj)->car)
    #define Cdr(obj)  (TheCons(obj)->cdr)
  # Zugriff auf Objekte, die Symbole sind:
    #define Symbol_value(obj)  (TheSymbol(obj)->symvalue)
    #define Symbol_function(obj)  (TheSymbol(obj)->symfunction)
    #define Symbol_plist(obj)  (TheSymbol(obj)->proplist)
    #define Symbol_name(obj)  (TheSymbol(obj)->pname)
    #define Symbol_package(obj)  (TheSymbol(obj)->homepackage)
  # L�nge (Anzahl Objekte) eines Record, obj muss ein Srecord/Xrecord sein:
    #define Record_length(obj)  \
      (Record_type(obj) < rectype_limit ? Srecord_length(obj) : Xrecord_length(obj))


# ####################### Typtestpr�dikate ################################ #
# Die gibt es in zwei Formen:
# 1.  ???p, mit 'if' abzufragen:  if ???p(object)
# 2.  if_???p, aufzurufen als
#         if_???p(object, statement1, statement2)
#       statt
#         if ???p(object) statement1 else statement2

# UP: testet auf Pointergleichheit EQ
# eq(obj1,obj2)
# > obj1,obj2: Lisp-Objekte
# < ergebnis: TRUE, falls Objekte gleich
  #if defined(WIDE_STRUCT) || defined(OBJECT_STRUCT)
    #define eq(obj1,obj2)  (as_oint(obj1) == as_oint(obj2))
  #else
    #define eq(obj1,obj2)  ((obj1) == (obj2))
  #endif

# Test auf NIL
  #define nullp(obj)  (eq(obj,NIL))

# Test auf Cons
  #ifdef TYPECODES
    #if defined(cons_bit_o)
      # define consp(obj)  (as_oint(obj) & wbit(cons_bit_o))
      #define consp(obj)  (wbit_test(as_oint(obj),cons_bit_o))
      #ifdef fast_mtypecode
        #ifdef WIDE_STRUCT
          #undef consp
          #define consp(obj)  (typecode(obj) & bit(cons_bit_t))
        #endif
        #define mconsp(obj)  (mtypecode(obj) & bit(cons_bit_t))
      #else
        #define mconsp(obj)  consp(obj)
      #endif
    #else
      #define consp(obj)  (typecode(obj) == cons_type)
      #define mconsp(obj)  (mtypecode(obj) == cons_type)
    #endif
  #else
    #define consp(obj)  ((as_oint(obj) & 7) == cons_bias)
    #define mconsp(obj)  consp(obj)
  #endif

# Test auf Atom
  #ifdef TYPECODES
    #if defined(cons_bit_o)
      # define atomp(obj)  ((as_oint(obj) & wbit(cons_bit_o))==0)
      #define atomp(obj)  (!wbit_test(as_oint(obj),cons_bit_o))
      #ifdef fast_mtypecode
        #ifdef WIDE_STRUCT
          #undef atomp
          #define atomp(obj)  ((typecode(obj) & bit(cons_bit_t))==0)
        #endif
        #define matomp(obj)  ((mtypecode(obj) & bit(cons_bit_t))==0)
      #else
        #define matomp(obj)  atomp(obj)
      #endif
    #else
      #define atomp(obj)  (!(typecode(obj) == cons_type))
      #define matomp(obj)  (!(mtypecode(obj) == cons_type))
    #endif
  #else
    #define atomp(obj)  (!consp(obj))
    #define matomp(obj)  atomp(obj)
  #endif

# For all type tests below this line, the argument must be side-effect free.
# Ideally a variable, but a STACK_(n) reference works as well.

# Test auf Liste
  #define listp(obj)  (nullp(obj) || consp(obj))

#ifndef TYPECODES

# Test auf Object variabler L�nge
  #define varobjectp(obj)  ((as_oint(obj) & 3) == varobject_bias)

#endif

# Test auf Symbol
  #ifdef TYPECODES
    #if defined(symbol_bit_o)
      # define symbolp(obj)  (as_oint(obj) & wbit(symbol_bit_o))
      #define symbolp(obj)  (wbit_test(as_oint(obj),symbol_bit_o))
      #ifdef WIDE_STRUCT
        #undef symbolp
        #define symbolp(obj)  (typecode(obj) & bit(symbol_bit_t))
      #endif
    #else
      #define symbolp(obj)  (typecode(obj) == symbol_type)
    #endif
  #else
    #define symbolp(obj)  \
      (varobjectp(obj) && (Record_type(obj) == Rectype_Symbol))
  #endif

# Test auf Zahl
  #ifdef TYPECODES
    # define numberp(obj)  (as_oint(obj) & wbit(number_bit_o))
    #define numberp(obj)  (wbit_test(as_oint(obj),number_bit_o))
    #ifdef WIDE_STRUCT
      #undef numberp
      #define numberp(obj)  (typecode(obj) & bit(number_bit_t))
    #endif
  #else
    #define immediate_number_p(obj)  \
      ((as_oint(obj) & 0x27) == (fixnum_type&sfloat_type))
    #define numberp(obj)  \
      (immediate_number_p(obj) \
       || (varobjectp(obj)     \
           && ((uintB)(Record_type(obj)-Rectype_Bignum) <= Rectype_Complex-Rectype_Bignum) \
      )   )
  #endif

# Test auf Vector (Typbytes %001,%010,%011,%101,%110,%111)
  #ifdef TYPECODES
    #define vectorp(obj)  \
      ((tint)((typecode(obj) & ~bit(notsimple_bit_t))-1) <= (tint)(svector_type-1))
  #else
    #define vectorp(obj)  \
      (varobjectp(obj) && ((uintB)((Record_type(obj) & ~4) - 1) <= 2))
  #endif

# Test auf simple-vector oder simple-bit-vector oder simple-string
  #ifdef TYPECODES
    #define simplep(obj)  \
      ((tint)(typecode(obj) - 1) <= (tint)(svector_type-1))
  #else
    #define simplep(obj)  \
      (varobjectp(obj) && ((uintB)(Record_type(obj) - 1) <= 2))
  #endif

# Test eines Array auf simple-vector oder simple-bit-vector oder simple-string
  #ifdef TYPECODES
    #define array_simplep(obj)  \
      (typecode(obj) <= svector_type)
  #else
    #define array_simplep(obj)  \
      ((uintB)Record_type(obj) < 4)
  #endif

# Test auf simple-vector
  #ifdef TYPECODES
    #define simple_vector_p(obj)  \
      (typecode(obj) == svector_type)
  #else
    #define simple_vector_p(obj)  \
      (varobjectp(obj) && (Record_type(obj) == Rectype_Svector))
  #endif

# Test auf general-vector=(vector t)
  #ifdef TYPECODES
    #define general_vector_p(obj)  \
      ((typecode(obj) & ~bit(notsimple_bit_t)) == svector_type)
  #else
    #define general_vector_p(obj)  \
      (varobjectp(obj) && ((Record_type(obj) & ~4) == Rectype_Svector))
  #endif

# Test auf simple-string
  #ifdef TYPECODES
    #define simple_string_p(obj)  \
      (typecode(obj) == sstring_type)
  #else
    #define simple_string_p(obj)  \
      (varobjectp(obj) && (Record_type(obj) == Rectype_Sstring))
  #endif

# Test auf string
  #ifdef TYPECODES
    #define stringp(obj)  \
      ((typecode(obj) & ~bit(notsimple_bit_t)) == sstring_type)
  #else
    #define stringp(obj)  \
      (varobjectp(obj) && ((Record_type(obj) & ~4) == Rectype_Sstring))
  #endif

# Test auf simple-bit-vector
  #ifdef TYPECODES
    #define simple_bit_vector_p(obj)  \
      (typecode(obj) == sbvector_type)
  #else
    #define simple_bit_vector_p(obj)  \
      (varobjectp(obj) && (Record_type(obj) == Rectype_Sbvector))
  #endif

# Test auf bit-vector
  #ifdef TYPECODES
    #define bit_vector_p(obj)  \
      ((typecode(obj) == sbvector_type)                                  \
       || ((typecode(obj) == bvector_type)                               \
           && ((Iarray_flags(obj) & arrayflags_atype_mask) == Atype_Bit) \
      )   )
  #else
    #define bit_vector_p(obj)  \
      (varobjectp(obj)                                                       \
       && ((Record_type(obj) == Rectype_Sbvector)                            \
           || ((Record_type(obj) == Rectype_bvector)                         \
               && ((Iarray_flags(obj) & arrayflags_atype_mask) == Atype_Bit) \
      )   )   )
  #endif

# Test auf byte-vector
  #ifdef TYPECODES
    #define byte_vector_p(obj)  \
      ((typecode(obj) & ~bit(notsimple_bit_t)) == sbvector_type)
  #else
    #define byte_vector_p(obj)  \
      (varobjectp(obj) && ((Record_type(obj) & ~4) == Rectype_Sbvector))
  #endif

# Test auf byte-vector, ausgenommen simple-bit-vector
  #ifdef TYPECODES
    #define general_byte_vector_p(obj)  \
      (typecode(obj) == bvector_type)
  #else
    #define general_byte_vector_p(obj)  \
      (varobjectp(obj) && (Record_type(obj) == Rectype_bvector))
  #endif

# Test auf Array allgemein
  #ifdef TYPECODES
    #define arrayp(obj)  \
      ((tint)(typecode(obj) - 1) <= (tint)(vector_type-1))
  #else
    #define arrayp(obj)  \
      (varobjectp(obj) && ((uintB)(Record_type(obj)-1) <= 7-1))
  #endif

# Test auf Array, der kein Vector ist (Typbyte %100)
  #ifdef TYPECODES
    #define mdarrayp(obj)  \
      (typecode(obj) == mdarray_type)
  #else
    #define mdarrayp(obj)  \
      (varobjectp(obj) && (Record_type(obj) == Rectype_mdarray))
  #endif

#ifdef TYPECODES
  # Test auf Closure/Structure/Stream/Instanz/OtherRecord
    #define if_recordp(obj,statement1,statement2)  \
      { switch (typecode(obj))              \
          { case_record: statement1; break; \
            default: statement2; break;     \
      }   }
#else
  # Test auf Srecord/Xrecord
    #define if_recordp(obj,statement1,statement2)  \
      if (orecordp(obj))                                                       \
        switch (Record_type(obj))                                              \
          { case Rectype_Sbvector: case Rectype_Sstring: case Rectype_Svector: \
            case Rectype_mdarray:                                              \
            case Rectype_bvector: case Rectype_string: case Rectype_vector:    \
            case Rectype_Bignum: case Rectype_Lfloat:                          \
              goto not_record;                                                 \
            default: { statement1 } break;                                     \
          }                                                                    \
      else                                                                     \
        not_record: { statement2 }
#endif

# Test auf Closure
  #ifdef TYPECODES
    #define closurep(obj)  (typecode(obj)==closure_type)
  #else
    #define closurep(obj)  \
      (varobjectp(obj) && (Record_type(obj) == Rectype_Closure))
  #endif

# Test auf compilierte Closure
  # In einer Closure ist die zweite Komponente
  # entweder eine Liste (der Lambdabody bei interpretierten Closures)
  # oder ein Simple-Bit-Vector (der Codevektor bei compilierten Closures).
  #define cclosurep(obj)  \
    (closurep(obj) && simple_bit_vector_p(TheClosure(obj)->clos_codevec))

# Test auf generische Funktion
  #define genericfunctionp(obj)  \
    (cclosurep(obj)                                                     \
     && (TheCodevec(TheClosure(obj)->clos_codevec)->ccv_flags & bit(4)) \
    )

# Test auf CLOS-Instanz
  #ifdef TYPECODES
    #define instancep(obj)  (typecode(obj)==instance_type)
  #else
    #define instancep(obj)  \
      (varobjectp(obj) && (Record_type(obj) == Rectype_Instance))
  #endif

# Test auf CLOS-Klasse
# Unser CLOS implementiert alle Klassen als Instanzen einer (nicht notwendig
# direkten) Unterklasse von <class>.
  #define if_classp(obj,statement1,statement2)  \
    if (structurep(obj))                                           \
      { var object list = Cdr(TheStructure(obj)->structure_types); \
        var object sublist = O(class_structure_types);             \
        # (tailp sublist list) bestimmen:                          \
        loop                                                       \
          { if (eq(list,sublist)) goto obj##_classp_yes;           \
            if (atomp(list)) goto obj##_classp_no;                 \
            list = Cdr(list);                                      \
          }                                                        \
        obj##_classp_yes: statement1;                              \
      }                                                            \
    else                                                           \
      { obj##_classp_no: statement2; }

# Test auf Other-Record
# This is not really a type test (because there is no well-defined type
# Other-Record). It's just a precondition for calling Record_type(obj).
  #ifdef TYPECODES
    #define orecordp(obj)  (typecode(obj)==orecord_type)
  #else
    #define orecordp(obj)  varobjectp(obj)
  #endif

# Test auf Structure
  #ifdef case_structure
    #define structurep(obj)  (typecode(obj)==structure_type)
  #else
    #define structurep(obj)  \
      (orecordp(obj) && (Record_type(obj) == Rectype_Structure))
  #endif

# Test auf Stream
  #ifdef case_stream
    #define streamp(obj)  (typecode(obj)==stream_type)
  #else
    #define streamp(obj)  \
      (orecordp(obj) && (Record_type(obj) == Rectype_Stream))
  #endif

# Test auf Package
  #define packagep(obj)  \
    (orecordp(obj) && (Record_type(obj) == Rectype_Package))

# Test auf Hash-Table
  #define hash_table_p(obj)  \
    (orecordp(obj) && (Record_type(obj) == Rectype_Hashtable))

# Test auf Readtable
  #define readtablep(obj)  \
    (orecordp(obj) && (Record_type(obj) == Rectype_Readtable))

# Test auf Pathname
  #define pathnamep(obj)  \
    (orecordp(obj) && (Record_type(obj) == Rectype_Pathname))

# Test auf Logical Pathname
#ifdef LOGICAL_PATHNAMES
  #define logpathnamep(obj)  \
    (orecordp(obj) && (Record_type(obj) == Rectype_Logpathname))
#else
  #define logpathnamep(obj)  FALSE
#endif

# Test auf Extended Pathname (d.h. Pathname oder Logical Pathname)
# define xpathnamep(obj)  (pathnamep(obj) || logpathnamep(obj))
#ifdef LOGICAL_PATHNAMES
  #define xpathnamep(obj)  \
    (orecordp(obj)                                    \
     && ((Record_type(obj) == Rectype_Pathname)       \
         || (Record_type(obj) == Rectype_Logpathname) \
    )   )
#else
  #define xpathnamep(obj)  pathnamep(obj)
#endif

# Test auf Random-State
  #define random_state_p(obj)  \
    (orecordp(obj) && (Record_type(obj) == Rectype_Random_State))

# Test auf Byte
  #define bytep(obj)  \
    (orecordp(obj) && (Record_type(obj) == Rectype_Byte))

# Test auf Fsubr
  #define fsubrp(obj)  \
    (orecordp(obj) && (Record_type(obj) == Rectype_Fsubr))

# Test auf Loadtimeeval
  #define loadtimeevalp(obj)  \
    (orecordp(obj) && (Record_type(obj) == Rectype_Loadtimeeval))

# Test auf Symbolmacro
  #define symbolmacrop(obj)  \
    (orecordp(obj) && (Record_type(obj) == Rectype_Symbolmacro))

# Test auf Fpointer
  #define fpointerp(obj)  \
    (orecordp(obj) && (Record_type(obj) == Rectype_Fpointer))

# Test auf Faddress
  #define faddressp(obj)  \
    (orecordp(obj) && (Record_type(obj) == Rectype_Faddress))

# Test auf Fvariable
  #define fvariablep(obj)  \
    (orecordp(obj) && (Record_type(obj) == Rectype_Fvariable))

# Test auf Ffunction
#ifdef DYNAMIC_FFI
  #define ffunctionp(obj)  \
    (orecordp(obj) && (Record_type(obj) == Rectype_Ffunction))
#else
  #define ffunctionp(obj)  ((void)(obj), 0)
#endif

# Test for Weakpointer
  #define weakpointerp(obj)  \
    (orecordp(obj) && (Record_type(obj) == Rectype_Weakpointer))

# test for socket-server and for socket-stream
#ifdef SOCKET_STREAMS
  #define socket_server_p(obj)  \
    (orecordp(obj) && (Record_type(obj) == Rectype_Socket_Server))
  #define socket_stream_p(obj)  \
    (streamp(obj) && (TheStream(obj)->strmtype==strmtype_socket))
#endif

#ifdef YET_ANOTHER_RECORD
# Test auf Yetanother
  #define yetanotherp(obj)  \
    (orecordp(obj) && (Record_type(obj) == Rectype_Yetanother))
#endif

# Test auf Character
  #ifdef TYPECODES
    #define charp(obj)  (typecode(obj)==char_type)
  #else
    #define charp(obj)  ((as_oint(obj) & 0x3F) == char_type)
  #endif

# Test for base character
  #define base_char_p(obj)  \
    ((as_oint(obj) & ~((oint)(bit(base_char_int_len)-1)<<oint_data_shift)) == type_zero_oint(char_type))

# Test auf SUBR (compiliertes funktionales Objekt)
  #ifdef TYPECODES
    #define subrp(obj)  (typecode(obj)==subr_type)
  #else
    #define subrp(obj)  ((as_oint(obj) & 3) == subr_bias)
  #endif

# Test auf Pointer in den STACK (normalerweise auf einen Frame)
  #ifdef TYPECODES
    #define framepointerp(obj)  (typecode(obj)==system_type) # andere F�lle??
  #else
    #define framepointerp(obj)  ((as_oint(obj) & 3) == machine_bias) # andere F�lle??
  #endif

#ifndef TYPECODES

# Test auf Maschinen-Pointer
  #define machinep(obj)  ((as_oint(obj) & 3) == machine_bias)

# Test auf Read-Label
  #define read_label_p(obj)  ((as_oint(obj) & 0x3F) == read_label_type)

# Test auf System-Pointer
  #define systemp(obj)  ((as_oint(obj) & 0x3F) == system_type)

#endif

# Test auf reelle Zahl
  #ifdef TYPECODES
    #define if_realp(obj,statement1,statement2)  \
      {var object obj_from_if_realp = (obj);                      \
       var tint type_from_if_realp = typecode(obj_from_if_realp); \
       if ( (type_from_if_realp & bit(number_bit_t))              \
            && !(type_from_if_realp==complex_type) )              \
         { statement1 } else { statement2 }                       \
      }
  #else
    #define if_realp(obj,statement1,statement2)  \
      if (((as_oint(obj) & 0x27) == fixnum_type) \
          || (varobjectp(obj)                    \
              && ((uintB)(Record_type(obj)-Rectype_Bignum) <= Rectype_Ratio-Rectype_Bignum) \
         )   )                                   \
        { statement1 } else { statement2 }
  #endif

# Test auf rationale Zahl
  #ifdef TYPECODES
    #define if_rationalp(obj,statement1,statement2)  \
      {var object obj_from_if_rationalp = (obj);                          \
       var tint type_from_if_rationalp = typecode(obj_from_if_rationalp); \
       if ( (!(type_from_if_rationalp==complex_type))                     \
            &&                                                            \
            ((type_from_if_rationalp &                                    \
              ~((fixnum_type|bignum_type|ratio_type|bit(sign_bit_t)) & ~(fixnum_type&bignum_type&ratio_type)) \
             ) == (fixnum_type&bignum_type&ratio_type)                    \
          ) )                                                             \
         { statement1 } else { statement2 }                               \
      }
  #else
    #define if_rationalp(obj,statement1,statement2)  \
      if (((as_oint(obj) & 0x37) == fixnum_type)         \
          || (varobjectp(obj)                            \
              && ((Record_type(obj) == Rectype_Bignum)   \
                  || (Record_type(obj) == Rectype_Ratio) \
         )   )   )                                       \
        { statement1 } else { statement2 }
  #endif

# Test auf ganze Zahl
  #ifdef TYPECODES
    #define integerp(obj)  \
      ((typecode(obj) &                                                           \
        ~((fixnum_type|bignum_type|bit(sign_bit_t)) & ~(fixnum_type&bignum_type)) \
       ) == (fixnum_type&bignum_type)                                             \
      )
  #else
    #define integerp(obj)  \
     (((as_oint(obj) & 0x37) == fixnum_type)                       \
      || (varobjectp(obj) && (Record_type(obj) == Rectype_Bignum)) \
     )
  #endif

# Test auf Fixnum
  #ifdef TYPECODES
    #define fixnump(obj)  ((typecode(obj) & ~bit(sign_bit_t)) == fixnum_type)
  #else
    #define fixnump(obj)  ((as_oint(obj) & 0x37) == fixnum_type)
  #endif

# Test auf Fixnum >=0
  #ifdef TYPECODES
    #define posfixnump(obj)  (typecode(obj) == fixnum_type)
  #else
    #define posfixnump(obj)  ((as_oint(obj) & 0x3F) == fixnum_type)
  #endif

# Test auf Bignum
  #ifdef TYPECODES
    #define bignump(obj)  ((typecode(obj) & ~bit(sign_bit_t)) == bignum_type)
  #else
    #define bignump(obj)  \
      (varobjectp(obj) && (Record_type(obj) == Rectype_Bignum))
  #endif

# Test auf Bignum >=0
  #ifdef TYPECODES
    #define posbignump(obj)  (typecode(obj) == bignum_type)
  #else
    #define posbignump(obj)  \
      (varobjectp(obj)                         \
       && (Record_type(obj) == Rectype_Bignum) \
       && ((Record_flags(obj) & bit(7)) == 0)  \
      )
  #endif

# Test auf Ratio
  #ifdef TYPECODES
    #define ratiop(obj)  ((typecode(obj) & ~bit(sign_bit_t)) == ratio_type)
  #else
    #define ratiop(obj)  (varobjectp(obj) && (Record_type(obj) == Rectype_Ratio))
  #endif

# Test auf Float
  #ifdef TYPECODES
    #define floatp(obj)  \
      ((typecode(obj) &  \
       ~((sfloat_type|ffloat_type|dfloat_type|lfloat_type|bit(sign_bit_t)) & ~(sfloat_type&ffloat_type&dfloat_type&lfloat_type)) \
       ) == (sfloat_type&ffloat_type&dfloat_type&lfloat_type))
  #else
    #define floatp(obj)  \
      (((as_oint(obj) & 0x37) == sfloat_type) \
       || (varobjectp(obj)                    \
           && ((uintB)(Record_type(obj)-Rectype_Lfloat) <= Rectype_Ffloat-Rectype_Lfloat) \
      )   )
  #endif

# Test auf Short-Float
  #ifdef TYPECODES
    #define short_float_p(obj)  ((typecode(obj) & ~bit(sign_bit_t)) == sfloat_type)
  #else
    #define short_float_p(obj)  ((as_oint(obj) & 0x37) == sfloat_type)
  #endif

# Test auf Single-Float
  #ifdef TYPECODES
    #define single_float_p(obj)  ((typecode(obj) & ~bit(sign_bit_t)) == ffloat_type)
  #else
    #define single_float_p(obj)  (varobjectp(obj) && (Record_type(obj) == Rectype_Ffloat))
  #endif

# Test auf Double-Float
  #ifdef TYPECODES
    #define double_float_p(obj)  ((typecode(obj) & ~bit(sign_bit_t)) == dfloat_type)
  #else
    #define double_float_p(obj)  (varobjectp(obj) && (Record_type(obj) == Rectype_Dfloat))
  #endif

# Test auf Long-Float
  #ifdef TYPECODES
    #define long_float_p(obj)  ((typecode(obj) & ~bit(sign_bit_t)) == lfloat_type)
  #else
    #define long_float_p(obj)  (varobjectp(obj) && (Record_type(obj) == Rectype_Lfloat))
  #endif

# Test auf Complex
  #ifdef TYPECODES
    #define complexp(obj)  (typecode(obj) == complex_type)
  #else
    #define complexp(obj)  (varobjectp(obj) && (Record_type(obj) == Rectype_Complex))
  #endif

# Test einer reellen Zahl, ob sie >=0 ist:
  #ifdef TYPECODES
    # define positivep(obj)  ((as_oint(obj) & wbit(sign_bit_o)) == 0)
    #define positivep(obj)  (!wbit_test(as_oint(obj),sign_bit_o))
    #ifdef WIDE_STRUCT
      #undef positivep
      #define positivep(obj)  ((typecode(obj) & bit(sign_bit_t)) == 0)
    #endif
  #else
    #define positivep(obj)  \
      ((as_oint(obj) & wbit(1))                                      \
       ? /* fixnum, sfloat */ (as_oint(obj) & wbit(sign_bit_o)) == 0 \
       : /* bignum, [fdl]float */ (Record_flags(obj) & bit(7)) == 0  \
      )
  #endif


# Fallunterscheidungen nach Typcodes:
# Beispiel:
#   switch (typecode(obj)) {
#     case_symbol: ....
#     case_orecord:
#       switch (Record_type(obj)) {
#         case_Rectype_Symbol_above;
#         ...
#       }
#   }

#ifdef case_structure
  #define case_Rectype_Structure_above
#else
  #define case_Rectype_Structure_above  \
    case Rectype_Structure: goto case_structure;
#endif

#ifdef case_stream
  #define case_Rectype_Stream_above
#else
  #define case_Rectype_Stream_above  \
    case Rectype_Stream: goto case_stream;
#endif

#ifdef TYPECODES
  #define case_Rectype_Closure_above
  #define case_Rectype_Instance_above
  #define case_Rectype_Sbvector_above
  #define case_Rectype_Sstring_above
  #define case_Rectype_Svector_above
  #define case_Rectype_mdarray_above
  #define case_Rectype_obvector_above
  #define case_Rectype_ostring_above
  #define case_Rectype_ovector_above
  #define case_Rectype_Bignum_above
  #define case_Rectype_Lfloat_above
  #define case_Rectype_Dfloat_above
  #define case_Rectype_Ffloat_above
  #define case_Rectype_Ratio_above
  #define case_Rectype_Complex_above
  #define case_Rectype_Symbol_above
  # Composite cases:
  #define case_Rectype_string_above
  #define case_Rectype_bvector_above
  #define case_Rectype_vector_above
  #define case_Rectype_array_above
  #define case_Rectype_number_above
  #define case_Rectype_float_above
  #define case_Rectype_integer_above
#else
  #define case_Rectype_Closure_above  \
    case Rectype_Closure: goto case_closure;
  #define case_Rectype_Instance_above  \
    case Rectype_Instance: goto case_instance;
  #define case_Rectype_Sbvector_above  \
    case Rectype_Sbvector: goto case_sbvector;
  #define case_Rectype_Sstring_above  \
    case Rectype_Sstring: goto case_sstring;
  #define case_Rectype_Svector_above  \
    case Rectype_Svector: goto case_svector;
  #define case_Rectype_mdarray_above  \
    case Rectype_mdarray: goto case_mdarray;
  #define case_Rectype_obvector_above  \
    case Rectype_bvector: goto case_obvector;
  #define case_Rectype_ostring_above  \
    case Rectype_string: goto case_ostring;
  #define case_Rectype_ovector_above  \
    case Rectype_vector: goto case_ovector;
  #define case_Rectype_Bignum_above  \
    case Rectype_Bignum: goto case_bignum;
  #define case_Rectype_Lfloat_above  \
    case Rectype_Lfloat: goto case_lfloat;
  #define case_Rectype_Dfloat_above  \
    case Rectype_Dfloat: goto case_dfloat;
  #define case_Rectype_Ffloat_above  \
    case Rectype_Ffloat: goto case_ffloat;
  #define case_Rectype_Ratio_above  \
    case Rectype_Ratio: goto case_ratio;
  #define case_Rectype_Complex_above  \
    case Rectype_Complex: goto case_complex;
  #define case_Rectype_Symbol_above  \
    case Rectype_Symbol: goto case_symbol;
  # Composite cases:
  #define case_Rectype_string_above  \
    case Rectype_Sstring: case Rectype_string: goto case_string;
  #define case_Rectype_bvector_above  \
    case Rectype_Sbvector: case Rectype_bvector: goto case_bvector;
  #define case_Rectype_vector_above  \
    case Rectype_Svector: case Rectype_vector: goto case_vector;
  #define case_Rectype_array_above  \
    case Rectype_Sstring: case Rectype_string:   \
    case Rectype_Sbvector: case Rectype_bvector: \
    case Rectype_Svector: case Rectype_vector:   \
    case Rectype_mdarray:                        \
      goto case_array;
  #define case_Rectype_number_above  /* don't forget immediate_number_p */ \
    case Rectype_Complex: case Rectype_Ratio:                      \
    case Rectype_Ffloat: case Rectype_Dfloat: case Rectype_Lfloat: \
    case Rectype_Bignum:                                           \
      goto case_number;
  #define case_Rectype_float_above  /* don't forget short_float_p */ \
    case Rectype_Ffloat: case Rectype_Dfloat: case Rectype_Lfloat: \
      goto case_float;
  #define case_Rectype_integer_above  /* don't forget fixnump */ \
    case Rectype_Bignum: goto case_integer;
#endif


# ################# Deklarationen zur Arithmetik ########################## #


# Typenhierarchie:
# Number (N) =
#    Real (R) =
#       Float (F) =
#          Short float (SF)
#          Single float (FF)
#          Double float (DF)
#          Long float (LF)
#       Rational (RA) =
#          Integer (I) =
#             Fixnum (FN)
#             Bignum (BN)
#          Ratio (RT)
#    Complex (C)


# Typfeld:
# Bits zum Testen, ob dieser Typ vorliegt (Bit gesetzt, wenn ja).
# _bit_t zum Test im Typbyte (tint)
# _bit_o zum Test im Objekt (oint)

#ifndef NUMBER_BITS_INVERTED
  #define number_wbit_test  wbit_test
#else
  #define number_wbit_test  !wbit_test
#endif

#ifdef TYPECODES

# siehe oben:
# #define number_bit_t     4  # gesetzt nur bei Zahlen
# #define number_bit_o     (number_bit_t+oint_type_shift)    # gesetzt nur bei Zahlen

# float_bit:
# in einer Zahl: Bit gesetzt, falls es sich um ein Float handelt.
#                Bit gel�scht, falls es sich um eine rationale oder komplexe Zahl handelt.
# (Bei NUMBER_BITS_INVERTED genau umgekehrt.)
# #define float_bit_t      1
# #define float_bit_o      (float_bit_t+oint_type_shift)

# float1_bit:
# In einem Floating-point: entscheidet genauer:
#ifndef NUMBER_BITS_INVERTED
# Float-Bit   1 2
#             0 0    Short Float (SF)
#             0 1    Single Float (FF)
#             1 0    Double Float (DF)
#             1 1    Long Float (LF)
#else
# Float-Bit   1 2
#             0 0    Long Float (LF)
#             0 1    Double Float (DF)
#             1 0    Single Float (FF)
#             1 1    Short Float (SF)
#endif
# #define float1_bit_t     3
# #define float1_bit_o     (float1_bit_t+oint_type_shift)
# #define float2_bit_t     2
# #define float2_bit_o     (float2_bit_t+oint_type_shift)

# ratio_bit:
# In rationalen Zahlen: Bit gesetzt, falls es sich um einen echten Bruch hand.
#                       Bit gel�scht, falls es sich um ein Integer handelt.
# (Bei NUMBER_BITS_INVERTED genau umgekehrt.)
# #define ratio_bit_t      3
# #define ratio_bit_o      (ratio_bit_t+oint_type_shift)

# bignum_bit:
# In ganzen Zahlen: Bit gesetzt, falls es sich um ein Bignum handelt.
#                   Bit gel�scht, falls es sich um ein Fixnum handelt.
# (Bei NUMBER_BITS_INVERTED genau umgekehrt.)
# #define bignum_bit_t     2
# #define bignum_bit_o     (bignum_bit_t+oint_type_shift)

# vorz_bit:
# Bei Reals:
# gibt das Vorzeichen der Zahl an.
# Bit gesetzt, falls Zahl < 0,
# Bit gel�scht, falls Zahl >=0.
  #define vorz_bit_t       sign_bit_t
                           # sollte = 0 sein, damit das Vorzeichen-Extend
                           # bei Fixnums einfacher geht.
  #define vorz_bit_o       (vorz_bit_t+oint_type_shift)

#endif

# Liefert das Vorzeichen einer reellen Zahl (0 falls >=0, -1 falls <0)
  #ifdef TYPECODES
    #if (vorz_bit_o<32) && !defined(WIDE_STRUCT)
      #define R_sign(obj)  ((signean)sign_of_sint32( (sint32)((uint32)as_oint(obj) << (31-vorz_bit_o)) ))
    #else
      # define R_sign(obj)  ((signean)sign_of_sint32( (sint32)(uint32)(as_oint(obj) >> (vorz_bit_o-31)) ))
      #define R_sign(obj)  ((signean)sign_of_sint32( (sint32)((uint32)typecode(obj) << (31-vorz_bit_t)) ))
    #endif
  #else
    #define R_sign(obj)  ((signean)sign_of_sint32(_R_sign(obj)))
    #define _R_sign(obj)  \
      ((as_oint(obj) & wbit(1))                                       \
       ? /* fixnum, sfloat */ (sint32)as_oint(obj) << (31-sign_bit_o) \
       : /* [fdl]float */ (sint32)(sintB)Record_flags(obj)            \
      )
  #endif

# Liefert das Vorzeichen eines Fixnum/Bignum/Ratio/
# Short-/Single-/Double-/Long-Float.
  #ifdef TYPECODES
    #define FN_sign(obj)  R_sign(obj)
    #define BN_sign(obj)  R_sign(obj)
    #define RT_sign(obj)  R_sign(obj)
    #define SF_sign(obj)  R_sign(obj)
    #define FF_sign(obj)  R_sign(obj)
    #define DF_sign(obj)  R_sign(obj)
    #define LF_sign(obj)  R_sign(obj)
  #else
    #define FN_sign(obj)  \
      ((signean)sign_of_sint32((sint32)as_oint(obj) << (31-sign_bit_o)))
    #define BN_sign(obj)  \
      ((signean)sign_of_sint32((sint32)(sintB)Record_flags(obj)))
    #define RT_sign(obj)  \
      ((signean)sign_of_sint32((sint32)(sintB)Record_flags(obj)))
    #define SF_sign(obj)  \
      ((signean)sign_of_sint32((sint32)as_oint(obj) << (31-sign_bit_o)))
    #define FF_sign(obj)  \
      ((signean)sign_of_sint32((sint32)(sintB)Record_flags(obj)))
    #define DF_sign(obj)  \
      ((signean)sign_of_sint32((sint32)(sintB)Record_flags(obj)))
    #define LF_sign(obj)  \
      ((signean)sign_of_sint32((sint32)(sintB)Record_flags(obj)))
  #endif

# Stellt fest, ob zwei reelle Zahlen dasselbe Vorzeichen haben:
  #ifdef TYPECODES
    #define same_sign_p(obj1,obj2)  \
      (wbit_test(as_oint(obj1)^as_oint(obj2),vorz_bit_o)==0)
  #else
    #define same_sign_p(obj1,obj2)  \
      ((sint32)(_R_sign(obj1) ^ _R_sign(obj2)) >= 0)
  #endif


# Typtestmacros:
# (Liefern /=0, falls erf�llt. Pr�fix 'm', wenn Argument im Speicher sitzt.)

# Testet ein Objekt, ob es eine Zahl ist: (siehe oben)
  # define numberp(obj)  ...

# Testet eine Zahl, ob es ein Float ist.
  #ifdef TYPECODES
    #ifndef NUMBER_BITS_INVERTED
      # define N_floatp(obj)  ( as_oint(obj) & wbit(float_bit_o) )
      #define N_floatp(obj)  (wbit_test(as_oint(obj),float_bit_o))
    #else
      #define N_floatp(obj)  (!wbit_test(as_oint(obj),float_bit_o))
    #endif
  #else
    #define N_floatp(obj)  floatp(obj)
  #endif

# Testet eine Zahl, ob es ein Integer ist.
  #ifdef TYPECODES
    #ifndef NUMBER_BITS_INVERTED
      #define N_integerp(obj)  (!( as_oint(obj) & (wbit(float_bit_o)|wbit(ratio_bit_o)) ))
    #else
      #define N_integerp(obj)  (!( (wbit(float_bit_o)|wbit(ratio_bit_o)) & ~as_oint(obj) ))
    #endif
  #else
    #define N_integerp(obj)  integerp(obj)
  #endif

# Testet eine reelle Zahl, ob sie rational ist.
  #ifdef TYPECODES
    #ifndef NUMBER_BITS_INVERTED
      # define R_rationalp(obj)  (!( as_oint(obj) & wbit(float_bit_o) ))
      #define R_rationalp(obj)  (!wbit_test(as_oint(obj),float_bit_o))
    #else
      #define R_rationalp(obj)  (wbit_test(as_oint(obj),float_bit_o))
    #endif
  #else
    #define R_rationalp(obj)  (!floatp(obj))
  #endif

# Testet eine reelle Zahl, ob sie ein Float ist.
  #ifdef TYPECODES
    #ifndef NUMBER_BITS_INVERTED
      # define R_floatp(obj)  ( as_oint(obj) & wbit(float_bit_o) )
      #define R_floatp(obj)  (wbit_test(as_oint(obj),float_bit_o))
    #else
      #define R_floatp(obj)  (!wbit_test(as_oint(obj),float_bit_o))
    #endif
  #else
    #define R_floatp(obj)  floatp(obj)
  #endif

# Testet eine reelle Zahl, ob sie <0 ist.
  #ifdef TYPECODES
    # define R_minusp(obj)  ( as_oint(obj) & wbit(vorz_bit_o) )
    #define R_minusp(obj)  (wbit_test(as_oint(obj),vorz_bit_o))
  #else
    #define R_minusp(obj)  (!positivep(obj))
  #endif

# Testet eine rationale Zahl, ob sie ganz ist.
  #ifdef TYPECODES
    #ifndef NUMBER_BITS_INVERTED
      # define RA_integerp(obj)  (!( as_oint(obj) & wbit(ratio_bit_o) ))
      #define RA_integerp(obj)  (!wbit_test(as_oint(obj),ratio_bit_o))
    #else
      #define RA_integerp(obj)  (wbit_test(as_oint(obj),ratio_bit_o))
    #endif
  #else
    #define RA_integerp(obj)  (!ratiop(obj))
  #endif

# Testet eine rationale Zahl, ob sie gebrochen ist.
  #ifdef TYPECODES
    #ifndef NUMBER_BITS_INVERTED
      # define RA_ratiop(obj)  ( as_oint(obj) & wbit(ratio_bit_o) )
      #define RA_ratiop(obj)  (wbit_test(as_oint(obj),ratio_bit_o))
    #else
      #define RA_ratiop(obj)  (!wbit_test(as_oint(obj),ratio_bit_o))
    #endif
  #else
    #define RA_ratiop(obj)  ratiop(obj)
  #endif

# Testet eine ganze Zahl, ob sie ein Bignum ist.
  #ifndef NUMBER_BITS_INVERTED
    # define I_bignump(obj)  ( as_oint(obj) & wbit(bignum_bit_o) )
    #define I_bignump(obj)  (wbit_test(as_oint(obj),bignum_bit_o))
  #else
    #define I_bignump(obj)  (!wbit_test(as_oint(obj),bignum_bit_o))
  #endif

# Testet eine ganze Zahl, ob sie ein Fixnum ist.
  #ifndef NUMBER_BITS_INVERTED
    # define I_fixnump(obj)  (!( as_oint(obj) & wbit(bignum_bit_o) ))
    #define I_fixnump(obj)  (!wbit_test(as_oint(obj),bignum_bit_o))
  #else
    #define I_fixnump(obj)  (wbit_test(as_oint(obj),bignum_bit_o))
  #endif

# Testet ein Fixnum, ob es >= 0 ist.
  #ifdef TYPECODES
    #define FN_positivep(obj)  positivep(obj)
  #else
    #define FN_positivep(obj)  ((as_oint(obj) & wbit(sign_bit_o)) == 0)
  #endif

# Testet ein Bignum, ob es >= 0 ist.
  #ifdef TYPECODES
    #define BN_positivep(obj)  positivep(obj)
  #else
    #define BN_positivep(obj)  ((Record_flags(obj) & bit(7)) == 0)
  #endif

# Testet eine Zahl, ob sie eine reelle Zahl ist.
  #define N_realp(obj)  (!complexp(obj))

# Testet eine Zahl, ob sie eine komplexe Zahl ist.
  #define N_complexp(obj)  complexp(obj)

# Testet zwei ganze Zahlen, ob sie beide Bignum sind.
  #ifndef NUMBER_BITS_INVERTED
    #define I_I_bignums_p(obj1,obj2)  \
      (wbit_test(as_oint(obj1)&as_oint(obj2),bignum_bit_o))
  #else
    #define I_I_bignums_p(obj1,obj2)  \
      (!wbit_test(as_oint(obj1)|as_oint(obj2),bignum_bit_o))
  #endif

# Test auf ein Integer eines vorgegebenen Bereiches.
# obj sollte eine Variable sein
  #define uint8_p(obj)  \
    ((as_oint(obj) & ~((oint)0xFF << oint_data_shift)) == as_oint(Fixnum_0))
  #define sint8_p(obj)  \
    (((as_oint(obj) ^ (FN_positivep(obj) ? 0 : as_oint(Fixnum_minus1)^as_oint(Fixnum_0))) & ~((oint)0x7F << oint_data_shift)) == as_oint(Fixnum_0))
  #define uint16_p(obj)  \
    ((as_oint(obj) & ~((oint)0xFFFF << oint_data_shift)) == as_oint(Fixnum_0))
  #define sint16_p(obj)  \
    (((as_oint(obj) ^ (FN_positivep(obj) ? 0 : as_oint(Fixnum_minus1)^as_oint(Fixnum_0))) & ~((oint)0x7FFF << oint_data_shift)) == as_oint(Fixnum_0))
  #if (oint_data_len>=32)
    #define uint32_p(obj)  \
      ((as_oint(obj) & ~((oint)0xFFFFFFFFUL << oint_data_shift)) == as_oint(Fixnum_0))
  #else
    #define uint32_p(obj)  \
      (posfixnump(obj) \
       || (posbignump(obj) \
           && (Bignum_length(obj) <= ceiling(33,intDsize)) \
           && ((Bignum_length(obj) < ceiling(33,intDsize)) \
               || (TheBignum(obj)->data[0] < (uintD)bit(32%intDsize)) \
      )   )   )
  #endif
  #if (oint_data_len>=31)
    #define sint32_p(obj)  \
      (((as_oint(obj) ^ (FN_positivep(obj) ? 0 : as_oint(Fixnum_minus1)^as_oint(Fixnum_0))) & ~((oint)0x7FFFFFFFUL << oint_data_shift)) == as_oint(Fixnum_0))
  #else
    #define sint32_p(obj)  \
      (fixnump(obj) \
       || (bignump(obj) \
           && (Bignum_length(obj) <= ceiling(32,intDsize)) \
           && ((Bignum_length(obj) < ceiling(32,intDsize)) \
               || ((TheBignum(obj)->data[0] ^ (BN_positivep(obj) ? (uintD)0 : ~(uintD)0)) < (uintD)bit(31%intDsize)) \
      )   )   )
  #endif
  #define uint64_p(obj)  \
    (posfixnump(obj) \
     || (posbignump(obj) \
         && (Bignum_length(obj) <= ceiling(65,intDsize)) \
         && ((Bignum_length(obj) < ceiling(65,intDsize)) \
             || (TheBignum(obj)->data[0] < (uintD)bit(64%intDsize)) \
    )   )   )
  #define sint64_p(obj)  \
    (fixnump(obj) \
     || (bignump(obj) \
         && (Bignum_length(obj) <= ceiling(64,intDsize)) \
         && ((Bignum_length(obj) < ceiling(64,intDsize)) \
             || ((TheBignum(obj)->data[0] ^ (BN_positivep(obj) ? (uintD)0 : ~(uintD)0)) < (uintD)bit(63%intDsize)) \
    )   )   )
  #if (int_bitsize==16)
    #define uint_p  uint16_p
    #define sint_p  sint16_p
  #else # (int_bitsize==32)
    #define uint_p  uint32_p
    #define sint_p  sint32_p
  #endif
  #if (long_bitsize==32)
    #define ulong_p  uint32_p
    #define slong_p  sint32_p
  #else # (long_bitsize==64)
    #define ulong_p  uint64_p
    #define slong_p  sint64_p
  #endif


# ####################### TIMEBIBL zu TIME.D ############################## #

# Typ, der f�r 'Internal Time' verwendet wird:
#ifdef TIME_1
  typedef uintL internal_time;      # abgegriffener Wert des Tick-Z�hlers
  #ifdef TIME_AMIGAOS
    #define ticks_per_second  50UL    # 1 Tick = 1/50 sec, 50Hz-Z�hler
  #endif
  #ifdef TIME_MSDOS
    #define ticks_per_second  100UL   # 1 Tick = 1/100 sec, 100Hz-Z�hler
  #endif
  #if defined(TIME_UNIX_TIMES) || defined(TIME_RISCOS)
    #define ticks_per_second  CLK_TCK
  #endif
  #define sub_internal_time(x,y, z)  z = (x) - (y)
  #define add_internal_time(x,y, z)  z = (x) + (y)
#endif
#ifdef TIME_2
  #ifdef TIME_UNIX
    typedef struct { uintL tv_sec;    # ganze Sekunden seit 1.1.1970 00:00 GMT,
                                      # Ein 'uintL' f�r tv_sec reicht f�r 136 Jahre.
                     uintL tv_usec;   # zus�tzliche Mikrosekunden
                   }
            internal_time;
    #define ticks_per_second  1000000UL  # 1 Tick = 1 �sec
    #define sub_internal_time(x,y, z)  # z:=x-y  \
      { (z).tv_sec = (x).tv_sec - (y).tv_sec;                   \
        if ((x).tv_usec < (y).tv_usec)                          \
          { (x).tv_usec += ticks_per_second; (z).tv_sec -= 1; } \
        (z).tv_usec = (x).tv_usec - (y).tv_usec;                \
      }
    #define add_internal_time(x,y, z)  # z:=x+y  \
      { (z).tv_sec = (x).tv_sec + (y).tv_sec;                   \
        (z).tv_usec = (x).tv_usec + (y).tv_usec;                \
        if ((z).tv_usec >= ticks_per_second)                    \
          { (z).tv_usec -= ticks_per_second; (z).tv_sec += 1; } \
      }
  #endif
  #ifdef TIME_WIN32
    typedef # struct _FILETIME { DWORD dwLowDateTime; DWORD dwHighDateTime; }
            FILETIME  # Anzahl 0.1 �sec seit 1.1.1601 00:00 GMT.
            internal_time;
    #define ticks_per_second  10000000UL  # 1 Tick = 0.1 �sec
    #define sub_internal_time(x,y, z)  # z:=x-y  \
      { (z).dwHighDateTime = (x).dwHighDateTime - (y).dwHighDateTime;           \
        if ((x).dwLowDateTime < (y).dwLowDateTime) { (z).dwHighDateTime -= 1; } \
        (z).dwLowDateTime = (x).dwLowDateTime - (y).dwLowDateTime;              \
      }
    #define add_internal_time(x,y, z)  # z:=x+y  \
      { (z).dwHighDateTime = (x).dwHighDateTime + (y).dwHighDateTime;           \
        (z).dwLowDateTime = (x).dwLowDateTime + (y).dwLowDateTime;              \
        if ((z).dwLowDateTime < (x).dwLowDateTime) { (z).dwHighDateTime += 1; } \
      }
  #endif
#endif

#ifndef HAVE_RUN_TIME

# UP: H�lt die Run-Time-Stoppuhr an
# run_time_stop();
  extern void run_time_stop (void);
# wird verwendet von STREAM

# UP: L�sst die Run-Time-Stoppuhr weiterlaufen
# run_time_restart();
  extern void run_time_restart (void);
# wird verwendet von STREAM

#else

# Man braucht keine Run-Time-Stoppuhr
  #define run_time_stop()
  #define run_time_restart()

#endif

#ifdef TIME_1

# UP: Liefert die Real-Time
# get_real_time()
# < uintL ergebnis: Zeit seit LISP-System-Start (in 1/200 sec bzw. in 1/50 sec bzw. in 1/100 sec bzw. in 1/CLK_TCK sec)
  extern uintL get_real_time (void);
# wird verwendet von STREAM, LISPARIT

#endif

#ifdef TIME_2

# UP: Liefert die Real-Time
# get_real_time()
# < internal_time* ergebnis: absolute Zeit
  extern void get_real_time (internal_time*);
# wird verwendet von LISPARIT

#endif

# UP: Liefert die Run-Time
# get_running_times(&timescore);
# < timescore.runtime:  Run-Time seit LISP-System-Start (in Ticks)
# < timescore.realtime: Real-Time seit LISP-System-Start (in Ticks)
# < timescore.gctime:   GC-Time seit LISP-System-Start (in Ticks)
# < timescore.gccount:  Anzahl der GC's seit LISP-System-Start
# < timescore.gcfreed:  Gr��e des von den GC's bisher wiederbeschafften Platzes
  typedef struct { internal_time runtime;
                   internal_time realtime;
                   internal_time gctime;
                   uintL gccount;
                   uintL2 gcfreed; }
          timescore;
  extern void get_running_times (timescore*);
# wird verwendet von

# UP: Liefert die Run-Time
# get_running_time(runtime);
# < runtime: Run-Time (in Ticks)
  #ifndef HAVE_RUN_TIME
    #define get_running_time(runtime)  runtime = get_time()
    extern uintL get_time (void);
  #endif
  #if defined(TIME_UNIX) || defined(TIME_WIN32) || defined(TIME_UNIX_TIMES)
    #define get_running_time(runtime)  get_run_time(&runtime)
    #if defined(TIME_UNIX) || defined(TIME_WIN32)
      extern void get_run_time (internal_time* runtime);
    #endif
    #ifdef TIME_UNIX_TIMES
      extern uintL get_run_time (internal_time* runtime);
    #endif
  #endif
# wird verwendet von SPVW

# Zeitangabe in Decoded-Time:
  typedef struct { object Sekunden, Minuten, Stunden, Tag, Monat, Jahr; }
          decoded_time;

#if defined(MSDOS)
# UP: Wandelt das DOS-Zeitformat in Decoded-Time um.
# convert_time(time,date,&timepoint);
# > uintW time: Uhrzeit
#         Als Word: Bits 15..11: Stunde in {0,...,23},
#                   Bits 10..5:  Minute in {0,...,59},
#                   Bits 4..0:   Sekunde/2 in {0,...,29}.
# > uintW date: Datum
#         Als Word: Bits 15..9: Jahr-1980 in {0,...,119},
#                   Bits 8..5:  Monat in {1,...,12},
#                   Bits 4..0:  Tag in {1,...,31}.
# < timepoint.Sekunden, timepoint.Minuten, timepoint.Stunden,
#   timepoint.Tag, timepoint.Monat, timepoint.Jahr, jeweils als Fixnums
  extern void convert_timedate (uintW time, uintW date, decoded_time* timepoint);
# wird verwendet von PATHNAME
#endif
#ifdef AMIGAOS
# UP: Wandelt das Amiga-Zeitformat in Decoded-Time um.
# convert_time(&datestamp,&timepoint);
# > struct DateStamp datestamp: Uhrzeit
#          datestamp.ds_Days   : Anzahl Tage seit 1.1.1978
#          datestamp.ds_Minute : Anzahl Minuten seit 00:00 des Tages
#          datestamp.ds_Tick   : Anzahl Ticks seit Beginn der Minute
# < timepoint.Sekunden, timepoint.Minuten, timepoint.Stunden,
#   timepoint.Tag, timepoint.Monat, timepoint.Jahr, jeweils als Fixnums
  extern void convert_time (const struct DateStamp * datestamp, decoded_time* timepoint);
# wird verwendet von PATHNAME
#endif
#if defined(UNIX) || defined(MSDOS) || defined(RISCOS)
# UP: Wandelt das System-Zeitformat in Decoded-Time um.
# convert_time(&time,&timepoint);
# > time_t time: Zeit im System-Zeitformat
# < timepoint.Sekunden, timepoint.Minuten, timepoint.Stunden,
#   timepoint.Tag, timepoint.Monat, timepoint.Jahr, jeweils als Fixnums
  extern void convert_time (const time_t* time, decoded_time* timepoint);
# wird verwendet von PATHNAME
#endif
#ifdef WIN32_NATIVE
# UP: Wandelt das System-Zeitformat in Decoded-Time um.
# convert_time(&time,&timepoint);
# > FILETIME time: Zeit im System-Zeitformat
# < timepoint.Sekunden, timepoint.Minuten, timepoint.Stunden,
#   timepoint.Tag, timepoint.Monat, timepoint.Jahr, jeweils als Fixnums
  extern void convert_time (const FILETIME* time, decoded_time* timepoint);
#endif

#ifdef TIME_RELATIVE

# UP: Merkt sich die Uhrzeit beim LISP-System-Start.
# set_start_time(&timepoint);
# > timepoint: Zeit beim LISP-System-Start
# >   timepoint.Sekunden in {0,...,59},
# >   timepoint.Minuten in {0,...,59},
# >   timepoint.Stunden in {0,...,23},
# >   timepoint.Tag in {1,...,31},
# >   timepoint.Monat in {1,...,12},
# >   timepoint.Jahr in {1980,...,2999},
# >   jeweils als Fixnums.
# kann GC ausl�sen
  extern void set_start_time (const decoded_time* timepoint);
# wird verwendet von SPVW

#endif

# UP: Initialisiert die Zeitvariablen beim LISP-System-Start.
# init_time();
  extern void init_time (void);
# wird verwendet von SPVW


# ####################### SPVWBIBL zu SPVW.D ############################## #

/*
                          Die Stacks
                          ==========

Es werden zwei Stacks verwendet:
  - der C-Programmstack (Stackpointer SP = Register A7),
  - der LISP-Stack (Stackpointer STACK).
Alle Unterprogrammaufrufe geschehen mittels BSR/JSR �ber den Programmstack,
er dient au�erdem zur Zwischenspeicherung von Daten, die keine LISP-Objekte
sind. Der LISP-Stack wird verwendet zur Ablage der Frames und zur Zwischen-
speicherung von LISP-Objekten.
F�r beide Stacks werden die Wachstumsgrenzen von der Speicherverwaltung
kontrolliert �ber folgende Macros:
  check_SP();             testet den Programmstack gegen �berlauf
  check_STACK();          testet den LISP-Stack gegen �berlauf
  get_space_on_STACK(n);  testet, ob noch D0.L Bytes auf dem LISP-Stack frei sind
Auf dem LISP-Stack d�rfen grunds�tzlich nur Langw�rter abgelegt werden.
Ist dabei FRAME_BIT gesetzt, so handelt es sich um das untere Ende eines
Frames; dieses Langwort ist ein Pointer �ber den Frame, zusammen mit
einem Frame-Typ-Byte; falls darin SKIP2_BIT gel�scht ist, ist das
dar�berliegende Langwort kein LISP-Objekt.
Alle anderen Langw�rter auf dem LISP-Stack stellen LISP-Objekte dar.
*/

# Maschinenstack: SP
# SP() liefert den aktuellen Wert des SP.
# setSP(adresse); setzt den SP auf einen gegebenen Wert. Extrem gef�hrlich!
# FAST_SP definiert, falls SP-Zugriffe schnell sind.
  #ifdef GNU
    # Definition des Registers, in dem SP liegt.
    #ifdef MC680X0
      #define SP_register "sp"  # %sp = %a7
    #endif
    #ifdef SPARC
      #define SP_register "%sp"  # %sp = %o6
    #endif
    #ifdef HPPA
      #define SP_register "%r30"  # %sp = %r30
    #endif
    #ifdef MIPS
      #define SP_register "$sp"  # $sp = $29
    #endif
    #ifdef M88000
      #define SP_register "%r31"  # %sp = %r31
    #endif
    #ifdef RS6000
      #define SP_register "r1"
    #endif
    #ifdef ARM
      #define SP_register "%sp"  # %sp = %r13
    #endif
    #ifdef CONVEX
      #define SP_register "sp"  # $sp = $a0
    #endif
    #ifdef DECALPHA
      #define SP_register "$30"  # $sp = $30
    #endif
    #ifdef I80386
      #define SP_register "%esp"
    #endif
    #ifdef VAX
      #define SP_register "sp"
    #endif
  #endif
  #if defined(GNU) && !defined(NO_ASM)
    # Assembler-Anweisung, die das SP-Register in eine Variable kopiert.
    #ifdef MC680X0
      #ifdef __REGISTER_PREFIX__ # GNU C Version >= 2.4 hat %/ und __REGISTER_PREFIX__
        # Aber der Wert von __REGISTER_PREFIX__ ist unbrauchbar, weil wir evtl.
        # cross-compilieren.
        #define REGISTER_PREFIX  "%/"
      #else
        #define REGISTER_PREFIX  "" # oder "%%", je nach verwendetem Assembler
      #endif
      #define ASM_get_SP_register(resultvar)  ("movel "REGISTER_PREFIX"sp,%0" : "=g" (resultvar) : )
    #endif
    #ifdef SPARC
      #define ASM_get_SP_register(resultvar)  ("mov %%sp,%0" : "=r" (resultvar) : )
    #endif
    #ifdef HPPA
      #define ASM_get_SP_register(resultvar)  ("copy %%r30,%0" : "=r" (resultvar) : )
    #endif
    #ifdef MIPS
      #define ASM_get_SP_register(resultvar)  ("move\t%0,$sp" : "=r" (resultvar) : )
    #endif
    #ifdef M88000
      #define ASM_get_SP_register(resultvar)  ("or %0,#r0,#r31" : "=r" (resultvar) : )
    #endif
    #ifdef RS6000
      #define ASM_get_SP_register(resultvar)  ("mr %0,1" : "=r" (resultvar) : )
    #endif
    #ifdef ARM
      #define ASM_get_SP_register(resultvar)  ("mov\t%0, sp" : "=r" (resultvar) : )
    #endif
    #ifdef CONVEX
      #define ASM_get_SP_register(resultvar)  ("mov sp,%0" : "=r" (resultvar) : )
    #endif
    #ifdef DECALPHA
      #define ASM_get_SP_register(resultvar)  ("bis $30,$30,%0" : "=r" (resultvar) : )
    #endif
    #ifdef I80386
      #define ASM_get_SP_register(resultvar)  ("movl %%esp,%0" : "=g" (resultvar) : )
    #endif
  #endif
  #if defined(GNU) && defined(MC680X0) && !defined(NO_ASM)
    # Zugriff auf eine globale Register"variable" SP
    #define SP()  \
      ({var aint __SP;                                                          \
        __asm__ __volatile__ ("movel "REGISTER_PREFIX"sp,%0" : "=g" (__SP) : ); \
        __SP;                                                                   \
       })
    #define setSP(adresse)  \
      ({ __asm__ __volatile__ ("movel %0,"REGISTER_PREFIX"sp" : : "g" ((aint)(adresse)) : "sp" ); })
    #define FAST_SP
  #elif defined(GNU) && defined(I80386) && !defined(NO_ASM)
    # Zugriff auf eine Register"variable" %esp
    #define SP()  \
      ({var aint __SP;                                           \
        __asm__ __volatile__ ("movl %%esp,%0" : "=g" (__SP) : ); \
        __SP;                                                    \
       })
    #define setSP(adresse)  \
      ({ __asm__ __volatile__ ("movl %0,%%esp" : : "g" ((aint)(adresse)) : "sp" ); })
    #define FAST_SP
  #elif defined(GNU) && defined(SP_register)
    register __volatile__ aint __SP __asm__(SP_register);
    #define SP()  __SP
    #if defined(SPARC)
      # Wir d�rfen hier kein setSP() durchf�hren, ohne zu beachten, dass
      # 1. %sp ein Alignment von 8 Byte beachten muss,
      # 2. oberhalb von %sp immer 92 Byte frei bleiben m�ssen (dorthin kommen
      #    die Registerinhalte, wenn durch ein 'save' in einem Unterprogramm
      #    ein 'register window overflow trap' ausgel�st wird).
    #endif
  #elif defined(WATCOM) && defined(I80386) && !defined(NO_ASM)
    # Zugriff auf ein Register %esp
    #define SP  getSP
    extern_C void* getSP (void);
    extern_C void setSP (void* adresse);
    #pragma aux  getSP =  0x89 0xe0 /* mov %esp,%eax */  parm value [eax] modify nomemory;
    #pragma aux  setSP =  0x89 0xc4 /* mov %eax,%esp */  parm caller [eax] modify nomemory [esp];
    #define FAST_SP
  #elif defined(MICROSOFT) && defined(I80386) && !defined(NO_ASM)
    # Zugriff auf ein Register %esp
    #define SP  getSP
    static __inline aint getSP () { __asm mov eax,esp }
    static __inline aint setSP (aint address) { __asm mov esp,address }
  #elif defined(MC680X0) || defined(SPARC) || defined(MIPS) || defined(I80386)
    # Zugriffsfunktionen extern, in Assembler
    #define SP  getSP
    extern_C void* SP (void);
    extern_C void setSP (void* adresse);
  #else
    # Zugriffsfunktion portabel in C
    extern void* SP (void);
  #endif
#if defined(stack_grows_down) # defined(MC680X0) || defined(I80386) || defined(SPARC) || defined(MIPS) || defined(M88000) || defined(DECALPHA) || ...
  #define SP_DOWN # SP w�chst nach unten
  #define SPoffset 0 # top-of-SP ist *(SP+SPoffset)
#endif
#if defined(stack_grows_up) # defined(HPPA) || ...
  #define SP_UP # SP w�chst nach oben
  #define SPoffset -1 # top-of-SP ist *(SP+SPoffset)
#endif
#if (defined(SP_DOWN) && defined(SP_UP)) || (!defined(SP_DOWN) && !defined(SP_UP))
  #error "Unknown SP direction -- SP_DOWN/SP_UP neu einstellen!"
#endif
# Darauf aufbauend:
# SPint  ist der Typ der Elemente auf dem SP, ein Integertyp mindestens so
#        breit wie uintL und mindestens so breit wie aint bzw. void*.
# SP_(n) = (n+1)tes Langwort auf dem SP.
# _SP_(n) = &SP_(n).
# pushSP(item)  legt ein Langwort auf dem SP ab. Synonym: -(SP).
# popSP(item=)  liefert item=SP_(0) und nimmt es dabei vom SP herunter.
# skipSP(n);  nimmt n Langworte vom SP herunter.
  #if (oint_addr_len <= intLsize)
    typedef uintL  SPint;
  #else
    typedef aint  SPint;
  #endif
  #ifdef SP_DOWN
    #define skipSPop  +=
    #define SPop      +
  #endif
  #ifdef SP_UP
    #define skipSPop  -=
    #define SPop      -
  #endif
  #define _SP_(n)  (((SPint*)SP()) + SPoffset SPop (uintP)(n))
  #if !(defined(GNU) && (defined(MC680X0)) && !defined(NO_ASM)) # im allgemeinen
    #define SP_(n)  (((SPint*)SP())[SPoffset SPop (uintP)(n)])
    #define skipSP(n)  \
      {var register SPint* sp = (SPint*)SP(); \
       sp skipSPop (uintP)(n);                \
       setSP(sp);                             \
      }
    #define pushSP(item)  \
      {var register SPint* sp = (SPint*)SP();                                \
       sp skipSPop -1;                                                       \
       setSP(sp);             # Erst SP herabsetzen (wegen Interruptgefahr!) \
       sp[SPoffset] = (item); # dann item als top-of-SP eintragen            \
      }
    #define popSP(item_zuweisung)  \
      {var register SPint* sp = (SPint*)SP();                                    \
       item_zuweisung sp[SPoffset]; # Erst item als top-of-SP holen              \
       sp skipSPop 1;                                                            \
       setSP(sp);                   # dann erst (Interruptgefahr!) SP hochsetzen \
      }
  #endif
  #if defined(GNU) && defined(MC680X0) && !defined(NO_ASM)
    # Mit GNU auf einem 680X0 liegt SP in einem Register. Zugriff und
    # Ver�nderung von SP bilden daher eine ununterbrechbare Einheit.
    # Und es gilt SP_DOWN und SPoffset=0.
    #define SP_(n)  \
      ({var register uintL __n = sizeof(SPint) * (n); \
        var register SPint __item;                    \
        __asm__ __volatile__ ("movel "REGISTER_PREFIX"sp@(%1:l),%0" : "=g" (__item) : "r" (__n) ); \
        __item;                                       \
       })
    #define skipSP(n)  \
      {var register uintL __n = sizeof(SPint) * (n);                               \
       __asm__ __volatile__ ("addl %0,"REGISTER_PREFIX"sp" : : "g" (__n) : "sp" ); \
      }
    #define pushSP(item)  \
      {var register SPint __item = (item);                                               \
       __asm__ __volatile__ ("movel %0,"REGISTER_PREFIX"sp@-" : : "g" (__item) : "sp" ); \
      }
    #define popSP(item_zuweisung)  \
      {var register SPint __item;                                                         \
       __asm__ __volatile__ ("movel "REGISTER_PREFIX"sp@+,%0" : "=r" (__item) : : "sp" ); \
       item_zuweisung __item;                                                             \
      }
  #endif
# Gr��e eines jmp_buf im SP:
  #define jmpbufsize  ceiling(sizeof(jmp_buf),sizeof(SPint))

# LISP-Stack: STACK
  #if !defined(STACK_register)
    # eine globale Variable
    #ifndef MULTITHREAD
      extern object* STACK;
    #else
      #define STACK  (current_thread()->_STACK)
    #endif
  #else
    # eine globale Registervariable
    register object* STACK __asm__(STACK_register);
  #endif
  #if defined(SPARC) && !defined(GNU) && !defined(__SUNPRO_C) && !defined(MULTITHREAD) && (SAFETY < 2)
    # eine globale Registervariable, aber Zugriffsfunktionen extern in Assembler
    #define STACK  _getSTACK()
    extern_C object* _getSTACK (void);
    #define setSTACK(zuweisung)  \
      { var object* tempSTACK; _setSTACK(temp##zuweisung); } # �hem, igitt!
    extern_C void _setSTACK (void* new_STACK);
  #else
    #define setSTACK(zuweisung)  zuweisung
  #endif
#if defined(AMIGAOS)
  #define STACK_DOWN # STACK w�chst nach unten
#endif
#if defined(UNIX) || defined(DJUNIX) || defined(EMUNIX) || defined(WATCOM) || defined(RISCOS) || defined(WIN32) || defined(HYPERSTONE)
  #define STACK_UP # STACK w�chst nach oben
#endif
#if (defined(STACK_DOWN) && defined(STACK_UP)) || (!defined(STACK_DOWN) && !defined(STACK_UP))
  #error "Unknown STACK direction -- STACK_DOWN/STACK_UP neu einstellen!"
#endif

# Jeder Aufruf einer externen Funktion (oder eine Folge von solchen) muss
# zwischen
#   begin_call();
# und
#   end_call();
# eingerahmt werden.
# Zweck: Damit im Falle einer Unterbrechung w�hrend des entsprechenden
# Zeitraums der STACK - falls er in einem Register liegt - auf einen halbwegs
# aktuellen Wert gebracht werden kann.
# Soll w�hrend des Ablaufs einer externen Funktion doch wieder auf den STACK
# zugegriffen werden, so ist der entsprechende Code zwischen
#   begin_callback();
# und
#   end_callback();
# einzurahmen.
#ifdef HAVE_SAVED_mv_count
  #ifndef MULTITHREAD
    extern uintC saved_mv_count;
  #else
    #define saved_mv_count  (current_thread()->_saved_mv_count)
  #endif
  #define SAVE_mv_count()     saved_mv_count = mv_count
  #define RESTORE_mv_count()  mv_count = saved_mv_count
#else
  #define SAVE_mv_count()
  #define RESTORE_mv_count()
#endif
#ifdef HAVE_SAVED_value1
  #ifndef MULTITHREAD
    extern object saved_value1;
  #else
    #define saved_value1  (current_thread()->_saved_value1)
  #endif
  #define SAVE_value1()     saved_value1 = value1
  #define RESTORE_value1()  value1 = saved_value1
#else
  #define SAVE_value1()
  #define RESTORE_value1()
#endif
#ifdef HAVE_SAVED_subr_self
  #ifndef MULTITHREAD
    extern object saved_subr_self;
  #else
    #define saved_subr_self  (current_thread()->_saved_subr_self)
  #endif
  #define SAVE_subr_self()     saved_subr_self = subr_self
  #define RESTORE_subr_self()  subr_self = saved_subr_self
#else
  #define SAVE_subr_self()
  #define RESTORE_subr_self()
#endif
#define SAVE_GLOBALS()     SAVE_mv_count(); SAVE_value1(); SAVE_subr_self();
#define RESTORE_GLOBALS()  RESTORE_mv_count(); RESTORE_value1(); RESTORE_subr_self();
#if defined(HAVE_SAVED_STACK)
  #ifndef MULTITHREAD
    extern object* saved_STACK;
  #else
    #define saved_STACK  (current_thread()->_saved_STACK)
  #endif
  #define begin_call()  SAVE_GLOBALS(); saved_STACK = STACK
  #define end_call()  RESTORE_GLOBALS(); saved_STACK = (object*)NULL
  #define begin_callback()  SAVE_REGISTERS( STACK = saved_STACK; ); end_call()
  #define end_callback()  SAVE_GLOBALS(); RESTORE_REGISTERS( saved_STACK = STACK; )
#else
  #define begin_call()  SAVE_GLOBALS()
  #define end_call()  RESTORE_GLOBALS()
  #define begin_callback()  SAVE_REGISTERS(;); end_call()
  #define end_callback()  SAVE_GLOBALS(); RESTORE_REGISTERS(;)
#endif

# Jeder Betriebsystem-Aufruf (oder eine Folge von solchen) muss zwischen
#   begin_system_call();
# und
#   end_system_call();
# eingerahmt werden.
# Zweck: Damit im Falle einer Unterbrechung w�hrend des entsprechenden
# Zeitraums der STACK - falls er in einem Register liegt - auf einen halbwegs
# aktuellen Wert gebracht werden kann.
# W�hrend eine Break-Semaphore gesetzt ist, kann man sich daher die Benutzung
# dieser Macros sparen.
#if defined(AMIGAOS) || defined(NO_ASYNC_INTERRUPTS)
  # AMIGAOS: Solange nicht ixemul.library benutzt wird, ist w�hrend
  #   Betriebssystem-Aufrufen das Programm sowieso nicht unterbrechbar.
  # NO_ASYNC_INTERRUPTS: Wenn wir auf asynchrone Interrupts nicht reagieren,
  #   ist das Programm nicht unterbrechbar.
  #define begin_system_call()
  #define end_system_call()
#else
  #define begin_system_call()  begin_call()
  #define end_system_call()  end_call()
#endif
# Dasselbe f�r setjmp()/longjmp(). Hier vermeiden wir aber, soweit m�glich,
# jeden unn�tigen Overhead.
# W�hrend eine Break-Semaphore gesetzt ist, kann man sich die Benutzung
# dieser Macros sparen.
#if 0
  # Disassembly von setjmp() und longjmp() zeigt, dass das STACK-Register
  # nicht willk�rlich benutzt wird.
  #define begin_setjmp_call()
  #define end_setjmp_call()
  #define begin_longjmp_call()
  #define end_longjmp_call()
#elif (defined(I80386) && defined(UNIX_LINUX))
  # Disassembly von setjmp() zeigt, dass das STACK-Register %ebx
  # nicht willk�rlich benutzt wird.
  #define begin_setjmp_call()
  #define end_setjmp_call()
  #define begin_longjmp_call()  begin_system_call()
  #define end_longjmp_call()  end_system_call()
#else
  #define begin_setjmp_call()  begin_system_call()
  #define end_setjmp_call()  end_system_call()
  #define begin_longjmp_call()  begin_system_call()
  #define end_longjmp_call()  end_system_call()
#endif
# Dasselbe f�r die Arithmetik-Funktionen, die STACK_register benutzen.
# Das sind auf I80386 (%ebx) die SHIFT_LOOPS, MUL_LOOPS, DIV_LOOPS.
#if defined(I80386) && !defined(NO_ARI_ASM) && (SAFETY < 3) && defined(HAVE_SAVED_STACK)
  #define begin_arith_call()  begin_system_call()
  #define end_arith_call()  end_system_call()
#else
  #define begin_arith_call()
  #define end_arith_call()
#endif

#if (defined(UNIX) && !defined(UNIX_MINT)) || defined(EMUNIX) || defined(RISCOS) || defined(WIN32) # || defined(AMIGAOS) # ?JCH??
  # Unter Unix wird der Speicherbereich f�r den SP vom Betriebssystem
  # bereitgestellt, kein malloc() n�tig.
  # Ebenso unter EMX (ausgenommen RSXW32 mit seinem Mini-60KB-Stack).
  #define NO_SP_MALLOC
#endif

#if defined(NO_SP_MALLOC) && !defined(AMIGAOS) && !defined(WIN32_NATIVE)
  # F�r den SP ist das Betriebssystem verantwortlich.
  # Woher sollen wir einen vern�nftigen Wert f�r SP_bound bekommen?
  #define NO_SP_CHECK
#elif defined(HAVE_STACK_OVERFLOW_RECOVERY)
  # Erkennung von SP-�berlauf durch eine Guard-Page.
  #define NOCOST_SP_CHECK
#endif

# Testet auf SP-�berlauf.
# check_SP();            testet auf �berlauf
# check_SP_notUNIX();    dito, au�er wenn tempor�rer �berlauf nicht ins Gewicht f�llt
  #define check_SP()  if (SP_overflow()) SP_ueber()
  #if !(defined(NO_SP_CHECK) || defined(NOCOST_SP_CHECK))
    #ifdef SP_DOWN
      #define SP_overflow()  ( (aint)SP() < (aint)SP_bound )
    #endif
    #ifdef SP_UP
      #define SP_overflow()  ( (aint)SP() > (aint)SP_bound )
    #endif
  #else # NO_SP_CHECK || NOCOST_SP_CHECK
    #define SP_overflow()  FALSE
    #ifdef NOCOST_SP_CHECK
      #ifdef SP_DOWN
        #define near_SP_overflow()  ( (aint)SP() < (aint)SP_bound+0x1000 )
      #endif
      #ifdef SP_UP
        #define near_SP_overflow()  ( (aint)SP() > (aint)SP_bound-0x1000 )
      #endif
    #endif
  #endif
  #ifndef MULTITHREAD
    extern void* SP_bound;
  #else
    #define SP_bound  (current_thread()->_SP_bound);
  #endif
  nonreturning_function(extern, SP_ueber, (void));
  #ifdef UNIX
    #define check_SP_notUNIX()
  #else
    #define check_SP_notUNIX()  check_SP()
  #endif

# Testet auf STACK-�berlauf.
# check_STACK();
  #define check_STACK()  if (STACK_overflow()) STACK_ueber()
  #ifdef STACK_DOWN
    #define STACK_overflow()  ( (aint)STACK < (aint)STACK_bound )
  #endif
  #ifdef STACK_UP
    #define STACK_overflow()  ( (aint)STACK > (aint)STACK_bound )
  #endif
  #ifndef MULTITHREAD
    extern void* STACK_bound;
  #else
    #define STACK_bound  (current_thread()->_STACK_bound)
  #endif
  nonreturning_function(extern, STACK_ueber, (void));

# Testet, ob noch n Bytes auf dem STACK frei sind.
# get_space_on_STACK(n);
  #ifdef STACK_DOWN
    #define get_space_on_STACK(n)  \
      if ( (aint)STACK < (aint)STACK_bound + (aint)(n) ) STACK_ueber()
  #else
    #define get_space_on_STACK(n)  \
      if ( (aint)STACK + (aint)(n) > (aint)STACK_bound ) STACK_ueber()
  #endif

# LISP-Interpreter verlassen
# quit();
# > final_exitcode: 0 bei normalem Ende, 1 bei Abbruch
  nonreturning_function(extern, quit, (void));
  extern boolean final_exitcode;
# wird verwendet von CONTROL

# Fehlermeldung wegen Erreichen einer unerreichbaren Programmstelle.
# Kehrt nicht zur�ck.
# fehler_notreached(file,line);
# > file: Filename (mit Anf�hrungszeichen) als konstanter ASCIZ-String
# > line: Zeilennummer
  nonreturning_function(extern, fehler_notreached, (const char * file, uintL line));
# wird von allen Modulen verwendet

# Sprache, in der mit dem Benutzer kommuniziert wird:
#ifndef LANGUAGE_STATIC
  #define language_english   0
  #define language_deutsch   1
  #define language_francais  2
  #ifndef GNU_GETTEXT
    # Sprache wird zur Laufzeit von der Variablen language bestimmt.
    extern uintL language;
    #define ENGLISH  (language==language_english)
    #define DEUTSCH  (language==language_deutsch)
    #define FRANCAIS  (language==language_francais)
  #else # GNU_GETTEXT
    #include "libintl.h"
    # Fetch the message translations from a message catalog.
    #ifndef gettext  # Sometimes `gettext' is a macro...
      extern char* gettext (const char * msgid);
    #endif
    extern const char * clgettext (const char * msgid);
    # These macros are grotesque, but they have the advantage to
    # keep the source legible and require no preprocessor work.
    # They work as long as
    # - For every international message, all 3 flavors are present
    #   and FRANCAIS is listed after ENGLISH. (Well, DEUTSCH is
    #   optional.)
    # - `clgettext' is a function, not a macro. (Well, it may be a
    #   macro without arguments, expanding to a function name.)
    #define ENGLISH  1 ? clgettext ( 1
    #define DEUTSCH  0
    #define FRANCAIS  "" ) : 0
    #
    # Fetch the message translations of a string.
    # localized_string(obj)
    # > obj: String
    # < ergebnis: String
    # kann GC ausl�sen
      extern object localized_string (object obj);
    #
    # Fetch the "translation" of a Lisp object.
    # localized_object(obj)
    # > obj: String
    # kann GC ausl�sen
      extern object localized_object (object obj);
  #endif
#endif
# wird von allen Modulen verwendet

# Ausgabe eines konstanten ASCIZ-Strings, direkt �bers Betriebssystem:
# asciz_out(string);
  extern void asciz_out (const char * asciz);
# Ditto mit bis zu zwei eingebetteten %s-Argumenten:
  extern void asciz_out_s (const char * asciz, const char * arg1);
  extern void asciz_out_ss (const char * asciz, const char * arg1, const char * arg2);
# Ditto mit bis zu drei eingebetteten %d/%x-Argumenten:
  #define asciz_out_1(asciz,arg1)  asciz_out_1_((asciz),(unsigned long)(arg1))
  #define asciz_out_2(asciz,arg1,arg2)  asciz_out_2_((asciz),(unsigned long)(arg1),(unsigned long)(arg2))
  #define asciz_out_3(asciz,arg1,arg2,arg3)  asciz_out_3_((asciz),(unsigned long)(arg1),(unsigned long)(arg2),(unsigned long)(arg3))
  extern void asciz_out_1_ (const char * asciz, unsigned long arg1);
  extern void asciz_out_2_ (const char * asciz, unsigned long arg1, unsigned long arg2);
  extern void asciz_out_3_ (const char * asciz, unsigned long arg1, unsigned long arg2, unsigned long arg3);
# wird verwendet von SPVW

# uintL in Dezimalnotation direkt �bers Betriebssystem ausgeben:
# dez_out(zahl);
  #define dez_out(x)  dez_out_((uintL)(x))
  extern void dez_out_ (uintL zahl);
# wird zum Debuggen verwendet

# unsigned long in Hexadezimalnotation direkt �bers Betriebssystem ausgeben:
# hex_out(zahl);
  #define hex_out(x)  hex_out_((unsigned long)(x))
  extern void hex_out_ (unsigned long zahl);
# wird zum Debuggen verwendet

# Speicherbereich in Hexadezimalnotation direkt �bers Betriebssystem ausgeben:
# mem_hex_out(buf,count);
  extern void mem_hex_out (const void* buf, uintL count);
# wird zum Debuggen verwendet

# Lisp-Objekt in Lisp-Notation relativ direkt �bers Betriebssystem ausgeben:
# object_out(obj);
# kann GC ausl�sen
  extern void object_out (object obj);
# wird zum Debuggen verwendet

# UP, f�hrt eine Garbage Collection aus
# gar_col();
# kann GC ausl�sen
  extern void gar_col(void);
# wird verwendet von DEBUG

# GC-Statistik
  extern uintL gc_count;
  extern uintL2 gc_space;
  extern internal_time gc_time;
# wird verwendet von TIME

# UP, beschafft ein Cons
# allocate_cons()
# < ergebnis: Pointer auf neues CONS, mit CAR und CDR =NIL
# kann GC ausl�sen
  extern object allocate_cons (void);
# wird verwendet von LIST, SEQUENCE, PACKAGE, EVAL, CONTROL, RECORD,
#                    PREDTYPE, IO, STREAM, PATHNAME, SYMBOL, ARRAY, LISPARIT

# UP: Liefert ein neu erzeugtes uninterniertes Symbol mit gegebenem Printnamen.
# make_symbol(string)
# > string: Simple-String
# < ergebnis: neues Symbol mit diesem Namen, mit Home-Package=NIL.
# kann GC ausl�sen
  extern object make_symbol (object string);
# wird verwendet von PACKAGE, IO, SYMBOL

# UP, beschafft Vektor
# allocate_vector(len)
# > len: L�nge des Vektors
# < ergebnis: neuer Vektor (Elemente werden mit NIL initialisiert)
# kann GC ausl�sen
  extern object allocate_vector (uintL len);
# wird verwendet von ARRAY, IO, EVAL, PACKAGE, CONTROL, HASHTABL

# UP, beschafft Bit-Vektor
# allocate_bit_vector(len)
# > len: L�nge des Bitvektors (in Bits)
# < ergebnis: neuer Bitvektor (LISP-Objekt)
# kann GC ausl�sen
  extern object allocate_bit_vector (uintL len);
# wird verwendet von ARRAY, IO, RECORD, LISPARIT, STREAM

# UP, beschafft String
# allocate_string(len)
# > len: L�nge des Strings (in Bytes)
# < ergebnis: neuer Simple-String (LISP-Objekt)
# kann GC ausl�sen
  extern object allocate_string (uintL len);
# wird verwendet von ARRAY, CHARSTRG, STREAM, PATHNAME

# UP, beschafft indirekten Array
# allocate_iarray(flags,rank,type)
# > uintB flags: Flags
# > uintC (eigentlich uintWC) rank: Rang
# > tint type: Typinfo
# < ergebnis: LISP-Objekt Array
# kann GC ausl�sen
  extern object allocate_iarray (uintB flags, uintC rank, tint type);
# wird verwendet von ARRAY, IO

# UP, beschafft Simple-Record
# allocate_srecord(flags,rectype,reclen,type)
# > uintB flags: Flags
# > sintB rectype: n�here Typinfo
# > uintC (eigentlich uintW) reclen: L�nge
# > tint type: Typinfo
# < ergebnis: LISP-Objekt Record (Elemente werden mit NIL initialisiert)
# kann GC ausl�sen
  #ifdef TYPECODES
    #define allocate_srecord(flags,rectype,reclen,type)  \
      allocate_srecord_(                                                    \
         (BIG_ENDIAN_P ? ((uintW)(flags)<<intBsize)+(uintW)(uintB)(rectype) \
                       : (uintW)(flags)+((uintW)(uintB)(rectype)<<intBsize) \
         ),                                                                 \
         reclen,                                                            \
         type)
    extern object allocate_srecord_ (uintW flags_rectype, uintC reclen, tint type);
  #else
    #define allocate_srecord(flags,rectype,reclen,type)  /* ignore type */ \
      allocate_srecord_(((uintW)(flags)<<8)+(uintW)(uintB)(rectype),reclen)
    extern object allocate_srecord_ (uintW flags_rectype, uintC reclen);
  #endif
# wird verwendet von RECORD, EVAL

# UP, beschafft Extended-Record
# allocate_xrecord(flags,rectype,reclen,recxlen,type)
# > uintB flags: Flags
# > sintB rectype: n�here Typinfo
# > uintC (eigentlich uintB) reclen: L�nge
# > uintC (eigentlich uintB) recxlen: Extra-L�nge
# > tint type: Typinfo
# < ergebnis: LISP-Objekt Record (Elemente werden mit NIL bzw. 0 initialisiert)
# kann GC ausl�sen
  #ifdef TYPECODES
    #define allocate_xrecord(flags,rectype,reclen,recxlen,type)  \
      allocate_xrecord_(                                                    \
         (BIG_ENDIAN_P ? ((uintW)(flags)<<intBsize)+(uintW)(uintB)(rectype) \
                       : (uintW)(flags)+((uintW)(uintB)(rectype)<<intBsize) \
         ),                                                                 \
         reclen,                                                            \
         recxlen,                                                           \
         type)
    extern object allocate_xrecord_ (uintW flags_rectype, uintC reclen, uintC recxlen, tint type);
  #else
    #define allocate_xrecord(flags,rectype,reclen,recxlen,type)  \
      allocate_xrecord_((((uintW)(flags)<<8)+(uintW)(uintB)(rectype)),reclen,recxlen)
    extern object allocate_xrecord_ (uintW flags_rectype, uintC reclen, uintC recxlen);
  #endif
# wird verwendet von

# UP, beschafft Closure
# allocate_closure(reclen)
# > uintC reclen: L�nge
# < ergebnis: LISP-Objekt Closure (Elemente werden mit NIL initialisiert)
  #define allocate_closure(reclen)  \
    allocate_srecord(0,Rectype_Closure,reclen,closure_type)
# wird verwendet von EVAL, RECORD

# Copying a compiled closure:
# newclos = allocate_cclosure_copy(oldclos);
# kann GC ausl�sen
  #define allocate_cclosure_copy(oldclos)  \
    allocate_closure(Cclosure_length(oldclos))
# do_cclosure_copy(newclos,oldclos);
  #define do_cclosure_copy(newclos,oldclos)  \
    { var object* newptr = &((Srecord)TheCclosure(newclos))->recdata[0]; \
      var object* oldptr = &((Srecord)TheCclosure(oldclos))->recdata[0]; \
      var uintC count;                                                   \
      dotimespC(count,Cclosure_length(oldclos),                          \
        { *newptr++ = *oldptr++; }                                       \
        );                                                               \
    }
# wird verwendet von EVAL, IO, RECORD

# UP, beschafft Structure
# allocate_structure(reclen)
# > uintC reclen: L�nge
# < ergebnis: LISP-Objekt Structure (Elemente werden mit NIL initialisiert)
# kann GC ausl�sen
  #ifdef case_structure
    #define allocate_structure(reclen)  \
      allocate_srecord(0,Rectype_Structure,reclen,structure_type)
  #else
    #define allocate_structure(reclen)  \
      allocate_srecord(0,Rectype_Structure,reclen,orecord_type)
  #endif
# wird verwendet von RECORD

# UP, beschafft Stream
# allocate_stream(strmflags,strmtype,reclen,recxlen)
# > uintB strmflags: Flags
# > uintB strmtype: n�here Typinfo
# > uintC reclen: L�nge in Objekten
# > uintC recxlen: Extra-L�nge in Bytes
# < ergebnis: LISP-Objekt Stream (Elemente werden mit NIL initialisiert)
# kann GC ausl�sen
  #ifdef case_stream
    #define allocate_stream(strmflags,strmtype,reclen,recxlen)  \
      allocate_xrecord(strmflags,strmtype,reclen,recxlen,stream_type)
  #else
    extern object allocate_stream (uintB strmflags, uintB strmtype, uintC reclen, uintC recxlen);
  #endif
# wird verwendet von STREAM

# UP, beschafft Package
# allocate_package()
# < ergebnis: LISP-Objekt Package
# kann GC ausl�sen
  #define allocate_package()  \
    allocate_xrecord(0,Rectype_Package,package_length,0,orecord_type)
# wird verwendet von PACKAGE

# UP, beschafft Hash-Table
# allocate_hash_table()
# < ergebnis: LISP-Objekt Hash-Table
# kann GC ausl�sen
  #define allocate_hash_table()  \
    allocate_xrecord(0,Rectype_Hashtable,hashtable_length,0,orecord_type)
# wird verwendet von

# UP, beschafft Readtable
# allocate_readtable()
# < ergebnis: LISP-Objekt Readtable
# kann GC ausl�sen
  #define allocate_readtable()  \
    allocate_xrecord(0,Rectype_Readtable,readtable_length,0,orecord_type)
# wird verwendet von IO

# UP, beschafft Pathname
# allocate_pathname()
# < ergebnis: LISP-Objekt Pathname
# kann GC ausl�sen
  #define allocate_pathname()  \
    allocate_xrecord(0,Rectype_Pathname,pathname_length,0,orecord_type)
# wird verwendet von PATHNAME

#ifdef LOGICAL_PATHNAMES
# UP, beschafft Logical Pathname
# allocate_logpathname()
# < ergebnis: LISP-Objekt Logical Pathname
# kann GC ausl�sen
  #define allocate_logpathname()  \
    allocate_xrecord(0,Rectype_Logpathname,logpathname_length,0,orecord_type)
# wird verwendet von PATHNAME
#endif

# UP, beschafft Random-State
# allocate_random_state()
# < ergebnis: LISP-Objekt Random-State
# kann GC ausl�sen
  #define allocate_random_state()  \
    allocate_xrecord(0,Rectype_Random_State,random_state_length,0,orecord_type)
# wird verwendet von IO, LISPARIT

# UP, beschafft Byte
# allocate_byte()
# < ergebnis: LISP-Objekt Byte
# kann GC ausl�sen
  #define allocate_byte()  \
    allocate_xrecord(0,Rectype_Byte,byte_length,0,orecord_type)
# wird verwendet von LISPARIT

# UP, beschafft Fsubr
# allocate_fsubr()
# < ergebnis: LISP-Objekt Fsubr
# kann GC ausl�sen
  #define allocate_fsubr()  \
    allocate_xrecord(0,Rectype_Fsubr,fsubr_length,fsubr_xlength,orecord_type)
# wird verwendet von SPVW

# UP, beschafft Load-time-Eval
# allocate_loadtimeeval()
# < ergebnis: LISP-Objekt Load-time-Eval
# kann GC ausl�sen
  #define allocate_loadtimeeval()  \
    allocate_xrecord(0,Rectype_Loadtimeeval,loadtimeeval_length,0,orecord_type)
# wird verwendet von IO, RECORD

# UP, beschafft Symbol-Macro
# allocate_symbolmacro()
# < ergebnis: LISP-Objekt Symbol-Macro
# kann GC ausl�sen
  #define allocate_symbolmacro()  \
    allocate_xrecord(0,Rectype_Symbolmacro,symbolmacro_length,0,orecord_type)
# wird verwendet von CONTROL, RECORD

#ifdef FOREIGN
# UP, beschafft Foreign-Pointer-Verpackung
# allocate_fpointer(foreign)
# > foreign: vom Typ FOREIGN
# < ergebnis: LISP-Objekt, das foreign enth�lt
# kann GC ausl�sen
  extern object allocate_fpointer (FOREIGN foreign);
# wird verwendet von REXX
#endif

# UP, beschafft Foreign-Addresse
# allocate_faddress()
# < ergebnis: LISP-Objekt Foreign-Addresse
# kann GC ausl�sen
  #define allocate_faddress()  \
    allocate_xrecord(0,Rectype_Faddress,faddress_length,faddress_xlength,orecord_type)
# wird verwendet von FOREIGN

# UP, beschafft Foreign-Variable
# allocate_fvariable()
# < ergebnis: LISP-Objekt Foreign-Variable
# kann GC ausl�sen
  #define allocate_fvariable()  \
    allocate_xrecord(0,Rectype_Fvariable,fvariable_length,0,orecord_type)
# wird verwendet von FOREIGN

# UP, beschafft Foreign-Funktion
# allocate_ffunction()
# < ergebnis: LISP-Objekt Foreign-Funktion
# kann GC ausl�sen
  #define allocate_ffunction()  \
    allocate_xrecord(0,Rectype_Ffunction,ffunction_length,0,orecord_type)
# wird verwendet von FOREIGN

# UP, allocates a Weakpointer
# allocate_weakpointer()
# < result: a fresh weak-pointer
# kann GC ausl�sen
  #define allocate_weakpointer()  \
    allocate_xrecord(0,Rectype_Weakpointer,weakpointer_length,weakpointer_xlength,orecord_type)
# wird verwendet von RECORD

# UP, beschafft Finalisierer
# allocate_finalizer()
# < ergebnis: LISP-Objekt Finalisierer
# kann GC ausl�sen
  #define allocate_finalizer()  \
    allocate_xrecord(0,Rectype_Finalizer,finalizer_length,0,orecord_type)
# wird verwendet von RECORD

# UP, beschafft Socket-Server
# allocate_socket_server()
# < ergebnis: LISP-Objekt Socket-Server
#ifdef SOCKET_STREAMS
  #define allocate_socket_server() \
    allocate_xrecord(0,Rectype_Socket_Server,socket_server_length,0,orecord_type)
#endif

#ifdef YET_ANOTHER_RECORD
# UP, beschafft Yetanother
# allocate_yetanother()
# < ergebnis: LISP-Objekt Yetanother
# kann GC ausl�sen
  #define allocate_yetanother()  \
    allocate_xrecord(0,Rectype_Yetanother,yetanother_length,0,orecord_type)
# wird verwendet von
#endif

# UP, beschafft Handle-Verpackung
# allocate_handle(handle)
# < ergebnis: LISP-Objekt, das handle enth�lt
# kann GC ausl�sen
  #ifdef FOREIGN_HANDLE
    # kann GC ausl�sen
    extern object allocate_handle (Handle handle);
  #else
    #define allocate_handle(handle)  fixnum((uintL)(handle))
  #endif

# UP, beschafft Bignum
# allocate_bignum(len,sign)
# > uintC (eigentlich uintWC) len: L�nge der Zahl (in Digits)
# > sintB sign: Flag f�r Vorzeichen (0 = +, -1 = -)
# < ergebnis: neues Bignum (LISP-Objekt)
# kann GC ausl�sen
  extern object allocate_bignum (uintC len, sintB sign);
# wird verwendet von LISPARIT, STREAM

# UP, beschafft Single-Float
# allocate_ffloat(value)
# > ffloat value: Zahlwert (Bit 31 = Vorzeichen)
# < ergebnis: neues Single-Float (LISP-Objekt)
# kann GC ausl�sen
  extern object allocate_ffloat (ffloat value);
# wird verwendet von LISPARIT

# UP, beschafft Double-Float
#ifdef intQsize
# allocate_dfloat(value)
# > dfloat value: Zahlwert (Bit 63 = Vorzeichen)
# < ergebnis: neues Double-Float (LISP-Objekt)
# kann GC ausl�sen
  extern object allocate_dfloat (dfloat value);
#else
# allocate_dfloat(semhi,mlo)
# > semhi,mlo: Zahlwert (Bit 31 von semhi = Vorzeichen)
# < ergebnis: neues Double-Float (LISP-Objekt)
# kann GC ausl�sen
  extern object allocate_dfloat (uint32 semhi, uint32 mlo);
#endif
# wird verwendet von LISPARIT

# UP, beschafft Long-Float
# allocate_lfloat(len,expo,sign)
# > uintC (eigentlich uintWC) len: L�nge der Mantisse (in Digits)
# > uintL expo: Exponent
# > signean sign: Vorzeichen (0 = +, -1 = -)
# < ergebnis: neues Long-Float, noch ohne Mantisse
# Ein LISP-Objekt liegt erst dann vor, wenn die Mantisse eingetragen ist!
# kann GC ausl�sen
  extern object allocate_lfloat (uintC len, uintL expo, signean sign);
# wird verwendet von LISPARIT

# UP, erzeugt Bruch
# make_ratio(num,den)
# > object num: Z�hler (muss Integer /= 0 sein, relativ prim zu den)
# > object den: Nenner (muss Integer > 1 sein)
# < ergebnis: Bruch
# kann GC ausl�sen
  extern object make_ratio (object num, object den);
# wird verwendet von LISPARIT

# UP, erzeugt komplexe Zahl
# make_complex(real,imag)
# > real: Realteil (muss reelle Zahl sein)
# > imag: Imagin�rteil (muss reelle Zahl /= Fixnum 0 sein)
# < ergebnis: komplexe Zahl
# kann GC ausl�sen
  extern object make_complex (object real, object imag);
# wird verwendet von LISPARIT

# UP: Liefert einen LISP-String mit vorgegebenem Inhalt.
# make_string(charptr,len)
# > uintB* charptr: Adresse einer Zeichenfolge
# > uintL len: L�nge der Zeichenfolge
# < ergebnis: Simple-String mit den len Zeichen ab charptr als Inhalt
# kann GC ausl�sen
  extern object make_string (const uintB* charptr, uintL len);
# wird verwendet von PATHNAME, LISPARIT

# UP: Liefert die L�nge eines ASCIZ-Strings.
# asciz_length(asciz)
# > char* asciz: ASCIZ-String
#       (Adresse einer durch ein Nullbyte abgeschlossenen Zeichenfolge)
# < ergebnis: L�nge der Zeichenfolge (ohne Nullbyte)
  extern uintL asciz_length (const char * asciz);
# wird verwendet von SPVW

# UP: Vergleicht zwei ASCIZ-Strings.
# asciz_equal(asciz1,asciz2)
# > char* asciz1: erster ASCIZ-String
# > char* asciz2: zweiter ASCIZ-String
# < ergebnis: TRUE falls die Zeichenfolgen gleich sind
  extern boolean asciz_equal (const char * asciz1, const char * asciz2);
# wird verwendet von STREAM

#if defined(GNU) && (SAFETY < 2)
  #ifdef HAVE_BUILTIN_STRLEN
    #define asciz_length(a)  ((uintL)__builtin_strlen(a))
  #endif
  #ifdef HAVE_BUILTIN_STRCMP
    #define asciz_equal(a1,a2)  (__builtin_strcmp(a1,a2)==0)
  #endif
#endif
#ifndef asciz_length
  #ifdef HAVE_SAVED_STACK
    # Kann nicht strlen() statt asciz_length() benutzen, denn das w�rde
    # ein begin_system_call()/end_system_call() erfordern.
  #else
    # Gehen wir davon aus, dass strlen() effizient implementiert ist.
    #ifdef STDC_HEADERS
      #include <string.h> # deklariert strlen()
    #endif
    #ifdef RETSTRLENTYPE # wenn strlen() kein Macro ist
      extern_C RETSTRLENTYPE strlen (STRLEN_CONST char* s);
    #endif
    #define asciz_length(a)  ((uintL)strlen(a))
  #endif
#endif
#ifndef asciz_equal
  #if 1
    # strcmp() ist vermutlich Overkill f�r asciz_equal().
  #else
    # Gehen wir davon aus, dass strcmp() es auch tut.
    #ifdef STDC_HEADERS
      #include <string.h> # deklariert strcmp()
    #else
      extern_C int strcmp (char* s1, char* s2);
    #endif
    #define asciz_equal(p1,p2)  (strcmp(p1,p2)==0)
  #endif
#endif

# UP: Wandelt einen ASCIZ-String in einen LISP-String um.
# asciz_to_string(asciz)
# > char* asciz: ASCIZ-String
#       (Adresse einer durch ein Nullbyte abgeschlossenen Zeichenfolge)
# < ergebnis: String mit der Zeichenfolge (ohne Nullbyte) als Inhalt
# kann GC ausl�sen
  extern object asciz_to_string (const char * asciz);
# wird verwendet von SPVW/CONSTSYM, STREAM, PATHNAME, PACKAGE, GRAPH

# UP: Wandelt einen String in einen ASCIZ-String um.
# string_to_asciz(obj,encoding)
# > object obj: String
# > object encoding: Encoding
# < ergebnis: Simple-Bit-Vektor mit denselben Zeichen als Bytes und einem
#             Nullbyte mehr am Schluss
# < TheAsciz(ergebnis): Adresse der darin enthaltenen Bytefolge
# kann GC ausl�sen
  extern object string_to_asciz (object obj);
  #define TheAsciz(obj)  ((char*)(&TheSbvector(obj)->data[0]))
# wird verwendet von STREAM, PATHNAME

# Wandelt einen String in einen ASCIZ-String im C-Stack um.
# with_string_0(string,asciz,statement);
# with_sstring_0(simple_string,asciz,statement);
# copies the contents of string (which should be a Lisp string) to a safe area
# (zero-terminating it), binds the variable asciz pointing to it, and
# executes the statement.
#if 0
  #define with_string_0(string,ascizvar,statement)  \
    { var char* ascizvar = TheAsciz(string_to_asciz(string)); \
      statement                                               \
    }
  #define with_sstring_0  with_string_0
#else
  #define with_string_0(string,ascizvar,statement)  \
    { var uintL ascizvar##_len;                                          \
      var const chart* ptr1 = unpack_string(string,&ascizvar##_len);     \
     {var DYNAMIC_ARRAY(ascizvar##_data,uintB,ascizvar##_len+1);         \
      {var uintB* ptr2 = &ascizvar##_data[0];                            \
       var uintL count;                                                  \
       dotimesL(count,ascizvar##_len, { *ptr2++ = as_cint(*ptr1++); } ); \
       *ptr2 = '\0';                                                     \
      }                                                                  \
      {var char* ascizvar = (char*) &ascizvar##_data[0];                 \
       statement                                                         \
      }                                                                  \
      FREE_DYNAMIC_ARRAY(ascizvar##_data);                               \
    }}
  #define with_sstring_0(string,ascizvar,statement)  \
    { var object ascizvar##_string = (string);                           \
      var uintL ascizvar##_len = Sstring_length(ascizvar##_string);      \
      var const chart* ptr1 = &TheSstring(ascizvar##_string)->data[0];   \
     {var DYNAMIC_ARRAY(ascizvar##_data,uintB,ascizvar##_len+1);         \
      {var uintB* ptr2 = &ascizvar##_data[0];                            \
       var uintL count;                                                  \
       dotimesL(count,ascizvar##_len, { *ptr2++ = as_cint(*ptr1++); } ); \
       *ptr2 = '\0';                                                     \
      }                                                                  \
      {var char* ascizvar = (char*) &ascizvar##_data[0];                 \
       statement                                                         \
      }                                                                  \
      FREE_DYNAMIC_ARRAY(ascizvar##_data);                               \
    }}
#endif
# wird verwendet von PATHNAME, MISC, FOREIGN

# In some foreign modules, we call library functions that can do callbacks.
# When we pass a parameter to such a library function, maybe it first does a
# callback - which may involve garbage collection - and only then looks at
# the parameter. Therefore all the parameters, especially strings, must be
# located in areas that are not moved by garbage collection. The following
# macro helps achieving this.

# Wandelt einen String in einen String im C-Stack um.
# with_string(string,charptr,len,statement);
# with_sstring(simple_string,charptr,len,statement);
# copies the contents of string (which should be a Lisp string) to a safe area,
# binds the variable charptr pointing to it and the variable len to its length,
# and executes the statement.
  #define with_string(string,charptrvar,lenvar,statement)  \
    { var uintL lenvar;                                          \
      var const chart* ptr1 = unpack_string(string,&lenvar);     \
     {var DYNAMIC_ARRAY(charptrvar##_data,uintB,lenvar);         \
      {var uintB* ptr2 = &charptrvar##_data[0];                  \
       var uintL count;                                          \
       dotimesL(count,lenvar, { *ptr2++ = as_cint(*ptr1++); } ); \
      }                                                          \
      {var char* charptrvar = (char*) &charptrvar##_data[0];     \
       statement                                                 \
      }                                                          \
      FREE_DYNAMIC_ARRAY(charptrvar##_data);                     \
    }}
  #define with_sstring(string,charptrvar,lenvar,statement)  \
    { var object charptrvar##_string = (string);                         \
      var uintL charptrvar##_len = Sstring_length(charptrvar##_string);  \
      var const chart* ptr1 = &TheSstring(charptrvar##_string)->data[0]; \
     {var DYNAMIC_ARRAY(charptrvar##_data,uintB,lenvar);                 \
      {var uintB* ptr2 = &charptrvar##_data[0];                          \
       var uintL count;                                                  \
       dotimesL(count,lenvar, { *ptr2++ = as_cint(*ptr1++); } );         \
      }                                                                  \
      {var char* charptrvar = (char*) &charptrvar##_data[0];             \
       statement                                                         \
      }                                                                  \
      FREE_DYNAMIC_ARRAY(charptrvar##_data);                             \
    }}
# wird verwendet von PATHNAME

# UP: Liefert eine Tabelle aller Zirkularit�ten innerhalb eines Objekts.
# (Eine Zirkularit�t ist ein in diesem Objekt enthaltenes Teil-Objekt,
# auf den es mehr als einen Zugriffsweg gibt.)
# get_circularities(obj,pr_array,pr_closure)
# > object obj: Objekt
# > boolean pr_array: Flag, ob Arrayelemente rekursiv als Teilobjekte gelten
# > boolean pr_closure: Flag, ob Closurekomponenten rekursiv als Teilobjekte gelten
# < ergebnis: T falls Stack�berlauf eintrat,
#             NIL falls keine Zirkularit�ten vorhanden,
#             #(0 ...) ein (n+1)-elementiger Vektor, der die Zahl 0 und die n
#                      Zirkularit�ten als Elemente enth�lt, n>0.
# kann GC ausl�sen
  extern object get_circularities (object obj, boolean pr_array, boolean pr_closure);
# wird verwendet von IO

# UP: Entflicht #n# - Referenzen im Objekt *ptr mit Hilfe der Aliste alist.
# > *ptr : Objekt
# > alist : Aliste (Read-Label --> zu substituierendes Objekt)
# < *ptr : Objekt mit entflochtenen Referenzen
# < ergebnis : fehlerhafte Referenz oder nullobj falls alles OK
  extern object subst_circ (object* ptr, object alist);
# wird verwendet von IO

# UP: L�uft durch den gesamten Speicher durch, und ruft dabei f�r jedes
# Objekt obj: fun(arg,obj,bytelen) auf.
# map_heap_objects(fun,arg);
# > fun: C-Funktion
# > arg: beliebiges vorgegebenes Argument
  typedef void map_heap_function (void* arg, object obj, uintL bytelen);
  extern void map_heap_objects (map_heap_function* fun, void* arg);
# wird verwendet von PREDTYPE

# UP: Liefert die Gr��e eines Objekts in Bytes.
# varobject_bytelength(obj)
# > obj: Heap-Objekt variabler L�nge
# < ergebnis; die Anzahl der von ihm belegten Bytes (inklusive Header)
  extern uintL varobject_bytelength (object obj);
# wird verwendet von PREDTYPE

# Break-Semaphoren
# Solange eine Break-Semaphore gesetzt ist, kann das Lisp-Programm nicht
# unterbrochen werden. Zweck:
# - Sicherstellung von Konsistenzen,
# - Nicht reentrante Datenstrukturen (wie z.B. DTA_buffer) k�nnen nicht
#   rekursiv verwendet werden.
  typedef union {uintB einzeln[8]; uintL gesamt[2]; } break_sems_;
  extern break_sems_ break_sems;
  #define break_sem_0  break_sems.einzeln[0]
  #define break_sem_1  break_sems.einzeln[1]
  #define break_sem_2  break_sems.einzeln[2]
  #define break_sem_3  break_sems.einzeln[3]
  #define break_sem_4  break_sems.einzeln[4]
  #define break_sem_5  break_sems.einzeln[5]
  #define break_sem_6  break_sems.einzeln[6]
  #define break_sem_7  break_sems.einzeln[7]
# wird verwendet von SPVW, Macros set/clr_break_sem_0/1/2/3/4/5/6/7

# Testet, ob alle Break-Semaphoren gel�scht sind.
  #define break_sems_cleared()  \
    (break_sems.gesamt[0] == 0 && break_sems.gesamt[1] == 0)
# wird verwendet von SPVW, WIN32AUX

# L�scht alle Break-Semaphoren. Sehr gef�hrlich!
  #define clear_break_sems()  \
    (break_sems.gesamt[0] = 0, break_sems.gesamt[1] = 0)
# wird verwendet von SPVW

# Setzt Break-Semaphore 0 und sch�tzt so gegen Unterbrechungen
# set_break_sem_0();
  #define set_break_sem_0()  (break_sem_0 = 1)
# wird verwendet von SPVW

# L�scht Break-Semaphore 0 und gibt so Unterbrechungen wieder frei
# clr_break_sem_0();
  #define clr_break_sem_0()  (break_sem_0 = 0)
# wird verwendet von SPVW

# Setzt Break-Semaphore 1 und sch�tzt so gegen Unterbrechungen
# set_break_sem_1();
  #define set_break_sem_1()  (break_sem_1 = 1)
# wird verwendet von SPVW, ARRAY

# L�scht Break-Semaphore 1 und gibt so Unterbrechungen wieder frei
# clr_break_sem_1();
  #define clr_break_sem_1()  (break_sem_1 = 0)
# wird verwendet von SPVW, ARRAY

# Setzt Break-Semaphore 2 und sch�tzt so gegen Unterbrechungen
# set_break_sem_2();
  #define set_break_sem_2()  (break_sem_2 = 1)
# wird verwendet von PACKAGE, HASHTABL

# L�scht Break-Semaphore 2 und gibt so Unterbrechungen wieder frei
# clr_break_sem_2();
  #define clr_break_sem_2()  (break_sem_2 = 0)
# wird verwendet von PACKAGE, HASHTABL

# Setzt Break-Semaphore 3 und sch�tzt so gegen Unterbrechungen
# set_break_sem_3();
  #define set_break_sem_3()  (break_sem_3 = 1)
# wird verwendet von PACKAGE

# L�scht Break-Semaphore 3 und gibt so Unterbrechungen wieder frei
# clr_break_sem_3();
  #define clr_break_sem_3()  (break_sem_3 = 0)
# wird verwendet von PACKAGE

# Setzt Break-Semaphore 4 und sch�tzt so gegen Unterbrechungen
# set_break_sem_4();
  #define set_break_sem_4()  (break_sem_4 = 1)
# wird verwendet von STREAM, PATHNAME

# L�scht Break-Semaphore 4 und gibt so Unterbrechungen wieder frei
# clr_break_sem_4();
  #define clr_break_sem_4()  (break_sem_4 = 0)
# wird verwendet von STREAM, PATHNAME

# Incrementiert Break-Semaphore 5 und sch�tzt so gegen Unterbrechungen
# inc_break_sem_5();
  #define inc_break_sem_5()  (break_sem_5++)
# wird verwendet von SPVW

# Decrementiert Break-Semaphore 5 und gibt so Unterbrechungen wieder frei
# dec_break_sem_5();
  #define dec_break_sem_5()  (break_sem_5--)
# wird verwendet von SPVW

# L�scht Break-Semaphore 5 und gibt so Unterbrechungen wieder frei
# clr_break_sem_5();
  #define clr_break_sem_5()  (break_sem_5 = 0)
# wird verwendet von SPVW

# Flag, ob SYS::READ-FORM sich ILISP-kompatibel verhalten soll:
  extern boolean ilisp_mode;

# Liefert die Gr��e des von statischen LISP-Objekten belegten Platzes.
  extern uintL static_space (void);
# wird verwendet von DEBUG

# Liefert die Gr��e des von den LISP-Objekten belegten Platzes.
  extern uintL used_space (void);
# wird verwendet von TIME, DEBUG

# Liefert die Gr��e des f�r LISP-Objekte noch verf�gbaren Platzes.
  extern uintL free_space (void);
# wird verwendet von DEBUG

# UP, speichert Speicherabbild auf Diskette
# savemem(stream);
# > object stream: offener File-Output-Stream, wird geschlossen
# kann GC ausl�sen
  extern void savemem (object stream);
# wird verwendet von PATHNAME

# UP: Ruft ein Fremdprogramm auf.
# execute(memneed)
# > -(STACK): Filename des Fremdprogramms, ein Simple-ASCIZ-String
# > -(STACK): Argumente (Command Tail), ein Simple-String
# > uintL memneed: F�rs Fremdprogramm zu reservierende Byte-Zahl (gerade)
# < sintL ergebnis : Falls negativ, Fehlernummer.
#                    Sonst Returncode des aufgerufenen Programms.
# STACK wird aufger�umt
# kann GC ausl�sen
  extern sintL execute (uintL memneed);
# wird verwendet von PATHNAME

#ifdef HAVE_SIGNALS
# Temporarily do not ignore the status of subprocesses.
  extern void begin_want_sigcld (void);
  extern void end_want_sigcld (void);
# wird verwendet von PATHNAME
#endif


# Deklaration der FSUBRs.
# Als C-Funktionen: C_name, vom Typ fsubr_function (keine Argumente, kein Wert)

# C-Funktionen sichtbar machen:
  #define LISPSPECFORM  LISPSPECFORM_A
  #include "fsubr.c"
  #undef LISPSPECFORM
# wird verwendet von

# Fsubr-Tabelle sichtbar machen:
  #define LISPSPECFORM  LISPSPECFORM_C
  struct fsubr_tab_ {
                      #include "fsubr.c"
                    };
  #undef LISPSPECFORM
  extern const struct fsubr_tab_ fsubr_tab;
# wird verwendet von CONTROL, SPVW


# Deklaration der SUBR-Tabelle.
# Als C-Funktionen: C_name
# vom Typ subr_norest_function (keine Argumente, kein Wert)
# bzw. subr_rest_function (zwei Argumente, kein Wert):
  typedef Values subr_norest_function (void);
  typedef Values subr_rest_function (uintC argcount, object* rest_args_pointer);

# Als LISP-Subr:    L(name)

# C-Funktionen sichtbar machen:
  #define LISPFUN  LISPFUN_A
  #include "subr.c"
  #undef LISPFUN
# wird verwendet von

# Subr-Tabelle sichtbar machen:
  #define LISPFUN  LISPFUN_C
  extern struct subr_tab_ {
                            #include "subr.c"
                          }
         subr_tab_data;
  #undef LISPFUN
# wird verwendet von Macro L

# Abk�rzung f�rs LISP-Subr mit einem gegebenen Namen: L(name)
  #if !defined(MAP_MEMORY_TABLES)
    #define subr_tab  subr_tab_data
    #ifdef TYPECODES
      #define subr_tab_ptr_as_object(subr_addr)  (type_constpointer_object(subr_type,subr_addr))
    #else
      #define subr_tab_ptr_as_object(subr_addr)  as_object((oint)(subr_addr)+subr_bias)
    #endif
    #define L(name)  subr_tab_ptr_as_object(&subr_tab.D_##name)
  #else
    # define subr_tab_addr  ((struct subr_tab_ *)type_constpointer_object(subr_type,0))
    #define subr_tab_addr  ((struct subr_tab_ *)type_zero_oint(subr_type))
    #define subr_tab  (*subr_tab_addr)
    #define subr_tab_ptr_as_object(subr_addr)  (as_object((oint)(subr_addr)))
    #define L(name)  subr_tab_ptr_as_object(&subr_tab_addr->D_##name)
  #endif
# wird verwendet von allen Modulen


# Pseudofunktionen sind Adressen von C-Funktionen, die direkt angesprungen werden k�nnen.
# F�r SAVEMEM/LOADMEM gibt es eine Tabelle aller Pseudofunktionen.
  typedef object pseudofun_(); # C-Funktion mit Objekt als Ergebnis
  typedef pseudofun_ *  Pseudofun; # Pointer auf so eine Funktion

# Deklaration der Pseudofunktionen-Tabelle:
  #define PSEUDOFUN  PSEUDOFUN_A
  extern struct pseudofun_tab_ {
                                 #include "pseudofun.c"
                               }
         pseudofun_tab;
  #undef PSEUDOFUN
# wird verwendet von STREAM, SPVW


# Deklaration der Symbol-Tabelle:
  #define LISPSYM  LISPSYM_A
  extern struct symbol_tab_ {
                              #include "constsym.c"
                            }
         symbol_tab_data;
  #undef LISPSYM
# wird verwendet von Macro S

# Abk�rzung f�r LISP-Symbol mit einem gegebenen Namen: S(name)
  #define S(name)  S_help_(S_##name)
  #if !defined(MAP_MEMORY_TABLES)
    #define symbol_tab  symbol_tab_data
    #ifdef TYPECODES
      #define S_help_(name)  (type_constpointer_object(symbol_type,&symbol_tab.name))
    #else
      #if defined(OBJECT_STRUCT)
        #define S_help_(name)  as_object((oint)&symbol_tab.name+varobject_bias)
      #else
        #define S_help_(name)  objectplus(&symbol_tab.name,varobject_bias)
      #endif
    #endif
  #else
    # define symbol_tab_addr ((struct symbol_tab_ *)type_constpointer_object(symbol_type,0))
    #define symbol_tab_addr ((struct symbol_tab_ *)type_zero_oint(symbol_type))
    #define symbol_tab  (*symbol_tab_addr)
    #define S_help_(name)  (as_object((oint)(&symbol_tab_addr->name)))
    #if 0 # Manche Compiler erlauben obigen Ausdruck
          # - obwohl eine 'constant expression' -
          # nicht als Initialisierer von static-Variablen.
          # Wir m�ssen nachhelfen:
      #undef S_help_
      #define S_help_(name)  (as_object( (char*)(&((struct symbol_tab_ *)0)->name) + (uintP)symbol_tab_addr ))
    #endif
  #endif
# wird verwendet von allen Modulen

#define NIL  S(nil)
#define T    S(t)

# Der Macro NIL_IS_CONSTANT gibt an, ob NIL vom C-Compiler als
# 'constant expression' anerkannt wird. Wenn ja, k�nnen die Tabellen
# zum gro�en Teil bereits vom C-Compiler initialisiert werden.
  #if (oint_addr_shift==0)
    #define NIL_IS_CONSTANT  TRUE
  #else
    #define NIL_IS_CONSTANT  FALSE
  #endif

# Deklaration der Tabelle der sonstigen festen Objekte:
  #define LISPOBJ  LISPOBJ_A
  extern struct object_tab_ {
                              #include "constobj.c"
                            }
         object_tab;
  #undef LISPOBJ
# wird verwendet von Macro O

# Abk�rzung f�r sonstiges LISP-Objekt mit einem gegebenem Namen:
  #define O(name)  (object_tab.name)

# Abk�rzung f�r von language abh�ngiges LISP-Objekt mit einem gegebenem Namen:
# OLS(name)  falls es sich um LISP-Strings handelt, mit LISPOBJ_LS definiert,
# OL(name)   falls es sich um andere LISP-Objekte handelt, von LISPOBJ_L.
# kann GC ausl�sen
  #ifndef GNU_GETTEXT
    #ifdef LANGUAGE_STATIC
      #define OL(name)  O(name)
    #else
      #define OL(name)  ((&O(name))[language])
    #endif
    #define OLS(name)  OL(name)
  #else # GNU_GETTEXT
    #define OLS(name)  localized_string(O(name))
    #define OL(name)  localized_object(O(name))
  #endif

#if (defined(GENERATIONAL_GC) && defined(SPVW_MIXED)) || defined(SELFMADE_MMAP)
# handle_fault_range(PROT_READ,start,end) macht einen Adressbereich lesbar,
# handle_fault_range(PROT_READ_WRITE,start,end) macht ihn schreibbar.
  extern boolean handle_fault_range (int prot, aint start_address, aint end_address);
#endif


# ###################### MODBIBL zu MODULES.D ############################ #

#if defined(DYNAMIC_MODULES) && !defined(HAVE_DYNLOAD)
  #error "Dynamic modules require dynamic loading!"
#endif

# Anzahl der externen Module:
  extern uintC module_count;

# Daten f�r die Initialisierung der subr_tab eines Moduls:
  typedef struct { const char* packname; # Name der Home-Package des Symbols oder NULL
                   const char* symname; # Name des Symbols
                 }
          subr_initdata;

# Daten f�r die Initialisierung der object_tab eines Moduls:
  typedef struct { const char* initstring; } # Initialisierungs-String
          object_initdata;

# Tabelle bzw. Liste der Module:
  typedef struct module_
                 { const char* name; # Name
                   subr_* stab; const uintC* stab_size; # eine eigene subr_tab
                   object* otab; const uintC* otab_size; # eine eigene object_tab
                   boolean initialized;
                   # Daten zur Initialisierung:
                   const subr_initdata* stab_initdata;
                   const object_initdata* otab_initdata;
                   # Funktionen zur Initialisierung
                   void (*initfunction1) (struct module_ *); # nur einmal
                   void (*initfunction2) (struct module_ *); # immer bei Programmstart
                   #ifdef DYNAMIC_MODULES
                   struct module_ * next; # verkettete Liste
                   #endif
                 }
          module_;
  #ifdef DYNAMIC_MODULES
    extern module_ modules[]; # Listenanfang
    BEGIN_DECLS
    extern void add_module (module_ * new_module);
    END_DECLS
  #else
    extern module_ modules[]; # 1+module_count Eintr�ge, dann ein leerer Eintrag
  #endif

#ifdef HAVE_DYNLOAD
# Attaches a shared library to this process' memory, and attempts to load
# a number of clisp modules from it.
  extern void dynload_modules (const char * library, uintC modcount, const char * const * modnames);
#endif


# ####################### EVALBIBL zu EVAL.D ############################## #

/*

Spezifikationen f�r den Evaluator
#################################

SUBRs und FSUBRs
================

Sie werden konstruiert mit
  LISPFUN             f�r allgemeine LISP-Funktionen,
  LISPFUNN            f�r normale LISP-Funktionen (nur required-Parameter),
  LISPSPECFORM        f�r Special-Forms (FSUBRs).
Beachte, dass SUBRs mit KEY_ANZ=0 vom Evaluator als SUBRs ohne Keyword-
Parameter betrachtet werden (was zur Folge hat, dass in diesem Fall das
ALLOW_FLAG bedeutungslos ist und kein Keyword, auch nicht :ALLOW-OTHER-KEYS,
akzeptiert wird)!

Werte
=====

Folgendes Format wird f�r die �bergabe von multiple values verwendet:
value1 enth�lt den ersten Wert (NIL falls keine Werte).
mv_count enth�lt die Anzahl der Werte.
Falls mindestens ein Wert vorhanden:   value1 = erster Wert.
Falls mindestens zwei Werte vorhanden: value2 = zweiter Wert.
Falls mindestens drei Werte vorhanden: value3 = dritter Wert.
Alle Werte sind in mv_space abgelegt.
Empfohlene Befehle zur R�ckgabe (an den Aufrufer) von
  0 Werten:   value1=NIL; mv_count=0;
  1 Wert:     value1=...; mv_count=1;
  2 Werten:   value1=...; value2=...; mv_count=2;
  3 Werten:   value1=...; value2=...; value3=...; mv_count=3;
  mehr als 3 Werten:
              if (Wertezahl >= mv_limit) goto fehler_zuviele_werte;
              Werte der Reihe nach auf den STACK legen
              STACK_to_mv(Wertezahl);

Parameter�bergabe an SUBRs
==========================

Die Argumente werden auf dem LISP-Stack �bergeben, dabei liegt das erste
Argument zuoberst. Zuerst kommen die required-Argumente, dann die optionalen
Argumente (jeweils #UNBOUND, falls nicht angegeben), dann die
Keyword-Argumente (wieder jeweils #UNBOUND, falls nicht angegeben).
In subr_self befindet sich das SUBR-Objekt.
Ist kein &REST-Argument vorgesehen, so ist dies alles. Ist &REST-Argument
vorgesehen, so folgen im Stack alle weiteren Argumente (nach den optionalen)
einzeln, und es werden �bergeben: die Anzahl dieser Argumente und ein Pointer
�bers erste dieser Argumente. (Dann ist die Anzahl der LISP-Objekte auf dem
Stack also nicht immer dieselbe!)
Beim R�cksprung m�ssen alle Argumente vom LISP-Stack entfernt sein
(d.h. z.B. bei SUBRs mit &REST: der Stackpointer STACK muss den Wert
args_pointer = rest_args_pointer STACKop (feste Argumentezahl)
= Pointer �bers erste Argument �berhaupt) haben, und mv_count/mv_space
muss die Werte enthalten.

Parameter�bergabe an FSUBRs
===========================

Die Parameter werden auf dem LISP-Stack �bergeben, dabei liegt der erste
Parameter zuoberst. Zuerst kommen die required-Parameter, dann die optionalen
Parameter (#UNBOUND, falls nicht angegeben), dann - falls Body-Flag wahr -
der gesamte restliche Body (meist eine Liste).
Die Anzahl der auf dem LISP-Stack liegenden Objekte ist also immer dieselbe,
n�mlich  reqParameterZahl + optParameterZahl + (0 oder 1 falls Body-Flag).
Beim Aufruf enth�lt subr_self das FSUBR-Objekt, und die gesamte Form befindet
sich im EVAL-Frame, direkt �ber den Parametern.
Beim R�cksprung m�ssen alle Parameter vom LISP-Stack entfernt sein
(d.h. der Stackpointer STACK muss um Objektezahl erh�ht worden sein),
und mv_count/mv_space muss die Werte enthalten.

Environments
============

Allgemeines
-----------
Das lexikalische Environment ist aufgeteilt in 5 Komponenten:
  - Das Variablen-Environment (VAR_ENV),
  - Das Funktions- und Macro-Environment (FUN_ENV),
  - Das Block-Environment (BLOCK_ENV),
  - Das Tagbody-Environment (GO_ENV),
  - Das Deklarations-Environment (DECL_ENV).
Das Environment wird in 5 "globalen Variablen" gehalten. Bei Ver�nderung
wird es mit speziellen Frames dynamisch gebunden.
An SYM_FUNCTION, MACROEXP, MACROEXP0, PARSE_DD wird ein einzelnes
Funktions- und Macro-Environment �bergeben.
GET_CLOSURE erwartet einen Pointer auf alle Environments en bloc: A3 mit
VAR_(A3)=VAR_ENV, FUN_(A3)=FUN_ENV, BLOCK_(A3)=BLOCK_ENV, GO_(A3)=GO_ENV,
DECL_(A3)=DECL_ENV.

Das Variablen-Environment
-------------------------
Es enth�lt die lokalen Variablenbindungen.
Ein Variablen-Environment ist gegeben durch einen Pointer auf einen
Variablenbindungs-Frame oder durch NIL (das bedeutet ein leeres lexikalisches
Environment) oder durch einen Vektor folgenden Aufbaus:
Der Vektor enth�lt n Bindungen und hat die L�nge 2n+1. Die Elemente sind
n-mal jeweils Variable (ein Symbol) und zugeh�riger Wert (als "Wert" kann
auch #<SPECDECL> auftreten, dann ist die Variable dynamisch zu referenzieren)
und als letztes Element das Vorg�nger-Environment.

Das Funktions- und Macro-Environment
------------------------------------
Es enth�lt die lokalen Funktions- und Macro-Definitionen.
Ein Funktions- und Macro-Environment ist gegeben durch einen Pointer auf
einen Funktions- oder Macrobindungs-Frame oder durch NIL (das bedeutet ein
leeres lexikalisches Environment) oder durch einen Vektor folgenden Aufbaus:
Der Vektor enth�lt n Bindungen und hat die L�nge 2n+1. Die Elemente sind
n-mal jeweils Funktionsname (ein Symbol) und zugeh�rige Definition (eine
Closure oder NIL oder ein Cons (SYS::MACRO . Closure) ) und als letztes
Element das Vorg�nger-Environment.

Das Block-Environment
---------------------
Es enth�lt die lexikalisch sichtbaren Block-Exitpoints.
Ein Block-Environment ist gegeben durch einen Pointer auf einen Block-Frame
oder durch eine Assoziationsliste, deren Elemente jeweils als CAR den
Block-Namen (ein Symbol) haben und als CDR entweder den Pointer auf den
zugeh�rigen Frame oder, falls der Block bereits verlassen wurde, #DISABLED.

Das Tagbody-Environment
-----------------------
Es enth�lt die lexikalisch sichtbaren Go-Marken der Tagbodys.
Ein Tagbody-Environment ist gegeben durch einen Pointer auf einen
Tagbody-Frame oder durch eine Assoziationsliste, deren Elemente jeweils als
CAR einen Vektor (mit den Go-Marken als Elementen) haben und als CDR entweder
den Pointer auf den zugeh�rigen Frame oder, falls der Tagbody bereits
verlassen wurde, #<DISABLED>.

Das Deklarations-Environment
----------------------------
Es enth�lt die lexikalisch sichtbaren Deklarationen.
Ein Deklarations-Environment ist gegeben durch eine Liste von Declaration-
Specifiers, deren CAR jeweils entweder OPTIMIZE oder DECLARATION oder
ein benutzerdefinierter Deklarationstyp ist.

�bergabe von Environments an LISP-Funktionen
--------------------------------------------
Daf�r gibt es zwei Datenstrukturen:
Bei �bergabe als zweites Argument an Macro-Expander-Funktionen (CLTL S.
145-146) und bei Annahme durch MACROEXPAND und MACROEXPAND-1 (CLTL S. 151)
handelt es sich nur um einen 2-elementigen Simple-Vector, bestehend aus einem
genesteten Variablen-Environment und einem genesteten Funktions- und Macro-
Environment. Dasselbe bei �bergabe an SYSTEM::%EXPAND-LAMBDABODY-MAIN u.�.
Bei �bergabe als zweites Argument an den Wert von *EVALHOOK* bzw. als drittes
Argument an den Wert von *APPLYHOOK* (CLTL S. 322) und bei Annahme durch
EVALHOOK und APPLYHOOK (CLTL S. 323) handelt es sich um einen 5-elementigen
Simple-Vector mit den f�nf Einzelkomponenten, alle genestet.

Frames
======
F�r den Aufruf von SUBRs, FSUBRs und compilierten Closures werden keine
Frames verwendet.
Es gibt folgende 14 Arten von Frames:
  - Environmentbindungs-Frame (ENV_FRAME),
  - APPLY-Frame (APPLY_FRAME),
  - EVAL-Frame (EVAL_FRAME),
  - dynamischer Variablenbindungs-Frame (DYNBIND_FRAME),
  - Variablenbindungs-Frame (VAR_FRAME),
  - Funktions- oder Macrobindungs-Frame (FUN_FRAME),
  - interpretierter Block-Frame (IBLOCK_FRAME),
  - compilierter Block-Frame (CBLOCK_FRAME),
  - interpretierter Tagbody-Frame (ITAGBODY_FRAME),
  - compilierter Tagbody-Frame (CTAGBODY_FRAME),
  - Catch-Frame (CATCH_FRAME),
  - Unwind-Protect-Frame (UNWIND_PROTECT_FRAME),
  - Handler-Frame (HANDLER_FRAME),
  - Driver-Frame (DRIVER_FRAME).
Zuunterst in einem Frame kommt ein Langwort, das die Frametyp-Information
und einen Pointer �ber den Frame (= den Wert des STACK vor Aufbau und nach
Abbau des Frame) enth�lt.
In der Frame-Info sind die Bits
  SKIP2_BIT      gel�scht, falls dar�ber noch ein weiteres Langwort kommt,
                   das kein LISP-Objekt ist und deswegen von der GC
                   �bersprungen werden muss,
  EXITPOINT_BIT  gesetzt bei allen au�er VAR und FUN,
  NESTED_BIT     bei IBLOCK und ITAGBODY gesetzt, wenn Exitpoint bzw.
                   Go-Marken bereits in eine Aliste gesteckt wurden.
Die Normalwerte f�r die Frametyp-Info-Bytes sind ENVxx_FRAME_INFO,
APPLY_FRAME_INFO, EVAL_FRAME_INFO, VAR_FRAME_INFO, FUN_FRAME_INFO,
IBLOCK_FRAME_INFO, CBLOCK_FRAME_INFO, ITAGBODY_FRAME_INFO, CTAGBODY_FRAME_INFO,
CATCH_FRAME_INFO, UNWIND_PROTECT_FRAME_INFO, DRIVER_FRAME_INFO.
Die Routine, die in (SP).L mit SP=SP_(STACK) steht (bei IBLOCK-, CBLOCK-,
ITAGBODY-, CTAGBODY-, CATCH-, UNWIND-PROTECT-Frames), wird
angesprungen durch   MOVE.L SP_(STACK),SP ! RTS  .
Bei DRIVER-Frames durch   MOVE.L SP_(STACK),SP ! MOVE.L (SP),-(SP) ! RTS  .
In der portablen C-Version steht in SP_(STACK) ein Pointer auf einen
setjmp/longjmp-Buffer.

Environmentbindungs-Frames
--------------------------
Sie enthalten dynamische Bindungen von maximal 5 Environments.
Frame-Info ist ENVxx_FRAME_INFO (xx je nachdem, welche der Environments hier
gebunden sind). Aufbau:
    Offset        Stack-Inhalt
  20/16/12/8/4  [alter Wert von DECL_ENV]
  16/12/8/4     [alter Wert von GO_ENV]
  12/8/4        [alter Wert von BLOCK_ENV]
  8/4           [alter Wert von FUN_ENV]
  4             [alter Wert von VAR_ENV]
  0             Frame-Info; Pointer �ber Frame
Im einzelnen:
ENV1V_frame    f�r 1 VAR_ENV
ENV1F_frame    f�r 1 FUN_ENV
ENV1B_frame    f�r 1 BLOCK_ENV
ENV1G_frame    f�r 1 GO_ENV
ENV1D_frame    f�r 1 DECL_ENV
ENV2VD_frame   f�r 1 VAR_ENV und 1 DECL_ENV
ENV5_frame     f�r alle 5 Environments

APPLY-Frames
------------
Sie werden erzeugt bei jedem Aufruf (APPLY oder FUNCALL) einer interpretierten
Closure.
Aufbau:
  Offset     Stack-Inhalt
  4n+12
  4n+8      Argument 1
  ...
  12        Argument n
  8         Funktion, die gerade aufgerufen wird
  4         SP
  0         Frame-Info; Pointer �ber Frame
SP ist ein Pointer in den Programmstack. R�cksprung zu (SP).L nach Aufl�sung
des APPLY-Frames gibt den Inhalt von A0/... als Werte der Form zur�ck.
Die Frame-Info hat den Wert APPLY_FRAME_INFO oder TRAPPED_APPLY_FRAME_INFO.

EVAL-Frames
-----------
Sie werden erzeugt bei jedem Aufruf des EVAL-Unterprogramms.
Aufbau:
  Offset     Stack-Inhalt
  8         Form, die gerade evaluiert wird
  4         SP
  0         Frame-Info; Pointer �ber Frame
SP ist ein Pointer in den Programmstack. R�cksprung zu (SP).L nach Aufl�sung
des EVAL-Frames gibt den Inhalt von A0/... als Werte der Form zur�ck.
Die Frame-Info hat den Wert EVAL_FRAME_INFO oder TRAPPED_EVAL_FRAME_INFO.

Dynamische Variablenbindungs-Frames
-----------------------------------
Sie binden dynamisch Symbole an Werte.
Der Aufbau eines solchen Frames mit n Bindungen ist wie folgt:
  Offset  Stack-Inhalt
  8n+4
  8n      Wert 1
  8n-4    Symbol 1
  ...     ...
  8       Wert n
  4       Symbol n
  0       Frame-Info; Pointer �ber Frame
Der Inhalt des Frameinfo-Bytes ist DYNBIND_FRAME_INFO.

Variablenbindungs-Frames
------------------------
Sie werden erzeugt beim Anwenden von interpretierten Closures (f�r die in der
Lambda-Liste spezifizierten Variablenbindungen und ggfs. in den Deklarationen
angegebenen dynamischen Referenzen) und von LET und LET*, sowie von allen
Konstrukten, die implizit LET oder LET* benutzen (wie DO, DO*, PROG, PROG*,
DOLIST, DOTIMES, ...).
Der Aufbau eines Variablenbindungs-Frames mit n Bindungen ist wie folgt:
#ifndef NO_symbolflags
  Offset  Stack-Inhalt
  12+8n
  8+8n    Wert 1
  4+8n    Symbol 1
  ...     ...
  16      Wert n
  12      Symbol n
  8       NEXT_ENV
  4       m
  0       Frame-Info; Pointer �ber Frame
#else
  Offset  Stack-Inhalt
  12+12n
  8+12n   Wert 1
  4+12n   Symbol 1
  12n     Markierungsbits 1
  ...     ...
  20      Wert n
  16      Symbol n
  12      Markierungsbits n
  8       NEXT_ENV
  4       m
  0       Frame-Info; Pointer �ber Frame
#endif
Die Symbol/Wert-Paare sind dabei in der Reihenfolge numeriert und abgelegt,
in der die Bindungen aktiv werden (d.h. z.B. bei interpretierten Closures:
zuerst die dynamischen Referenzen (SPECIAL-Deklarationen), dann die required-
Parameter, dann die optionalen Parameter, dann der Rest-Parameter, dann die
Keyword-Parameter, dann die AUX-Variablen).
Die Symbole enthalten im Stack folgende Markierungsbits: ACTIVE_BIT, ist
gesetzt, wenn die Bindung aktiv ist, DYNAM_BIT ist gesetzt, wenn die Bindung
dynamisch ist. (Dynamische Referenzen sind als lexikalisch gekennzeichnet
mit dem speziellen Wert #SPECDECL!).
NEXT_ENV ist das n�chsth�here Variablen-Environment.
m ist ein Langwort, 0 <= m <= n, und bedeutet die Anzahl der Bindungen, die
noch nicht durch NEST-Operationen in einen Vektor gesteckt wurden. Also
sind die Symbol/Wert-Paare 1,...,n-m aktiv gewesen, inzwischen aber genestet
und deswegen im Stack (sofern es statische Bindungen waren) wieder inaktiv.
Nur noch einige der Paare n-m+1,...,n k�nnen statisch und aktiv sein.
Der Inhalt des Frameinfo-Bytes ist VAR_FRAME_INFO.

Funktions- und Macrobindungs-Frames
-----------------------------------
Sie werden erzeugt von FLET und MACROLET.
Der Aufbau eines Variablenbindungs-Frames mit n Bindungen ist wie folgt:
  Offset  Stack-Inhalt
  12+8n
  8+8n    Wert 1
  4+8n    Symbol 1
  ...     ...
  16      Wert n
  12      Symbol n
  8       NEXT_ENV
  4       m
  0       Frame-Info; Pointer �ber Frame
NEXT_ENV ist das n�chsth�here Funktions-Environment.
m ist ein Langwort, 0 <= m <= n, und bedeutet die Anzahl der Bindungen, die
noch nicht durch NEST-Operationen in einen Vektor gesteckt wurden. Also sind
die Symbol/Wert-Paare 1,...,n-m aktiv gewesen, inzwischen aber genestet und
deswegen im Stack wieder inaktiv. Nur noch die Paare n-m+1,...,n sind aktiv.
Markierungsbits werden hier im Gegensatz zu den Variablenbindungs-Frames
nicht ben�tigt.
Alle Werte sind Closures oder Conses (SYSTEM::MACRO . Closure).
Der Inhalt des Frameinfo-Bytes ist FUN_FRAME_INFO.

Interpretierte Block-Frames
---------------------------
Sie werden erzeugt von BLOCK und allen Konstrukten, die ein implizites BLOCK
enthalten (z.B. DO, DO*, LOOP, PROG, PROG*, ...). Der Aufbau ist folgender:
  Offset  Stack-Inhalt
  16
  12       NAME
  8        NEXT_ENV
  4        SP
  0        Frame-Info; Pointer �ber Frame
NAME ist der Name des Blocks. NEXT_ENV ist das n�chsth�here Block-Environment.
SP ist ein Pointer in den Programmstack, (SP).L ist eine Routine, die den
Block-Frame aufl�st und den Block mit den Werten A0-A2/... verl�sst.
Frame-Info ist IBLOCK_FRAME_INFO, evtl. mit gesetztem NESTED_BIT (dann zeigt
NEXT_ENV auf eine Aliste, deren erstes Element das Paar (NAME . <Framepointer>)
ist, weil der Block noch nicht DISABLED ist).

Compilierte Block-Frames
------------------------
Aufbau:
  Offset  Stack-Inhalt
   12
   8        Cons (NAME . <Framepointer>)
   4        SP
   0        Frame-Info; Pointer �ber Frame
NAME ist der Name des Blocks.
SP ist ein Pointer in den Programmstack, (SP).L ist eine Routine, die den
Block-Frame aufl�st und den Block mit den Werten A0-A2/... verl�sst.
Frame-Info ist CBLOCK_FRAME_INFO.

Interpretierte Tagbody-Frames
-----------------------------
Sie werden erzeugt von TAGBODY und allen Konstrukten, die ein implizites
TAGBODY enthalten (z.B. DO, DO*, PROG, PROG*, ...).
Der Aufbau eines Tagbody-Frames mit n Tags ist folgender:
  Offset  Stack-Inhalt
  12+8n
  8+8n     BODY 1
  4+8n     MARKE 1
  ...      ...
  16       BODY n
  12       MARKE n
  8        NEXT_ENV
  4        SP
  0        Frame-Info; Pointer �ber Frame
Die Marken sind die Sprungziele; es sind Symbole ud Integers, die sich im
Body befinden. Der zugeh�rige "Wert" BODY i enth�lt den Teil des Bodys, der
auf MARKE i folgt. NEXT_ENV ist das n�chsth�here Tagbody-Environment.
SP ist ein Pointer in den Programmstack, (SP).L ist eine Routine, die die
Aktion (GO MARKEi) ausf�hrt, wenn sie mit BODYi in A0 angesprungen wird.
Frame-Info ist ITAGBODY_FRAME_INFO, evtl. mit gesetztem NESTED_BIT (dann
zeigt NEXT_ENV auf eine Aliste, deren erstes Element die Form
(#(MARKE1 ... MARKEn) . <Framepointer>) hat, weil der Tagbody noch nicht
DISABLED ist).

Compilierte Tagbody-Frames
--------------------------
Aufbau:
  Offset  Stack-Inhalt
   12
   8        Cons (#(MARKE1 ... MARKEn) . <Framepointer>)
   4        SP
   0        Frame-Info; Pointer �ber Frame
MARKE1, ..., MARKEn sind die Namen der Tags (im compilierten Code eigentlich
nur noch zu Fehlermeldungszwecken vorhanden).
SP ist ein Pointer in den Programmstack, (SP).L ist eine Routine, die die
Aktion (GO MARKEi) ausf�hrt, wenn sie mit value1 = i (1 <= i <= n) angesprungen
wird.
Frame-Info ist CTAGBODY_FRAME_INFO.

Catch-Frames
------------
Sie werden erzeugt von der Special-Form CATCH. Ihr Aufbau ist wie folgt:
  Offset  Stack-Inhalt
   12
   8        TAG
   4        SP
   0        Frame-Info; Pointer �ber Frame
Dabei ist TAG die Marke des Catchers.
SP ist ein Pointer in den Programmstack, (SP).L ist eine Routine, die den
Frame aufl�st und die Werte A0-A2/... zur�ckgibt.
Frame-Info ist CATCH_FRAME_INFO.

Unwind-Protect-Frames
---------------------
Sie werden erzeugt von der Special-Form UNWIND-PROTECT und allen Konstrukten,
die ein implizites UNWIND-PROTECT enthalten (wie WITH-OPEN-STREAM oder
WITH-OPEN-FILE). Ihr Aufbau ist wie folgt:
  Offset  Stack-Inhalt
   8
   4        SP
   0        Frame-Info; Pointer �ber Frame
SP ist ein Pointer in den Programmstack. (SP).L ist eine Routine, die den
Frame aufl�st, die aktuellen Werte A0-A2/... rettet, den Cleanup durchf�hrt,
die geretteten Werte zur�ckschreibt und schlie�lich die Adresse anspringt
(mit RTS), die anstelle ihrer eigenen im Programmstack eingetragen wurde,
und dabei D6 unver�ndert l�sst.

Handler-Frames
--------------
Sie werden erzeugt vom Macro HANDLER-BIND. Ihr Aufbau ist wie folgt:
  Offset  Stack-Inhalt
   16
   12       Cons (#(type1 label1 ... typem labelm) . SPdepth)
   8        Closure
   4        SP
   0        Frame-Info; Pointer �ber Frame
SP ist ein Pointer in den Programmstack. Wenn eine Condition vom Typ typei
auftritt, wird als Handler die Closure ab Byte labeli abinterpretiert, wobei
zuerst ein St�ck Programmstack der L�nge SPdepth dupliziert wird.

Driver-Frames
-------------
Sie werden erzeut beim Eintritt in eine Top-Level-Schleife (meist eine
READ-EVAL-PRINT-Schleife) und dienen dazu, nach Fehlermeldungen die
vorherige Top-Level-Schleife fortzusetzen. Der Aufbau ist einfach:
  Offset  Stack-Inhalt
   8
   4        SP
   0        Frame-Info; Pointer �ber Frame
SP ist ein Pointer in den Programmstack. (SP).L ist eine Routine, die
wieder in die zugeh�rige Top-Level-Schleife einsteigt.

*/

# STACK:
# STACK ist der LISP-Stack.
# STACK_0 ist das erste Objekt auf dem STACK.
# STACK_1 ist das zweite Objekt auf dem STACK.
# etc., allgemein STACK_(n) = (n+1)tes Objekt auf dem STACK.
# pushSTACK(object)  legt ein Objekt auf dem STACK ab. Synonym: -(STACK).
# popSTACK()  liefert STACK_0 und nimmt es dabei vom STACK herunter.
# skipSTACK(n);  nimmt n Objekte vom STACK herunter.
# Will man den Wert des STACK retten, so geht das so:
#   var object* temp = STACK; ... (kein Zugriff �ber temp !) ... setSTACK(STACK = temp);
#   jedoch: Zugriff �ber  STACKpointable(temp)  m�glich.
# Will man einen Pointer, der durch den Stack laufen kann, so geht das so:
#   var object* ptr = &STACK_0;  oder  = STACKpointable(STACK);
#   assert( *(ptr STACKop 0) == STACK_0 );
#   assert( *(ptr STACKop 1) == STACK_1 );
#   ...
#   ptr skipSTACKop n;
#   assert( *(ptr STACKop 0) == STACK_(n) );
#   ...
#   Dieser Pointer darf nicht wieder dem STACK zugewiesen werden!
# Bringt man im STACK Bl�cke von Objekten unter und will den (n+1)-ten Block,
#   so geht das so:  STACKblock_(type,n). Dabei sollte type ein
#   struct-Typ sein mit sizeof(type) ein Vielfaches  von sizeof(object).

  #ifdef STACK_DOWN
    #define STACK_(n)  (STACK[(sintP)(n)])
    #define STACKpointable(STACKvar)  ((object*)(STACKvar))
    #define skipSTACKop  +=
    #define STACKop      +
    #define cmpSTACKop   <
    #define STACKblock_(type,n)  (((type*)STACK)[(sintP)(n)])
  #endif
  #ifdef STACK_UP
    #define STACK_(n)  (STACK[-1-(sintP)(n)])
    #define STACKpointable(STACKvar)  ((object*)(STACKvar)-1)
    #define skipSTACKop  -=
    #define STACKop      -
    #define cmpSTACKop   >
    #define STACKblock_(type,n)  (((type*)STACK)[-1-(sintP)(n)])
  #endif
  #define pushSTACK(obj)  (STACK_(-1) = (obj), STACK skipSTACKop -1)
    # Fast �quivalent zu  *--STACK = obj  bzw.  *STACK++ = obj  , jedoch
    # Vorsicht: erst Objekt in STACK_(-1) eintragen, dann erst STACK ver�ndern!
  #define popSTACK()  (STACK skipSTACKop 1, STACK_(-1))
  #define skipSTACK(n)  (STACK skipSTACKop (sintP)(n))

  #if defined(GNU) && defined(MC680X0) && !defined(NO_ASM) && !defined(WIDE) && defined(STACK_register)
    # Mit GNU auf einem 680X0 liegt STACK in einem Register. Zugriff und
    # Ver�nderung von STACK bilden daher eine ununterbrechbare Einheit.
    #undef pushSTACK
    #undef popSTACK
    #ifdef STACK_DOWN
      # define pushSTACK(obj)  (*--STACK = (obj))
      #define pushSTACK(obj)  \
        ({ __asm__ __volatile__ ("movel %0,"REGISTER_PREFIX""STACK_register"@-" : : "g" ((object)(obj)) : STACK_register ); })
      # define popSTACK()  (*STACK++)
      #define popSTACK()  \
        ({var object __result;                                                                                         \
          __asm__ __volatile__ ("movel "REGISTER_PREFIX""STACK_register"@+,%0" : "=g" (__result) : : STACK_register ); \
          __result;                                                                                                    \
         })
    #endif
    #ifdef STACK_UP
      # define pushSTACK(obj)  (*STACK++ = (obj))
      #define pushSTACK(obj)  \
        ({ __asm__ __volatile__ ("movel %0,"REGISTER_PREFIX""STACK_register"@+" : : "g" ((object)(obj)) : STACK_register ); })
      # define popSTACK()  (*--STACK)
      #define popSTACK()  \
        ({var object __result;                                                                                         \
          __asm__ __volatile__ ("movel "REGISTER_PREFIX""STACK_register"@-,%0" : "=g" (__result) : : STACK_register ); \
          __result;                                                                                                    \
         })
    #endif
  #endif
  #if defined(SPARC) && !defined(GNU) && !defined(__SUNPRO_C) && !defined(MULTITHREAD) && (SAFETY < 2)
    #undef pushSTACK
    #undef popSTACK
    #undef skipSTACK
    #define pushSTACK(obj)  (STACK_(-1) = (obj), _setSTACK(STACK STACKop -1))
    #define popSTACK()  (_setSTACK(STACK STACKop 1), STACK_(-1))
    #define skipSTACK(n)  (_setSTACK(STACK STACKop (sintP)(n)))
  #endif

  #define STACK_0  (STACK_(0))
  #define STACK_1  (STACK_(1))
  #define STACK_2  (STACK_(2))
  #define STACK_3  (STACK_(3))
  #define STACK_4  (STACK_(4))
  #define STACK_5  (STACK_(5))
  #define STACK_6  (STACK_(6))
  #define STACK_7  (STACK_(7))
  #define STACK_8  (STACK_(8))
  #define STACK_9  (STACK_(9))
  #define STACK_10  (STACK_(10))
  # usw.


# Werte:

# Maximalzahl multiple values + 1
  #define mv_limit  128
# Werte werden immer im MULTIPLE_VALUE_SPACE mv_space �bergeben:
  # uintC mv_count : Anzahl der Werte, >=0, <mv_limit
  # object mv_space [mv_limit-1] : die Werte.
  #   Bei mv_count>0 sind genau die ersten mv_count Elemente belegt.
  #   Bei mv_count=0 ist der erste Wert = NIL.
  #   Die Werte in mv_space unterliegen nicht der Garbage Collection!
  #if !defined(mv_count_register)
    # eine globale Variable
    #ifndef MULTITHREAD
      extern uintC mv_count;
    #else
      #define mv_count  (current_thread()->_mv_count)
    #endif
  #else
    # ein globales Register
    register uintC mv_count __asm__(mv_count_register);
  #endif
  #ifndef MULTITHREAD
    extern object mv_space [mv_limit-1];
  #else
    #define mv_space  (current_thread()->_mv_space)
  #endif
  # Synonyme:
  #if !defined(value1_register)
    #ifndef MULTITHREAD
      #define value1  mv_space[0]
    #else
      # Der erste Wert mv_space[0] wird an den Anfang von struct thread_ verschoben:
      #define value1  (current_thread()->_value1)
      #define VALUE1_EXTRA # und muss deswegen immer extra behandelt werden...
    #endif
  #else
    # Der erste Wert mv_space[0] wird permanent in einem Register gelagert:
    register object value1 __asm__(value1_register);
    #define VALUE1_EXTRA # und muss deswegen immer extra behandelt werden...
  #endif
  #define value2  mv_space[1]
  #define value3  mv_space[2]
  #define value4  mv_space[3]
  #define value5  mv_space[4]
  #define value6  mv_space[5]
  #define value7  mv_space[6]
  #define value8  mv_space[7]
  #define value9  mv_space[8]
# Zur �bergabe mit setjmp/longjmp braucht man evtl. noch globale Variablen:
  #ifdef NEED_temp_mv_count
    #ifndef MULTITHREAD
      extern uintC temp_mv_count;
    #else
      #define temp_mv_count  (current_thread()->_temp_mv_count)
    #endif
    #define LONGJMP_SAVE_mv_count()  temp_mv_count = mv_count
    #define LONGJMP_RESTORE_mv_count()  mv_count = temp_mv_count
  #else
    #define LONGJMP_SAVE_mv_count()
    #define LONGJMP_RESTORE_mv_count()
  #endif
  #ifdef NEED_temp_value1
    #ifndef MULTITHREAD
      extern object temp_value1;
    #else
      #define temp_value1  (current_thread()->_temp_value1)
    #endif
    #define LONGJMP_SAVE_value1()  temp_value1 = value1
    #define LONGJMP_RESTORE_value1()  value1 = temp_value1
  #else
    #define LONGJMP_SAVE_value1()
    #define LONGJMP_RESTORE_value1()
  #endif
# wird verwendet von EVAL, CONTROL,
#                    Macros LIST_TO_MV, MV_TO_LIST, STACK_TO_MV, MV_TO_STACK

# Liefert die untersten count Objekte vom STACK als Multiple Values.
# STACK_to_mv(count)
# count: Anzahl der Objekte, < mv_limit.
  #if !defined(VALUE1_EXTRA)
    #define STACK_to_mv(countx)  \
      { var uintC count = (countx);                            \
        mv_count = count;                                      \
        if (count == 0)                                        \
          { value1 = NIL; }                                    \
          else                                                 \
          { object* mvp = &mv_space[count]; # Zeiger hinter Platz f�r letzten Wert \
            dotimespC(count,count, { *--mvp = popSTACK(); } ); \
      }   }
  #else
    #define STACK_to_mv(countx)  \
      { var uintC count = (countx);                                \
        mv_count = count;                                          \
        if (count == 0)                                            \
          { value1 = NIL; }                                        \
          else                                                     \
          { count--;                                               \
            if (count > 0)                                         \
              { object* mvp = &mv_space[1+count]; # Zeiger hinter Platz f�r letzten Wert \
                dotimespC(count,count, { *--mvp = popSTACK(); } ); \
              }                                                    \
            value1 = popSTACK();                                   \
      }   }
  #endif
# wird verwendet von EVAL, CONTROL

# Legt alle Werte auf dem STACK ab.
# mv_to_STACK()
# > mv_count/mv_space : Werte
# < Werte auf dem Stack (erster Wert zuoberst)
# STACK-Overflow wird abgepr�ft.
# ver�ndert STACK
  #if !defined(VALUE1_EXTRA)
    #define mv_to_STACK()  \
      { var uintC count = mv_count;                           \
        if (count==0) ; # keine Werte -> nichts auf den STACK \
          else                                                \
          { var object* mvp = &mv_space[0];                   \
            dotimespC(count,count, { pushSTACK(*mvp++); } );  \
            check_STACK();                                    \
      }   }
  #else
    #define mv_to_STACK()  \
      { var uintC count = mv_count;                              \
        if (count==0) ; # keine Werte -> nichts auf den STACK    \
          else                                                   \
          { pushSTACK(value1);                                   \
            count--;                                             \
            if (count > 0)                                       \
              { var object* mvp = &mv_space[1];                  \
                dotimespC(count,count, { pushSTACK(*mvp++); } ); \
              }                                                  \
            check_STACK();                                       \
      }   }
  #endif
# wird verwendet von EVAL, CONTROL

# Liefert die Elemente einer Liste als Multiple Values.
# list_to_mv(list,fehler_statement)
# fehler_statement: im Fehlerfall (zuviele Werte).
  #if !defined(VALUE1_EXTRA)
    #define list_to_mv(lst,fehler_statement)  \
      {var object l = (lst);                                                   \
       var uintC count = 0;                                                    \
       if (atomp(l))                                                           \
         value1 = NIL;                                                         \
         else                                                                  \
         { var object* mvp = &mv_space[0];                                     \
           *mvp++ = Car(l); l = Cdr(l); count++; if (atomp(l)) goto mv_fertig; \
           *mvp++ = Car(l); l = Cdr(l); count++; if (atomp(l)) goto mv_fertig; \
           *mvp++ = Car(l); l = Cdr(l); count++; if (atomp(l)) goto mv_fertig; \
           do { *mvp++ = Car(l); l = Cdr(l);                                   \
                count++; if (count==mv_limit) { fehler_statement; }            \
              }                                                                \
              while (consp(l));                                                \
         }                                                                     \
       mv_fertig:                                                              \
       if (!nullp(l)) { subr_self = L(values_list); fehler_proper_list(l); }   \
       mv_count = count;                                                       \
      }
  #else
    #define list_to_mv(lst,fehler_statement)  \
      {var object l = (lst);                                                   \
       var uintC count = 0;                                                    \
       if (atomp(l))                                                           \
         value1 = NIL;                                                         \
         else                                                                  \
         { value1 = Car(l); l = Cdr(l); count++; if (atomp(l)) goto mv_fertig; \
          {var object* mvp = &mv_space[1];                                     \
           *mvp++ = Car(l); l = Cdr(l); count++; if (atomp(l)) goto mv_fertig; \
           *mvp++ = Car(l); l = Cdr(l); count++; if (atomp(l)) goto mv_fertig; \
           do { *mvp++ = Car(l); l = Cdr(l);                                   \
                count++; if (count==mv_limit) { fehler_statement; }            \
              }                                                                \
              while (consp(l));                                                \
         }}                                                                    \
       mv_fertig:                                                              \
       if (!nullp(l)) { subr_self = L(values_list); fehler_proper_list(l); }   \
       mv_count = count;                                                       \
      }
  #endif
# wird verwendet von EVAL, CONTROL

# Liefert die Liste der Multiple Values auf -(STACK).
# mv_to_list()
# kann GC ausl�sen
  #define mv_to_list()  \
    { mv_to_STACK(); # erst alle Werte auf den Stack               \
      pushSTACK(NIL); # Listenanfang                               \
      { var uintC count;                                           \
        dotimesC(count,mv_count, # bis alle Werte verbraucht sind: \
          { var object l = allocate_cons(); # neue Zelle           \
            Cdr(l) = popSTACK(); # Liste bisher                    \
            Car(l) = STACK_0; # n�chster Wert                      \
            STACK_0 = l; # neues Cons sichern                      \
          });                                                      \
    } }
# wird verwendet von EVAL, CONTROL, DEBUG

# Fehlermeldung bei zu vielen Werten
# fehler_mv_zuviel(caller);
# > caller: Aufrufer, ein Symbol
  nonreturning_function(extern, fehler_mv_zuviel, (object caller));
# wird verwendet von EVAL, CONTROL, LISPARIT

# W�hrend der Ausf�hrung eines SUBR, FSUBR: das aktuelle SUBR bzw. FSUBR.
# subr_self
# (Nur solange g�ltig, bis ein anderes SUBR oder eine andere Lisp-Funktion
# aufgerufen wird.)
  #if !defined(subr_self_register)
    #ifndef MULTITHREAD
      extern object subr_self;
    #else
      #define subr_self  (current_thread()->_subr_self)
    #endif
  #else
    register object subr_self __asm__(subr_self_register);
  #endif

# Innerhalb des Body eines SUBR: Zugriff auf die Argumente.
# Ein SUBR mit fester Argumentezahl kann �ber den STACK auf die Argumente
#   zugreifen: STACK_0 = letztes Argument, STACK_1 = vorletztes Argument etc.
#   STACK aufr�umen: mit skipSTACK(Argumentezahl) .
# Ein SUBR mit beliebig vielen Argumenten (&REST-Parameter) bekommt �bergeben:
#     uintC argcount              die Anzahl der restlichen Argumente
#     object* rest_args_pointer   Pointer �ber die restlichen Argumente
#   Zus�tzlich:
#     object* args_end_pointer    Pointer unter alle Argumente, von STACK abh�ngig
#   Zus�tzlich m�glich:
#     object* args_pointer = rest_args_pointer STACKop (feste Argumentezahl);
#                                 Pointer �ber das erste Argument
#   Typische Abarbeitungsschleifen:
#     von vorne:
#       until (argcount==0)
#         { var object arg = NEXT(rest_args_pointer); ...; argcount--; }
#       until (rest_args_pointer==args_end_pointer)
#         { var object arg = NEXT(rest_args_pointer); ...; }
#     von hinten:
#       until (argcount==0)
#         { var object arg = BEFORE(args_end_pointer); ...; argcount--; }
#       until (rest_args_pointer==args_end_pointer)
#         { var object arg = BEFORE(args_end_pointer); ...; }
#   Die Macros NEXT und BEFORE ver�ndern ihr Argument!
#   STACK aufr�umen: mit set_args_end_pointer(args_pointer)
#     oder skipSTACK((feste Argumentezahl) + (uintL) (restliche Argumentezahl)) .
  #define args_end_pointer  STACK
  #define set_args_end_pointer(new_args_end_pointer)  \
    setSTACK(STACK = (new_args_end_pointer))
  #ifdef STACK_DOWN
    #define NEXT(argpointer)  (*(--(argpointer)))
    #define BEFORE(argpointer)  (*((argpointer)++))
  #endif
  #ifdef STACK_UP
    #define NEXT(argpointer)  (*((argpointer)++))
    #define BEFORE(argpointer)  (*(--(argpointer)))
  #endif
# Next(pointer) liefert denselben Wert wie NEXT(pointer),
# ohne dabei jedoch den Wert von pointer zu ver�ndern.
# Before(pointer) liefert denselben Wert wie BEFORE(pointer),
# ohne dabei jedoch den Wert von pointer zu ver�ndern.
  #define Next(pointer)  (*(STACKpointable(pointer) STACKop -1))
  #define Before(pointer)  (*(STACKpointable(pointer) STACKop 0))

# Environments:

typedef struct { object var_env;   # Variablenbindungs-Environment
                 object fun_env;   # Funktionsbindungs-Environment
                 object block_env; # Block-Environment
                 object go_env;    # Tagbody/Go-Environment
                 object decl_env;  # Deklarations-Environment
               }
        environment;

# Das aktuelle Environment:
  #ifndef MULTITHREAD
    extern environment aktenv;
  #else
    #define aktenv  (current_thread()->_aktenv)
  #endif

# Macro: Legt f�nf einzelne Environment auf den STACK
# und bildet daraus ein einzelnes Environment.
# make_STACK_env(venv,fenv,benv,genv,denv, env5 = );
# > object venv,fenv,benv,genv,denv: 5 einzelne Environments
# < environment* env5: Pointer auf im Stack liegendes Environment
  #ifdef STACK_UP
    #define make_STACK_env(venv,fenv,benv,genv,denv,env5_zuweisung)  \
      { pushSTACK(venv); pushSTACK(fenv); pushSTACK(benv); pushSTACK(genv); pushSTACK(denv); \
        env5_zuweisung &STACKblock_(environment,0);                                           \
      }
  #endif
  #ifdef STACK_DOWN
    #define make_STACK_env(venv,fenv,benv,genv,denv,env5_zuweisung)  \
      { pushSTACK(denv); pushSTACK(genv); pushSTACK(benv); pushSTACK(fenv); pushSTACK(venv); \
        env5_zuweisung &STACKblock_(environment,0);                                           \
      }
  #endif

# Frameinfobits in Frames:
# im Frame-Info-Byte (tint):
#if (oint_type_len>=7) && 0 # vorl�ufig??
# Bitnummern im Frame-Info-Byte:
# belegen Bits 6..0 (bzw. Bits 7,5..0 falls garcol_bit_t=7).
  #ifdef TYPECODES
    #define FB7  garcol_bit_t
    #define FB6  (garcol_bit_t>TB5 ? TB5 : TB6)
    #define FB5  (garcol_bit_t>TB4 ? TB4 : TB5)
    #define FB4  (garcol_bit_t>TB3 ? TB3 : TB4)
    #define FB3  (garcol_bit_t>TB2 ? TB2 : TB3)
    #define FB2  (garcol_bit_t>TB1 ? TB1 : TB2)
    #define FB1  (garcol_bit_t>TB0 ? TB0 : TB1)
  #else
    #define FB7  garcol_bit_o
    #define FB6  30
    #define FB5  29
    #define FB4  28
    #define FB3  27
    #define FB2  26
    #define FB1  25
  #endif
# davon abh�ngig:
  #define frame_bit_t    FB7  # garcol_bit als FRAME-Kennzeichen
  #define skip2_bit_t    FB6  # gel�scht wenn GC zwei Langworte �berspringen muss
  #define unwind_bit_t   FB5  # gesetzt, wenn beim Aufl�sen (UNWIND) des Frames
                              # etwas zu tun ist
  # skip2-Bit=1 ==> unwind-Bit=1.
  # zur n�heren Information innerhalb der Frames mit skip2-Bit=1:
    #define envbind_bit_t  FB4  # Bit ist gesetzt bei ENV-Frames.
                                # Bit ist gel�scht bei DYNBIND-Frames.
    # zur n�heren Identifikation innerhalb der ENV-Frames:
      #define envbind_case_mask_t  (bit(FB3)|bit(FB2)|bit(FB1))
    # zur Unterscheidung in DYNBIND/CALLBACK:
      #define callback_bit_t  FB3  # Bit ist gesetzt bei CALLBACK-Frames.
                                   # Bit ist gel�scht bei DYNBIND-Frames.
  # zur n�heren Unterscheidung innerhalb der Frames mit skip2-Bit=0:
    #define entrypoint_bit_t  FB4  # Bit ist gesetzt, wenn FRAME einen
                                   # nicht-lokalen Einsprung enth�lt, mit Offset SP_ ist SP im STACK.
                                   # Bit ist gel�scht bei VAR-Frame und FUN-Frame.
    # zur n�heren Unterscheidung in BLOCK/TAGBODY/APPLY/EVAL/CATCH/UNWIND_PROTECT/HANDLER/DRIVER:
      #define blockgo_bit_t    FB3  # Bit gesetzt bei BLOCK- und TAGBODY-FRAME
      # zur n�heren Unterscheidung in BLOCK/TAGBODY:
        # Bit FB2 gesetzt bei TAGBODY, gel�scht bei BLOCK,
        #define cframe_bit_t     FB1  # gesetzt bei compilierten, gel�scht bei
                                    # interpretierten BLOCK/TAGBODY-Frames
        #define nested_bit_t unwind_bit_t # f�r IBLOCK und ITAGBODY, gesetzt,
                                    # wenn Exitpoint bzw. Tags genestet wurden
      # zur n�heren Unterscheidung in APPLY/EVAL/CATCH/UNWIND_PROTECT/HANDLER/DRIVER:
        #define dynjump_bit_t  FB2    # gel�scht bei APPLY und EVAL, gesetzt
                                      # bei CATCH/UNWIND_PROTECT/DRIVER-Frames
        #define trapped_bit_t unwind_bit_t # f�r APPLY und EVAL, gesetzt, wenn
                                    # beim Aufl�sen des Frames unterbrochen wird
        # unwind-Bit gesetzt bei UNWIND_PROTECT/DRIVER/TRAPPED_APPLY/TRAPPED_EVAL,
        # gel�scht sonst.
        #define eval_bit_t     FB1    # gesetzt bei EVAL-Frames,
                                      # gel�scht bei APPLY-Frames
        #define driver_bit_t   FB1    # gesetzt bei DRIVER-Frames,
                                      # gel�scht bei UNWIND_PROTECT-Frames
        #define handler_bit_t  FB1    # gesetzt bei HANDLER-Frames,
                                      # gel�scht bei CATCH-Frames
    # zur n�heren Unterscheidung in VAR/FUN:
      #define fun_bit_t        FB3  # gesetzt bei FUNCTION-FRAME, gel�scht bei VAR-FRAME
# in Objekten auf dem STACK (oint):
  #define frame_bit_o  (frame_bit_t+oint_type_shift)
  #define skip2_bit_o  (skip2_bit_t+oint_type_shift)
  #define unwind_bit_o  (unwind_bit_t+oint_type_shift)
    #define envbind_bit_o  (envbind_bit_t+oint_type_shift)
    #define callback_bit_o  (callback_bit_t+oint_type_shift)
    #define entrypoint_bit_o  (entrypoint_bit_t+oint_type_shift)
      #define blockgo_bit_o  (blockgo_bit_t+oint_type_shift)
        #define cframe_bit_o  (cframe_bit_t+oint_type_shift)
        #define nested_bit_o  (nested_bit_t+oint_type_shift)
        #define dynjump_bit_o  (dynjump_bit_t+oint_type_shift)
        #define trapped_bit_o  (trapped_bit_t+oint_type_shift)
        #define eval_bit_o  (eval_bit_t+oint_type_shift)
        #define driver_bit_o  (driver_bit_t+oint_type_shift)
        #define handler_bit_o  (handler_bit_t+oint_type_shift)
      #define fun_bit_o  (fun_bit_t+oint_type_shift)
# einzelne Frame-Info-Bytes:
  #define DYNBIND_frame_info          /* %11100.. */ (bit(FB7)|bit(FB6)|bit(FB5))
  #ifdef HAVE_SAVED_REGISTERS
  #define CALLBACK_frame_info         /* %11101.. */ (bit(FB7)|bit(FB6)|bit(FB5)|bit(FB3))
  #endif
  #define ENV1V_frame_info            /* %1111000 */ (bit(FB7)|bit(FB6)|bit(FB5)|bit(FB4))
  #define ENV1F_frame_info            /* %1111001 */ (bit(FB7)|bit(FB6)|bit(FB5)|bit(FB4)|bit(FB1))
  #define ENV1B_frame_info            /* %1111010 */ (bit(FB7)|bit(FB6)|bit(FB5)|bit(FB4)|bit(FB2))
  #define ENV1G_frame_info            /* %1111011 */ (bit(FB7)|bit(FB6)|bit(FB5)|bit(FB4)|bit(FB2)|bit(FB1))
  #define ENV1D_frame_info            /* %1111100 */ (bit(FB7)|bit(FB6)|bit(FB5)|bit(FB4)|bit(FB3))
  #define ENV2VD_frame_info           /* %1111101 */ (bit(FB7)|bit(FB6)|bit(FB5)|bit(FB4)|bit(FB3)|bit(FB1))
  #define ENV5_frame_info             /* %1111110 */ (bit(FB7)|bit(FB6)|bit(FB5)|bit(FB4)|bit(FB3)|bit(FB2))
  #define VAR_frame_info              /* %10100.. */ (bit(FB7)|bit(FB5))
  #define FUN_frame_info              /* %10101.. */ (bit(FB7)|bit(FB5)|bit(FB3))
  #define IBLOCK_frame_info           /* %1001100 */ (bit(FB7)|bit(FB4)|bit(FB3))
  #define NESTED_IBLOCK_frame_info    /* %1011100 */ (bit(FB7)|bit(FB5)|bit(FB4)|bit(FB3))
  #define CBLOCK_frame_info           /* %1011101 */ (bit(FB7)|bit(FB5)|bit(FB4)|bit(FB3)|bit(FB1))
  #define ITAGBODY_frame_info         /* %1001110 */ (bit(FB7)|bit(FB4)|bit(FB3)|bit(FB2))
  #define NESTED_ITAGBODY_frame_info  /* %1011110 */ (bit(FB7)|bit(FB5)|bit(FB4)|bit(FB3)|bit(FB2))
  #define CTAGBODY_frame_info         /* %1011111 */ (bit(FB7)|bit(FB5)|bit(FB4)|bit(FB3)|bit(FB2)|bit(FB1))
  #define APPLY_frame_info            /* %1001000 */ (bit(FB7)|bit(FB4))
  #define TRAPPED_APPLY_frame_info    /* %1011000 */ (bit(FB7)|bit(FB5)|bit(FB4))
  #define EVAL_frame_info             /* %1001001 */ (bit(FB7)|bit(FB4)|bit(FB1))
  #define TRAPPED_EVAL_frame_info     /* %1011001 */ (bit(FB7)|bit(FB5)|bit(FB4)|bit(FB1))
  #define CATCH_frame_info            /* %1001010 */ (bit(FB7)|bit(FB4)|bit(FB2))
  #define HANDLER_frame_info          /* %1001011 */ (bit(FB7)|bit(FB4)|bit(FB2)|bit(FB1))
  #define UNWIND_PROTECT_frame_info   /* %1011010 */ (bit(FB7)|bit(FB5)|bit(FB4)|bit(FB2))
  #define DRIVER_frame_info           /* %1011011 */ (bit(FB7)|bit(FB5)|bit(FB4)|bit(FB2)|bit(FB1))
#endif
#if (oint_type_len==6) || 1 # vorl�ufig??
# Bitnummern im Frame-Info-Byte:
# belegen Bits 5..0 (bzw. Bits 7,4..0 falls garcol_bit_t=7).
  #ifdef TYPECODES
    #define FB6  garcol_bit_t
    #define FB5  (garcol_bit_t>TB4 ? TB4 : TB5)
    #define FB4  (garcol_bit_t>TB3 ? TB3 : TB4)
    #define FB3  (garcol_bit_t>TB2 ? TB2 : TB3)
    #define FB2  (garcol_bit_t>TB1 ? TB1 : TB2)
    #define FB1  (garcol_bit_t>TB0 ? TB0 : TB1)
  #else
    #define FB6  garcol_bit_o
    #define FB5  30
    #define FB4  29
    #define FB3  28
    #define FB2  27
    #define FB1  26
  #endif
# davon abh�ngig:
  #define frame_bit_t    FB6  # garcol_bit als FRAME-Kennzeichen
  #define skip2_bit_t    FB5  # gel�scht wenn GC zwei Langworte �berspringen muss
  # define unwind_limit_t  ...  # dar�ber:
                              # ist beim Aufl�sen (UNWIND) des Frames etwas zu tun
  # skip2-Bit=1 ==> >= unwind-limit.
  # zur n�heren Information innerhalb der Frames mit skip2-Bit=1:
    #define envbind_bit_t  FB4  # Bit ist gesetzt bei ENV-Frames.
                                # Bit ist gel�scht bei DYNBIND-Frames.
    # zur n�heren Identifikation innerhalb der ENV-Frames:
      #define envbind_case_mask_t  (bit(FB3)|bit(FB2)|bit(FB1))
    # zur Unterscheidung in DYNBIND/CALLBACK:
      #define callback_bit_t  FB3  # Bit ist gesetzt bei CALLBACK-Frames.
                                   # Bit ist gel�scht bei DYNBIND-Frames.
  # zur n�heren Unterscheidung innerhalb der Frames mit skip2-Bit=0:
    # define entrypoint_limit_t  ...  # darunter:
                                   # wenn FRAME einen nicht-lokalen Einsprung enth�lt,
                                   # mit Offset SP_ ist SP im STACK.
                                   # dar�ber: bei VAR-Frame und FUN-Frame.
    # zur n�heren Unterscheidung in BLOCK/TAGBODY/APPLY/EVAL/CATCH/UNWIND_PROTECT/HANDLER/DRIVER:
      #define blockgo_bit_t    FB3  # Bit gesetzt bei BLOCK- und TAGBODY-FRAME
      # zur n�heren Unterscheidung in BLOCK/TAGBODY:
        # Bit FB1 gesetzt bei TAGBODY, gel�scht bei BLOCK,
        #define cframe_bit_t   FB2  # gesetzt bei compilierten, gel�scht bei
                                    # interpretierten BLOCK/TAGBODY-Frames
        #define nested_bit_t   FB4  # f�r IBLOCK und ITAGBODY, gesetzt,
                                    # wenn Exitpoint bzw. Tags genestet wurden
      # zur n�heren Unterscheidung in APPLY/EVAL/CATCH/UNWIND_PROTECT/HANDLER/DRIVER:
        #define dynjump_bit_t  FB2  # gel�scht bei APPLY und EVAL, gesetzt
                                    # bei CATCH/UNWIND_PROTECT/HANDLER/DRIVER-Frames
        #define trapped_bit_t  FB4  # f�r APPLY und EVAL, gesetzt, wenn
                                    # beim Aufl�sen des Frames unterbrochen wird
        # >= unwind_limit_t bei UNWIND_PROTECT/DRIVER/TRAPPED_APPLY/TRAPPED_EVAL,
        # < unwind_limit_t sonst.
        #define eval_bit_t     FB1  # gesetzt bei EVAL-Frames,
                                    # gel�scht bei APPLY-Frames
        #define driver_bit_t   FB1  # gesetzt bei DRIVER-Frames,
                                    # gel�scht bei UNWIND_PROTECT-Frames
        #define handler_bit_t  FB1  # gesetzt bei HANDLER-Frames,
                                    # gel�scht bei CATCH-Frames
    # zur n�heren Unterscheidung in VAR/FUN:
      #define fun_bit_t        FB1  # gesetzt bei FUNCTION-FRAME, gel�scht bei VAR-FRAME
# in Objekten auf dem STACK (oint):
  #define frame_bit_o  (frame_bit_t+oint_type_shift)
  #define skip2_bit_o  (skip2_bit_t+oint_type_shift)
    #define envbind_bit_o  (envbind_bit_t+oint_type_shift)
    #define callback_bit_o  (callback_bit_t+oint_type_shift)
      #define blockgo_bit_o  (blockgo_bit_t+oint_type_shift)
        #define cframe_bit_o  (cframe_bit_t+oint_type_shift)
        #define nested_bit_o  (nested_bit_t+oint_type_shift)
        #define dynjump_bit_o  (dynjump_bit_t+oint_type_shift)
        #define trapped_bit_o  (trapped_bit_t+oint_type_shift)
        #define eval_bit_o  (eval_bit_t+oint_type_shift)
        #define driver_bit_o  (driver_bit_t+oint_type_shift)
        #define handler_bit_o  (handler_bit_t+oint_type_shift)
      #define fun_bit_o  (fun_bit_t+oint_type_shift)
# einzelne Frame-Info-Bytes:
  #define APPLY_frame_info            /* %100000 */ (bit(FB6))
  #define EVAL_frame_info             /* %100001 */ (bit(FB6)|bit(FB1))
  #define CATCH_frame_info            /* %100010 */ (bit(FB6)|bit(FB2))
  #define HANDLER_frame_info          /* %100011 */ (bit(FB6)|bit(FB2)|bit(FB1))
  #define IBLOCK_frame_info           /* %100100 */ (bit(FB6)|bit(FB3))
  #define ITAGBODY_frame_info         /* %100101 */ (bit(FB6)|bit(FB3)|bit(FB1))
  #define unwind_limit_t                            (bit(FB6)|bit(FB3)|bit(FB2))
  #define CBLOCK_frame_info           /* %100110 */ (bit(FB6)|bit(FB3)|bit(FB2))
  #define CTAGBODY_frame_info         /* %100111 */ (bit(FB6)|bit(FB3)|bit(FB2)|bit(FB1))
  #define TRAPPED_APPLY_frame_info    /* %101000 */ (bit(FB6)|bit(FB4))
  #define TRAPPED_EVAL_frame_info     /* %101001 */ (bit(FB6)|bit(FB4)|bit(FB1))
  #define UNWIND_PROTECT_frame_info   /* %101010 */ (bit(FB6)|bit(FB4)|bit(FB2))
  #define DRIVER_frame_info           /* %101011 */ (bit(FB6)|bit(FB4)|bit(FB2)|bit(FB1))
  #define NESTED_IBLOCK_frame_info    /* %101100 */ (bit(FB6)|bit(FB4)|bit(FB3))
  #define NESTED_ITAGBODY_frame_info  /* %101101 */ (bit(FB6)|bit(FB4)|bit(FB3)|bit(FB1))
  #define entrypoint_limit_t                        (bit(FB6)|bit(FB4)|bit(FB3)|bit(FB2))
  #define VAR_frame_info              /* %101110 */ (bit(FB6)|bit(FB4)|bit(FB3)|bit(FB2))
  #define FUN_frame_info              /* %101111 */ (bit(FB6)|bit(FB4)|bit(FB3)|bit(FB2)|bit(FB1))
  #define DYNBIND_frame_info          /* %1100.. */ (bit(FB6)|bit(FB5))
  #ifdef HAVE_SAVED_REGISTERS
  #define CALLBACK_frame_info         /* %1101.. */ (bit(FB6)|bit(FB5)|bit(FB3))
  #endif
  #define ENV1V_frame_info            /* %111000 */ (bit(FB6)|bit(FB5)|bit(FB4))
  #define ENV1F_frame_info            /* %111001 */ (bit(FB6)|bit(FB5)|bit(FB4)|bit(FB1))
  #define ENV1B_frame_info            /* %111010 */ (bit(FB6)|bit(FB5)|bit(FB4)|bit(FB2))
  #define ENV1G_frame_info            /* %111011 */ (bit(FB6)|bit(FB5)|bit(FB4)|bit(FB2)|bit(FB1))
  #define ENV1D_frame_info            /* %111100 */ (bit(FB6)|bit(FB5)|bit(FB4)|bit(FB3))
  #define ENV2VD_frame_info           /* %111101 */ (bit(FB6)|bit(FB5)|bit(FB4)|bit(FB3)|bit(FB1))
  #define ENV5_frame_info             /* %111110 */ (bit(FB6)|bit(FB5)|bit(FB4)|bit(FB3)|bit(FB2))
#endif

# Bits f�r Symbole in VAR-Frames:
  # bit(active_bit),bit(dynam_bit),bit(svar_bit) m�ssen in ein uintB passen:
  #if !((active_bit<intBsize) && (dynam_bit<intBsize) && (svar_bit<intBsize))
    #error "Symbol bits don't fit in a single byte -- Symbol-Bits passen nicht in ein Byte!"
  #endif
  #ifdef NO_symbolflags
    # Bits werden im Stack separat als Fixnums abgelegt.
    #undef oint_symbolflags_shift
    #define oint_symbolflags_shift  oint_data_shift
  #else
    #if (oint_symbolflags_shift==oint_addr_shift)
      # bit(active_bit),bit(dynam_bit),bit(svar_bit) m�ssen echte Teiler
      # von varobject_alignment sein:
      #if (varobject_alignment % bit(active_bit+1)) || (varobject_alignment % bit(dynam_bit+1)) || (varobject_alignment % bit(svar_bit+1))
        #error "No more room for three bits in a symbol -- Kein Platz f�r drei Bits in der Adresse eines Symbols!"
      #endif
    #endif
  #endif
  #define active_bit_o  (active_bit+oint_symbolflags_shift)  # gesetzt: Bindung ist aktiv
  #define dynam_bit_o   (dynam_bit+oint_symbolflags_shift)   # gesetzt: Bindung ist dynamisch
  #define svar_bit_o    (svar_bit+oint_symbolflags_shift)    # gesetzt: n�chster Parameter ist supplied-p-Parameter f�r diesen

# Offsets f�r Daten in Frames, �ber STACK_(Offset) zu adressieren:
  #define frame_form      2  # EVAL
  #define frame_closure   2  # APPLY, HANDLER
  #define frame_anz       1  # VAR, FUN
  #define frame_SP        1  # IBLOCK, CBLOCK, ITAGBODY, CTAGBODY,
                             # EVAL, CATCH, UNWIND-PROTECT, HANDLER, DRIVER
  #define frame_next_env  2  # VAR, FUN, IBLOCK, ITAGBODY
  #define frame_ctag      2  # CBLOCK, CTAGBODY
  #define frame_tag       2  # CATCH
  #define frame_handlers  3  # HANDLER
  #define frame_name      3  # IBLOCK
  #define frame_args      3  # APPLY
  #define frame_bindings  3  # VAR, FUN, ITAGBODY
# Aufbau einzelner Bindungen in VAR-Frames:
  #ifdef NO_symbolflags
    #define varframe_binding_size  3
    #define varframe_binding_mark   0
    #define varframe_binding_sym    1
    #define varframe_binding_value  2
    #define pushSTACK_symbolwithflags(symbol,flags)  \
      pushSTACK(symbol); pushSTACK(as_object(as_oint(Fixnum_0) | (oint)(flags)))
  #else
    #define varframe_binding_size  2
    #define varframe_binding_mark   0
    #define varframe_binding_sym    0
    #define varframe_binding_value  1
    #define pushSTACK_symbolwithflags(symbol,flags)  \
      pushSTACK(as_object(as_oint(symbol) | (oint)(flags)))
  #endif

# Spezieller Wert zur Markierung nicht mehr "lebender" BLOCK- und TAGBODY-
# Referenzen (ersetzt den Frame-Pointer im CDR des entsprechenden Cons)
  #define disabled  make_system(0xDDDDDDUL)

# Wert zur Markierung als special deklarierter Referenzen
  #define specdecl  make_system(0xECDECDUL)

# Hantieren mit Frames:
# Eine lokale Variable FRAME enthalte den Wert von STACK nach Aufbau
# eines Frames. Dann kann man mit FRAME_(n) genauso wie mit STACK_(n)
# zugreifen:
  #ifdef STACK_DOWN
    #define FRAME_(n)  (FRAME[(sintP)(n)])
  #endif
  #ifdef STACK_UP
    #define FRAME_(n)  (FRAME[-1-(sintP)(n)])
  #endif
# make_framepointer(FRAME) ist der Frame-Pointer als Lisp-Objekt.
# framecode(FRAME_(0)) ist das Frame-Info-Byte (vom Typ fcint),
# topofframe(FRAME_(0)) ist ein Pointer �ber den Frame.
# FRAME = uTheFramepointer(obj) ist ein Frame-Pointer als Pointer in den Stack.
#         [uTheFramepointer ist das genaue Gegenteil von make_framepointer.]
# FRAME = TheFramepointer(obj) ebenfalls, aber evtl. doch noch mit Typinfo!
#         [Eine Abschw�chung von uTheFramepointer, die zum Zugreifen ausreicht.]
  #ifdef TYPECODES
    #if !defined(SINGLEMAP_MEMORY_STACK)
      #define make_framepointer(stack_ptr)  type_pointer_object(system_type,stack_ptr)
      #define topofframe(bottomword)  (object*)upointer(bottomword)
      #define uTheFramepointer(obj)  (object*)upointer(obj)
    #else
      #define make_framepointer(stack_ptr)  (as_object((oint)(stack_ptr)))
      #define topofframe(bottomword)  (object*)as_oint(type_pointer_object(system_type,upointer(bottomword)))
      #define uTheFramepointer(obj)  TheFramepointer(obj) # = (object*)(obj)
    #endif
    #define framecode(bottomword)  mtypecode(bottomword)
    typedef tint fcint;
  #else
    # Here the bottomword consists of the frame size, not the top of frame itself.
    # This leaves room for the frame info byte.
    #define make_framepointer(stack_ptr)  make_machine(stack_ptr)
    #ifdef STACK_UP
      #define topofframe(bottomword)  \
        (object*)((uintP)(&(bottomword))-(as_oint(bottomword)&(wbit(FB1)-1))+sizeof(object))
    #endif
    #ifdef STACK_DOWN
      #define topofframe(bottomword)  \
        (object*)((uintP)(&(bottomword))+(as_oint(bottomword)&(wbit(FB1)-1)))
    #endif
    #define uTheFramepointer(obj)  TheFramepointer(obj) # = (object*)(obj)
    #define framecode(bottomword)  (as_oint(bottomword) & minus_wbit(FB1))
    typedef oint fcint;
  #endif
# wird verwendet von EVAL, CONTROL, DEBUG

# Zur Bestimmung der Gr��e eines Frames:
# STACK_item_count(new_STACK_ptr,old_STACK_ptr)
# berechnet die Anzahl der STACK-Elemente zwischen einem �lteren Stackpointer
# old_STACK_ptr und einem neueren new_STACK_ptr.
# (Also count mit  old_STACK_ptr = new_STACK_ptr STACKop count .)
  #ifdef STACK_DOWN
    #define STACK_item_count(new_STACK_ptr,old_STACK_ptr)  \
      (uintL)((old_STACK_ptr) - (new_STACK_ptr))
  #endif
  #ifdef STACK_UP
    #define STACK_item_count(new_STACK_ptr,old_STACK_ptr)  \
      (uintL)((new_STACK_ptr) - (old_STACK_ptr))
  #endif

# Beendet einen Frame.
# finish_frame(frametype);
# > object* top_of_frame: Pointer �bern Frame
# erniedrigt STACK um 1
  #ifdef TYPECODES
    #if !defined(SINGLEMAP_MEMORY_STACK)
      #define framebottomword(type,top_of_frame,bot_of_frame)  \
        type_pointer_object(type,top_of_frame)
    #else # top_of_frame hat selber schon Typinfo system_type
      #define framebottomword(type,top_of_frame,bot_of_frame)  \
        as_object(type_zero_oint(type)-type_zero_oint(system_type)+(oint)(top_of_frame))
    #endif
    #define finish_frame(frametype)  \
      pushSTACK(framebottomword(frametype##_frame_info,top_of_frame,bot_of_frame_ignored))
  #else
    #ifdef STACK_UP
      #define framebottomword(type,top_of_frame,bot_of_frame)  \
        as_object((oint)(type)+(oint)((uintP)(bot_of_frame)-(uintP)(top_of_frame)))
    #endif
    #ifdef STACK_DOWN
      #define framebottomword(type,top_of_frame,bot_of_frame)  \
        as_object((oint)(type)+(oint)((uintP)(top_of_frame)-(uintP)(bot_of_frame)))
    #endif
    #define finish_frame(frametype)  \
      (STACK_(-1) = framebottomword(frametype##_frame_info,top_of_frame,STACK STACKop -1), skipSTACK(-1))
  #endif
# wird verwendet von EVAL, CONTROL

# Baut einen Frame f�r alle 5 Environments
# make_ENV5_frame();
# erniedrigt STACK um 5
  #define make_ENV5_frame()  \
    {var object* top_of_frame = STACK; \
     pushSTACK(aktenv.decl_env);       \
     pushSTACK(aktenv.go_env);         \
     pushSTACK(aktenv.block_env);      \
     pushSTACK(aktenv.fun_env);        \
     pushSTACK(aktenv.var_env);        \
     finish_frame(ENV5);               \
    }
# wird verwendet von EVAL, CONTROL, DEBUG

# Beendet einen Frame mit Entrypoint und setzt den Einsprungpunkt hierher.
# finish_entry_frame(frametype,returner,retval_zuweisung,reentry_statement);
# > object* top_of_frame: Pointer �bern Frame
# > jmp_buf* returner: longjmp-Buffer f�r Wiedereintritt
# > retval_zuweisung: Zuweisung des setjmp()-Wertes an eine Variable
# > reentry_statement: Was sofort nach Wiedereintritt zu tun ist.
# erniedrigt STACK um 1
  #define finish_entry_frame(frametype,returner,retval_zuweisung,reentry_statement)  \
    { pushSTACK(as_object((aint)(returner))); # SP in den Stack                 \
      pushSTACK(nullobj); # Dummy in den Stack, bis Wiedereintritt erlaubt ist  \
      begin_setjmp_call();                                                      \
      if (!((retval_zuweisung setjmpl(returner))==0)) # Wiedereinspungpunkt herstellen \
        { end_longjmp_call(); LONGJMP_RESTORE_mv_count(); LONGJMP_RESTORE_value1(); reentry_statement } # nach dem Wiedereintritt \
        else                                                                    \
        { end_setjmp_call(); STACK_0 = framebottomword(frametype##_frame_info,top_of_frame,STACK); } \
    }
# wird verwendet von EVAL, CONTROL, DEBUG

# Springt einen Frame mit Entrypoint an, der bei STACK beginnt.
# (Wichtig: Beim Einsprung muss der STACK denselben Wert haben wie beim Aufbau
# des Frames, da der STACK bei setjmp/longjmp vielleicht gerettet wird!)
# Kehrt nie zur�ck und r�umt den SP auf!!
# Die multiple values werden �bergeben.
# enter_frame_at_STACK();
  #define enter_frame_at_STACK()  \
    { var jmp_buf* returner = (jmp_buf*)(aint)as_oint(STACK_(frame_SP)); # der returner von finish_entry_frame \
      LONGJMP_SAVE_value1(); LONGJMP_SAVE_mv_count();                                                          \
      begin_longjmp_call();                                                                                    \
      longjmpl(&!*returner,(aint)returner); # dorthin springen, eigene Adresse (/=0) �bergeben                 \
      NOTREACHED                                                                                               \
    }
# wird verwendet von EVAL

# Bei Driver-Frames ist evtl. auch noch der Wert
# von NUM_STACK_normal vor Aufbau des Frames enthalten:
  typedef struct { jmp_buf returner; # zuerst - wie bei allen - der jmp_buf
                   #ifdef HAVE_NUM_STACK
                   uintD* old_NUM_STACK_normal;
                   #endif
                 }
          DRIVER_frame_data;

# UP: Wendet eine Funktion auf ihre Argumente an.
# apply(function,args_on_stack,other_args);
# > function: Funktion
# > Argumente: args_on_stack Argumente auf dem STACK,
#              restliche Argumentliste in other_args
# < STACK: aufger�umt (d.h. STACK wird um args_on_stack erh�ht)
# < mv_count/mv_space: Werte
# ver�ndert STACK, kann GC ausl�sen
  extern Values apply (object fun, uintC args_on_stack, object other_args);
# wird verwendet von EVAL, CONTROL, IO, PATHNAME, ERROR

# UP: Wendet eine Funktion auf ihre Argumente an.
# funcall(function,argcount);
# > function: Funktion
# > Argumente: argcount Argumente auf dem STACK
# < STACK: aufger�umt (d.h. STACK wird um argcount erh�ht)
# < mv_count/mv_space: Werte
# ver�ndert STACK, kann GC ausl�sen
  extern Values funcall (object fun, uintC argcount);
# wird verwendet von allen Modulen

# UP: Wertet eine Form im aktuellen Environment aus.
# eval(form);
# > form: Form
# < mv_count/mv_space: Werte
# kann GC ausl�sen
  extern Values eval (object form);
# wird verwendet von CONTROL, DEBUG

# UP: Wertet eine Form in einem gegebenen Environment aus.
# eval_5env(form,var,fun,block,go,decl);
# > var_env: Wert f�r VAR_ENV
# > fun_env: Wert f�r FUN_ENV
# > block_env: Wert f�r BLOCK_ENV
# > go_env: Wert f�r GO_ENV
# > decl_env: Wert f�r DECL_ENV
# > form: Form
# < mv_count/mv_space: Werte
# kann GC ausl�sen
  extern Values eval_5env (object form, object var_env, object fun_env, object block_env, object go_env, object decl_env);
# wird verwendet von

# UP: Wertet eine Form in einem leeren Environment aus.
# eval_noenv(form);
# > form: Form
# < mv_count/mv_space: Werte
# kann GC ausl�sen
  extern Values eval_noenv (object form);
# wird verwendet von CONTROL, IO, DEBUG, SPVW

# UP: Wertet eine Form im aktuellen Environment aus. Nimmt dabei auf
# *EVALHOOK* und *APPLYHOOK* keine R�cksicht.
# eval_no_hooks(form);
# > form: Form
# < mv_count/mv_space: Werte
# kann GC ausl�sen
  extern Values eval_no_hooks (object form);
# wird verwendet von CONTROL

# UP: bindet *EVALHOOK* und *APPLYHOOK* dynamisch an die gegebenen Werte.
# bindhooks(evalhook_value,applyhook_value);
# > evalhook_value: Wert f�r *EVALHOOK*
# > applyhook_value: Wert f�r *APPLYHOOK*
# ver�ndert STACK
  extern void bindhooks (object evalhook_value, object applyhook_value);
# wird verwendet von CONTROL

# UP: L�st einen Frame auf, auf den STACK zeigt.
# unwind();
# Die Werte mv_count/mv_space bleiben dieselben.
# Falls es kein Unwind-Protect-Frame ist: kehrt normal zur�ck.
# Falls es ein Unwind-Protect-Frame ist:
#   rettet die Werte, klettert STACK und SP hoch
#   und springt dann unwind_protect_to_save.fun an.
# ver�ndert STACK
# kann GC ausl�sen
  typedef /* nonreturning */ void (*restart)(object* upto_frame);
  typedef struct { restart fun; object* upto_frame; } unwind_protect_caller;
  #ifndef MULTITHREAD
    extern unwind_protect_caller unwind_protect_to_save;
  #else
    #define unwind_protect_to_save  (current_thread()->_unwind_protect_to_save)
  #endif
  extern void unwind (void);
# wird verwendet von CONTROL, DEBUG, SPVW

# UP: "unwindet" den STACK bis zum n�chsten DRIVER_FRAME und
# springt in die entsprechende Top-Level-Schleife.
# reset();
  nonreturning_function(extern, reset, (void));
# wird verwendet von SPVW, CONTROL

# UP: bindet dynamisch die Symbole der Liste symlist
# an die Werte aus der Liste vallist.
# progv(symlist,vallist);
# > symlist, vallist: zwei Listen
# Es wird genau ein Variablenbindungsframe aufgebaut.
# ver�ndert STACK
  extern void progv (object symlist, object vallist);
# wird verwendet von CONTROL

# UP: L�st die dynamische Schachtelung im STACK auf bis zu dem Frame
# (ausschlie�lich), auf den upto zeigt, und springt diesen dann an.
# unwind_upto(upto);
# > upto: Pointer auf einen Frame (in den Stack, ohne Typinfo).
# Rettet die Werte mv_count/mv_space.
# ver�ndert STACK,SP
# kann GC ausl�sen
# Springt dann den gefundenen Frame an.
  nonreturning_function(extern, unwind_upto, (object* upto_frame));
# wird verwendet von CONTROL, DEBUG

# UP: throwt zum Tag tag und �bergibt dabei die Werte mv_count/mv_space.
# Kommt nur dann zur�ck, wenn es keinen CATCH-Frame dieses Tags gibt.
# throw_to(tag);
  extern void throw_to (object tag);
# wird verwendet von CONTROL

# UP: Ruft alle Handler zur Condition cond auf. Kommt nur zur�ck, wenn keiner
# dieser Handler sich zust�ndig f�hlt (d.h. wenn jeder Handler zur�ckkehrt).
# invoke_handlers(cond);
# kann GC ausl�sen
  extern void invoke_handlers (object cond);
  typedef struct { object condition; object* stack; SPint* sp; object spdepth; }
          handler_args_t;
  #ifndef MULTITHREAD
    extern handler_args_t handler_args;
  #else
    #define handler_args  (current_thread()->_handler_args)
  #endif
  typedef struct stack_range { struct stack_range * next;
                               object* low_limit; object* high_limit;
                             }
          stack_range;
  #ifndef MULTITHREAD
    extern stack_range* inactive_handlers;
  #else
    #define inactive_handlers  (current_thread()->_inactive_handlers)
  #endif
# wird verwendet von ERROR

# UP: Stellt fest, ob ein Objekt ein Funktionsname, d.h. ein Symbol oder
# eine Liste der Form (SETF symbol), ist.
# funnamep(obj)
# > obj: Objekt
# < ergebnis: TRUE falls Funktionsname
  extern boolean funnamep (object obj);
# wird verwendet von CONTROL

# Liefert den zu einem Funktionsnamen geh�rigen Block-Namen.
# funname_blockname(obj)
# > obj: ein Symbol oder (SETF symbol)
# < ergebnis: Blockname, ein Symbol
  #define funname_blockname(obj)  \
    (atomp(obj) ? (obj) : Car(Cdr(obj)))

# UP: Stellt fest, ob ein Symbol im aktuellen Environment einen Macro darstellt.
# sym_macrop(symbol)
# > symbol: Symbol
# < ergebnis: TRUE falls sym einen Symbol-Macro darstellt
  extern boolean sym_macrop (object sym);
# wird verwendet von CONTROL

# UP: Setzt den Wert eines Symbols im aktuellen Environment.
# setq(symbol,value);
# > symbol: Symbol, keine Konstante
# > value: gew�nschter Wert des Symbols im aktuellen Environment
  extern void setq (object sym, object value);
# wird verwendet von CONTROL

# UP: Liefert zu einem Symbol seine Funktionsdefinition in einem Environment
# sym_function(sym,fenv)
# > sym: Funktionsname (z.B. Symbol)
# > fenv: ein Funktions- und Macrobindungs-Environment
# < ergebnis: Funktionsdefinition, entweder unbound (falls undefinierte Funktion)
#             oder Closure/SUBR/FSUBR oder ein Cons (SYS::MACRO . expander).
  extern object sym_function (object sym, object fenv);
# wird verwendet von CONTROL

# UP: "nestet" ein FUN-Environment, d.h. schreibt alle aktiven Bindungen
# aus dem Stack in neu allozierte Vektoren.
# nest_fun(env)
# > env: FUN-Env
# < ergebnis: selbes Environment, kein Pointer in den Stack
# kann GC ausl�sen
  extern object nest_fun (object env);
# wird verwendet von CONTROL

# UP: Nestet die Environments in *env (d.h. schreibt alle Informationen in
# Stack-unabh�ngige Strukturen) und schiebt sie auf den STACK.
# nest_env(env)
# > environment* env: Pointer auf f�nf einzelne Environments
# < environment* ergebnis: Pointer auf die Environments im STACK
# ver�ndert STACK, kann GC ausl�sen
  extern environment* nest_env (environment* env);
# wird verwendet von Macro nest_aktenv

# UP: Nestet die aktuellen Environments (d.h. schreibt alle Informationen in
# Stack-unabh�ngige Strukturen) und schiebt sie auf den STACK.
# (Die Werte VAR_ENV, FUN_ENV, BLOCK_ENV, GO_ENV, DECL_ENV werden nicht
# ver�ndert, da evtl. noch inaktive Bindungen in Frames sitzen, die ohne
# Ver�nderung von VAR_ENV aktiviert werden k�nnen m�ssen.)
# nest_aktenv()
# < environment* ergebnis: Pointer auf die Environments im STACK
# ver�ndert STACK, kann GC ausl�sen
  # extern environment* nest_aktenv (void);
  #define nest_aktenv()  nest_env(&aktenv)
# wird verwendet von CONTROL

# UP: Erg�nzt ein Deklarations-Environment um ein decl-spec.
# augment_decl_env(declspec,env)
# > declspec: Deklarations-Specifier, ein Cons
# > env: Deklarations-Environment
# < ergebnis: neues (evtl. augmentiertes) Deklarations-Environment
# kann GC ausl�sen
  extern object augment_decl_env (object new_declspec, object env);
# wird verwendet von CONTROL

# UP: expandiert eine Form, falls m�glich, (nicht jedoch, wenn FSUBR-Aufruf
# oder Symbol) in einem Environment
# macroexp(form,venv,fenv);
# > form: Form
# > venv: ein Variablen- und Symbolmacro-Environment
# > fenv: ein Funktions- und Macrobindungs-Environment
# < value1: die Expansion
# < value2: NIL, wenn nicht expandiert,
#           T, wenn expandiert wurde
# kann GC ausl�sen
  extern void macroexp (object form, object venv, object fenv);
# wird verwendet von CONTROL

# UP: expandiert eine Form, falls m�glich, (auch, wenn FSUBR-Aufruf)
# in einem Environment
# macroexp0(form,env);
# > form: Form
# > env: ein Macroexpansions-Environment
# < value1: die Expansion
# < value2: NIL, wenn nicht expandiert,
#           T, wenn expandiert wurde
# kann GC ausl�sen
  extern void macroexp0 (object form, object env);
# wird verwendet von CONTROL

# UP: Parse-Declarations-Docstring. Trennt von einer Formenliste diejenigen
# ab, die als Deklarationen bzw. Dokumentationsstring angesehen werden
# m�ssen.
# parse_dd(formlist,venv,fenv)
# > formlist: ( {decl|doc-string} . body )
# > venv: ein Variablen- und Symbolmacro-Environment (f�r die Macroexpansionen)
# > fenv: Funktions- und Macrobindungs-Environment (f�r die Macroexpansionen)
# < value1: body
# < value2: Liste der decl-specs
# < value3: Doc-String oder NIL
# < ergebnis: TRUE falls eine (COMPILE)-Deklaration vorkam, FALSE sonst
# kann GC ausl�sen
  extern boolean parse_dd (object formlist, object venv, object fenv);
# wird verwendet von CONTROL

# UP: Erzeugt zu einem Lambdabody die entsprechende Closure durch Zerlegen
# der Lambdaliste und eventuelles Macroexpandieren aller Formen.
# get_closure(lambdabody,name,blockp,env)
# > lambdabody: (lambda-list {decl|doc} {form})
# > name: Name, ein Symbol oder (SETF symbol)
# > blockp: ob ein impliziter BLOCK einzuschieben ist
# > env: Pointer auf die f�nf einzelnen Environments:
#        env->var_env = VENV, env->fun_env = FENV,
#        env->block_env = BENV, env->go_env = GENV,
#        end->decl_env = DENV.
# < ergebnis: Closure
# kann GC ausl�sen
  extern object get_closure (object lambdabody, object name, boolean blockp, environment* env);
# wird verwendet von CONTROL, SYMBOL, PREDTYPE

# UP: Wandelt ein Argument in eine Funktion um.
# coerce_function(obj)
# > obj: Objekt
# > subr_self: Aufrufer (ein SUBR)
# < ergebnis: Objekt als Funktion (SUBR oder Closure)
# kann GC ausl�sen
  extern object coerce_function (object obj);
# wird verwendet von IO, FOREIGN

# Bindet ein Symbol dynamisch an einen Wert.
# Baut hierzu einen dynamischen Variablenbindungsframe f�r 1 Variable auf.
# dynamic_bind(var,val)
# > var: ein Symbol
# > val: der neue Wert
# verringert STACK um 3 Eintr�ge
# ver�ndert STACK
  #define dynamic_bind(variable,val_to_use)  \
    { var object* top_of_frame = STACK;         \
      var object sym_to_bind = (variable);      \
      # Frame aufbauen:                         \
      pushSTACK(Symbol_value(sym_to_bind));     \
      pushSTACK(sym_to_bind);                   \
      finish_frame(DYNBIND);                    \
      # Wert modifizieren:                      \
      Symbol_value(sym_to_bind) = (val_to_use); \
    }
# wird verwendet von IO, EVAL, DEBUG, ERROR

# L�st einen dynamischen Variablenbindungsframe f�r 1 Variable auf.
# dynamic_unbind()
# erh�ht STACK um 3 Eintr�ge
# ver�ndert STACK
  #define dynamic_unbind()  \
    { # Wert zur�ckschreiben:              \
      Symbol_value(STACK_(1)) = STACK_(2); \
      # Frame abbauen:                     \
      skipSTACK(3);                        \
    }
# wird verwendet von IO, DEBUG

# F�hrt "implizites PROGN" aus.
# implicit_progn(body,default)
# F�hrt body als implizites PROGN aus. Falls body leer, ist default der Wert.
# kann GC ausl�sen
  #define implicit_progn(body,default)  \
    { var object rest = (body);                                          \
      if atomp(rest)                                                     \
        { value1 = (default); mv_count=1; } # default als Wert           \
        else                                                             \
          do { pushSTACK(Cdr(rest)); eval(Car(rest)); rest=popSTACK(); } \
             while (consp(rest));                                        \
    }
# wird verwendet von EVAL, CONTROL

# Maximalzahl von Parametern in einer Lambdaliste
# (= Wert von LAMBDA-PARAMETERS-LIMIT - 1)
  #define lp_limit_1  ((uintL)(bitm(intCsize)-1))

# Maximalzahl von Argumenten bei einem Funktionsaufruf
# (= Wert von CALL-ARGUMENTS-LIMIT - 1)
  #define ca_limit_1  ((uintL)(bitm(intCsize)-1))

# Der Macro LISPSPECFORM leitet eine LISP-Special-Form-Deklaration ein.
# LISPSPECFORM(name,req_anz,opt_anz,body_flag)
# > name: C-Name der Funktion und des Symbols.
# > req_anz: Anzahl der required Parameter
# > opt_anz: Anzahl der optionalen Parameter
# > body_flag: body oder nobody, zeigt an, ob &BODY vorhanden
# Siehe FSUBR.D
  #define LISPSPECFORM  LISPSPECFORM_B
# wird verwendet von CONTROL

# Der Macro LISPFUN leitet eine LISP-Funktions-Deklaration ein.
# LISPFUN(name,req_anz,opt_anz,rest_flag,key_flag,key_anz,allow_flag,keywords)
# > name: der Funktionsname (ein C-Identifier)
# > req_anz: die Anzahl der required-Parameter (eine Zahl)
# > opt_anz: die Anzahl der optional-Parameter (eine Zahl)
# > rest_flag: entweder norest oder rest, zeigt an, ob &REST vorhanden
# > key_flag: entweder nokey oder key, zeigt an, ob &KEY vorhanden
# > key_anz: Anzahl der Keyword-Parameter, eine Zahl (0 falls nokey)
# > allow_flag: entweder noallow oder allow, zeigt an, on &ALLOW-OTHER-KEYS
#               nach &KEY vorhanden (noallow falls nokey)
# > keywords: entweder NIL oder ein Ausdruck der Form v(kw(keyword1),...,kw(keywordn))
#             (NIL falls nokey)
# Siehe SUBR.D
  #define LISPFUN  LISPFUN_B
# wird verwendet von allen Modulen

# Der Macro LISPFUNN leitet eine einfache LISP-Funktions-Deklaration ein.
# LISPFUNN(name,req_anz)
# > name: der Funktionsname (ein C-Identifier)
# > req_anz: die (feste) Anzahl der Argumente (eine Zahl)
# Siehe SUBR.D
# wird verwendet von allen Modulen


# ##################### CTRLBIBL zu CONTROL.D ############################# #

# Fehler, wenn ein Block bereits verlassen wurde.
# fehler_block_left(name);
# > name: Block-Name
  nonreturning_function(extern, fehler_block_left, (object name));
# wird verwendet von EVAL

# Fehlermeldung wegen undefinierter Funktion.
# fehler_undef_function(caller,symbol);
# > caller: Aufrufer (ein Symbol)
# > symbol: Symbol oder (SETF symbol)
  nonreturning_function(extern, fehler_undef_function, (object caller, object symbol));
# wird verwendet von PREDTYPE

# ####################### ARRBIBL zu ARRAY.D ############################## #

# ARRAY-TOTAL-SIZE-LIMIT wird so gro� gew�hlt, dass die Total-Size eines
# jeden Arrays ein Fixnum (>=0, <2^oint_data_len) ist:
  #define arraysize_limit_1  ((uintL)(bitm(oint_data_len)-1))

# ARRAY-RANK-LIMIT wird so gro� gew�hlt, dass der Rang eines jeden Arrays
# ein uintWC ist:
  #define arrayrank_limit_1  ((uintL)(bitm(intWCsize)-1))

# UP: Kopiert einen Simple-Vector
# copy_svector(vector)
# > vector : Simple-Vector
# < ergebnis : neuer Simple-Vector desselben Inhalts
# kann GC ausl�sen
  extern object copy_svector (object vector);
# wird verwendet von IO, REXX

# UP: Kopiert einen Simple-Bit-Vector
# copy_sbvector(vector)
# > vector : Simple-Bit-Vector
# < ergebnis : neuer Simple-Bit-Vector desselben Inhalts
# kann GC ausl�sen
  extern object copy_sbvector (object vector);
# wird verwendet von RECORD

# UP: Bestimmt die aktive L�nge eines Vektors (wie in LENGTH)
# vector_length(vector)
# > vector: ein Vektor
# < ergebnis: seine L�nge als uintL
  extern uintL vector_length (object vector);
# wird verwendet von SEQUENCE, CHARSTRG, PREDTYPE, IO, HASHTABL, SPVW

# Wandelt element-type in einen der Standard-Typen um
# und liefert seinen Elementtyp-Code.
# eltype_code(element_type)
# > element_type: Type-Specifier
# < ergebnis: Elementtyp-Code Atype_xxx
# Standard-Typen sind die m�glichen Ergebnisse von ARRAY-ELEMENT-TYPE
# (Symbole T, BIT, CHARACTER und Listen (UNSIGNED-BYTE n)).
# Das Ergebnis ist ein Obertyp von element-type.
# kann GC ausl�sen
  extern uintB eltype_code (object element_type);
# wird verwendet von SEQUENCE

# UP: erzeugt einen Bytevektor
# allocate_byte_vector(atype,len)
# > uintB atype: Atype_nBit
# > uintL len: L�nge (in n-Bit-Bl�cken)
# < ergebnis: neuer Semi-Simple-Bytevektor dieser L�nge
# kann GC ausl�sen
  extern object allocate_byte_vector (uintB atype, uintL len);
# wird verwendet von CLX

# UP: Bildet einen Simple-Vektor mit gegebenen Elementen.
# vectorof(len)
# > uintC len: gew�nschte Vektorl�nge
# > auf STACK: len Objekte, erstes zuoberst
# < ergebnis: Simple-Vektor mit diesen Objekten
# Erh�ht STACK
# ver�ndert STACK, kann GC ausl�sen
  extern object vectorof (uintC len);
# wird verwendet von PREDTYPE

# UP: Liefert zu einem Array gegebener Gr��e den Datenvektor und den Offset.
# �berpr�ft auch, ob alle Elemente des Arrays physikalisch vorhanden sind.
# iarray_displace_check(array,size,&index)
# > object array: indirekter Array
# > uintL size: Gr��e
# < ergebnis: Datenvektor
# < index: wird um den Offset in den Datenvektor erh�ht.
  extern object iarray_displace_check (object array, uintL size, uintL* index);
# wird verwendet von IO, CHARSTRG, PREDTYPE, STREAM, SEQUENCE

# UP: Liefert zu einem Array gegebener Gr��e den Datenvektor und den Offset.
# �berpr�ft auch, ob alle Elemente des Arrays physikalisch vorhanden sind.
# array_displace_check(array,size,&index)
# > object array: Array
# > uintL size: Gr��e
# < ergebnis: Datenvektor
# < index: wird um den Offset in den Datenvektor erh�ht.
  extern object array_displace_check (object array, uintL size, uintL* index);
# wird verwendet von PATHNAME, HASHTABL, PREDTYPE, IO

# F�hrt einen AREF-Zugriff aus.
# datenvektor_aref(datenvektor,index)
# > datenvektor : ein Datenvektor (simpler Vektor oder semi-simpler Byte-Vektor)
# > index : (gepr�fter) Index in den Datenvektor
# < ergebnis : (AREF datenvektor index)
# kann GC ausl�sen
  extern object datenvektor_aref (object datenvektor, uintL index);
# wird verwendet von IO

# UP: fragt ein Bit in einem Simple-Bit-Vector ab
# if (sbvector_btst(sbvector,index)) ...
# > sbvector: ein Simple-Bit-Vector
# > index: Index (Variable, sollte < (length sbvector) sein)
  #define sbvector_btst(sbvector_from_sbvector_btst,index_from_sbvector_btst)  \
    ( # im Byte (index div 8) das Bit 7 - (index mod 8) : \
     TheSbvector(sbvector_from_sbvector_btst)->data[(uintL)(index_from_sbvector_btst)/8] \
       & bit((~(uintL)(index_from_sbvector_btst)) % 8)    \
    )
# wird verwendet von ARRAY, SEQUENCE, IO

# UP: l�scht ein Bit in einem Simple-Bit-Vector
# sbvector_bclr(sbvector,index);
# > sbvector: ein Simple-Bit-Vector
# > index: Index (Variable, sollte < (length sbvector) sein)
  #define sbvector_bclr(sbvector_from_sbvector_bclr,index_from_sbvector_bclr)  \
    ( # im Byte (index div 8) das Bit 7 - (index mod 8) l�schen: \
      TheSbvector(sbvector_from_sbvector_bclr)->data[(uintL)(index_from_sbvector_bclr)/8] \
        &= ~bit((~(uintL)(index_from_sbvector_bclr)) % 8)        \
    )
# wird verwendet von IO

# UP: setzt ein Bit in einem Simple-Bit-Vector
# sbvector_bset(sbvector,index);
# > sbvector: ein Simple-Bit-Vector
# > index: Index (Variable, sollte < (length sbvector) sein)
  #define sbvector_bset(sbvector_from_sbvector_bset,index_from_sbvector_bset)  \
    ( # im Byte (index div 8) das Bit 7 - (index mod 8) setzen: \
      TheSbvector(sbvector_from_sbvector_bset)->data[(uintL)(index_from_sbvector_bset)/8] \
        |= bit((~(uintL)(index_from_sbvector_bset)) % 8)        \
    )
# wird verwendet von SEQUENCE, IO

# UP, liefert den Element-Typ eines Arrays
# array_element_type(array)
# > array : ein Array (simple oder nicht)
# < ergebnis : Element-Typ, eines der Symbole T, BIT, CHARACTER, oder eine Liste
# kann GC ausl�sen
  extern object array_element_type (object array);
# wird verwendet von PREDTYPE, IO

# UP, bildet Liste der Dimensionen eines Arrays
# array_dimensions(array)
# > array: ein Array (simple oder nicht)
# < ergebnis: Liste seiner Dimensionen
# kann GC ausl�sen
  extern object array_dimensions (object array);
# wird verwendet von PREDTYPE, IO

# UP, liefert Dimensionen eines Arrays und ihre Teilprodukte
# array_dims_sizes(array,&dims_sizes);
# > array: (echter) Array vom Rang r
# > struct { uintL dim; uintL dimprod; } dims_sizes[r]: Platz f�rs Ergebnis
# < f�r i=1,...r:  dims_sizes[r-i] = { Dim_i, Dim_i * ... * Dim_r }
  typedef struct { uintL dim; uintL dimprod; }  array_dim_size;
  extern void array_dims_sizes (object array, array_dim_size* dims_sizes);
# wird verwendet von IO

# Liefert die Gesamtgr��e eines Arrays
# array_total_size(array)
# > array: ein Array (simple oder nicht)
# < uintL ergebnis: seine Gesamtgr��e
  #define array_total_size(array)  \
    (array_simplep(array)                                                    \
      ? Sarray_length(array) # simpler Vektor: L�nge                         \
      : TheIarray(array)->totalsize # nicht-simpler Array enth�lt Total-Size \
    )
# wird verwendet von ARRAY, PREDTYPE, IO, SEQUENCE

# Unterprogramm f�r Bitvektor-Vergleich:
# bit_compare(array1,index1,array2,index2,count)
# > array1: erster Bit-Array,
# > index1: absoluter Index in array1
# > array2: zweiter Bit-Array,
# > index2: absoluter Index in array2
# > count: Anzahl der zu vergleichenden Bits
# < ergebnis: TRUE, wenn die Ausschnitte bitweise gleich sind, FALSE sonst.
  extern boolean bit_compare (object array1, uintL index1,
                              object array2, uintL index2,
                              uintL bitcount);
# wird verwendet von PREDTYPE

# UP: Testet, ob ein Array einen Fill-Pointer hat.
# array_has_fill_pointer_p(array)
# > array: ein Array
# < TRUE, falls ja; FALSE falls nein.
  extern boolean array_has_fill_pointer_p (object array);
# wird verwendet von SEQUENCE, STREAM, IO

# UP: erzeugt einen mit Nullen gef�llten Bitvektor
# allocate_bit_vector_0(len)
# > uintL len: L�nge des Bitvektors (in Bits)
# < ergebnis: neuer Bitvektor, mit Nullen gef�llt
# kann GC ausl�sen
  extern object allocate_bit_vector_0 (uintL len);
# wird verwendet von SEQUENCE

# Folgende beide Funktionen arbeiten auf "Semi-Simple String"s.
# Das sind CHARACTER-Arrays mit FILL-POINTER, die aber nicht adjustierbar
# und nicht displaced sind und deren Datenvektor ein Simple-String ist.
# Beim �berschreiten der L�nge wird ihre L�nge verdoppelt
# (so dass der Aufwand f�rs Erweitern nicht sehr ins Gewicht f�llt).

# UP: Liefert einen Semi-Simple String gegebener L�nge, Fill-Pointer =0.
# make_ssstring(len)
# > uintL len: L�nge >0
# < ergebnis: neuer Semi-Simple String dieser L�nge
# kann GC ausl�sen
  extern object make_ssstring (uintL len);
# wird verwendet von STREAM, IO

# UP: Schiebt ein Character in einen Semi-Simple String und erweitert ihn
# dabei eventuell.
# ssstring_push_extend(ssstring,ch)
# > ssstring: Semi-Simple String
# > ch: Character
# < ergebnis: derselbe Semi-Simple String
# kann GC ausl�sen
  extern object ssstring_push_extend (object ssstring, chart ch);
# wird verwendet von STREAM, IO

# UP: Stellt sicher, dass ein Semi-Simple String eine bestimmte L�nge hat
# und erweitert ihn dazu eventuell.
# ssstring_extend(ssstring,size)
# > ssstring: Semi-Simple String
# > size: gew�nschte Mindestgr��e
# < ergebnis: derselbe Semi-Simple String
# kann GC ausl�sen
  extern object ssstring_extend (object ssstring, uintL needed_len);
# wird verwendet von STREAM

# Folgende beide Funktionen arbeiten auf "Semi-Simple Byte-Vector"s.
# Das sind Simple-Bit-Arrays mit Fill-Pointer, die aber nicht adjustierbar
# und nicht displaced sind und deren Datenvektor ein Simple-Bit-Vektor ist.
# Beim �berschreiten der L�nge wird ihre L�nge verdoppelt
# (so dass der Aufwand f�rs Erweitern nicht sehr ins Gewicht f�llt).

# UP: Liefert einen Semi-Simple Byte-Vector mit len Bytes, Fill-Pointer =0.
# make_ssbvector(len)
# > uintL len: L�nge (in Bytes!) >0
# < ergebnis: neuer Semi-Simple Byte-Vector dieser L�nge
# kann GC ausl�sen
  extern object make_ssbvector (uintL len);
# wird verwendet von IO

# UP: Schiebt ein Byte in einen Semi-Simple Byte-Vector und erweitert ihn
# dabei eventuell.
# ssbvector_push_extend(ssbvector,b)
# > ssbvector: Semi-Simple Byte-Vector
# > b: Byte
# < ergebnis: derselbe Semi-Simple Byte-Vector
# kann GC ausl�sen
  extern object ssbvector_push_extend (object ssbvector, uintB b);
# wird verwendet von IO

# ##################### CHARBIBL zu CHARSTRG.D ############################ #

# Spezielle Characters: (siehe auch oben)
# #define BEL   7  #  #\Bell
# #define BS    8  #  #\Backspace
# #define TAB   9  #  #\Tab
# #define LF   10  #  #\Linefeed
# #define CR   13  #  #\Return
# #define PG   12  #  #\Page
  #define NL   10  #  #\Newline
  #define NLstring  "\n"  # C-String, der #\Newline enth�lt
  #define ESC  27  #  #\Escape
  #define ESCstring  "\033"  # C-String, der #\Escape enth�lt

# Wandelt Byte ch in einen Gro�buchstaben
# up_case(ch)
  extern chart up_case (chart ch);
# wird verwendet von IO, PREDTYPE, PATHNAME

# Wandelt Byte ch in einen Kleinbuchstaben
# down_case(ch)
  extern chart down_case (chart ch);
# wird verwendet von IO, PATHNAME

# Stellt fest, ob ein Character alphanumerisch ist.
# alphanumericp(ch)
# > ch: Character-Code
# < ergebnis: TRUE falls alphanumerisch, FALSE sonst.
  extern boolean alphanumericp (chart ch);
# wird verwendet von IO, PATHNAME

# Stellt fest, ob ein Character ein Graphic-Character ("druckend") ist.
# graphic_char_p(ch)
# > ch: Character-Code
# < ergebnis: TRUE falls druckend, FALSE sonst.
  extern boolean graphic_char_p (chart ch);
# wird verwendet von STREAM, PATHNAME

# UP: verfolgt einen String.
# unpack_string(string,&len)
# > object string: ein String.
# < uintL len: Anzahl der Zeichen des Strings.
# < chart* ergebnis: Anfangsadresse der Characters
  extern chart* unpack_string (object string, uintL* len);
# wird verwendet von STREAM, HASHTABL, PACKAGE, SPVW, GRAPH

# UP: vergleicht zwei Strings auf Gleichheit
# string_gleich(string1,string2)
# > string1: String
# > string2: simple-string
# < ergebnis: /=0, wenn gleich
  extern boolean string_gleich (object string1, object string2);
# wird verwendet von PACKAGE, STREAM, IO

# UP: vergleicht zwei Strings auf Gleichheit, case-insensitive
# string_equal(string1,string2)
# > string1: String
# > string2: simple-string
# < ergebnis: /=0, wenn gleich
  extern boolean string_equal (object string1, object string2);
# wird verwendet von IO, PATHNAME

# UP: kopiert einen String und macht dabei einen Simple-String draus.
# copy_string(string)
# > string: String
# < ergebnis: Simple-String mit denselben Zeichen
# kann GC ausl�sen
  extern object copy_string (object string);
# wird verwendet von IO, PATHNAME

# UP: wandelt einen String in einen Simple-String um.
# coerce_ss(obj)
# > obj: Lisp-Objekt, sollte ein String sein.
# < ergebnis: Simple-String mit denselben Zeichen
# kann GC ausl�sen
  extern object coerce_ss (object obj);
# wird verwendet von STREAM, PATHNAME, PACKAGE

# UP: Konversion eines Objekts zu einem Character
# coerce_char(obj)
# > obj: Lisp-Objekt
# < ergebnis: Character oder NIL
  extern object coerce_char (object obj);
# wird verwendet von PREDTYPE

# UP: Liefert den Namen eines Zeichens.
# char_name(code)
# > chart code: Code eines Zeichens
# < ergebnis: Simple-String (Name dieses Zeichens) oder NIL
  extern object char_name (chart code);
# wird verwendet von IO

# UP: Bestimmt das Character mit einem gegebenen Namen
# name_char(string)
# > string: String
# < ergebnis: Character mit diesem Namen, oder NIL falls keins existiert
  extern object name_char (object string);
# wird verwendet von IO

# UP: �berpr�ft die Grenzen f�r ein String-Argument
# test_string_limits(&string,&start,&len)
# > STACK_2: String-Argument
# > STACK_1: optionales :start-Argument
# > STACK_0: optionales :end-Argument
# > subr_self: Aufrufer (ein SUBR)
# < object string: String
# < uintL start: Wert des :start-Arguments
# < uintL len: Anzahl der angesprochenen Characters
# < chart* ergebnis: Ab hier kommen die angesprochenen Characters
# erh�ht STACK um 3
  extern chart* test_string_limits (object* string_, uintL* start_, uintL* len_);
# wird verwendet von STREAM, PATHNAME, IO

# UP: wandelt die Characters eines Stringst�cks in Gro�buchstaben
# nstring_upcase(charptr,len);
# > chart* charptr: Ab hier kommen die angesprochenen Characters
# > uintL len: Anzahl der angesprochenen Characters
  extern void nstring_upcase (chart* charptr, uintL len);
# wird verwendet von

# UP: wandelt die Characters eines Stringst�cks in Kleinbuchstaben
# nstring_downcase(charptr,len);
# > chart* charptr: Ab hier kommen die angesprochenen Characters
# > uintL len: Anzahl der angesprochenen Characters
  extern void nstring_downcase (chart* charptr, uintL len);
# wird verwendet von PATHNAME

# UP: wandelt die Worte eines Stringst�cks in solche, die
# mit Gro�buchstaben anfangen und mit Kleinbuchstaben weitergehen.
# nstring_capitalize(charptr,len);
# > chart* charptr: Ab hier kommen die angesprochenen Characters
# > uintL len: Anzahl der angesprochenen Characters
  extern void nstring_capitalize (chart* charptr, uintL len);
# wird verwendet von PATHNAME

# UP: wandelt einen String in Gro�buchstaben
# string_upcase(string)
# > string: String
# < ergebnis: neuer Simple-String, in Gro�buchstaben
# kann GC ausl�sen
  extern object string_upcase (object string);
# wird verwendet von MISC, PATHNAME

# UP: wandelt einen String in Kleinbuchstaben
# string_downcase(string)
# > string: String
# < ergebnis: neuer Simple-String, in Kleinbuchstaben
# kann GC ausl�sen
  extern object string_downcase (object string);
# wird verwendet von PATHNAME

# Returns a substring of a simple-string.
# subsstring(string,start,end)
# > object string: a simple-string
# > uintL start: start index
# > uintL end: end index
# with 0 <= start <= end <= Sstring_length(string)
# < object result: (subseq string start end), a freshly created simple-string
  extern object subsstring (object string, uintL start, uintL end);
# wird verwendet von PATHNAME

# UP: bildet einen aus mehreren Strings zusammengeh�ngten String.
# string_concat(argcount)
# > uintC argcount: Anzahl der Argumente
# > auf dem STACK: die Argumente (sollten Strings sein)
# > subr_self: Aufrufer (ein SUBR) (unn�tig, falls alle Argumente Strings sind)
# < ergebnis: Gesamtstring, neu erzeugt
# < STACK: aufger�umt
# kann GC ausl�sen
  extern object string_concat (uintC argcount);
# wird verwendet von PACKAGE, PATHNAME, DEBUG, SYMBOL

# ###################### DEBUGBIB zu DEBUG.D ############################ #

# Startet den normalen Driver (Read-Eval-Print-Loop)
# driver();
  extern void driver (void);
# wird verwendet von SPVW

# Startet einen untergeordneten Driver (Read-Eval-Print-Loop)
# break_driver(continuable);
# > continuable: Flag, ob nach Beendigung des Drivers fortgefahren werden kann.
# kann GC ausl�sen
  extern void break_driver (object continuable);
# wird verwendet von ERROR, EVAL

# ##################### HASHBIBL zu HASHTABL.D ########################## #

# UP: Sucht ein Objekt in einer Hash-Tabelle.
# gethash(obj,ht)
# > obj: Objekt, als Key
# > ht: Hash-Tabelle
# < ergebnis: zugeh�riger Value, falls gefunden, nullobj sonst
  extern object gethash (object obj, object ht);
# wird verwendet von EVAL, RECORD, PATHNAME, FOREIGN

# UP: Sucht ein Key in einer Hash-Tabelle und liefert den vorigen Wert.
# shifthash(ht,obj,value) == (SHIFTF (GETHASH obj ht) value)
# > ht: Hash-Tabelle
# > obj: Objekt
# > value: neuer Wert
# < ergebnis: alter Wert
# kann GC ausl�sen
  extern object shifthash (object ht, object obj, object value);
# wird verwendet von SEQUENCE, PATHNAME, FOREIGN

# Macro: Durchl�uft eine Hash-Tabelle.
# map_hashtable(ht,key,value,statement)
# map_hashtable_nogc(ht,key,value,statement)
# > ht: Hash-Tabelle
# Ruft statement auf, wobei key und value jeweils ein Paar aus der Tabelle
# sind. Die erste Form ist n�tig, wenn das statement GC ausl�sen kann.
  #define map_hashtable(ht,key,value,statement)  \
    { var object ht_from_map_hashtable = (ht);                              \
      var uintL index_from_map_hashtable =                                  \
        2*posfixnum_to_L(TheHashtable(ht_from_map_hashtable)->ht_maxcount); \
      pushSTACK(TheHashtable(ht_from_map_hashtable)->ht_kvtable);           \
      loop                                                                  \
        { if (index_from_map_hashtable==0) break;                           \
          index_from_map_hashtable -= 2;                                    \
          { var object* KVptr_from_map_hashtable = &TheSvector(STACK_0)->data[index_from_map_hashtable]; \
            var object key = KVptr_from_map_hashtable[0];                   \
            if (!eq(key,unbound))                                           \
              { var object value = KVptr_from_map_hashtable[1];             \
                statement;                                                  \
        } }   }                                                             \
      skipSTACK(1);                                                         \
    }
  #define map_hashtable_nogc(ht,key,value,statement)  \
    { var object ht_from_map_hashtable = (ht);                              \
      var uintL index_from_map_hashtable =                                  \
        posfixnum_to_L(TheHashtable(ht_from_map_hashtable)->ht_maxcount);   \
      var object* KVptr_from_map_hashtable =                                \
        &TheSvector(TheHashtable(ht_from_map_hashtable)->ht_kvtable)->data[2*index_from_map_hashtable]; \
      loop                                                                  \
        { if (index_from_map_hashtable==0) break;                           \
          index_from_map_hashtable--; KVptr_from_map_hashtable -= 2;        \
          { var object key = KVptr_from_map_hashtable[0];                   \
            if (!eq(key,unbound))                                           \
              { var object value = KVptr_from_map_hashtable[1];             \
                statement;                                                  \
        } }   }                                                             \
    }
# wird verwendet von

# ######################### IOBIBL zu IO.D ############################## #

# spezielles Objekt, das EOF anzeigt
  #define eof_value  make_system(0xE0FE0FUL)
# wird verwendet von IO, STREAM, DEBUG, SPVW

# Hilfswert zum Erkennen einzelner Dots
  #define dot_value  make_system(0xD0DD0DUL)
# wird verwendet von IO, SPVW

# UP: Initialisiert den Reader.
# init_reader();
# kann GC ausl�sen
  extern void init_reader (void);
# wird verwendet von SPVW

# UP: Liest ein Objekt ein.
# stream_read(&stream,recursive-p,whitespace-p)
# > recursive-p: gibt an, ob rekursiver Aufruf von READ, mit Error bei EOF
# > whitespace-p: gibt an, ob danach whitespace zu verbrauchen ist
# > stream: Stream
# < stream: Stream
# < ergebnis: gelesenes Objekt (eof_value bei EOF, dot_value bei einzelnem Punkt)
# kann GC ausl�sen
  extern object stream_read (const object* stream_, object recursive_p, object whitespace_p);
# wird verwendet von SPVW, DEBUG

# UP: Gibt einen Simple-String elementweise auf einen Stream aus.
# write_sstring(&stream,string);
# > string: Simple-String
# > stream: Stream
# < stream: Stream
# kann GC ausl�sen
  extern void write_sstring (const object* stream_, object string);
# wird verwendet von EVAL, DEBUG, ERROR, PACKAGE, SPVW

# UP: Gibt einen String elementweise auf einen Stream aus.
# write_string(&stream,string);
# > string: String
# > stream: Stream
# < stream: Stream
# kann GC ausl�sen
  extern void write_string (const object* stream_, object string);
# wird verwendet von PACKAGE, DEBUG

# UP: Gibt ein Objekt auf einen Stream aus.
# prin1(&stream,obj);
# > obj: Objekt
# > stream: Stream
# < stream: Stream
# kann GC ausl�sen
  extern void prin1 (const object* stream_, object obj);
# wird verwendet von EVAL, DEBUG, PACKAGE, ERROR, SPVW

# UP: Gibt ein Newline auf einen Stream aus.
# terpri(&stream);
# > stream: Stream
# < stream: Stream
# kann GC ausl�sen
  # extern void terpri (const object* stream_);
  #define terpri(stream_)  write_ascii_char(stream_,NL)
# wird verwendet von IO, DEBUG, PACKAGE, ERROR, SPVW

# ####################### LISTBIBL zu LIST.D ############################## #

# UP: Kopiert eine Liste
# copy_list(list)
# > list: Liste
# < ergebnis: Kopie der Liste
# kann GC ausl�sen
  extern object copy_list (object list);
# wird verwendet von PACKAGE

# UP: Dreht eine Liste konstruktiv um.
# reverse(list)
# > list: Liste (x1 ... xm)
# < ergebnis: umgedrehte Liste (xm ... x1)
# kann GC ausl�sen
  extern object reverse (object list);
# wird verwendet von SEQUENCE, PACKAGE, PATHNAME

# UP: Bestimmt die L�nge einer Liste
# llength(obj)
# > obj: Objekt
# < uintL ergebnis: L�nge von obj, als Liste aufgefasst
# Testet nicht auf zyklische Listen.
  extern uintL llength (object obj);
# wird verwendet von CONTROL, EVAL, SEQUENCE, RECORD, IO, PACKAGE, HASHTABL, STREAM

# UP: Bildet eine Liste mit genau len Elementen
# make_list(len)
# > (STACK): Initialisierungswert f�r die Elemente
# > uintL len: gew�nschte Listenl�nge
# < ergebnis: Liste mit D1.L Elementen
# kann GC ausl�sen
  extern object make_list (uintL len);
# wird verwendet von

# UP: Dreht eine Liste destruktiv um.
# nreverse(list)
# > list: Liste (x1 ... xm)
# < ergebnis: Liste (xm ... x1), EQ zur alten
  extern object nreverse (object list);
# wird verwendet von SEQUENCE, EVAL, CONTROL, IO, PATHNAME, ERROR, DEBUG, PACKAGE

# UP: A0 := (nreconc A0 A1)
# nreconc(list,obj)
# > list: Liste
# > obj: Objekt
# < ergebnis: (nreconc A0 A1)
  extern object nreconc (object list, object obj);
# wird verwendet von SEQUENCE, IO, PATHNAME, CONTROL, DEBUG

# UP: Bilde (delete obj (the list list) :test #'EQ)
# deleteq(list,obj)
# Entferne aus der Liste list alle Elemente, die EQ zu obj sind.
# > obj: zu streichendes Element
# > list: Liste
# < ergebnis: modifizierte Liste
  extern object deleteq (object list, object obj);
# wird verwendet von PACKAGE, STREAM

# UP: Bildet eine Liste mit gegebenen Elementen.
# listof(len)
# > uintC len: gew�nschte Listenl�nge
# > auf STACK: len Objekte, erstes zuoberst
# < ergebnis: Liste dieser Objekte
# Erh�ht STACK
# ver�ndert STACK, kann GC ausl�sen
  extern object listof (uintC len);
# wird verwendet von STREAM, PATHNAME, PACKAGE, ARRAY, EVAL, PREDTYPE, REXX, ERROR, SPVW

# ####################### MISCBIBL zu MISC.D ############################## #

# ####################### ERRBIBL zu ERROR.D ############################## #

# Klassifikation der bekannten Condition-Typen:
# (Genauer gesagt, handelt es sich hier immer um die SIMPLE-... Typen.)
  typedef enum
  {
    # all kinds of conditions
    condition,
      # conditions that require interactive intervention
      serious_condition,
        # serious conditions that occur deterministically
        error,
          # mostly statically detectable errors of a program
          program_error,
            # statically detectable errors of a program, source available
            source_program_error,
          # not statically detectable errors in program control
          control_error,
          # errors that occur while doing arithmetic operations
          arithmetic_error,
            # trying to evaluate a mathematical function at a singularity
            division_by_zero,
            # trying to get too close to infinity in the floating point domain
            floating_point_overflow,
            # trying to get too close to zero in the floating point domain
            floating_point_underflow,
          # trying to access a location which contains #<UNBOUND>
          cell_error,
            # trying to get the value of an unbound variable
            unbound_variable,
            # trying to get the global function definition of an undefined function
            undefined_function,
            # trying to get the value of an unbound slot
            unbound_slot,
          # when some datum does not belong to the expected type
          type_error,
            # when some keyword does not belong to one of the allowed keywords
            keyword_error,
          # errors during operation on packages
          package_error,
          # attempted violation of *PRINT-READABLY*
          print_not_readable,
          # errors related to parsing
          parse_error,
          # errors while doing stream I/O
          stream_error,
            # unexpected end of stream
            end_of_file,
          # errors with pathnames, OS level errors with streams
          file_error,
        # "Virtual memory exhausted"
        storage_condition,
      # conditions for which user notification is appropriate
      warning,
    # junk
    condition_for_broken_compilers_that_dont_like_trailing_commas
  }
  conditiontype;

# Fehlermeldung mit Errorstring. Kehrt nicht zur�ck.
# fehler(errortype,errorstring);
# > errortype: Condition-Typ
# > errorstring: Konstanter ASCIZ-String.
#   Bei jeder Tilde wird ein LISP-Objekt vom STACK genommen und statt der
#   Tilde ausgegeben.
# > auf dem STACK: Initialisierungswerte f�r die Condition, je nach errortype
  nonreturning_function(extern, fehler, (conditiontype errortype, const char * errorstring));
# wird von allen Modulen verwendet

# Just like OS_error, but signal a FILE-ERROR.
# OS_file_error(pathname);
# > pathname: Pathname
# > end_system_call() already called
  nonreturning_function(extern, OS_file_error, (object pathname));
#if defined(DEBUG_OS_ERROR)
  # Show the file and line number of the caller of OS_file_error(). For debugging.
  #define OS_file_error(pathname)  \
    (asciz_out_s("\n[%s:",__FILE__), asciz_out_1("%d] ",__LINE__), (OS_file_error)(pathname))
#endif

# Just like OS_error, but takes a file stream and signals a FILE-ERROR.
# OS_filestream_error(stream);
# > stream: a file stream
# > end_system_call() already called
  nonreturning_function(extern, OS_filestream_error, (object stream));
#if defined(DEBUG_OS_ERROR)
  # Show the file and line number of the caller of OS_filestream_error(). For debugging.
  #define OS_filestream_error(stream)  \
    (asciz_out_s("\n[%s:",__FILE__), asciz_out_1("%d] ",__LINE__), (OS_filestream_error)(stream))
#endif

#if defined(UNIX) || defined(DJUNIX) || defined(EMUNIX) || defined(WATCOM) || defined(RISCOS)
  # Ausgabe eines Fehlers, direkt �bers Betriebssystem
  # errno_out(errorcode);
  # > int errorcode: Fehlercode
    extern void errno_out (int errorcode);
#endif
#if defined(AMIGAOS)
  # Ausgabe eines Fehlers, direkt �bers Betriebssystem
  # errno_out(errorcode);
  # > LONG errorcode: Fehlercode
    extern void errno_out (LONG errorcode);
#endif
#if defined(WIN32_NATIVE)
  # Ausgabe eines Fehlers, direkt �bers Betriebssystem
  # errno_out(errorcode);
  # > DWORD errorcode: Fehlercode
    extern void errno_out (DWORD errorcode);
#endif

# UP: F�hrt eine Break-Schleife wegen Tastaturunterbrechung aus.
# > -(STACK) : aufrufende Funktion
# ver�ndert STACK, kann GC ausl�sen
  extern void tast_break (void);
# wird verwendet von EVAL, IO, SPVW, STREAM

# Fehlermeldung, wenn ein Objekt keine Liste ist.
# fehler_list(obj);
# > obj: Nicht-Liste
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(extern, fehler_list, (object obj));
# wird verwendet von LIST, EVAL

# Fehlermeldung, wenn ein Objekt keine echte Liste ist.
# fehler_proper_list(obj);
# > obj: Ende der Liste, Nicht-Liste
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(extern, fehler_proper_list, (object obj));
# wird verwendet von LIST

# Fehlermeldung, wenn ein Objekt kein Symbol ist.
# fehler_kein_symbol(caller,obj);
# > caller: Aufrufer (ein Symbol)
# > obj: Nicht-Symbol
  nonreturning_function(extern, fehler_kein_symbol, (object caller, object obj));
# wird verwendet von EVAL, CONTROL

# Fehlermeldung, wenn ein Objekt kein Symbol ist.
# fehler_symbol(obj);
# > subr_self: Aufrufer (ein SUBR oder FSUBR)
# > obj: Nicht-Symbol
  nonreturning_function(extern, fehler_symbol, (object obj));
# wird verwendet von SYMBOL, CONTROL

# Fehlermeldung, wenn ein Objekt kein Simple-Vector ist.
# fehler_kein_svector(caller,obj);
# > caller: Aufrufer (ein Symbol)
# > obj: Nicht-Svector
  nonreturning_function(extern, fehler_kein_svector, (object caller, object obj));
# wird verwendet von ARRAY, EVAL

# Fehlermeldung, wenn ein Objekt kein Vektor ist.
# fehler_vector(obj);
# > subr_self: Aufrufer (ein SUBR)
# > obj: Nicht-Vektor
  nonreturning_function(extern, fehler_vector, (object obj));
# wird verwendet von ARRAY

# Fehlermeldung, falls ein Argument kein Fixnum >=0 ist:
# fehler_posfixnum(obj);
# > obj: Das fehlerhafte Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(extern, fehler_posfixnum, (object obj));
# wird verwendet von STREAM

# Fehlermeldung, falls ein Argument kein Character ist:
# fehler_char(obj);
# > obj: Das fehlerhafte Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(extern, fehler_char, (object obj));
# wird verwendet von CHARSTRG

# Fehlermeldung, falls ein Argument kein String ist:
# fehler_string(obj);
# > obj: Das fehlerhafte Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(extern, fehler_string, (object obj));
# wird verwendet von CHARSTRG, FOREIGN

# Fehlermeldung, falls ein Argument kein Simple-String ist:
# fehler_sstring(obj);
# > obj: Das fehlerhafte Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(extern, fehler_sstring, (object obj));
# wird verwendet von CHARSTRG

# Fehlermeldung, wenn ein Argument kein Stream ist:
# fehler_stream(obj);
# > obj: Das fehlerhafte Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(extern, fehler_stream, (object obj));
# wird verwendet von IO, STREAM, DEBUG

# Fehlermeldung, wenn ein Argument kein Stream vom geforderten Stream-Typ ist:
# fehler_streamtype(obj,type);
# > obj: Das fehlerhafte Argument
# > type: geforderter Stream-Typ
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(extern, fehler_streamtype, (object obj, object type));
# wird verwendet von STREAM

# Fehlermeldung, wenn ein Argument ein Lambda-Ausdruck statt einer Funktion ist:
# fehler_lambda_expression(obj);
# obj: Das fehlerhafte Argument
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(extern, fehler_lambda_expression, (object obj));
# wird verwendet von EVAL, SYMBOL

#ifdef HAVE_FFI
# �berpr�fung eines Arguments
# check_...(obj);
# > obj: Argument
# > subr_self: Aufrufer (ein SUBR)
# obj sollte eine Variable sein
  #define check_char(obj)  \
    if (!charp(obj)) { fehler_char(obj); }
  #define check_uint8(obj)  \
    if (!uint8_p(obj)) { fehler_uint8(obj); }
  #define check_sint8(obj)  \
    if (!sint8_p(obj)) { fehler_sint8(obj); }
  #define check_uint16(obj)  \
    if (!uint16_p(obj)) { fehler_uint16(obj); }
  #define check_sint16(obj)  \
    if (!sint16_p(obj)) { fehler_sint16(obj); }
  #define check_uint32(obj)  \
    if (!uint32_p(obj)) { fehler_uint32(obj); }
  #define check_sint32(obj)  \
    if (!sint32_p(obj)) { fehler_sint32(obj); }
  #define check_uint64(obj)  \
    if (!uint64_p(obj)) { fehler_uint64(obj); }
  #define check_sint64(obj)  \
    if (!sint64_p(obj)) { fehler_sint64(obj); }
  #define check_uint(obj)  \
    if (!uint_p(obj)) { fehler_uint(obj); }
  #define check_sint(obj)  \
    if (!sint_p(obj)) { fehler_sint(obj); }
  #define check_ulong(obj)  \
    if (!ulong_p(obj)) { fehler_ulong(obj); }
  #define check_slong(obj)  \
    if (!slong_p(obj)) { fehler_slong(obj); }
  #define check_ffloat(obj)  \
    if (!single_float_p(obj)) { fehler_ffloat(obj); }
  #define check_dfloat(obj)  \
    if (!double_float_p(obj)) { fehler_dfloat(obj); }
  nonreturning_function(extern, fehler_uint8, (object obj));
  nonreturning_function(extern, fehler_sint8, (object obj));
  nonreturning_function(extern, fehler_uint16, (object obj));
  nonreturning_function(extern, fehler_sint16, (object obj));
  nonreturning_function(extern, fehler_uint32, (object obj));
  nonreturning_function(extern, fehler_sint32, (object obj));
  nonreturning_function(extern, fehler_uint64, (object obj));
  nonreturning_function(extern, fehler_sint64, (object obj));
  nonreturning_function(extern, fehler_uint, (object obj));
  nonreturning_function(extern, fehler_sint, (object obj));
  nonreturning_function(extern, fehler_ulong, (object obj));
  nonreturning_function(extern, fehler_slong, (object obj));
  nonreturning_function(extern, fehler_ffloat, (object obj));
  nonreturning_function(extern, fehler_dfloat, (object obj));
# wird verwendet vom FFI
#endif

# ##################### PACKBIBL zu PACKAGE.D ############################# #

# UP: testet, ob ein Symbol in einer Package accessible ist und dabei nicht
# von einem anderen Symbol desselben Namens verdeckt wird.
# accessiblep(sym,pack)
# > sym: Symbol
# > pack: Package
# < ergebnis: TRUE falls sym in pack accessible und nicht verdeckt ist,
#             FALSE sonst
  extern boolean accessiblep (object sym, object pack);
# wird verwendet von IO

# UP: testet, ob ein Symbol in einer Package als externes Symbol accessible
# ist.
# externalp(sym,pack)
# > sym: Symbol
# > pack: Package
# < ergebnis: TRUE falls sym in pack als externes Symbol accessible ist,
#             FALSE sonst
  extern boolean externalp (object sym, object pack);
# wird verwendet von IO

# UP: sucht ein externes Symbol gegebenen Printnamens in einer Package.
# find_external_symbol(string,pack,&sym)
# > string: String
# > pack: Package
# < ergebnis: TRUE, falls ein externes Symbol dieses Printnamens in pack gefunden.
# < sym: dieses Symbol, falls gefunden.
  extern boolean find_external_symbol (object string, object pack, object* sym_);
# wird verwendet von IO

# UP: sucht eine Package mit gegebenem Namen oder Nickname
# find_package(string)
# > string: String
# < ergebnis: Package mit diesem Namen oder NIL
  extern object find_package (object string);
# wird verwendet von IO, EVAL

# UP: Interniert ein Symbol gegebenen Printnamens in einer Package.
# intern(string,pack,&sym)
# > string: String
# > pack: Package
# < sym: Symbol
# < ergebnis: 0, wenn nicht gefunden, sondern neu erzeugt
#             1, wenn als externes Symbol vorhanden
#             2, wenn vererbt �ber use-list
#             3, wenn als internes Symbol vorhanden
# kann GC ausl�sen
  extern uintBWL intern (object string, object pack, object* sym_);
# wird verwendet von IO, SPVW

# UP: Interniert ein Symbol gegebenen Printnamens in der Keyword-Package.
# intern_keyword(string)
# > string: String
# < ergebnis: Symbol, ein Keyword
# kann GC ausl�sen
  extern object intern_keyword (object string);
# wird verwendet von IO, EVAL, GRAPH

# UP: Importiert ein Symbol in eine Package
# import(&sym,&pack);
# > sym: Symbol (im STACK)
# > pack: Package (im STACK)
# < sym: Symbol, EQ zum alten
# < pack: Package, EQ zur alten
# kann GC ausl�sen
  extern void import (const object* sym_, const object* pack_);
# wird verwendet von SPVW

# UP: Exportiert ein Symbol aus einer Package
# export(&sym,&pack);
# > sym: Symbol (im STACK)
# > pack: Package (im STACK)
# < sym: Symbol, EQ zum alten
# < pack: Package, EQ zur alten
# kann GC ausl�sen
  extern void export (const object* sym_, const object* pack_);
# wird verwendet von SPVW

# UP: liefert die aktuelle Package
# get_current_package()
# < ergebnis: aktuelle Package
  extern object get_current_package (void);
# wird verwendet von IO, EVAL

# UP: Initialisiert die Packageverwaltung
# init_packages();
  extern void init_packages (void);
# wird verwendet von SPVW

# ##################### PATHBIBL zu PATHNAME.D ############################ #

# UP: Liefert den Directory-Namestring eines halbwegs �berpr�ften Pathname
#     unter der Annahme, dass das Directory dieses Pathname existiert,
#     im Betriebssystem-Format.
# assume_dir_exists()
# > STACK_0: absoluter Pathname, halbwegs �berpr�ft
# < STACK_0: (evtl. derselbe) Pathname, noch besser aufgel�st
# < ergebnis:
#     falls Name=NIL: Directory-Namestring (f�rs BS)
#     falls Name/=NIL: Namestring (f�r BS, mit Nullbyte am Schluss)
# kann GC ausl�sen
  extern object assume_dir_exists (void);
# wird verwendet von STREAM

# UP: Initialisiert das Pathname-System.
# init_pathnames();
# kann GC ausl�sen
  extern void init_pathnames (void);
# wird verwendet von SPVW

# Sucht das ausf�hrbare Programm sofort nach Programmstart zu lokalisieren.
# find_executable(argv[0])
  extern int find_executable (const char * program_name);
# wird verwendet von SPVW

# ##################### PREDBIBL zu PREDTYPE.D ############################ #

# UP: testet auf Atomgleichheit EQL
# eql(obj1,obj2)
# > obj1,obj2: Lisp-Objekte
# < ergebnis: TRUE, falls Objekte gleich
  extern boolean eql (object obj1, object obj2);
# wird verwendet von CONTROL, EVAL, HASHTABL, LISPARIT

# UP: testet auf Gleichheit EQUAL
# equal(obj1,obj2)
# > obj1,obj2: Lisp-Objekte
# < ergebnis: TRUE, falls Objekte gleich
  extern boolean equal (object obj1, object obj2);
# wird verwendet von EVAL, PATHNAME, HASHTABL, MISC

# UP: testet auf laschere Gleichheit EQUALP
# equalp(obj1,obj2)
# > obj1,obj2: Lisp-Objekte
# < ergebnis: TRUE, falls Objekte gleich
  extern boolean equalp (object obj1, object obj2);
# wird verwendet von PATHNAME, HASHTABL

# UP: F�hrt eine Statistik �ber die Aktion einer GC.
# with_gc_statistics(fun);
# > fun: Funktion, die eine GC ausf�hrt
  typedef void gc_function (void);
  extern void with_gc_statistics (gc_function* fun);
# wird verwendet von SPVW

# ###################### SEQBIBL zu SEQUENCE.D ############################ #

# UP: Wandelt ein Objekt in eine Sequence gegebenen Typs um.
# coerce_sequence(obj,result_type)
# > obj: Objekt, sollte eine Sequence sein
# > result_type: Bezeichner (Symbol) des Sequence-Typs
# < Wert: Sequence vom Typ result_type
# kann GC ausl�sen
  extern Values coerce_sequence (object sequence, object result_type);
# wird verwendet von PREDTYPE, EVAL

# UP: L�uft durch eine Sequence durch und ruft f�r jedes Element eine Funktion
# auf.
# map_sequence(obj,fun,arg);
# > obj: Objekt, sollte eine Sequence sein
# > fun: Funktion, fun(arg,element) darf GC ausl�sen
# > arg: beliebiges vorgegebenes Argument
# kann GC ausl�sen
  typedef void map_sequence_function (void* arg, object element);
  extern void map_sequence (object obj, map_sequence_function* fun, void* arg);
# wird verwendet von ARRAY

# Fehler, wenn beide :TEST, :TEST-NOT - Argumente angegeben wurden.
# fehler_both_tests();
# > subr_self: Aufrufer (ein SUBR)
  nonreturning_function(extern, fehler_both_tests, (void));
# wird verwendet von LIST

# ###################### STRMBIBL zu STREAM.D ############################# #

# UP: Initialisiert die Stream-Variablen.
# init_streamvars(unixyp);
# > unixyp: Flag, ob *error-output* nach Unix-Art (vom Standard abweichend)
#           initialisert werden soll
# kann GC ausl�sen
  extern void init_streamvars (boolean unixyp);
# wird verwendet von SPVW

# Fehlermeldung, wenn eine Stream-Operation auf einem Stream nicht erlaubt ist.
# fehler_illegal_streamop(caller,stream);
# > caller: Aufrufer (ein Symbol)
# > stream: Stream
  nonreturning_function(extern, fehler_illegal_streamop, (object caller, object stream));
# wird verwendet von IO

# Liest ein Byte von einem Stream.
# read_byte(stream)
# > stream: Stream
# < ergebnis: gelesener Integer (eof_value bei EOF)
# kann GC ausl�sen
  extern object read_byte (object stream);
# wird verwendet von PATHNAME, SEQUENCE

# Schreibt ein Byte auf einen Stream.
# write_byte(stream,byte);
# > stream: Stream
# > byte: auszugebender Integer
# kann GC ausl�sen
  extern void write_byte(object stream, object byte);
# wird verwendet von SEQUENCE

# Liest ein Character von einem Stream.
# read_char(&stream)
# > stream: Stream
# < stream: Stream
# < ergebnis: gelesenes Character (eof_value bei EOF)
# kann GC ausl�sen
  extern object read_char (const object* stream_);
# wird verwendet von IO, DEBUG, SEQUENCE

# Schiebt das letzte gelesene Character auf einen Stream zur�ck.
# unread_char(&stream,ch);
# > ch: letztes gelesenes Character
# > stream: Stream
# < stream: Stream
  extern void unread_char (const object* stream_, object ch);
# wird verwendet von IO, DEBUG

# Liest ein Character von einem Stream, ohne es zu verbrauchen.
# peek_char(&stream)
# > stream: Stream
# < stream: Stream
# < ergebnis: gelesenes Character (eof_value bei EOF)
# kann GC ausl�sen
  extern object peek_char (const object* stream_);
# wird verwendet von IO

# Schreibt ein Character auf einen Stream.
# write_char(&stream,ch);
# > ch: auszugebendes Character
# > stream: Stream
# < stream: Stream
# kann GC ausl�sen
  extern void write_char (const object* stream_, object ch);
# wird verwendet von LISPARIT, IO, ERROR, SEQUENCE

# Schreibt ein Character auf einen Stream.
# write_code_char(&stream,ch);
# > ch: a character
# > stream: Stream
# < stream: Stream
# kann GC ausl�sen
  # extern void write_code_char (const object* stream_, chart ch);
  #define write_code_char(stream_,ch)  write_char(stream_,code_char(ch))
# wird verwendet von LISPARIT, IO

# Schreibt ein festes Standard-Char auf einen Stream.
# write_ascii_char(&stream,ch);
# > ch: a standard char, in ASCII encoding
# > stream: Stream
# < stream: Stream
# kann GC ausl�sen
  # extern void write_ascii_char (const object* stream_, uintB ch);
  #define write_ascii_char(stream_,ch)  write_char(stream_,code_char(as_chart(ch)))
# wird verwendet von LISPARIT, IO, DEBUG, Macro TERPRI

# UP: Stellt fest, ob ein Stream "interaktiv" ist, d.h. ob Input vom Stream
# vermutlich von einem vorher ausgegebenen Prompt abh�ngen wird.
# interactive_stream_p(stream)
# > stream: Stream
  extern boolean interactive_stream_p (object stream);
# wird verwendet von DEBUG

# UP: Schlie�t einen Stream.
# stream_close(&stream);
# > stream: Stream
# < stream: Stream
# kann GC ausl�sen
  extern void stream_close (const object* stream_);
# wird verwendet von PATHNAME, SPVW, DEBUG, MISC

# UP: Schlie�t eine Liste offener Files.
# close_some_files(list);
# > list: Liste von offenen Streams
# kann GC ausl�sen
  extern void close_some_files (object list);
# wird verwendet von SPVW

# UP: Schlie�t alle offenen Files.
# close_all_files();
# kann GC ausl�sen
  extern void close_all_files (void);
# wird verwendet von SPVW

# UP: Erkl�rt alle offenen File-Streams f�r geschlossen.
# closed_all_files();
  extern void closed_all_files (void);
# wird verwendet von SPVW

# UP: Stellt fest, ob im Stream stream ein Zeichen sofort verf�gbar ist.
# stream_listen(stream)
# > stream: Stream
# < ergebnis: ls_avail if a character is available,
#             ls_eof   if EOF is reached,
#             ls_wait  if no character is available, but not because of EOF
# kann GC ausl�sen
  extern signean stream_listen (object stream);
  #define ls_avail  0
  #define ls_eof   -1
  #define ls_wait   1
  #define ls_avail_p(x)  ((x) == 0)
  #define ls_eof_p(x)  ((x) < 0)
  #define ls_wait_p(x)  ((x) > 0)
# wird verwendet von IO, DEBUG

# UP: L�scht bereits eingegebenen interaktiven Input von einem Stream stream.
# clear_input(stream)
# > stream: Stream
# < ergebnis: TRUE falls Input gel�scht wurde
# kann GC ausl�sen
  extern boolean clear_input (object stream);
# wird verwendet von IO, DEBUG

# UP: Wartenden Output eines Stream stream ans Ziel bringen.
# finish_output(stream);
# > stream: Stream
# kann GC ausl�sen
  extern void finish_output (object stream);
# wird verwendet von IO

# UP: Wartenden Output eines Stream stream ans Ziel bringen.
# force_output(stream);
# > stream: Stream
# kann GC ausl�sen
  extern void force_output (object stream);
# wird verwendet von IO, DEBUG

# UP: Wartenden Output eines Stream stream l�schen.
# clear_output(stream);
# > stream: Stream
# kann GC ausl�sen
  extern void clear_output (object stream);
# wird verwendet von IO

# UP: Liefert die Line-Position eines Streams.
# get_line_position(stream)
# > stream: Stream
# < ergebnis: Line-Position (Fixnum >=0)
  extern object get_line_position (object stream);
# wird verwendet von IO, DEBUG

# UP: Liest mehrere Bytes von einem Stream.
# read_byte_array(stream,byteptr,len)
# > stream: Stream
# > uintB* byteptr: Adresse der zu f�llenden Bytefolge
# > uintL len: L�nge der zu f�llenden Bytefolge
# < uintB* ergebnis: Pointer ans Ende des gef�llten Bereiches oder NULL
  extern uintB* read_byte_array (object stream, uintB* byteptr, uintL len);
# wird verwendet von SEQUENCE

# UP: Schreibt mehrere Bytes auf einen Stream.
# write_byte_array(stream,byteptr,len)
# > stream: Stream
# > uintB* byteptr: Adresse der zu schreibenden Bytefolge
# > uintL len: L�nge der zu schreibenden Bytefolge
# < uintB* ergebnis: Pointer ans Ende des geschriebenen Bereiches oder NULL
  extern const uintB* write_byte_array (object stream, const uintB* byteptr, uintL len);
# wird verwendet von SEQUENCE

# UP: Liest mehrere Characters von einem Stream.
# read_char_array(stream,charptr,len)
# > stream: Stream
# > chart* charptr: Adresse der zu f�llenden Zeichenfolge
# > uintL len: L�nge der zu f�llenden Zeichenfolge
# < chart* ergebnis: Pointer ans Ende des gef�llten Bereiches oder NULL
  extern chart* read_char_array (object stream, chart* charptr, uintL len);
# wird verwendet von SEQUENCE

# UP: Schreibt mehrere Characters auf einen Stream.
# write_char_array(stream,charptr,len)
# > stream: Stream
# > chart* charptr: Adresse der zu schreibenden Zeichenfolge
# > uintL len: L�nge der zu schreibenden Zeichenfolge
# < chart* ergebnis: Pointer ans Ende des geschriebenen Bereiches oder NULL
  extern const chart* write_char_array (object stream, const chart* charptr, uintL len);
# wird verwendet von SEQUENCE

# UP: Liefert den Stream, der der Wert einer Variablen ist.
# var_stream(sym,strmflags)
# > sym: Variable (Symbol)
# > strmflags: Menge von Operationen, die auf dem Stream m�glich sein sollen
# < ergebnis: Stream
  extern object var_stream (object sym, uintB strmflags);
# wird verwendet von IO, PACKAGE, ERROR, DEBUG, SPVW

# UP: erzeugt ein File-Stream
# make_file_stream(direction,append_flag,handle_fresh)
# > STACK_4: Filename, ein Pathname oder NIL
# > STACK_3: Truename, ein Pathname oder NIL
# > STACK_2: :BUFFERED argument
# > STACK_1: :ELEMENT-TYPE argument
# > STACK_0: Handle des ge�ffneten Files
# > direction: Modus (0 = :PROBE, 1 = :INPUT, 4 = :OUTPUT, 5 = :IO, 3 = :INPUT-IMMUTABLE)
# > append_flag: TRUE falls der Stream gleich ans Ende positioniert werden
#         soll, FALSE sonst
# > handle_fresh: whether the handle is freshly created.
#                 This means 1. that it is currently positioned at position 0,
#                 2. if (direction & bit(2)), it is opened for read/write, not
#                 only for write.
#                 If the handle refers to a regular file, this together means
#                 that it supports file_lseek, reading/repositioning/writing
#                 and close/reopen.
# > subr_self: calling function
# If direction==5, handle_fresh must be TRUE.
# < ergebnis: File-Stream (oder evtl. File-Handle-Stream)
# < STACK: aufger�umt
# kann GC ausl�sen
  extern object make_file_stream (uintB direction, boolean append_flag, boolean handle_at_pos_0);
# wird verwendet von PATHNAME

# Liefert einen Broadcast-Stream zum Stream stream.
# make_broadcast1_stream(stream)
# kann GC ausl�sen
  extern object make_broadcast1_stream (object stream);
# wird verwendet von IO

# Liefert einen Two-Way-Stream zu einem Input-Stream und einem Output-Stream.
# make_twoway_stream(input_stream,output_stream)
# > input_stream : Input-Stream
# > output_stream : Output-Stream
# < ergebnis : Two-Way-Stream
# kann GC ausl�sen
  extern object make_twoway_stream (object input_stream, object output_stream);
# wird verwendet von SPVW

# Liefert einen String-Output-Stream.
# make_string_output_stream()
# kann GC ausl�sen
  extern object make_string_output_stream (void);
# wird verwendet von IO, EVAL, DEBUG, ERROR

# UP: Liefert das von einem String-Output-Stream Angesammelte.
# get_output_stream_string(&stream)
# > stream: String-Output-Stream
# < stream: geleerter Stream
# < ergebnis: Angesammeltes, ein Simple-String
# kann GC ausl�sen
  extern object get_output_stream_string (const object* stream_);
# wird verwendet von IO, EVAL, DEBUG, ERROR

# UP: Liefert einen Pretty-Printer-Hilfs-Stream.
# make_pphelp_stream()
# kann GC ausl�sen
  extern object make_pphelp_stream (void);
# wird verwendet von IO

# UP: Tells whether a stream is buffered.
# stream_isbuffered(stream)
# > stream: a file stream
# < result: TRUE if stream is buffered, else FALSE
  extern boolean stream_isbuffered (object stream);
# wird verwendet von IO

# UP: Returns the line current number of a stream.
# stream_line_number(stream)
# > stream: a stream
# < result: an integer or NIL
  extern object stream_line_number (object stream);
# wird verwendet von IO

#if (defined(UNIX) && !defined(NEXTAPP)) || defined(AMIGAOS) || defined(RISCOS)
# UP: Terminal wieder in Normalzustand schalten
# terminal_sane();
  extern void terminal_sane (void);
# wird verwendet von SPVW
#endif

# ####################### SYMBIBL zu SYMBOL.D ############################# #

# UP: Liefert die globale Funktionsdefinition eines Symbols,
# mit Test, ob das Symbol eine globale Funktion darstellt.
# Symbol_function_checked(symbol)
# > symbol: Symbol
# < ergebnis: seine globale Funktionsdefinition
  extern object Symbol_function_checked (object symbol);
# wird verwendet von

# UP: Holt eine Property aus der Property-Liste eines Symbols.
# get(symbol,key)
# > symbol: ein Symbol
# > key: ein mit EQ zu vergleichender Key
# < value: dazugeh�riger Wert aus der Property-Liste von symbol, oder unbound.
  extern object get (object symbol, object key);
# wird verwendet von IO, CONTROL, EVAL, PREDTYPE, SEQUENCE

# ##################### ARITBIBL zu LISTARIT.D ############################ #

# UP: Initialisiert die Arithmetik.
# init_arith();
# kann GC ausl�sen
  extern void init_arith (void);
# wird verwendet von SPVW

# Wandelt Longword in Integer um.
# L_to_I(wert)
# > wert: Wert des Integers, ein signed 32-Bit-Integer.
# < ergebnis: Integer mit diesem Wert.
# kann GC ausl�sen
  extern object L_to_I (sint32 wert);
# wird verwendet von TIME, REXX

# Wandelt Unsigned Longword in Integer >=0 um.
# UL_to_I(wert)
# > wert: Wert des Integers, ein unsigned 32-Bit-Integer.
# < ergebnis: Integer mit diesem Wert.
# kann GC ausl�sen
  #if (intLsize<=oint_data_len)
    #define UL_to_I(wert)  fixnum((uintL)(wert))
  #else
    extern object UL_to_I (uintL wert);
  #endif
# wird verwendet von MISC, TIME, STREAM, PATHNAME, HASHTABL, SPVW, ARRAY

# Wandelt Doppel-Longword in Integer um.
# L2_to_I(wert_hi,wert_lo)
# > wert_hi|wert_lo: Wert des Integers, ein signed 64-Bit-Integer.
# < ergebnis: Integer mit diesem Wert.
# kann GC ausl�sen
  extern object L2_to_I (sint32 wert_hi, uint32 wert_lo);
# wird verwendet von TIME, FOREIGN

#ifdef HAVE_FFI
# Wandelt Unsigned Doppel-Longword in Integer um.
# UL2_to_I(wert_hi,wert_lo)
# > wert_hi|wert_lo: Wert des Integers, ein unsigned 64-Bit-Integer.
# < ergebnis: Integer mit diesem Wert.
# kann GC ausl�sen
  extern object UL2_to_I (uint32 wert_hi, uint32 wert_lo);
# wird verwendet von FOREIGN, vom FFI
#endif

#ifdef intQsize
# Wandelt Quadword in Integer um.
# Q_to_I(wert)
# > wert: Wert des Integers, ein signed 64-Bit-Integer.
# < ergebnis: Integer mit diesem Wert.
# kann GC ausl�sen
  extern object Q_to_I (sint64 wert);
# wird verwendet vom FFI
#endif

#if defined(intQsize) || defined(WIDE_HARD)
# Wandelt Unsigned Quadword in Integer >=0 um.
# UQ_to_I(wert)
# > wert: Wert des Integers, ein unsigned 64-Bit-Integer.
# < ergebnis: Integer mit diesem Wert.
# kann GC ausl�sen
  extern object UQ_to_I (uint64 wert);
# wird verwendet von MISC, TIME, FFI
#endif

# Wandelt ein C-Integer gegebenen Typs in ein Integer um.
# val sollte eine Variable sein.
  #define uint8_to_I(val)  fixnum((uint8)(val))
  #define sint8_to_I(val)  L_to_I((sint32)(sint8)(val))
  #define uint16_to_I(val)  fixnum((uint16)(val))
  #define sint16_to_I(val)  L_to_I((sint32)(sint16)(val))
  #define uint32_to_I(val)  UL_to_I((uint32)(val))
  #define sint32_to_I(val)  L_to_I((sint32)(val))
  #ifdef intQsize
    #define uint64_to_I(val)  UQ_to_I((uint64)(val))
    #define sint64_to_I(val)  Q_to_I((sint64)(val))
  #elif defined(HAVE_FFI)
    #define uint64_to_I(val)  UL2_to_I((uint32)((val)>>32),(uint32)(val))
    #define sint64_to_I(val)  L2_to_I((sint32)((val)>>32),(uint32)(val))
  #endif
  #if (int_bitsize==16)
    #define uint_to_I(val)  uint16_to_I(val)
    #define sint_to_I(val)  sint16_to_I(val)
  #else # (int_bitsize==32)
    #define uint_to_I(val)  uint32_to_I(val)
    #define sint_to_I(val)  sint32_to_I(val)
  #endif
  #if (long_bitsize==32)
    #define ulong_to_I(val)  uint32_to_I(val)
    #define slong_to_I(val)  sint32_to_I(val)
  #else # (long_bitsize==64)
    #define ulong_to_I(val)  uint64_to_I(val)
    #define slong_to_I(val)  sint64_to_I(val)
  #endif
# wird verwendet von MISC, vom FFI

# Wandelt Integer >=0 in Unsigned Longword um.
# I_to_UL(obj)
# > obj: ein Objekt, sollte ein Integer >=0, <2^32 sein
# < ergebnis: der Wert des Integer als Unsigned Longword.
  extern uintL I_to_UL (object obj);
# wird verwendet von TIME, ARRAY

# Wandelt Integer in Signed Longword um.
# I_to_L(obj)
# > obj: ein Objekt, sollte ein Integer >=-2^31, <2^31 sein
# < ergebnis: der Wert des Integer als Longword.
  extern sintL I_to_L (object obj);
# wird verwendet von

#if (defined(HAVE_FFI) || defined(HAVE_AFFI)) && defined(HAVE_LONGLONG)

# Wandelt Integer >=0 in Unsigned Quadword um.
# I_to_UQ(obj)
# > obj: ein Objekt, sollte ein Integer >=0, <2^64 sein
# < ergebnis: der Wert des Integer als Unsigned Quadword.
  extern uint64 I_to_UQ (object obj);
# wird verwendet von FOREIGN, vom FFI

#endif

#if defined(HAVE_FFI) && defined(HAVE_LONGLONG)

# Wandelt Integer in Signed Quadword um.
# I_to_Q(obj)
# > obj: ein Objekt, sollte ein Integer >=-2^63, <2^63 sein
# < ergebnis: der Wert des Integer als Quadword.
  extern sint64 I_to_Q (object obj);
# wird verwendet von FOREIGN, vom FFI

#endif

# Wandelt ein Integer in ein C-Integer gegebenen Typs um.
# I_to_xintyy(obj) setzt voraus, dass xintyy_p(obj) schon abgepr�ft wurde.
  #define I_to_uint8(obj)  (uint8)(as_oint(obj) >> oint_data_shift)
  #define I_to_sint8(obj)  (sint8)(as_oint(obj) >> oint_data_shift)
  #define I_to_uint16(obj)  (uint16)(as_oint(obj) >> oint_data_shift)
  #define I_to_sint16(obj)  (sint16)(as_oint(obj) >> oint_data_shift)
  #if (oint_data_len>=32)
    #define I_to_uint32(obj)  (uint32)(as_oint(obj) >> oint_data_shift)
  #else
    #define I_to_uint32(obj)  I_to_UL(obj)
  #endif
  #if (oint_data_len>=31)
    #define I_to_sint32(obj)  (sint32)(as_oint(obj) >> oint_data_shift)
  #else
    #define I_to_sint32(obj)  I_to_L(obj)
  #endif
#if defined(HAVE_FFI) || defined(HAVE_AFFI)
 #ifdef HAVE_LONGLONG
  #define I_to_uint64(obj)  I_to_UQ(obj)
  #define I_to_sint64(obj)  I_to_Q(obj)
 #endif
  #if (int_bitsize==16)
    #define I_to_uint  I_to_uint16
    #define I_to_sint  I_to_sint16
  #else # (int_bitsize==32)
    #define I_to_uint  I_to_uint32
    #define I_to_sint  I_to_sint32
  #endif
  #if (long_bitsize==32)
    #define I_to_ulong  I_to_uint32
    #define I_to_slong  I_to_sint32
  #else # (long_bitsize==64)
    #define I_to_ulong  I_to_uint64
    #define I_to_slong  I_to_sint64
  #endif
#endif
# wird verwendet vom FFI

# I_I_comp(x,y) vergleicht zwei Integers x und y.
# Ergebnis: 0 falls x=y, +1 falls x>y, -1 falls x<y.
  extern signean I_I_comp (object x, object y);
# wird verwendet von SEQUENCE

# (1+ x), wo x ein Integer ist. Ergebnis Integer.
# I_1_plus_I(x)
# kann GC ausl�sen
  extern object I_1_plus_I (object x);
# wird verwendet von SEQUENCE, SPVW, SYMBOL

# (1- x), wo x ein Integer ist. Ergebnis Integer.
# I_minus1_plus_I(x)
# kann GC ausl�sen
  extern object I_minus1_plus_I (object x);
# wird verwendet von SEQUENCE

# (+ x y), wo x und y Integers sind. Ergebnis Integer.
# I_I_plus_I(x,y)
# kann GC ausl�sen
  extern object I_I_plus_I (object x, object y);
# wird verwendet von SEQUENCE

# (- x y), wo x und y Integers sind. Ergebnis Integer.
# I_I_minus_I(x,y)
# kann GC ausl�sen
  extern object I_I_minus_I (object x, object y);
# wird verwendet von SEQUENCE

# (ASH x y), wo x und y Integers sind. Ergebnis Integer.
# I_I_ash_I(x,y)
# kann GC ausl�sen
  extern object I_I_ash_I (object x, object y);
# wird verwendet von SEQUENCE

# (INTEGER-LENGTH x), wo x ein Integer ist. Ergebnis uintL.
# I_integer_length(x)
  extern uintL I_integer_length (object x);
# wird verwendet von ARRAY

#ifdef HAVE_FFI

# c_float_to_FF(&val) wandelt ein IEEE-Single-Float val in ein Single-Float um.
# kann GC ausl�sen
  extern object c_float_to_FF (const ffloatjanus* val_);

# FF_to_c_float(obj,&val);
# wandelt ein Single-Float obj in ein IEEE-Single-Float val um.
  extern void FF_to_c_float (object obj, ffloatjanus* val_);

# c_double_to_DF(&val) wandelt ein IEEE-Double-Float val in ein Double-Float um.
# kann GC ausl�sen
  extern object c_double_to_DF (const dfloatjanus* val_);

# DF_to_c_double(obj,&val);
# wandelt ein Double-Float obj in ein IEEE-Double-Float val um.
  extern void DF_to_c_double (object obj, dfloatjanus* val_);

#endif

# UP: Wandelt eine Zeichenkette mit Integer-Syntax in ein Integer um.
# Punkte werden �berlesen.
# read_integer(base,sign,string,index1,index2)
# > base: Lesebasis (>=2, <=36)
# > sign: Vorzeichen (/=0 falls negativ)
# > string: Simple-String (enth�lt Ziffern mit Wert <base und evtl. Punkt)
# > index1: Index der ersten Ziffer
# > index2: Index nach der letzten Ziffer
#   (also index2-index1 Ziffern, incl. evtl. Dezimalpunkt am Schluss)
# < ergebnis: Integer
# kann GC ausl�sen
  extern object read_integer (uintWL base,
         signean sign, object string, uintL index1, uintL index2);
# wird verwendet von IO

# UP: Wandelt eine Zeichenkette mit Rational-Syntax in eine rationale Zahl um.
# read_rational(base,sign,string,index1,index3,index2)
# > base: Lesebasis (>=2, <=36)
# > sign: Vorzeichen (/=0 falls negativ)
# > string: Simple-String (enth�lt Ziffern mit Wert <base und Bruchstrich)
# > index1: Index der ersten Ziffer
# > index3: Index von '/'
# > index2: Index nach der letzten Ziffer
#   (also index3-index1 Z�hler-Ziffern, index2-index3-1 Nenner-Ziffern)
# < ergebnis: rationale Zahl
# kann GC ausl�sen
  extern object read_rational (uintWL base,
         signean sign, object string, uintL index1, uintL index3, uintL index2);
# wird verwendet von IO

# UP: Wandelt eine Zeichenkette mit Float-Syntax in ein Float um.
# read_float(base,sign,string,index1,index4,index2,index3)
# > base: Lesebasis (=10)
# > sign: Vorzeichen (/=0 falls negativ)
# > string: Simple-String (enth�lt Ziffern und evtl. Punkt und Exponentmarker)
# > index1: Index vom Mantissenanfang (excl. Vorzeichen)
# > index4: Index nach dem Mantissenende
# > index2: Index beim Ende der Characters
# > index3: Index nach dem Dezimalpunkt (=index4 falls keiner da)
#   (also Mantisse mit index4-index1 Characters: Ziffern und max. 1 '.')
#   (also index4-index3 Nachkommaziffern)
#   (also bei index4<index2: index4 = Index des Exponent-Markers,
#    index4+1 = Index des Exponenten-Vorzeichens oder der ersten
#    Exponenten-Ziffer)
# < ergebnis: Float
# kann GC ausl�sen
  extern object read_float (uintWL base,
         signean sign, object string, uintL index1, uintL index4, uintL index2, uintL index3);
# wird verwendet von IO

# UP: Gibt ein Integer aus.
# print_integer(z,base,&stream);
# > z: Integer
# > base: Basis (>=2, <=36)
# > stream: Stream
# < stream: Stream
# kann GC ausl�sen
  extern void print_integer (object z, uintWL base, const object* stream_);
# wird verwendet von IO

# UP: Gibt ein Float aus.
# print_float(z,&stream);
# > z: Float
# > stream: Stream
# < stream: Stream
# kann GC ausl�sen
  extern void print_float (object z, const object* stream_);
# wird verwendet von IO

# UP: Multipliziert ein Integer mit 10 und addiert eine weitere Ziffer.
# mal_10_plus_x(y,x)
# > y: Integer Y (>=0)
# > x: Ziffernwert X (>=0,<10)
# < ergebnis: Integer Y*10+X (>=0)
# kann GC ausl�sen
  extern object mal_10_plus_x (object y, uintB x);
# wird verwendet von IO

# UP: entscheidet auf Zahlgleichheit
# number_gleich(x,y)
# > x,y: zwei Zahlen
# < ergebnis: TRUE, falls (= x y) gilt
  extern boolean number_gleich (object x, object y);
# wird verwendet von PREDTYPE

# UP: Wandelt ein Objekt in ein Float von gegebenem Typ um.
# coerce_float(obj,type)
# > obj: Objekt
# > type: Eines der Symbole
#         FLOAT, SHORT-FLOAT, SINGLE-FLOAT, DOUBLE-FLOAT, LONG-FLOAT
# > subr_self: Aufrufer (ein SUBR)
# < ergebnis: (coerce obj type)
# kann GC ausl�sen
  extern object coerce_float (object obj, object type);
# wird verwendet von PREDTYPE

# UP: Returns the decimal string representation of an integer >= 0.
# decimal_string(x)
# > object x: an integer >= 0
# < object result: a simple-string containing the digits
# kann GC ausl�sen
  extern object decimal_string (object x);
# wird verwendet von PATHNAME

# ###################### FRGNIBL zu FOREIGN.D ############################# #

#ifdef DYNAMIC_FFI

# Return the pointer encoded by a Foreign-Pointer. obj a variable
  #define Fpointer_value(obj)  \
    (fp_validp(TheFpointer(obj)) ? 0 : (validate_fpointer(obj), 0), \
     TheFpointer(obj)->fp_pointer                                   \
    )
  extern void validate_fpointer (object obj);

# Return the pointer encoded by a Foreign-Address. obj a variable
  #define Faddress_value(obj)  \
    ((void*)((uintP)Fpointer_value(TheFaddress(obj)->fa_base) + TheFaddress(obj)->fa_offset))

# Registers a foreign variable.
# register_foreign_variable(address,name,flags,size);
# > address: address of a variable in memory
# > name: its name
# > flags: fv_readonly for read-only variables
# > size: its size in bytes
# kann GC ausl�sen
  extern void register_foreign_variable (void* address, const char * name, uintBWL flags, uintL size);
# Specifies that the variable will not be written to.
#define fv_readonly  bit(0)
# Specifies that when the value is replaced and the variable contains pointers,
# the old storage will be free()d and new storage will be allocated via malloc().
#define fv_malloc    bit(1)

# Registers a foreign function.
# register_foreign_function(address,name,flags);
# > address: address of the function in memory
# > name: its name
# > flags: its language and parameter passing convention
# kann GC ausl�sen
  extern void register_foreign_function (void* address, const char * name, uintWL flags);
# Flags for language:
#define ff_lang_asm       bit(8)  # no argument passing conventions
#define ff_lang_c         bit(9)  # K&R C, with argument type promotions
#define ff_lang_ansi_c    bit(10) # ANSI C, without argument type promotions
# define ff_lang_pascal   bit(11) # not yet supported
#define ff_lang_stdcall   bit(15) # `stdcall' calling convention
# Varargs functions are not supported.
# Set this if pointers within the arg should point to alloca()ed data, i.e.
# have dynamic extent: are valid for this call only.
#define ff_alloca         bit(0)
# Set this if pointers within the arg should point to malloc()ed data. The
# function takes over responsibility for that storage. For return values,
# set this if free() shall be called for pointers within the resulting value.
#define ff_malloc         bit(1)
# Set this if the arg should point to a place where a return value can be
# stored.
#define ff_out            bit(4)
# Set this if the arg is also treated as a return value.
#define ff_inout          bit(5)

# Convert foreign data to Lisp data.
# kann GC ausl�sen
  extern object convert_from_foreign (object fvd, const void* data);

# Convert Lisp data to foreign data.
# The foreign data is allocated through malloc() and has more than dynamic
# extent. (Not exactly indefinite extent: It is deallocated the next time
# free_foreign() is called on it.)
  extern void convert_to_foreign_mallocing (object fvd, object obj, void* data);

# Convert Lisp data to foreign data.
# The foreign data storage is reused.
# DANGEROUS, especially for type C-STRING !!
# Also beware against NULL pointers! They are not treated specially.
  extern void convert_to_foreign_nomalloc (object fvd, object obj, void* data);

# Initialize the FFI.
  extern void init_ffi (void);
# wird verwendet von SPVW

# De-Initialize the FFI.
  extern void exit_ffi (void);
# wird verwendet von SPVW

#endif

# ####################### REXXBIBL zu REXX.D ############################## #

#ifdef REXX

# Initialisiert die Rexx-Schnittstelle.
# init_rexx();
# < ergebnis: Flag, ob erfolgreich initialisiert.
  extern boolean init_rexx (void);
# wird verwendet von SPVW

# Schlie�t die Rexx-Schnittstelle.
# close_rexx();
  extern void close_rexx (void);
# wird verwendet von SPVW

#endif

# ######################## GRAPHBIBL zu GRAPH.D ########################### #

#ifdef GRAPHICS_SWITCH

# Schaltet die Grafik auf Text-Modus zur�ck.
# switch_text_mode();
  extern void switch_text_mode (void);

#endif

# ######################## THREADBIBL zu THREAD.D ######################### #

#ifdef MULTITHREAD

# Structure containing all the per-thread global variables.
# (We could use a single instance of this structure also in the single-thread
# model, but it would make debugging less straightforward.)
  typedef struct
    {
      # Most often used:
        #if !defined(STACK_register)
          object* _STACK;
        #endif
        #if !defined(mv_count_register)
          uintC _mv_count;
        #endif
        #if !defined(value1_register)
          object _value1;
        #endif
        #if !defined(subr_self_register)
          object _subr_self;
        #endif
      # Less often used:
        #ifndef NO_SP_CHECK
          void* _SP_bound;
        #endif
        void* _STACK_bound;
        unwind_protect_caller _unwind_protect_to_save;
        #ifdef NEED_temp_mv_count
          uintC _temp_mv_count;
        #endif
        #ifdef NEED_temp_value1
          object _temp_value1;
        #endif
        #ifdef HAVE_SAVED_STACK
          object* _saved_STACK;
        #endif
        #ifdef HAVE_SAVED_mv_count
          uintC _saved_mv_count;
        #endif
        #ifdef HAVE_SAVED_value1
          object _saved_value1;
        #endif
        #ifdef HAVE_SAVED_subr_self
          object _saved_subr_self;
        #endif
        #if defined(HAVE_SAVED_REGISTERS)
          struct registers * _callback_saved_registers;
        #endif
        uintC _index; # this thread's index in allthreads[]
      # Used for exception handling only:
        handler_args_t _handler_args;
        stack_range* _inactive_handlers;
      # Big, rarely used arrays come last:
        object _mv_space [mv_limit-1];
      # Now the lisp objects (seen by the GC).
        # The Lisp object representing this thread:
        object _lthread;
        # The lexical environment:
        environment _aktenv;
        # The values of per-thread symbols:
        object _symvalues[unspecified];
    }
    thread_;
  #define thread_size(nsymvalues)  \
    (offsetofa(thread_,_symvalues)+nsymvalues*sizeof(object))
  #define thread_objects_offset(nsymvalues)  \
    (offsetof(thread_,_lthread))
  #define thread_objects_anz(nsymvalues)  \
    ((offsetofa(thread_,_symvalues)-offsetof(thread_,_lthread))/sizeof(object)+(nsymvalues))

# Size of a single thread's stack region. Must be a power of 2.
  #define THREAD_SP_SHIFT  22  # 4 MB should be sufficient, and leaves room
                               # for about 128 threads.
  #define THREAD_SP_SIZE  bit(THREAD_SP_SHIFT)
# Returns the stack pointer, or some address near the stack pointer.
  # Important for efficiency: Multiple calls to this function within a single
  # function must be combined to a single, inlined call. To reach this, we
  # use __asm__, not __asm__ __volatile__, and we don't use a global register
  # variable.
  #if defined(ASM_get_SP_register)
    #define roughly_SP()  \
      ({ var aint __SP; __asm__ ASM_get_SP_register(__SP); __SP; })
  #else
    #define roughly_SP()  (aint)__builtin_frame_address(0)
    # Note: If (__GNUC__ >= 2) && (__GNUC_MINOR__ >= 8) one can write
    # #define roughly_SP()  (aint)__builtin_sp()
    # but this isn't efficient because gcc somehow knows that the stack pointer
    # varies across the function (maybe because of our register declaration?).
  #endif
# Returns a pointer to the thread structure, given the thread's stack pointer.
  #ifdef SP_DOWN
    #ifndef MORRIS_GC
      #define sp_to_thread(sp)  \
        (thread_*)((aint)(sp) & minus_bit(THREAD_SP_SHIFT))
    #else
      # Morris GC doesn't like the backpointers to have garcol_bit set.
      #define sp_to_thread(sp)  \
        (thread_*)((aint)(sp) & (minus_bit(THREAD_SP_SHIFT) & ~wbit(garcol_bit_o)))
    #endif
  #endif
  #ifdef SP_UP
    #define sp_to_thread(sp)  \
      (thread_*)(((aint)(sp) | (bit(THREAD_SP_SHIFT)-1)) - 0x1FFFF)
  #endif
# Returns a pointer to the current thread structure.
  typedef thread_* current_thread_function (void);
  extern inline const current_thread_function current_thread;
  extern inline thread_* current_thread (void)
  { return sp_to_thread(roughly_SP()); }

#endif

# ######################################################################### #

