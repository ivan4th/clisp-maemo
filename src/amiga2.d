# Include-File: Amiga-Spezifisches, das nur von wenigen Modulen ben�tigt wird
# J�rg H�hle 12.6.1996


#include <proto/alib.h>

# Die Inlines sind jetzt Macros, also k�nnen Funktionen nicht mehr deklariert werden
#if !defined(GNU_INLINES)

# Verhindert Multitasking kurzzeitig.
# Forbid(); ... Permit();
# Aufrufe k�nnen geschachtelt werden.
  extern void Forbid (void); # siehe exec.library/Forbid
  extern void Permit (void); # siehe exec.library/Permit
# wird verwendet von REXX


# �ffnet eine 'shared library'.
# OpenLibrary(name,version)
# > name: Name als ASCIZ-String, mit .library am Schlu�
# > version: kleinste erw�nschte Versionsnummer, 0 bedeutet "egal"
# < struct Library * ergebnis: Library base Zeiger oder NULL
  extern struct Library * OpenLibrary (CONST UBYTE* name, unsigned long version); # siehe exec.library/OpenLibrary
# wird verwendet von REXX, FOREIGN

# Schlie�t eine ge�ffnete 'shared library'.
# CloseLibrary(library)
# > library: 'library base' Zeiger
  extern void CloseLibrary (struct Library * library);
# wird verwendet von REXX, FOREIGN


# "Port"s sind Einheiten zum Austausch von Nachrichten ("Messages").
# (Wir haben's hier nur mit den sogenannten "�ffentlichen Ports".)
# Sie tragen einen Namen.

# Sucht einen Port gegebenen Namens.
# FindPort(name)
# > name: Name des Ports
# < ergebnis: Port-Pointer oder NULL falls es keinen gibt
# Mu� von Forbid()/Permit() umrahmt sein.
  extern struct MsgPort * FindPort (CONST UBYTE* name); # siehe exec.library/FindPort
# wird verwendet von REXX

# Alloziert einen neuen Port.
# CreatePort(name,priority)
# > name: Name des Ports
# > priority: Priorit�t
# < ergebnis: Port-Pointer
  extern struct MsgPort * CreatePort (UBYTE* name, LONG priority); # siehe amiga.lib/CreatePort
# wird verwendet von REXX

# Meldet einen Port ab (vor dem Freigeben n�tig).
# RemPort(port)
# > port: Port-Pointer
  extern void RemPort (struct MsgPort * port); # siehe exec.library/RemPort
# wird verwendet von REXX

# Gibt einen Port wieder frei.
# DeletePort(port)
# > port: Port-Pointer
  extern void DeletePort (struct MsgPort * port); # siehe amiga.lib/DeletePort
# wird verwendet von REXX

# Holt eine Message an einem Port ab.
# GetMsg(port)
# > port: Port-Pointer
# < ergebnis: Message-Pointer oder NULL falls gerade keine Message anliegt.
# Die abgeholte Message wird aus der Warteschlange von Messages entfernt.
  extern struct Message * GetMsg (struct MsgPort * port); # siehe exec.library/GetMsg
# wird verwendet von REXX

# Beendet die Bearbeitung einer abgeholten Message.
# ReplyMsg(message);
# > message: Message-Pointer
  extern void ReplyMsg (struct Message * message); # siehe exec.library/ReplyMsg
# wird verwendet von REXX

# Schickt eine Message an einen Port.
# PutMsg(port,message);
# > port: Port-Pointer
# > message: Message-Pointer
# Der von der Message beanspruchte Speicher bleibt bis zu ihrer Beantwortung
# reserviert!
  extern void PutMsg (struct MsgPort * port, struct Message * message); # siehe exec.library/PutMsg
# wird verwendet von REXX

#if 0 # Von der CLISP-Library intern benutzte Funktionen
# extern struct List * NewList (struct List * list);
# extern long AllocSignal (long);
# extern void FreeSignal (long);
#endif

#endif # GNU_INLINES


#ifdef REXX

# ARexx (= Amiga-Rexx) ist ein auf obigen Ports aufbauendes Kommunikations-
# system zwischen Applikationen.

#include <rexx/rxslib.h>
#include <proto/rexxsyslib.h>

#if !defined(GNU_INLINES)

# Arexx-Messages haben ein spezielles Aussehen:

# Erzeugt eine Message-H�lle f�r ARexx.
# CreateRexxMsg(msgport,ext,host)
# > msgport: Adresse des ARexx message Ports, der die Empfangsbest�tigung bekommt
# > ext: (ASCIZ) Extension f�r aufzurufende Dateien, NULL bedeutet "REXX"
# > host: Name des ARexx message Ports, der externe Kommandos abarbeitet
# < ergebnis: ARexx Message oder NULL bei Fehler
  extern struct RexxMsg * CreateRexxMsg (struct MsgPort* msgport, UBYTE* extension, UBYTE* hostname); # siehe rexxsyslib/CreateRexxMsg
# wird verwendet von REXX

# Eine Message-H�lle hat Platz f�r 1 bis MAXRMARG Argument-Strings.

# Gibt die Argument-Strings in einer Message-H�lle wieder frei.
# ClearRexxMsg(msg,argcount);
# > msg: ARexx Message
# > argcount: Anzahl Argumente
  extern void ClearRexxMsg (struct RexxMsg * msg, ULONG argcount); # siehe rexxsyslib/ClearRexxMsg
# wird verwendet von REXX

# Gibt eine Message-H�lle wieder frei.
# DeleteRexxMsg(msg);
# > msg: ARexx Message
  extern void DeleteRexxMsg (struct RexxMsg * message); # siehe rexxsyslib/DeleteRexxMsg
# wird verwendet von REXX

# Au�erdem m�ssen auch Argument-Strings speziell verpackt werden:

# Erzeugt Argument-String Struktur f�r ARexx.
# CreateArgstring(string,length)
# > [string..string+length-1]: angesprochener Speicherbereich
# > length: L�nge, <2^16
# < ergebnis: verpackter, kopierter Argument-String
  extern UBYTE* CreateArgstring (UBYTE* string, ULONG length); # siehe rexxsyslib/CreateArgstring
# wird verwendet von REXX

# Gibt Argument-String Struktur wieder frei.
# DeleteArgstring(argstring);
# > argstring: verpackter Argument-String
  extern void DeleteArgstring (UBYTE* argstring); # siehe rexxsyslib/DeleteArgstring
# wird verwendet von REXX

# Liefert die L�nge eines verpackten Argument-Strings.
# LengthArgstring(argstring)
# > argstring: verpackter Argument-String
# < ergebnis: L�nge
  extern ULONG LengthArgstring (UBYTE* argstring); # siehe rexxsyslib/LengthArgstring
# wird verwendet von REXX

# Verpackt eine ganze Argumentliste.
# FillRexxMsg(msg,argcount,mask)
# > msg: Message-H�lle
# > argcount: Anzahl Argumente (>=1, <=16)
# > mask: Bitmaske f�r Argumenttyp in der H�lle (jeweils 0 = ASCIZ, 1 = LONG)
# < ergebnis: /=0 falls OK
  extern BOOL FillRexxMsg (struct RexxMsg * msg, ULONG argcount, ULONG mask); # siehe rexxsyslib.library/FillRexxMsg
# wird verwendet von

#endif # GNU_INLINES

#define RXERRORIMGONE 100L
#define RXADIR "AREXX"  # MsgPort f�r Asynchrone Bearbeitung

#endif # REXX

