# Hilfsfunktionen f�r CLISP auf AmigaOS
# J�rg H�hle 2.9.1997

#include "lispbibl.c"

# ==============================================================================

# Ein Wrapper um die Read-Funktion.
global long full_read (Handle handle, RW_BUF_T bufarea, long nbyte);
global long full_read(handle,bufarea,nbyte)
  var Handle handle;
  var RW_BUF_T bufarea;
  var long nbyte;
  { var char* buf = (char*) bufarea;
    var long done = 0;
    until (nbyte==0)
      { var long retval = Read(handle,(APTR)buf,nbyte);
        if (retval == 0) break; # EOF
        elif (retval < 0) { return retval; }
        else { buf += retval; done += retval; nbyte -= retval; }
      }
    return done;
  }

# Ein Wrapper um die Write-Funktion.
global long full_write (Handle handle, const RW_BUF_T bufarea, long nbyte);
global long full_write(handle,bufarea,nbyte)
  var Handle handle;
  var const RW_BUF_T bufarea;
  var long nbyte;
  { var CONST char* buf = (CONST char*) bufarea;
    var long done = 0;
    until (nbyte==0)
      { var long retval = Write(handle,(CONST APTR)buf,nbyte);
        if (retval == 0) break; # Wann passiert das?? Wenn Platte voll!
        elif (retval < 0) { return retval; }
        else { buf += retval; done += retval; nbyte -= retval; }
      }
    return done;
  }

# ==============================================================================

# Sofortiger Programmabbruch, Sprung in den Debugger
  global void abort (void);
  global void abort()
    {
      #if defined(GNU) && 0 # J�rg mag das nicht so sehr bis �berhaupt nicht
        __asm__ __volatile__ (" .word 0x4AFC "); # illegaler Befehl
      #else
        # Je pr�f�re Wait(0L) car ainsi le programme se met en attente infinie
        # et on peut essayer de savoir pourquoi en analysant la m�moire. Je ne
        # consid�re pas qu'une sortie de programme soit s�re puisque la m�moire
        # peut se trouver dans un mauvais �tat, il peut y avoir des fichiers
        # non ferm�s, des �Lock� allou�s, etc.                    J�rg 7.1.1993
        asciz_out(NLstring "CLISP panic! (halting)" NLstring);
        Wait(0L);
      #endif
    }

# ==============================================================================

