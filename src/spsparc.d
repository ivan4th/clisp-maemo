# Kleine Routine, die den Wert des Maschinenstacks zur�ckliefert.

  # (diese werden VOR der vorigen Instruktion ausgef�hrt):
  #define _             # Instruktion, die stets ausgef�hrt wird
  #define __            # Instruktion, die nur im Sprung-Fall ausgef�hrt wird
  # Abk�rzungen f�r Anweisungen:
  #define ret   jmp %i7+8    # return from subroutine
  #define retl  jmp %o7+8    # return from leaf subroutine (no save/restore)

        .seg "text"

        .global _getSP
        .global _get_g1
        .global __get_g1

#    extern void* getSP (void);
_getSP: retl
       _ mov %sp,%o0

#    extern long _get_g1 (void);
_get_g1:
__get_g1: retl
       _ mov %g1,%o0

