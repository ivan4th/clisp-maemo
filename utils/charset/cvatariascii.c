/* Konversionsprogramm Atari-Zeichensatz -> ASCII-Zeichensatz */
/* Bruno Haible 13.12.1991 */

#include <stdio.h>

main ()
{ static long tabelle[256];
  /* Tabelle initialisieren: */
  int atari;
  long ascii;
#define ATARI(x) atari=x;
#define ASCII(y) ascii=y;
#define ASCII2(y1,y2) ascii=(y2<<8)|y1;
#define ASCII3(y1,y2,y3) ascii=(y3<<16)|(y2<<8)|y1;
#define _ tabelle[atari]=ascii;
  { int i;
    for (i=0;i<128;i++) { ATARI(i) ASCII(i) _ }
  }
  ATARI(128) ASCII('C') _ /* � */
  ATARI(129) ASCII2('u','e') _ /* � */
  ATARI(130) ASCII2('\'','e') _ /* � */
  ATARI(131) ASCII2('^','a') _ /* � */
  ATARI(132) ASCII2('a','e') _ /* � */
  ATARI(133) ASCII2('`','a') _ /* � */
  ATARI(134) ASCII('a') _ /* � */
  ATARI(135) ASCII('c') _ /* � */
  ATARI(136) ASCII2('^','e') _ /* � */
  ATARI(137) ASCII2('\"','e') _ /* � */
  ATARI(138) ASCII2('`','e') _ /* � */
  ATARI(139) ASCII2('\"','i') _ /* � */
  ATARI(140) ASCII2('^','i') _ /* � */
  ATARI(141) ASCII2('`','i') _ /* � */
  ATARI(142) ASCII2('A','e') _ /* � */
  ATARI(143) ASCII('A') _ /* � */
  ATARI(144) ASCII2('\'','E') _ /* � */
  ATARI(145) ASCII2('a','e') _ /* � */
  ATARI(146) ASCII2('A','E') _ /* � */
  ATARI(147) ASCII2('^','o') _ /* � */
  ATARI(148) ASCII2('o','e') _ /* � */
  ATARI(149) ASCII2('`','o') _ /* � */
  ATARI(150) ASCII2('^','u') _ /* � */
  ATARI(151) ASCII2('`','u') _ /* � */
  ATARI(152) ASCII2('\"','y') _ /* � */
  ATARI(153) ASCII2('O','e') _ /* � */
  ATARI(154) ASCII2('U','e') _ /* � */
  ATARI(155) ASCII('c') _ /* � */
  ATARI(156) ASCII2('l','b') _ /* � */
  ATARI(157) ASCII3('y','e','n') _ /* � */
  ATARI(158) ASCII2('s','s') _ /* � */
  ATARI(159) ASCII2('f','l') _
  ATARI(160) ASCII2('\'','a') _ /* � */
  ATARI(161) ASCII2('\'','i') _ /* � */
  ATARI(162) ASCII2('\'','o') _ /* � */
  ATARI(163) ASCII2('\'','u') _ /* � */
  ATARI(164) ASCII2('~','n') _ /* � */
  ATARI(165) ASCII2('~','N') _ /* � */
  ATARI(166) ASCII('a') _ /* � */
  ATARI(167) ASCII('o') _ /* � */
  ATARI(168) ASCII('?') _ /* � */
  ATARI(169) ASCII(0) _
  ATARI(170) ASCII3('n','o','t') _ /* � */
  ATARI(171) ASCII3('1','/','2') _ /* � */
  ATARI(172) ASCII3('1','/','4') _ /* � */
  ATARI(173) ASCII('!') _ /* � */
  ATARI(174) ASCII2('<','<') _ /* � */
  ATARI(175) ASCII2('>','>') _ /* � */
  ATARI(176) ASCII2('~','a') _ /* � */
  ATARI(177) ASCII2('~','o') _ /* � */
  ATARI(178) ASCII('O') _ /* � */
  ATARI(179) ASCII('o') _ /* � */
  ATARI(180) ASCII2('o','e') _ /* oe */
  ATARI(181) ASCII2('O','e') _ /* OE */
  ATARI(182) ASCII2('`','A') _ /* � */
  ATARI(183) ASCII2('~','A') _ /* � */
  ATARI(184) ASCII2('~','O') _ /* � */
  ATARI(185) ASCII('\"') _ /* � */
  ATARI(186) ASCII('\'') _ /* � */
  ATARI(187) ASCII('+') _ /* + */
  ATARI(188) ASCII('P') _ /* � */
  ATARI(189) ASCII3('(','c',')') _ /* � */
  ATARI(190) ASCII3('(','R',')') _ /* � */
  ATARI(191) ASCII2('T','M') _ /* TM */
  ATARI(192) ASCII2('i','j') _
  ATARI(193) ASCII2('I','J') _
  ATARI(194) ASCII(0) _
  ATARI(195) ASCII(0) _
  ATARI(196) ASCII(0) _
  ATARI(197) ASCII(0) _
  ATARI(198) ASCII(0) _
  ATARI(199) ASCII(0) _
  ATARI(200) ASCII(0) _
  ATARI(201) ASCII(0) _
  ATARI(202) ASCII(0) _
  ATARI(203) ASCII(0) _
  ATARI(204) ASCII(0) _
  ATARI(205) ASCII(0) _
  ATARI(206) ASCII(0) _
  ATARI(207) ASCII(0) _
  ATARI(208) ASCII(0) _
  ATARI(209) ASCII(0) _
  ATARI(210) ASCII(0) _
  ATARI(211) ASCII(0) _
  ATARI(212) ASCII(0) _
  ATARI(213) ASCII(0) _
  ATARI(214) ASCII(0) _
  ATARI(215) ASCII(0) _
  ATARI(216) ASCII(0) _
  ATARI(217) ASCII(0) _
  ATARI(218) ASCII(0) _
  ATARI(219) ASCII(0) _
  ATARI(220) ASCII(0) _
  ATARI(221) ASCII2('S','S') _ /* � */
  ATARI(222) ASCII('^') _
  ATARI(223) ASCII2('o','o') _
  ATARI(224) ASCII(0) _
  ATARI(225) ASCII(0) _
  ATARI(226) ASCII(0) _
  ATARI(227) ASCII(0) _
  ATARI(228) ASCII(0) _
  ATARI(229) ASCII(0) _
  ATARI(230) ASCII('u') _ /* � */
  ATARI(231) ASCII(0) _
  ATARI(232) ASCII(0) _
  ATARI(233) ASCII(0) _
  ATARI(234) ASCII(0) _
  ATARI(235) ASCII(0) _
  ATARI(236) ASCII(0) _
  ATARI(237) ASCII(0) _
  ATARI(238) ASCII2('i','n') _
  ATARI(239) ASCII('n') _
  ATARI(240) ASCII('=') _
  ATARI(241) ASCII2('+','-') _ /* � */
  ATARI(242) ASCII2('>','=') _
  ATARI(243) ASCII2('<','=') _
  ATARI(244) ASCII(0) _
  ATARI(245) ASCII(0) _
  ATARI(246) ASCII(':') _ /* � */
  ATARI(247) ASCII('=') _
  ATARI(248) ASCII2('^','0') _ /* � */
  ATARI(249) ASCII(0) _
  ATARI(250) ASCII(0) _
  ATARI(251) ASCII(0) _
  ATARI(252) ASCII(0) _
  ATARI(253) ASCII2('^','2') _ /* � */
  ATARI(254) ASCII2('^','3') _ /* � */
  ATARI(255) ASCII(0) _ /* � */
#undef _
#undef ASCII3
#undef ASCII2
#undef ASCII
#undef ATARI
  { int fehler = 0;
    int c;
    while (!((c = getchar()) == EOF))
      { long cx = tabelle[c];
        if (cx == 0)
          { fehler++; }
          else
          { do { putchar(cx & 0xFF); cx = cx>>8; } while (!(cx == 0)); }
      }
    if (!(fehler == 0))
      { fprintf(stderr,"%d illegal characters\n",fehler); exit(1); }
      else
      if (ferror(stdin) || ferror(stdout))
        { exit(1); }
        else
        { exit(0); }
} }
