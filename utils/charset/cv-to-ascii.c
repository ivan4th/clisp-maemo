/* Konversionsprogramm ISO-Latin1-Zeichensatz -> ASCII-Zeichensatz */
/* Bruno Haible 11.12.1992 */

#include <stdio.h>

main ()
{ static int tabelle[256];
  /* Tabelle initialisieren: */
  int iso;
  long ascii;
#define ISO(x) iso=x;
#define ASCII(y) ascii=y;
#define ASCII2(y1,y2) ascii=(y2<<8)|y1;
#define ASCII3(y1,y2,y3) ascii=(y3<<16)|(y2<<8)|y1;
#define _ tabelle[iso]=ascii;
  { int i;
    for (i=0;i<128;i++) { ISO(i) ASCII(i) _ }
  }
  { int i;
    for (i=0;i<32;i++) { ISO(128+i) ASCII(i) _ }
  }
  ISO(160) ASCII(' ') _ /* � */
  ISO(161) ASCII('!') _ /* � */
  ISO(162) ASCII('c') _ /* � */
  ISO(163) ASCII2('l','b') _ /* � */
  ISO(164) ASCII(0) _ /* � */
  ISO(165) ASCII3('y','e','n') _ /* � */
  ISO(166) ASCII('|') _ /* � */
  ISO(167) ASCII2('S','S') _ /* � */
  ISO(168) ASCII('\"') _ /* � */
  ISO(169) ASCII3('(','c',')') _ /* � */
  ISO(170) ASCII('a') _ /* � */
  ISO(171) ASCII2('<','<') _ /* � */
  ISO(172) ASCII3('n','o','t') _ /* � */
  ISO(173) ASCII('-') _ /* � */
  ISO(174) ASCII3('(','R',')') _ /* � */
  ISO(175) ASCII(0) _ /* � */
  ISO(176) ASCII2('^','0') _ /* � */
  ISO(177) ASCII2('+','-') _ /* � */
  ISO(178) ASCII2('^','2') _ /* � */
  ISO(179) ASCII2('^','3') _ /* � */
  ISO(180) ASCII('\'') _ /* � */
  ISO(181) ASCII('u') _ /* � */
  ISO(182) ASCII('P') _ /* � */
  ISO(183) ASCII('.') _ /* � */
  ISO(184) ASCII(',') _ /* � */
  ISO(185) ASCII2('^','1') _ /* � */
  ISO(186) ASCII('o') _ /* � */
  ISO(187) ASCII2('>','>') _ /* � */
  ISO(188) ASCII3('1','/','4') _ /* � */
  ISO(189) ASCII3('1','/','2') _ /* � */
  ISO(190) ASCII3('3','/','4') _ /* � */
  ISO(191) ASCII('?') _ /* � */
  ISO(192) ASCII2('`','A') _ /* � */
  ISO(193) ASCII2('\'','A') _ /* � */
  ISO(194) ASCII2('^','A') _ /* � */
  ISO(195) ASCII2('~','A') _ /* � */
  ISO(196) ASCII2('A','e') _ /* � */
  ISO(197) ASCII('A') _ /* � */
  ISO(198) ASCII2('A','E') _ /* � */
  ISO(199) ASCII('C') _ /* � */
  ISO(200) ASCII2('`','E') _ /* � */
  ISO(201) ASCII2('\'','E') _ /* � */
  ISO(202) ASCII2('^','E') _ /* � */
  ISO(203) ASCII2('\"','E') _ /* � */
  ISO(204) ASCII2('`','I') _ /* � */
  ISO(205) ASCII2('\'','I') _ /* � */
  ISO(206) ASCII2('^','I') _ /* � */
  ISO(207) ASCII2('\"','I') _ /* � */
  ISO(208) ASCII('D') _ /* � */
  ISO(209) ASCII2('~','N') _ /* � */
  ISO(210) ASCII2('`','O') _ /* � */
  ISO(211) ASCII2('\'','O') _ /* � */
  ISO(212) ASCII2('^','O') _ /* � */
  ISO(213) ASCII2('~','O') _ /* � */
  ISO(214) ASCII2('O','e') _ /* � */
  ISO(215) ASCII('x') _ /* � */
  ISO(216) ASCII('O') _ /* � */
  ISO(217) ASCII2('`','U') _ /* � */
  ISO(218) ASCII2('\'','U') _ /* � */
  ISO(219) ASCII2('^','U') _ /* � */
  ISO(220) ASCII2('U','e') _ /* � */
  ISO(221) ASCII2('\'','Y') _ /* � */
  ISO(222) ASCII(0) _ /* � */
  ISO(223) ASCII2('s','s') _ /* � */
  ISO(224) ASCII2('`','a') _ /* � */
  ISO(225) ASCII2('\'','a') _ /* � */
  ISO(226) ASCII2('^','a') _ /* � */
  ISO(227) ASCII2('~','a') _ /* � */
  ISO(228) ASCII2('a','e') _ /* � */
  ISO(229) ASCII('a') _ /* � */
  ISO(230) ASCII2('a','e') _ /* � */
  ISO(231) ASCII('c') _ /* � */
  ISO(232) ASCII2('`','e') _ /* � */
  ISO(233) ASCII2('\'','e') _ /* � */
  ISO(234) ASCII2('^','e') _ /* � */
  ISO(235) ASCII2('\"','e') _ /* � */
  ISO(236) ASCII2('`','i') _ /* � */
  ISO(237) ASCII2('\'','i') _ /* � */
  ISO(238) ASCII2('^','i') _ /* � */
  ISO(239) ASCII2('\"','i') _ /* � */
  ISO(240) ASCII('d') _ /* � */
  ISO(241) ASCII2('~','n') _ /* � */
  ISO(242) ASCII2('`','o') _ /* � */
  ISO(243) ASCII2('\'','o') _ /* � */
  ISO(244) ASCII2('^','o') _ /* � */
  ISO(245) ASCII2('~','o') _ /* � */
  ISO(246) ASCII2('o','e') _ /* � */
  ISO(247) ASCII(':') _ /* � */
  ISO(248) ASCII('o') _ /* � */
  ISO(249) ASCII2('`','u') _ /* � */
  ISO(250) ASCII2('\'','u') _ /* � */
  ISO(251) ASCII2('^','u') _ /* � */
  ISO(252) ASCII2('u','e') _ /* � */
  ISO(253) ASCII2('\'','y') _ /* � */
  ISO(254) ASCII(0) _ /* � */
  ISO(255) ASCII2('\"','y') _ /* � */
#undef _
#undef ASCII3
#undef ASCII2
#undef ASCII
#undef ISO
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
