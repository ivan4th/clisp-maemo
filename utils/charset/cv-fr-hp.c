/* Konversionsprogramm HPUX-Zeichensatz -> SUN4-Zeichensatz */
/* Bruno Haible 4.9.1991 */

#include <stdio.h>

main ()
{ static int tabelle[256];
  /* Tabelle initialisieren: */
  int hp, sun4;
#define HP(x) hp=x;
#define SUN4(y) sun4=y;
#define _ tabelle[hp]=sun4;
  { int i;
    for (i=0;i<128;i++) { SUN4(i) HP(i) _ }
  }
  { int i;
    for (i=0;i<32;i++) { SUN4(128+i) HP(128+i) _ }
  }
  SUN4(160) HP(160) _ /* � */
  SUN4(192) HP(161) _ /* � */
  SUN4(194) HP(162) _ /* � */
  SUN4(200) HP(163) _ /* � */
  SUN4(202) HP(164) _ /* � */
  SUN4(203) HP(165) _ /* � */
  SUN4(206) HP(166) _ /* � */
  SUN4(207) HP(167) _ /* � */
  SUN4(180) HP(168) _ /* � */
  SUN4(-1) HP(169) _ /* accent grave */
  SUN4(-1) HP(170) _ /* circumflex */
  SUN4(168) HP(171) _ /* � */
  SUN4(-1) HP(172) _ /* tilde accent */
  SUN4(217) HP(173) _ /* � */
  SUN4(219) HP(174) _ /* � */
  SUN4(163) HP(175) _ /* Italian lira = � */
  SUN4(175) HP(176) _ /* over line */
  SUN4(221) HP(177) _ /* � */
  SUN4(253) HP(178) _ /* � */
  SUN4(176) HP(179) _ /* � */
  SUN4(199) HP(180) _ /* � */
  SUN4(231) HP(181) _ /* � */
  SUN4(209) HP(182) _ /* � */
  SUN4(241) HP(183) _ /* � */
  SUN4(161) HP(184) _ /* � */
  SUN4(191) HP(185) _ /* � */
  SUN4(164) HP(186) _ /* � */
  SUN4(163) HP(187) _ /* � */
  SUN4(165) HP(188) _ /* � */
  SUN4(167) HP(189) _ /* � */
  SUN4(-1) HP(190) _ /* Dutch guilder */
  SUN4(162) HP(191) _ /* � */
  SUN4(226) HP(192) _ /* � */
  SUN4(234) HP(193) _ /* � */
  SUN4(244) HP(194) _ /* � */
  SUN4(251) HP(195) _ /* � */
  SUN4(225) HP(196) _ /* � */
  SUN4(233) HP(197) _ /* � */
  SUN4(243) HP(198) _ /* � */
  SUN4(250) HP(199) _ /* � */
  SUN4(224) HP(200) _ /* � */
  SUN4(232) HP(201) _ /* � */
  SUN4(242) HP(202) _ /* � */
  SUN4(249) HP(203) _ /* � */
  SUN4(228) HP(204) _ /* � */
  SUN4(235) HP(205) _ /* � */
  SUN4(246) HP(206) _ /* � */
  SUN4(252) HP(207) _ /* � */
  SUN4(197) HP(208) _ /* � */
  SUN4(238) HP(209) _ /* � */
  SUN4(216) HP(210) _ /* � */
  SUN4(198) HP(211) _ /* � */
  SUN4(229) HP(212) _ /* � */
  SUN4(237) HP(213) _ /* � */
  SUN4(248) HP(214) _ /* � */
  SUN4(230) HP(215) _ /* � */
  SUN4(196) HP(216) _ /* � */
  SUN4(236) HP(217) _ /* � */
  SUN4(214) HP(218) _ /* � */
  SUN4(220) HP(219) _ /* � */
  SUN4(201) HP(220) _ /* � */
  SUN4(239) HP(221) _ /* � */
  SUN4(223) HP(222) _ /* � */
  SUN4(212) HP(223) _ /* � */
  SUN4(193) HP(224) _ /* � */
  SUN4(195) HP(225) _ /* � */
  SUN4(227) HP(226) _ /* � */
  SUN4(208) HP(227) _ /* � */
  SUN4(240) HP(228) _ /* � */
  SUN4(205) HP(229) _ /* � */
  SUN4(204) HP(230) _ /* � */
  SUN4(211) HP(231) _ /* � */
  SUN4(210) HP(232) _ /* � */
  SUN4(213) HP(233) _ /* � */
  SUN4(245) HP(234) _ /* � */
  SUN4(-1) HP(235) _ /* S caron */
  SUN4(-1) HP(236) _ /* s caron */
  SUN4(218) HP(237) _ /* � */
  SUN4(-1) HP(238) _ /* Y umlaut */
  SUN4(255) HP(239) _ /* � */
  SUN4(222) HP(240) _ /* � */
  SUN4(254) HP(241) _ /* � */
  SUN4(183) HP(242) _ /* � */
  SUN4(181) HP(243) _ /* � */
  SUN4(182) HP(244) _ /* pilcrow, paragraph */
  SUN4(190) HP(245) _ /* � */
  SUN4(173) HP(246) _ /* long dash */
  SUN4(188) HP(247) _ /* � */
  SUN4(189) HP(248) _ /* � */
  SUN4(170) HP(249) _ /* � */
  SUN4(186) HP(250) _ /* � */
  SUN4(171) HP(251) _ /* � */
  SUN4(-1) HP(252) _ /* solid */
  SUN4(187) HP(253) _ /* � */
  SUN4(177) HP(254) _ /* � */
  SUN4(-1) HP(255) _ /* inv. K */
#undef _
#undef SUN4
#undef HP
  { int fehler = 0;
    int c;
    while (!((c = getchar()) == EOF))
      { c = tabelle[c];
        if (c < 0) { fehler++; } else putchar(c);
      }
    if (!(fehler == 0))
      { fprintf(stderr,"%d illegal characters\n",fehler); exit(1); }
      else
      if (ferror(stdin) || ferror(stdout))
        { exit(1); }
        else
        { exit(0); }
} }
