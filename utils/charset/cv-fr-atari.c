/* Konversionsprogramm Atari-Zeichensatz -> SUN4-Zeichensatz */
/* Bruno Haible 17.1.1991 */

#include <stdio.h>

main ()
{ static int tabelle[256];
  /* Tabelle initialisieren: */
  int atari, sun4;
#define ATARI(x) atari=x;
#define SUN4(y) sun4=y;
#define _ tabelle[atari]=sun4;
  { int i;
    for (i=0;i<128;i++) { SUN4(i) ATARI(i) _ }
  }
  SUN4(199) ATARI(128) _ /* � */
  SUN4(252) ATARI(129) _ /* � */
  SUN4(233) ATARI(130) _ /* � */
  SUN4(226) ATARI(131) _ /* � */
  SUN4(228) ATARI(132) _ /* � */
  SUN4(224) ATARI(133) _ /* � */
  SUN4(229) ATARI(134) _ /* � */
  SUN4(231) ATARI(135) _ /* � */
  SUN4(234) ATARI(136) _ /* � */
  SUN4(235) ATARI(137) _ /* � */
  SUN4(232) ATARI(138) _ /* � */
  SUN4(239) ATARI(139) _ /* � */
  SUN4(238) ATARI(140) _ /* � */
  SUN4(236) ATARI(141) _ /* � */
  SUN4(196) ATARI(142) _ /* � */
  SUN4(197) ATARI(143) _ /* � */
  SUN4(201) ATARI(144) _ /* � */
  SUN4(230) ATARI(145) _ /* � */
  SUN4(198) ATARI(146) _ /* � */
  SUN4(244) ATARI(147) _ /* � */
  SUN4(246) ATARI(148) _ /* � */
  SUN4(242) ATARI(149) _ /* � */
  SUN4(251) ATARI(150) _ /* � */
  SUN4(249) ATARI(151) _ /* � */
  SUN4(255) ATARI(152) _ /* � */
  SUN4(214) ATARI(153) _ /* � */
  SUN4(220) ATARI(154) _ /* � */
  SUN4(162) ATARI(155) _ /* � */
  SUN4(163) ATARI(156) _ /* � */
  SUN4(165) ATARI(157) _ /* � */
  SUN4(223) ATARI(158) _ /* � */
  SUN4(-1) ATARI(159) _
  SUN4(225) ATARI(160) _ /* � */
  SUN4(237) ATARI(161) _ /* � */
  SUN4(243) ATARI(162) _ /* � */
  SUN4(250) ATARI(163) _ /* � */
  SUN4(241) ATARI(164) _ /* � */
  SUN4(209) ATARI(165) _ /* � */
  SUN4(170) ATARI(166) _ /* � */
  SUN4(186) ATARI(167) _ /* � */
  SUN4(191) ATARI(168) _ /* � */
  SUN4(-1) ATARI(169) _ /* f */
  SUN4(172) ATARI(170) _ /* � */
  SUN4(189) ATARI(171) _ /* � */
  SUN4(188) ATARI(172) _ /* � */
  SUN4(161) ATARI(173) _ /* � */
  SUN4(171) ATARI(174) _ /* � */
  SUN4(187) ATARI(175) _ /* � */
  SUN4(227) ATARI(176) _ /* � */
  SUN4(245) ATARI(177) _ /* � */
  SUN4(216) ATARI(178) _ /* � */
  SUN4(248) ATARI(179) _ /* � */
  SUN4(-1) ATARI(180) _ /* oe */
  SUN4(-1) ATARI(181) _ /* OE */
  SUN4(192) ATARI(182) _ /* � */
  SUN4(195) ATARI(183) _ /* � */
  SUN4(213) ATARI(184) _ /* � */
  SUN4(168) ATARI(185) _ /* � */
  SUN4(180) ATARI(186) _ /* � */
  SUN4(43) ATARI(187) _ /* + */
  SUN4(182) ATARI(188) _ /* � */
  SUN4(169) ATARI(189) _ /* � */
  SUN4(174) ATARI(190) _ /* � */
  SUN4(-1) ATARI(191) _ /* TM */
  SUN4(-1) ATARI(192) _
  SUN4(-1) ATARI(193) _
  SUN4(-1) ATARI(194) _
  SUN4(-1) ATARI(195) _
  SUN4(-1) ATARI(196) _
  SUN4(-1) ATARI(197) _
  SUN4(-1) ATARI(198) _
  SUN4(-1) ATARI(199) _
  SUN4(-1) ATARI(200) _
  SUN4(-1) ATARI(201) _
  SUN4(-1) ATARI(202) _
  SUN4(-1) ATARI(203) _
  SUN4(-1) ATARI(204) _
  SUN4(-1) ATARI(205) _
  SUN4(-1) ATARI(206) _
  SUN4(-1) ATARI(207) _
  SUN4(-1) ATARI(208) _
  SUN4(-1) ATARI(209) _
  SUN4(-1) ATARI(210) _
  SUN4(-1) ATARI(211) _
  SUN4(-1) ATARI(212) _
  SUN4(-1) ATARI(213) _
  SUN4(-1) ATARI(214) _
  SUN4(-1) ATARI(215) _
  SUN4(-1) ATARI(216) _
  SUN4(-1) ATARI(217) _
  SUN4(-1) ATARI(218) _
  SUN4(-1) ATARI(219) _
  SUN4(-1) ATARI(220) _
  SUN4(167) ATARI(221) _ /* � */
  SUN4(-1) ATARI(222) _
  SUN4(-1) ATARI(223) _
  SUN4(-1) ATARI(224) _
  SUN4(-1) ATARI(225) _
  SUN4(-1) ATARI(226) _
  SUN4(-1) ATARI(227) _
  SUN4(-1) ATARI(228) _
  SUN4(-1) ATARI(229) _
  SUN4(181) ATARI(230) _ /* � */
  SUN4(-1) ATARI(231) _
  SUN4(-1) ATARI(232) _
  SUN4(-1) ATARI(233) _
  SUN4(-1) ATARI(234) _
  SUN4(-1) ATARI(235) _
  SUN4(-1) ATARI(236) _
  SUN4(-1) ATARI(237) _
  SUN4(-1) ATARI(238) _
  SUN4(-1) ATARI(239) _
  SUN4(-1) ATARI(240) _
  SUN4(177) ATARI(241) _ /* � */
  SUN4(-1) ATARI(242) _
  SUN4(-1) ATARI(243) _
  SUN4(-1) ATARI(244) _
  SUN4(-1) ATARI(245) _
  SUN4(247) ATARI(246) _ /* � */
  SUN4(-1) ATARI(247) _
  SUN4(176) ATARI(248) _ /* � */
  SUN4(-1) ATARI(249) _
  SUN4(-1) ATARI(250) _
  SUN4(-1) ATARI(251) _
  SUN4(-1) ATARI(252) _
  SUN4(178) ATARI(253) _ /* � */
  SUN4(179) ATARI(254) _ /* � */
  SUN4(175) ATARI(255) _ /* � */
#undef _
#undef SUN4
#undef ATARI
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
