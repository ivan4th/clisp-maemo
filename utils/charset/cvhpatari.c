/* Konversionsprogramm HPUX-Zeichensatz -> Atari-Zeichensatz */
/* Bruno Haible 5.9.1991 */

#include <stdio.h>

main ()
{ static int tabelle[256];
  /* Tabelle initialisieren: */
  int atari, hp;
#define ATARI(x) atari=x;
#define HP(y) hp=y;
#define _ tabelle[hp]=atari;
  { int i;
    for (i=0;i<128;i++) { HP(i) ATARI(i) _ }
  }
  HP(160) ATARI(-1) _
  HP(161) ATARI(182) _ /* � */
  HP(162) ATARI(-1) _
  HP(163) ATARI(-1) _
  HP(164) ATARI(-1) _
  HP(165) ATARI(-1) _
  HP(166) ATARI(-1) _
  HP(167) ATARI(-1) _
  HP(168) ATARI(186) _ /* � */
  HP(169) ATARI(-1) _
  HP(170) ATARI(-1) _
  HP(171) ATARI(185) _ /* � */
  HP(172) ATARI(-1) _
  HP(173) ATARI(-1) _
  HP(174) ATARI(-1) _
  HP(175) ATARI(156) _ /* � */
  HP(176) ATARI(255) _ /* � */
  HP(177) ATARI(-1) _
  HP(178) ATARI(-1) _
  HP(179) ATARI(248) _ /* � */
  HP(180) ATARI(128) _ /* � */
  HP(181) ATARI(135) _ /* � */
  HP(182) ATARI(165) _ /* � */
  HP(183) ATARI(164) _ /* � */
  HP(184) ATARI(173) _ /* � */
  HP(185) ATARI(168) _ /* � */
  HP(186) ATARI(-1) _
  HP(187) ATARI(156) _ /* � */
  HP(188) ATARI(157) _ /* � */
  HP(189) ATARI(221) _ /* � */
  HP(190) ATARI(159) _ /*  */
  HP(191) ATARI(155) _ /* � */
  HP(192) ATARI(131) _ /* � */
  HP(193) ATARI(136) _ /* � */
  HP(194) ATARI(147) _ /* � */
  HP(195) ATARI(150) _ /* � */
  HP(196) ATARI(160) _ /* � */
  HP(197) ATARI(130) _ /* � */
  HP(198) ATARI(162) _ /* � */
  HP(199) ATARI(163) _ /* � */
  HP(200) ATARI(133) _ /* � */
  HP(201) ATARI(138) _ /* � */
  HP(202) ATARI(149) _ /* � */
  HP(203) ATARI(151) _ /* � */
  HP(204) ATARI(132) _ /* � */
  HP(205) ATARI(137) _ /* � */
  HP(206) ATARI(148) _ /* � */
  HP(207) ATARI(129) _ /* � */
  HP(208) ATARI(143) _ /* � */
  HP(209) ATARI(140) _ /* � */
  HP(210) ATARI(178) _ /* � */
  HP(211) ATARI(146) _ /* � */
  HP(212) ATARI(134) _ /* � */
  HP(213) ATARI(161) _ /* � */
  HP(214) ATARI(179) _ /* � */
  HP(215) ATARI(145) _ /* � */
  HP(216) ATARI(142) _ /* � */
  HP(217) ATARI(141) _ /* � */
  HP(218) ATARI(153) _ /* � */
  HP(219) ATARI(154) _ /* � */
  HP(220) ATARI(144) _ /* � */
  HP(221) ATARI(139) _ /* � */
  HP(222) ATARI(158) _ /* � */
  HP(223) ATARI(-1) _
  HP(224) ATARI(-1) _
  HP(225) ATARI(183) _ /* � */
  HP(226) ATARI(176) _ /* � */
  HP(227) ATARI(-1) _
  HP(228) ATARI(-1) _
  HP(229) ATARI(-1) _
  HP(230) ATARI(-1) _
  HP(231) ATARI(-1) _
  HP(232) ATARI(-1) _
  HP(233) ATARI(184) _ /* � */
  HP(234) ATARI(177) _ /* � */
  HP(235) ATARI(-1) _
  HP(236) ATARI(-1) _
  HP(237) ATARI(-1) _
  HP(238) ATARI(-1) _
  HP(239) ATARI(152) _ /* � */
  HP(240) ATARI(-1) _
  HP(241) ATARI(-1) _
  HP(242) ATARI(-1) _
  HP(243) ATARI(230) _ /* � */
  HP(244) ATARI(188) _ /* � */
  HP(245) ATARI(-1) _
  HP(246) ATARI(-1) _
  HP(247) ATARI(172) _ /* � */
  HP(248) ATARI(171) _ /* � */
  HP(249) ATARI(166) _ /* � */
  HP(250) ATARI(167) _ /* � */
  HP(251) ATARI(174) _ /* � */
  HP(252) ATARI(-1) _
  HP(253) ATARI(175) _ /* � */
  HP(254) ATARI(241) _ /* � */
  HP(255) ATARI(-1) _
#undef _
#undef HP
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
