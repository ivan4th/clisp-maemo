/*
 * Functions for characters and strings for CLISP
 * Bruno Haible 1990-2002
 * Sam Steingold 1998-2002
 * German comments translated into English: Stefan Kain 2002-09-20
 */

#include "lispbibl.c"

/* character conversion tables: */
#if defined(UNICODE)
/* here are the registered bijective case (small<-->CAP) transformations
 for Unicode. */
#elif defined(ISOLATIN_CHS)
/* here are the registered bijective case (small<-->CAP) transformations
  small 61 ... 7A E0 ... F6 F8 ... FE
  CAP   41 ... 5A C0 ... D6 D8 ... DE
  both  aA ... zZ àÀ ... öÖ øØ ... þÞ */
#elif defined(HPROMAN8_CHS)
/* here are the registered bijective case (small<-->CAP) transformations
  small 61 ... 7A C4 C5 D5 C6 C7 B2 C0 C1 D1 C2 C3 C8 C9 D9 CA CB
  CAP   41 ... 5A E0 DC E5 E7 ED B1 A2 A4 A6 DF AE A1 A3 E6 E8 AD
  which aA ... zZ áÁ éÉ íÍ óÓ úÚ ýÝ âÂ êÊ îÎ ôÔ ûÛ àÀ èÈ ìÌ òÒ ùÙ
  small CC CD DD CE CF EF E2 B7 EA D4 D7 D6 B5 EC E4 F1
  CAP   D8 A5 A7 DA DB EE E1 B6 E9 D0 D3 D2 B4 EB E3 F0
  which äÄ ëË ïÏ öÖ üÜ ÿŸ ãÃ ñÑ õÕ åÅ æÆ øØ çÇ šŠ ðÐ þÞ */
#elif defined(NEXTSTEP_CHS)
/* here are the registered bijective case (small<-->CAP) transformations
 small 61 ... 7A D5 ... E0 E2 E4 ... E7 EC ... F0 F1 F2 .. F4 F6 F7 F9 FA FC
 CAP   41 ... 5A 81 ... 8C 8D 8E ... 91 92 ... 96 E1 97 .. 99 9A 9B E9 EA 9C
 which aA ... zZ àÀ ... ìÌ íÍ îÎ ... ñÑ òÒ ... öÖ æÆ ùÙ .. ûÛ üÜ ýÝ øØ œŒ þÞ */
#elif defined(IBMPC_CHS)
/* here are the registered bijective case (small<-->CAP) transformations
  small 61 ... 7A 87 81 82 84 86 91 94 A4
  CAP   41 ... 5A 80 9A 90 8E 8F 92 99 A5
  both  aA ... zZ çÇ üÜ éÉ äÄ åÅ æÆ öÖ ñÑ */
#else /* defined(ASCII_CHS) */
/* here are the registered bijective case (small<-->CAP) transformations
  small 61 ... 7A
  CAP   41 ... 5A
  both  aA ... zZ */
#endif

#ifdef UNICODE
/* No-conversion table, used by up_case_table and down_case_table. */
static const uint16 nop_page[256] = {
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
};
#endif

/* Converts byte ch into an uppercase letter */
global chart up_case (chart ch) {
 #ifdef UNICODE
  #include "uni_upcase.c"
  var cint c = as_cint(ch);
  if (c < sizeof(up_case_table)/sizeof(up_case_table[0]) << 8)
    return as_chart(c+(sint16)up_case_table[c>>8][c&0xFF]);
  else
    return ch;
 #else
  /* table for conversion into uppercase letters: */
  local const cint up_case_table[char_code_limit] =
   #if defined(ISOLATIN_CHS)
    { 0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0A,0x0B,0x0C,0x0D,0x0E,0x0F,
      0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1A,0x1B,0x1C,0x1D,0x1E,0x1F,
      0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,0x28,0x29,0x2A,0x2B,0x2C,0x2D,0x2E,0x2F,
      0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x3A,0x3B,0x3C,0x3D,0x3E,0x3F,
      0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x4A,0x4B,0x4C,0x4D,0x4E,0x4F,
      0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57,0x58,0x59,0x5A,0x5B,0x5C,0x5D,0x5E,0x5F,
      0x60,0x41,0x42,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x4A,0x4B,0x4C,0x4D,0x4E,0x4F,
      0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57,0x58,0x59,0x5A,0x7B,0x7C,0x7D,0x7E,0x7F,
      0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,0x88,0x89,0x8A,0x8B,0x8C,0x8D,0x8E,0x8F,
      0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,0x98,0x99,0x9A,0x9B,0x9C,0x9D,0x9E,0x9F,
      0xA0,0xA1,0xA2,0xA3,0xA4,0xA5,0xA6,0xA7,0xA8,0xA9,0xAA,0xAB,0xAC,0xAD,0xAE,0xAF,
      0xB0,0xB1,0xB2,0xB3,0xB4,0xB5,0xB6,0xB7,0xB8,0xB9,0xBA,0xBB,0xBC,0xBD,0xBE,0xBF,
      0xC0,0xC1,0xC2,0xC3,0xC4,0xC5,0xC6,0xC7,0xC8,0xC9,0xCA,0xCB,0xCC,0xCD,0xCE,0xCF,
      0xD0,0xD1,0xD2,0xD3,0xD4,0xD5,0xD6,0xD7,0xD8,0xD9,0xDA,0xDB,0xDC,0xDD,0xDE,0xDF,
      0xC0,0xC1,0xC2,0xC3,0xC4,0xC5,0xC6,0xC7,0xC8,0xC9,0xCA,0xCB,0xCC,0xCD,0xCE,0xCF,
      0xD0,0xD1,0xD2,0xD3,0xD4,0xD5,0xD6,0xF7,0xD8,0xD9,0xDA,0xDB,0xDC,0xDD,0xDE,0xFF,
    };
   #elif defined(HPROMAN8_CHS)
    { 0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0A,0x0B,0x0C,0x0D,0x0E,0x0F,
      0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1A,0x1B,0x1C,0x1D,0x1E,0x1F,
      0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,0x28,0x29,0x2A,0x2B,0x2C,0x2D,0x2E,0x2F,
      0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x3A,0x3B,0x3C,0x3D,0x3E,0x3F,
      0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x4A,0x4B,0x4C,0x4D,0x4E,0x4F,
      0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57,0x58,0x59,0x5A,0x5B,0x5C,0x5D,0x5E,0x5F,
      0x60,0x41,0x42,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x4A,0x4B,0x4C,0x4D,0x4E,0x4F,
      0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57,0x58,0x59,0x5A,0x7B,0x7C,0x7D,0x7E,0x7F,
      0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,0x88,0x89,0x8A,0x8B,0x8C,0x8D,0x8E,0x8F,
      0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,0x98,0x99,0x9A,0x9B,0x9C,0x9D,0x9E,0x9F,
      0xA0,0xA1,0xA2,0xA3,0xA4,0xA5,0xA6,0xA7,0xA8,0xA9,0xAA,0xAB,0xAC,0xAD,0xAE,0xAF,
      0xB0,0xB1,0xB2,0xB3,0xB4,0xB4,0xB6,0xB6,0xB8,0xB9,0xBA,0xBB,0xBC,0xBD,0xBE,0xBF,
      0xA2,0xA4,0xDF,0xAE,0xE0,0xDC,0xE7,0xB2,0xA1,0xA3,0xE8,0xAD,0xD8,0xA5,0xDA,0xDB,
      0xD0,0xA6,0xD2,0xD3,0xD0,0xE5,0xD2,0xD3,0xD8,0xE6,0xDA,0xDB,0xDC,0xA7,0xDE,0xDF,
      0xE0,0xE1,0xE1,0xE3,0xE3,0xE5,0xE6,0xE7,0xE8,0xE9,0xE9,0xEB,0xEB,0xED,0xEE,0xEE,
      0xF0,0xF0,0xF2,0xF3,0xF4,0xF5,0xF6,0xF7,0xF8,0xF9,0xFA,0xFB,0xFC,0xFD,0xFE,0xFF,
    };
   #elif defined(NEXTSTEP_CHS)
    { 0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0A,0x0B,0x0C,0x0D,0x0E,0x0F,
      0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1A,0x1B,0x1C,0x1D,0x1E,0x1F,
      0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,0x28,0x29,0x2A,0x2B,0x2C,0x2D,0x2E,0x2F,
      0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x3A,0x3B,0x3C,0x3D,0x3E,0x3F,
      0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x4A,0x4B,0x4C,0x4D,0x4E,0x4F,
      0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57,0x58,0x59,0x5A,0x5B,0x5C,0x5D,0x5E,0x5F,
      0x60,0x41,0x42,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x4A,0x4B,0x4C,0x4D,0x4E,0x4F,
      0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57,0x58,0x59,0x5A,0x7B,0x7C,0x7D,0x7E,0x7F,
      0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,0x88,0x89,0x8A,0x8B,0x8C,0x8D,0x8E,0x8F,
      0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,0x98,0x99,0x9A,0x9B,0x9C,0x9D,0x9E,0x9F,
      0xA0,0xA1,0xA2,0xA3,0xA4,0xA5,0xA6,0xA7,0xA8,0xA9,0xAA,0xAB,0xAC,0xAD,0xAE,0xAF,
      0xB0,0xB1,0xB2,0xB3,0xB4,0xB5,0xB6,0xB7,0xB8,0xB9,0xBA,0xBB,0xBC,0xBD,0xBE,0xBF,
      0xC0,0xC1,0xC2,0xC3,0xC4,0xC5,0xC6,0xC7,0xC8,0xC9,0xCA,0xCB,0xCC,0xCD,0xCE,0xCF,
      0xD0,0xD1,0xD2,0xD3,0xD4,0x81,0x82,0x83,0x84,0x85,0x86,0x87,0x88,0x89,0x8A,0x8B,
      0x8C,0xE1,0x8D,0xE3,0x8E,0x8F,0x90,0x91,0xE8,0xE9,0xEA,0xEB,0x92,0x93,0x94,0x95,
      0x96,0xE1,0x97,0x98,0x99,0xF5,0x9A,0x9B,0xF8,0xE9,0xEA,0xFB,0x9C,0xFD,0xFE,0xFF,
    };
   #elif defined(IBMPC_CHS)
    { 0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0A,0x0B,0x0C,0x0D,0x0E,0x0F,
      0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1A,0x1B,0x1C,0x1D,0x1E,0x1F,
      0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,0x28,0x29,0x2A,0x2B,0x2C,0x2D,0x2E,0x2F,
      0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x3A,0x3B,0x3C,0x3D,0x3E,0x3F,
      0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x4A,0x4B,0x4C,0x4D,0x4E,0x4F,
      0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57,0x58,0x59,0x5A,0x5B,0x5C,0x5D,0x5E,0x5F,
      0x60,0x41,0x42,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x4A,0x4B,0x4C,0x4D,0x4E,0x4F,
      0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57,0x58,0x59,0x5A,0x7B,0x7C,0x7D,0x7E,0x7F,
      0x80,0x9A,0x90,0x83,0x8E,0x85,0x8F,0x80,0x88,0x89,0x8A,0x8B,0x8C,0x8D,0x8E,0x8F,
      0x90,0x92,0x92,0x93,0x99,0x95,0x96,0x97,0x98,0x99,0x9A,0x9B,0x9C,0x9D,0x9E,0x9F,
      0xA0,0xA1,0xA2,0xA3,0xA5,0xA5,0xA6,0xA7,0xA8,0xA9,0xAA,0xAB,0xAC,0xAD,0xAE,0xAF,
      0xB0,0xB1,0xB2,0xB3,0xB4,0xB5,0xB6,0xB7,0xB8,0xB9,0xBA,0xBB,0xBC,0xBD,0xBE,0xBF,
      0xC0,0xC1,0xC2,0xC3,0xC4,0xC5,0xC6,0xC7,0xC8,0xC9,0xCA,0xCB,0xCC,0xCD,0xCE,0xCF,
      0xD0,0xD1,0xD2,0xD3,0xD4,0xD5,0xD6,0xD7,0xD8,0xD9,0xDA,0xDB,0xDC,0xDD,0xDE,0xDF,
      0xE0,0xE1,0xE2,0xE3,0xE4,0xE5,0xE6,0xE7,0xE8,0xE9,0xEA,0xEB,0xEC,0xED,0xEE,0xEF,
      0xF0,0xF1,0xF2,0xF3,0xF4,0xF5,0xF6,0xF7,0xF8,0xF9,0xFA,0xFB,0xFC,0xFD,0xFE,0xFF,
    };
   #else /* standard ascii conversion table: only a..z --> A..Z */
    { 0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0A,0x0B,0x0C,0x0D,0x0E,0x0F,
      0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1A,0x1B,0x1C,0x1D,0x1E,0x1F,
      0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,0x28,0x29,0x2A,0x2B,0x2C,0x2D,0x2E,0x2F,
      0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x3A,0x3B,0x3C,0x3D,0x3E,0x3F,
      0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x4A,0x4B,0x4C,0x4D,0x4E,0x4F,
      0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57,0x58,0x59,0x5A,0x5B,0x5C,0x5D,0x5E,0x5F,
      0x60,0x41,0x42,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x4A,0x4B,0x4C,0x4D,0x4E,0x4F,
      0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57,0x58,0x59,0x5A,0x7B,0x7C,0x7D,0x7E,0x7F,
      0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,0x88,0x89,0x8A,0x8B,0x8C,0x8D,0x8E,0x8F,
      0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,0x98,0x99,0x9A,0x9B,0x9C,0x9D,0x9E,0x9F,
      0xA0,0xA1,0xA2,0xA3,0xA4,0xA5,0xA6,0xA7,0xA8,0xA9,0xAA,0xAB,0xAC,0xAD,0xAE,0xAF,
      0xB0,0xB1,0xB2,0xB3,0xB4,0xB5,0xB6,0xB7,0xB8,0xB9,0xBA,0xBB,0xBC,0xBD,0xBE,0xBF,
      0xC0,0xC1,0xC2,0xC3,0xC4,0xC5,0xC6,0xC7,0xC8,0xC9,0xCA,0xCB,0xCC,0xCD,0xCE,0xCF,
      0xD0,0xD1,0xD2,0xD3,0xD4,0xD5,0xD6,0xD7,0xD8,0xD9,0xDA,0xDB,0xDC,0xDD,0xDE,0xDF,
      0xE0,0xE1,0xE2,0xE3,0xE4,0xE5,0xE6,0xE7,0xE8,0xE9,0xEA,0xEB,0xEC,0xED,0xEE,0xEF,
      0xF0,0xF1,0xF2,0xF3,0xF4,0xF5,0xF6,0xF7,0xF8,0xF9,0xFA,0xFB,0xFC,0xFD,0xFE,0xFF,
    };
   #endif
  return as_chart(up_case_table[as_cint(ch)]);
 #endif
}

/* Converts byte ch into a lowercase letter */
global chart down_case (chart ch) {
 #ifdef UNICODE
  #include "uni_downcase.c"
  var cint c = as_cint(ch);
  if (c < sizeof(down_case_table)/sizeof(down_case_table[0]) << 8)
    return as_chart(c+(sint16)down_case_table[c>>8][c&0xFF]);
  else
    return ch;
 #else
  /* table for conversion into lowercase letters: */
  local const cint down_case_table[char_code_limit] =
   #if defined(ISOLATIN_CHS)
    { 0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0A,0x0B,0x0C,0x0D,0x0E,0x0F,
      0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1A,0x1B,0x1C,0x1D,0x1E,0x1F,
      0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,0x28,0x29,0x2A,0x2B,0x2C,0x2D,0x2E,0x2F,
      0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x3A,0x3B,0x3C,0x3D,0x3E,0x3F,
      0x40,0x61,0x62,0x63,0x64,0x65,0x66,0x67,0x68,0x69,0x6A,0x6B,0x6C,0x6D,0x6E,0x6F,
      0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77,0x78,0x79,0x7A,0x5B,0x5C,0x5D,0x5E,0x5F,
      0x60,0x61,0x62,0x63,0x64,0x65,0x66,0x67,0x68,0x69,0x6A,0x6B,0x6C,0x6D,0x6E,0x6F,
      0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77,0x78,0x79,0x7A,0x7B,0x7C,0x7D,0x7E,0x7F,
      0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,0x88,0x89,0x8A,0x8B,0x8C,0x8D,0x8E,0x8F,
      0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,0x98,0x99,0x9A,0x9B,0x9C,0x9D,0x9E,0x9F,
      0xA0,0xA1,0xA2,0xA3,0xA4,0xA5,0xA6,0xA7,0xA8,0xA9,0xAA,0xAB,0xAC,0xAD,0xAE,0xAF,
      0xB0,0xB1,0xB2,0xB3,0xB4,0xB5,0xB6,0xB7,0xB8,0xB9,0xBA,0xBB,0xBC,0xBD,0xBE,0xBF,
      0xE0,0xE1,0xE2,0xE3,0xE4,0xE5,0xE6,0xE7,0xE8,0xE9,0xEA,0xEB,0xEC,0xED,0xEE,0xEF,
      0xF0,0xF1,0xF2,0xF3,0xF4,0xF5,0xF6,0xD7,0xF8,0xF9,0xFA,0xFB,0xFC,0xFD,0xFE,0xDF,
      0xE0,0xE1,0xE2,0xE3,0xE4,0xE5,0xE6,0xE7,0xE8,0xE9,0xEA,0xEB,0xEC,0xED,0xEE,0xEF,
      0xF0,0xF1,0xF2,0xF3,0xF4,0xF5,0xF6,0xF7,0xF8,0xF9,0xFA,0xFB,0xFC,0xFD,0xFE,0xFF,
    };
   #elif defined(HPROMAN8_CHS)
    { 0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0A,0x0B,0x0C,0x0D,0x0E,0x0F,
      0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1A,0x1B,0x1C,0x1D,0x1E,0x1F,
      0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,0x28,0x29,0x2A,0x2B,0x2C,0x2D,0x2E,0x2F,
      0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x3A,0x3B,0x3C,0x3D,0x3E,0x3F,
      0x40,0x61,0x62,0x63,0x64,0x65,0x66,0x67,0x68,0x69,0x6A,0x6B,0x6C,0x6D,0x6E,0x6F,
      0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77,0x78,0x79,0x7A,0x5B,0x5C,0x5D,0x5E,0x5F,
      0x60,0x61,0x62,0x63,0x64,0x65,0x66,0x67,0x68,0x69,0x6A,0x6B,0x6C,0x6D,0x6E,0x6F,
      0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77,0x78,0x79,0x7A,0x7B,0x7C,0x7D,0x7E,0x7F,
      0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,0x88,0x89,0x8A,0x8B,0x8C,0x8D,0x8E,0x8F,
      0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,0x98,0x99,0x9A,0x9B,0x9C,0x9D,0x9E,0x9F,
      0xA0,0xC8,0xC0,0xC9,0xC1,0xCD,0xD1,0xDD,0xA8,0xA9,0xAA,0xAB,0xAC,0xCB,0xC3,0xAF,
      0xB0,0xB2,0xB2,0xB3,0xB5,0xB5,0xB7,0xB7,0xB8,0xB9,0xBA,0xBB,0xBC,0xBD,0xBE,0xBF,
      0xC0,0xC1,0xC2,0xC3,0xC4,0xC5,0xC6,0xC7,0xC8,0xC9,0xCA,0xCB,0xCC,0xCD,0xCE,0xCF,
      0xD4,0xD1,0xD6,0xD7,0xD4,0xD5,0xD6,0xD7,0xCC,0xD9,0xCE,0xCF,0xC5,0xDD,0xDE,0xC2,
      0xC4,0xE2,0xE2,0xE4,0xE4,0xD5,0xD9,0xC6,0xCA,0xEA,0xEA,0xEC,0xEC,0xC7,0xEF,0xEF,
      0xF1,0xF1,0xF2,0xF3,0xF4,0xF5,0xF6,0xF7,0xF8,0xF9,0xFA,0xFB,0xFC,0xFD,0xFE,0xFF,
    };
   #elif defined(NEXTSTEP_CHS)
    { 0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0A,0x0B,0x0C,0x0D,0x0E,0x0F,
      0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1A,0x1B,0x1C,0x1D,0x1E,0x1F,
      0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,0x28,0x29,0x2A,0x2B,0x2C,0x2D,0x2E,0x2F,
      0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x3A,0x3B,0x3C,0x3D,0x3E,0x3F,
      0x40,0x61,0x62,0x63,0x64,0x65,0x66,0x67,0x68,0x69,0x6A,0x6B,0x6C,0x6D,0x6E,0x6F,
      0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77,0x78,0x79,0x7A,0x5B,0x5C,0x5D,0x5E,0x5F,
      0x60,0x61,0x62,0x63,0x64,0x65,0x66,0x67,0x68,0x69,0x6A,0x6B,0x6C,0x6D,0x6E,0x6F,
      0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77,0x78,0x79,0x7A,0x7B,0x7C,0x7D,0x7E,0x7F,
      0x80,0xD5,0xD6,0xD7,0xD8,0xD9,0xDA,0xDB,0xDC,0xDD,0xDE,0xDF,0xE0,0xE2,0xE4,0xE5,
      0xE6,0xE7,0xEC,0xED,0xEE,0xEF,0xF0,0xF2,0xF3,0xF4,0xF6,0xF7,0xFC,0x9D,0x9E,0x9F,
      0xA0,0xA1,0xA2,0xA3,0xA4,0xA5,0xA6,0xA7,0xA8,0xA9,0xAA,0xAB,0xAC,0xAD,0xAE,0xAF,
      0xB0,0xB1,0xB2,0xB3,0xB4,0xB5,0xB6,0xB7,0xB8,0xB9,0xBA,0xBB,0xBC,0xBD,0xBE,0xBF,
      0xC0,0xC1,0xC2,0xC3,0xC4,0xC5,0xC6,0xC7,0xC8,0xC9,0xCA,0xCB,0xCC,0xCD,0xCE,0xCF,
      0xD0,0xD1,0xD2,0xD3,0xD4,0xD5,0xD6,0xD7,0xD8,0xD9,0xDA,0xDB,0xDC,0xDD,0xDE,0xDF,
      0xE0,0xF1,0xE2,0xE3,0xE4,0xE5,0xE6,0xE7,0xE8,0xF9,0xFA,0xEB,0xEC,0xED,0xEE,0xEF,
      0xF0,0xF1,0xF2,0xF3,0xF4,0xF5,0xF6,0xF7,0xF8,0xF9,0xFA,0xFB,0xFC,0xFD,0xFE,0xFF,
    };
   #elif defined(IBMPC_CHS)
    { 0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0A,0x0B,0x0C,0x0D,0x0E,0x0F,
      0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1A,0x1B,0x1C,0x1D,0x1E,0x1F,
      0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,0x28,0x29,0x2A,0x2B,0x2C,0x2D,0x2E,0x2F,
      0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x3A,0x3B,0x3C,0x3D,0x3E,0x3F,
      0x40,0x61,0x62,0x63,0x64,0x65,0x66,0x67,0x68,0x69,0x6A,0x6B,0x6C,0x6D,0x6E,0x6F,
      0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77,0x78,0x79,0x7A,0x5B,0x5C,0x5D,0x5E,0x5F,
      0x60,0x61,0x62,0x63,0x64,0x65,0x66,0x67,0x68,0x69,0x6A,0x6B,0x6C,0x6D,0x6E,0x6F,
      0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77,0x78,0x79,0x7A,0x7B,0x7C,0x7D,0x7E,0x7F,
      0x87,0x81,0x82,0x83,0x84,0x85,0x86,0x87,0x88,0x89,0x8A,0x8B,0x8C,0x8D,0x84,0x86,
      0x82,0x91,0x91,0x93,0x94,0x95,0x96,0x97,0x98,0x94,0x81,0x9B,0x9C,0x9D,0x9E,0x9F,
      0xA0,0xA1,0xA2,0xA3,0xA4,0xA4,0xA6,0xA7,0xA8,0xA9,0xAA,0xAB,0xAC,0xAD,0xAE,0xAF,
      0xB0,0xB1,0xB2,0xB3,0xB4,0xB5,0xB6,0xB7,0xB8,0xB9,0xBA,0xBB,0xBC,0xBD,0xBE,0xBF,
      0xC0,0xC1,0xC2,0xC3,0xC4,0xC5,0xC6,0xC7,0xC8,0xC9,0xCA,0xCB,0xCC,0xCD,0xCE,0xCF,
      0xD0,0xD1,0xD2,0xD3,0xD4,0xD5,0xD6,0xD7,0xD8,0xD9,0xDA,0xDB,0xDC,0xDD,0xDE,0xDF,
      0xE0,0xE1,0xE2,0xE3,0xE4,0xE5,0xE6,0xE7,0xE8,0xE9,0xEA,0xEB,0xEC,0xED,0xEE,0xEF,
      0xF0,0xF1,0xF2,0xF3,0xF4,0xF5,0xF6,0xF7,0xF8,0xF9,0xFA,0xFB,0xFC,0xFD,0xFE,0xFF,
    };
   #else /* standard ascii conversion table: only A..Z --> a..z */
    { 0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0A,0x0B,0x0C,0x0D,0x0E,0x0F,
      0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1A,0x1B,0x1C,0x1D,0x1E,0x1F,
      0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,0x28,0x29,0x2A,0x2B,0x2C,0x2D,0x2E,0x2F,
      0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x3A,0x3B,0x3C,0x3D,0x3E,0x3F,
      0x40,0x61,0x62,0x63,0x64,0x65,0x66,0x67,0x68,0x69,0x6A,0x6B,0x6C,0x6D,0x6E,0x6F,
      0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77,0x78,0x79,0x7A,0x5B,0x5C,0x5D,0x5E,0x5F,
      0x60,0x61,0x62,0x63,0x64,0x65,0x66,0x67,0x68,0x69,0x6A,0x6B,0x6C,0x6D,0x6E,0x6F,
      0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77,0x78,0x79,0x7A,0x7B,0x7C,0x7D,0x7E,0x7F,
      0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,0x88,0x89,0x8A,0x8B,0x8C,0x8D,0x8E,0x8F,
      0x90,0x91,0x92,0x93,0x94,0x95,0x96,0x97,0x98,0x99,0x9A,0x9B,0x9C,0x9D,0x9E,0x9F,
      0xA0,0xA1,0xA2,0xA3,0xA4,0xA5,0xA6,0xA7,0xA8,0xA9,0xAA,0xAB,0xAC,0xAD,0xAE,0xAF,
      0xB0,0xB1,0xB2,0xB3,0xB4,0xB5,0xB6,0xB7,0xB8,0xB9,0xBA,0xBB,0xBC,0xBD,0xBE,0xBF,
      0xC0,0xC1,0xC2,0xC3,0xC4,0xC5,0xC6,0xC7,0xC8,0xC9,0xCA,0xCB,0xCC,0xCD,0xCE,0xCF,
      0xD0,0xD1,0xD2,0xD3,0xD4,0xD5,0xD6,0xD7,0xD8,0xD9,0xDA,0xDB,0xDC,0xDD,0xDE,0xDF,
      0xE0,0xE1,0xE2,0xE3,0xE4,0xE5,0xE6,0xE7,0xE8,0xE9,0xEA,0xEB,0xEC,0xED,0xEE,0xEF,
      0xF0,0xF1,0xF2,0xF3,0xF4,0xF5,0xF6,0xF7,0xF8,0xF9,0xFA,0xFB,0xFC,0xFD,0xFE,0xFF,
    };
   #endif
  return as_chart(down_case_table[as_cint(ch)]);
 #endif
}

#ifdef UNICODE
/* Table of Unicode character attributes.
 unicode_attribute(c)
 > cint c: a character code
 < result: 0 = non-graphic
           1 = graphic, but not alphanumeric
           2 = graphic and numeric
           3 = graphic and alphabetic */
#include "uni_attribute.c"
#define unicode_attribute(c)                                            \
    ((c) < sizeof(unicode_attribute_table)/sizeof(unicode_attribute_table[0]) << 10 \
     ? (unicode_attribute_table[(c)>>10][((c)>>2)&0xFF] >> (((c)&0x3)*2)) & 0x3     \
     : 0)
#endif

/* UP: Determines, if a character is alphabetic.
 alphap(ch)
 > ch: character-code
 < result: true if alphabetic, otherwise false.
 Alphabetic characters have a code c, with */
#if defined(UNICODE)
/* java.lang.Character.isLetter(c) */
#else
/* $41 <= c <= $5A or $61 <= c <= $7A */
#if defined(ISOLATIN_CHS)
/* or $C0 <= c except c=$D7,$F7. */
#elif defined(HPROMAN8_CHS)
/* or $A1 <= c <= $A7 or $AD <= c <= $AE or $B1 <= c <= $B7 except c=$B3
   or $C0 <= c <= $F1. */
#elif defined(NEXTSTEP_CHS)
/* or $81 <= c <= $9D or $D5 <= c <= $FD. */
#elif defined(IBMPC_CHS)
/* or $80 <= c <= $9A or $9F <= c <= $A7. */
#endif
#endif
/* Therein, all uppercase- and all lowercase-
 characters are enclosed (see CLTL p. 236 top). */
local bool alphap (chart ch)
{
  var cint c = as_cint(ch);
 #ifdef UNICODE
  return (unicode_attribute(c) == 3 ? true : false);
 #else
  if (c < 0x41) goto no; if (c <= 0x5A) goto yes;
  if (c < 0x61) goto no; if (c <= 0x7A) goto yes;
 #if defined(ISOLATIN_CHS)
  if (c < 0xC0) goto no;
  if ((c == 0xD7) || (c == 0xF7)) goto no; else goto yes;
 #elif defined(HPROMAN8_CHS)
  if (c < 0xA1) goto no;
  if (c > 0xF1) goto no; if (c >= 0xC0) goto yes;
  if (c <= 0xA7) goto yes;
  if (c < 0xB1) {
    if (c < 0xAD) goto no; if (c <= 0xAE) goto yes; goto no;
  } else {
    if (c > 0xB7) goto no; if (c == 0xB3) goto no; else goto yes;
  }
 #elif defined(NEXTSTEP_CHS)
  if (c < 0x81) goto no; if (c <= 0x9D) goto yes;
  if (c < 0xD5) goto no; if (c <= 0xFD) goto yes;
 #elif defined(IBMPC_CHS)
  if (c < 0x80) goto no; if (c <= 0x9A) goto yes;
  if (c < 0x9F) goto no; if (c <= 0xA7) goto yes;
 #endif
 no: return false;
 yes: return true;
 #endif
}

/* Determines, if a character is numeric.
 numericp(ch)
 > ch: character-code
 < result: true if numeric, otherwise false. */
local bool numericp (chart ch);
#ifdef UNICODE
  #define numericp(ch)  (unicode_attribute(as_cint(ch)) == 2)
#else
  #define numericp(ch)  (('0' <= as_cint(ch)) && (as_cint(ch) <= '9'))
#endif

/* Determines, if a character is alphanumeric.
 alphanumericp(ch)
 > ch: character-code
 < result: true if alphanumeric, otherwise false.
 Alphanumeric characters comprise the alphabetic characters and the digits. */
global bool alphanumericp (chart ch)
{
 #ifdef UNICODE
  var cint c = as_cint(ch);
  return (unicode_attribute(c) >= 2 ? true : false);
 #else
  if (numericp(ch)) return true;
  return alphap(ch);
 #endif
}

/* Determines, if a character is a Graphic-Character ("printing") .
 graphic_char_p(ch)
 > ch: character-code
 < result: true if printing, otherwise false.
 Graphic-Characters are those with a Code c, with */
#if defined(UNICODE)
/*       (java.lang.Character.isDefined(c) || c == 0x20AC)
         && !(c < 0x0020 || (0x007F <= c <= 0x009F)) */
#elif defined(ISOLATIN_CHS) || defined(HPROMAN8_CHS)
/*       $20 <= c <= $7E or $A0 <= c < $100. */
#elif defined(NEXTSTEP_CHS)
/*       $20 <= c <= $7E or $80 <= c <= $A5 or c in {$A7,$A8,$AA,$AB,$AE..$B7}
         or $BA <= c <= $FD except c = $CD. */
#elif defined(IBMPC_CHS)
/*       $20 <= c < $100 or c in {1,..,6}u{14,..,25}u{28,..,31}.
         [c=11 and c=12 can also be printed, but c=12
          is our #\Page, and we discard c=11 for "equal rights"
           reasons.] */
#else /* defined(ASCII_CHS) */
/*       $20 <= c <= $7E. */
#endif
global bool graphic_char_p (chart ch) {
  /* This would be the same as iswprint(ch), assuming wide characters were
     Unicode. */
  var cint c = as_cint(ch);
 #ifdef UNICODE
  return (unicode_attribute(c) == 0 ? false : true);
 #else
 #if defined(ISOLATIN_CHS) || defined(HPROMAN8_CHS)
  if ((('~' >= c) && (c >= ' ')) || (c >= 0xA0)) goto yes; else goto no;
 #elif defined(NEXTSTEP_CHS)
  if (c <= '~') { if (c >= ' ') goto yes; else goto no; }
  if (c < 0xC0) {
    if (c < 0xA0) { if (c >= 0x80) goto yes; else goto no; }
    /* fetch bit c-0xA0 from the 32-bit-number
       %11111100111111111100110110111111: */
    if (0xFCFFCDBF & bit(c-0xA0)) goto yes; else goto no;
  } else {
    if ((c <= 0xFD) && !(c == 0xCD)) goto yes; else goto no;
  }
 #elif defined(IBMPC_CHS)
  if (c >= ' ') goto yes; /* >= ' ' -> yes */
  /* 0 <= c < 32. */
  /* fetch bit c from the 32-bit-number %11110011111111111100000001111110: */
  if (0xF3FFC07EUL & bit(c)) goto yes; else goto no;
 #else /* defined(ASCII_CHS) */
  if (c >= ' ') goto yes; else goto no;
 #endif
 no: return false;
 yes: return true;
 #endif
}

/* Returns the screen display width of a character.
 char_width(ch)
 > ch: character code
 < result: number of output columns occupied by ch */
global uintL char_width (chart ch);
#ifdef UNICODE
#include "uniwidth.h"
global inline int uc_width (ucs4_t uc, const char *encoding);
#include "width.c"
global uintL char_width (chart ch) {
  /* This would be the same as wcwidth(ch), assuming wide characters were
     Unicode, except that for non-printable characters we return 0, not -1. */
  extern const char* locale_encoding;
  int w = uc_width(as_cint(ch),locale_encoding);
  return (w >= 0 ? w : 0);
}
#else
global uintL char_width (chart ch) {
  return (graphic_char_p(ch) ? 1 : 0);
}
#endif

#if !defined(UNICODE) || defined(HAVE_SMALL_SSTRING)
/* Copies an array of uint8 to an array of uint8.
 copy_8bit_8bit(src,dest,len);
 > uint8* src: source
 > uint8* dest: destination
 > uintL len: number of elements to be copied, > 0 */
global void copy_8bit_8bit (const uint8* src, uint8* dest, uintL len) {
  dotimespL(len,len, {
    *dest++ = *src++;
  });
}
#endif

#if defined(HAVE_SMALL_SSTRING)
/* Copies an array of uint8 to an array of uint16.
 copy_8bit_16bit(src,dest,len);
 > uint8* src: source
 > uint16* dest: destination
 > uintL len: number of elements to be copied, > 0 */
global void copy_8bit_16bit (const uint8* src, uint16* dest, uintL len) {
  dotimespL(len,len, {
    *dest++ = *src++;
  });
}
#endif

#if defined(HAVE_SMALL_SSTRING)
/* Copies an array of uint8 to an array of uint32.
 copy_8bit_32bit(src,dest,len);
 > uint8* src: source
 > uint32* dest: destination
 > uintL len: number of elements to be copied, > 0 */
global void copy_8bit_32bit (const uint8* src, uint32* dest, uintL len) {
  dotimespL(len,len, {
    *dest++ = *src++;
  });
}
#endif

#if defined(HAVE_SMALL_SSTRING)
/* Copies an array of uint16 to an array of uint8.
 All source elements must fit into uint8.
 copy_16bit_8bit(src,dest,len);
 > uint16* src: source
 > uint8* dest: destination
 > uintL len: number of elements to be copied, > 0 */
global void copy_16bit_8bit (const uint16* src, uint8* dest, uintL len) {
  dotimespL(len,len, {
    *dest++ = *src++;
  });
}
#endif

#if defined(HAVE_SMALL_SSTRING)
/* Copies an array of uint16 to an array of uint16.
 copy_16bit_16bit(src,dest,len);
 > uint16* src: source
 > uint16* dest: destination
 > uintL len: number of elements to be copied, > 0 */
global void copy_16bit_16bit (const uint16* src, uint16* dest, uintL len) {
  dotimespL(len,len, {
    *dest++ = *src++;
  });
}
#endif

#if defined(HAVE_SMALL_SSTRING)
/* Copies an array of uint16 to an array of uint32.
 copy_16bit_32bit(src,dest,len);
 > uint16* src: source
 > uint32* dest: destination
 > uintL len: number of elements to be copied, > 0 */
global void copy_16bit_32bit (const uint16* src, uint32* dest, uintL len) {
  dotimespL(len,len, {
    *dest++ = *src++;
  });
}
#endif

#if defined(HAVE_SMALL_SSTRING)
/* Copies an array of uint32 to an array of uint8.
 All source elements must fit into uint8.
 copy_32bit_8bit(src,dest,len);
 > uint32* src: source
 > uint8* dest: destination
 > uintL len: number of elements to be copied, > 0 */
global void copy_32bit_8bit (const uint32* src, uint8* dest, uintL len) {
  dotimespL(len,len, {
    *dest++ = *src++;
  });
}
#endif

#if defined(HAVE_SMALL_SSTRING)
/* Copies an array of uint32 to an array of uint16.
 All source elements must fit into uint16.
 copy_32bit_16bit(src,dest,len);
 > uint32* src: source
 > uint16* dest: destination
 > uintL len: number of elements to be copied, > 0 */
global void copy_32bit_16bit (const uint32* src, uint16* dest, uintL len) {
  dotimespL(len,len, {
    *dest++ = *src++;
  });
}
#endif

#if defined(UNICODE)
/* Copies an array of uint32 to an array of uint32.
 copy_32bit_32bit(src,dest,len);
 > uint32* src: source
 > uint32* dest: destination
 > uintL len: number of elements to be copied, > 0 */
global void copy_32bit_32bit (const uint32* src, uint32* dest, uintL len) {
  dotimespL(len,len, {
    *dest++ = *src++;
  });
}
#endif

/* UP: unpack a string
 unpack_string_ro(string,&len,&offset)  [for read-only access]
 > object string: a string
 < uintL len: the fill-pointer length of the string
 < uintL offset: offset into the datastorage vector
 < object result: datastorage vector */
global object unpack_string_ro (object string, uintL* len, uintL* offset) {
  if (simple_string_p(string)) {
    simple_array_to_storage(string);
    *len = Sstring_length(string);
    *offset = 0;
    return string;
  } else {
    /* string, but not simple-string => follow the displacement
       determine the length (like vector_length() in array.d): */
    var uintL size;
    {
      var Iarray addr = TheIarray(string);
      var uintL offset_fil = offsetofa(iarray_,dims);
      if (iarray_flags(addr) & bit(arrayflags_dispoffset_bit))
        offset_fil += sizeof(uintL);
      if (iarray_flags(addr) & bit(arrayflags_fillp_bit))
        offset_fil += sizeof(uintL);
      size = *(uintL*)pointerplus(addr,offset_fil);
    }
    *len = size;
    /* follow the displacement: */
    *offset = 0;
    return iarray_displace_check(string,size,offset);
  }
}

/* UP: unpack a string
 unpack_string_rw(string,&len)  [for read-write access]
 > object string: a string
 < uintL len: the fill-pointer length of the string
 < uintL offset: Offset in the Data-Vector.
 < object result: Data-Vector */
global object unpack_string_rw (object string, uintL* len, uintL* offset) {
  var object unpacked = unpack_string_ro(string,len,offset);
  check_sstring_mutable(unpacked);
  return unpacked;
}

/* UP: compares two strings for equality
 string_gleich(string1,string2)
 > string1: string
 > string2: simple-string
 < result: /=0, if equal */
global bool string_gleich (object string1, object string2) {
  var uintL len1;
  var uintL offset1;
  string1 = unpack_string_ro(string1,&len1,&offset1);
  if (len1 != Sstring_length(string2))
    return false;
  /* Now both strings have exactly len1 characters. Compare them. */
  if (len1 > 0)
    return string_eqcomp(string1,offset1,string2,0,len1);
  return true;
}

/* UP: compares two strings for equality, case-insensitive
 string_equal(string1,string2)
 > string1: string
 > string2: simple-string
 < result: /=0, if equal */
global bool string_equal (object string1, object string2) {
  var uintL len1;
  var uintL offset1;
  string1 = unpack_string_ro(string1,&len1,&offset1);
  if (len1 != Sstring_length(string2))
    return false;
  /* Now both strings have exactly len1 characters. Compare them. */
  if (len1 > 0)
    return string_eqcomp_ci(string1,offset1,string2,0,len1);
  return true;
}

/* UP: Stores a character in a string.
 > string: a mutable string that is or was simple
 > index: (already checked) index into the string
 > element: a character
 < result: the possibly reallocated string
 can trigger GC */
global object sstring_store (object string, uintL index, chart element) {
  var object inner_string = string;
  simple_array_to_storage(inner_string);
  switch (Array_type(inner_string)) {
 #ifndef TYPECODES
  #ifdef UNICODE
   #ifdef HAVE_SMALL_SSTRING
    case Rectype_S8string: /* mutable Simple-String */
      if (as_cint(element) < cint8_limit) {
        TheS8string(inner_string)->data[index] = as_cint(element);
        break;
      }
      ASSERT(eq(string,inner_string));
      if (as_cint(element) < cint16_limit) {
        string = reallocate_small_string(inner_string,Rectype_S16string);
        inner_string = TheSiarray(string)->data;
        TheS16string(inner_string)->data[index] = as_cint(element);
        break;
      }
      string = reallocate_small_string(inner_string,Rectype_S32string);
      inner_string = TheSiarray(string)->data;
      TheS32string(inner_string)->data[index] = as_cint(element);
      break;
    case Rectype_S16string: /* mutable Simple-String */
      if (as_cint(element) < cint16_limit) {
        TheS16string(inner_string)->data[index] = as_cint(element);
        break;
      }
      pushSTACK(string);
      inner_string = reallocate_small_string(inner_string,Rectype_S32string);
      string = popSTACK();
      inner_string = TheSiarray(inner_string)->data;
      /*FALLTHROUGH*/
   #endif
    case Rectype_S32string: /* mutable Simple-String */
      TheS32string(inner_string)->data[index] = as_cint(element);
      break;
  #else
    case Rectype_S8string: /* mutable Simple-String */
      TheS8string(inner_string)->data[index] = as_cint(element);
      break;
  #endif
 #else
    case Array_type_sstring: /* Simple-String */
      TheSstring(inner_string)->data[index] = element;
      break;
 #endif
    default: NOTREACHED;
  }
  return string;
}

/* UP: Stores an array of characters in a string.
 > string: a mutable string that is or was simple
 > offset: (already checked) offset into the string
 > charptr[0..len-1]: a character array, not GC affected
 < result: the possibly reallocated string
 can trigger GC */
global object sstring_store_array (object string, uintL offset,
                                   const chart *charptr, uintL len)
{
  if (len > 0) {
    var object inner_string = string;
    simple_array_to_storage(inner_string);
    switch (Array_type(inner_string)) {
 #ifndef TYPECODES
  #ifdef UNICODE
   #ifdef HAVE_SMALL_SSTRING
      case Rectype_S8string: { /* mutable Simple-String */
        var bool fits_in_8bit = true;
        var bool fits_in_16bit = true;
        {
          var uintL n;
          var const chart* p = charptr;
          dotimespL(n,len, {
            if (!(as_cint(*p) < cint8_limit))
              fits_in_8bit = false;
            if (!(as_cint(*p) < cint16_limit)) {
              fits_in_16bit = false;
              break;
            }
            p++;
          });
        }
        if (fits_in_8bit) {
          var const chart* p = charptr;
          var cint8* q = &TheS8string(inner_string)->data[offset];
          dotimespL(len,len, {
            *q = as_cint(*p);
            p++;
            q++;
          });
          break;
        }
        ASSERT(eq(string,inner_string));
        if (fits_in_16bit) {
          string = reallocate_small_string(inner_string,Rectype_S16string);
          inner_string = TheSiarray(string)->data;
          var const chart* p = charptr;
          var cint16* q = &TheS16string(inner_string)->data[offset];
          dotimespL(len,len, {
            *q = as_cint(*p);
            p++;
            q++;
          });
          break;
        }
        string = reallocate_small_string(inner_string,Rectype_S32string);
        inner_string = TheSiarray(string)->data;
        var const chart* p = charptr;
        var cint32* q = &TheS32string(inner_string)->data[offset];
        dotimespL(len,len, {
          *q = as_cint(*p);
          p++;
          q++;
        });
      }
        break;
      case Rectype_S16string: { /* mutable Simple-String */
        var bool fits_in_16bit = true;
        {
          var uintL n;
          var const chart* p = charptr;
          dotimespL(n,len, {
            if (!(as_cint(*p) < cint16_limit)) {
              fits_in_16bit = false;
              break;
            }
            p++;
          });
        }
        if (fits_in_16bit) {
          var const chart* p = charptr;
          var cint16* q = &TheS16string(inner_string)->data[offset];
          dotimespL(len,len, {
            *q = as_cint(*p);
            p++;
            q++;
          });
          break;
        }
        pushSTACK(string);
        inner_string = reallocate_small_string(inner_string,Rectype_S32string);
        string = popSTACK();
        inner_string = TheSiarray(inner_string)->data;
      }
        /*FALLTHROUGH*/
   #endif
      case Rectype_S32string: { /* mutable Simple-String */
        var const chart* p = charptr;
        var cint32* q = &TheS32string(inner_string)->data[offset];
        dotimespL(len,len, {
          *q = as_cint(*p);
          p++;
          q++;
        });
      }
        break;
  #else
      case Rectype_S8string: { /* mutable Simple-String */
        var const chart* p = charptr;
        var cint8* q = &TheS8string(inner_string)->data[offset];
        dotimespL(len,len, {
          *q = as_cint(*p);
          p++;
          q++;
        });
      }
        break;
  #endif
 #else
      case Array_type_sstring: { /* Simple-String */
        var const chart* p = charptr;
        var cint8* q = &TheS8string(inner_string)->data[offset];
        dotimespL(len,len, {
          *q = as_cint(*p);
          p++;
          q++;
        });
      }
        break;
 #endif
      default: NOTREACHED;
    }
  }
  return string;
}

#ifdef UNICODE
/* UP: Creates a Simple-String with given elements.
 stringof(len)
 > uintL len: desired vector length
 > on STACK: len characters, first on top
 < result: Simple-String with these objects
 increases STACK
 changes STACK, can trigger GC */
global object stringof (uintL len) {
  var object new_string = allocate_string(len);
  if (len > 0) {
    var object* topargptr = STACK STACKop len;
    var object* argptr = topargptr;
    var chart* ptr = &TheSstring(new_string)->data[0];
    dotimespL(len,len, {
      *ptr++ = char_code(NEXT(argptr));
    });
    set_args_end_pointer(topargptr);
  }
  return new_string;
}
#endif

/* UP: Copies a string and thereby turns it into a Simple-String.
 copy_string(string)
 > string: String
 < result: mutable Normal-Simple-String with the same characters
 can trigger GC */
global object copy_string (object string) {
  var uintL len;
  var uintL offset;
  string = unpack_string_ro(string,&len,&offset);
  pushSTACK(string); /* save string */
  var object new_string = allocate_string(len);
  /* new_string = new Normal-Simple-String with given length len */
  string = popSTACK(); /* return string */
  if (len > 0) {
   #ifdef UNICODE
    SstringCase(string,
                { copy_8bit_32bit(&TheS8string(string)->data[offset],
                                  &TheS32string(new_string)->data[0],len); },
                { copy_16bit_32bit(&TheS16string(string)->data[offset],
                                   &TheS32string(new_string)->data[0],len); },
                { copy_32bit_32bit(&TheS32string(string)->data[offset],
                                   &TheS32string(new_string)->data[0],len); });
   #else
    copy_8bit_8bit(&TheSstring(string)->data[offset],
                   &TheSstring(new_string)->data[0],len);
   #endif
  }
  return new_string;
}

/* UP: converts a string into a Simple-String.
 coerce_ss(obj)
 > obj: Lisp-object, should be a string.
 < ergebnis: Simple-String with the same characters
 can trigger GC */
global object coerce_ss (object obj) {
 #ifdef TYPECODES
  switch (typecode(obj))
 #else
    if (orecordp(obj))
      switch (Record_type(obj)) {
        case_Rectype_Sstring_above;
        case_Rectype_ostring_above;
        default: break;
      }
  switch (0)
 #endif
    {
     case_sstring:
      /* Simple-String, returned unchanged */
      return obj;
     case_ostring:
      /* other string, copy it */
      return copy_string(obj);
     default:
       fehler_string(obj);
    }
}

#ifndef TYPECODES
/* UP: converts a string into an immutable Simple-String.
 coerce_imm_ss(obj)
 > obj: Lisp-object, should be a string.
 < result: immutable Simple-String with the same characters
 can trigger GC */
global object coerce_imm_ss (object obj)
{
  if (orecordp(obj))
    switch (Record_type(obj)) {
      #ifdef UNICODE
      #ifdef HAVE_SMALL_SSTRING
      case Rectype_Imm_S8string:
      case Rectype_Imm_S16string:
      #endif
      case Rectype_Imm_S32string:
      #else
      case Rectype_Imm_S8string:
      #endif
        /* immutable Simple-String, return unchanged */
        return obj;
      #ifdef UNICODE
      #ifdef HAVE_SMALL_SSTRING
      case Rectype_reallocstring:
      case Rectype_S8string:
      case Rectype_S16string:
      #endif
      case Rectype_S32string:
      #else
      case Rectype_S8string:
      #endif
      case Rectype_string: { /* other string, copy it */
          var uintL len;
          var uintL offset;
          var object string = unpack_string_ro(obj,&len,&offset);
          #ifdef UNICODE
          #ifdef HAVE_SMALL_SSTRING
          if (Record_type(string) == Rectype_S8string) {
            pushSTACK(string);
            var object new_string = allocate_imm_s8string(len);
            string = popSTACK();
            if (len > 0)
              copy_8bit_8bit(&TheS8string(string)->data[offset],
                             &TheS8string(new_string)->data[0],len);
            return new_string;
          }
          if (Record_type(string) == Rectype_S16string) {
            /* Check if all characters fit into an 8-bit character string. */
            var bool fits_in_8bit = true;
            if (len > 0) {
              var const cint16* ptr = &TheS16string(string)->data[offset];
              var uintL count;
              dotimespL(count,len, {
                if (!(*ptr < cint8_limit)) {
                  fits_in_8bit = false;
                  break;
                }
                ptr++;
              });
            }
            pushSTACK(string);
            var object new_string =
              (fits_in_8bit ? allocate_imm_s8string(len) :
               allocate_imm_s16string(len));
            string = popSTACK();
            if (len > 0) {
              if (fits_in_8bit)
                copy_16bit_8bit(&TheS16string(string)->data[offset],
                                &TheS8string(new_string)->data[0],len);
              else
                copy_16bit_16bit(&TheS16string(string)->data[offset],
                                 &TheS16string(new_string)->data[0],len);
            }
            return new_string;
          }
          ASSERT(Record_type(string) == Rectype_S32string);
          /* We use alloca for small-simple-strings, therefore their length
             should not be too large, or we risk an SP overflow and
             core dump. */
          if (len < 0x10000) {
            /* Check if all characters fit into an 8-bit or 16-bit character
               simple string: */
            var bool fits_in_8bit = true;
            var bool fits_in_16bit = true;
            if (len > 0) {
              var const cint32* ptr = &TheS32string(string)->data[offset];
              var uintL count;
              dotimespL(count,len, {
                if (!(*ptr < cint8_limit))
                  fits_in_8bit = false;
                if (!(*ptr < cint16_limit)) {
                  fits_in_16bit = false;
                  break;
                }
                ptr++;
              });
            }
            if (fits_in_16bit) {
              pushSTACK(string);
              var object new_string =
                (fits_in_8bit ? allocate_imm_s8string(len) :
                 allocate_imm_s16string(len));
              string = popSTACK();
              if (len > 0) {
                if (fits_in_8bit)
                  copy_32bit_8bit(&TheS32string(string)->data[offset],
                                  &TheS8string(new_string)->data[0],len);
                else
                  copy_32bit_16bit(&TheS32string(string)->data[offset],
                                   &TheS16string(new_string)->data[0],len);
              }
              return new_string;
            }
          }
          #endif
          pushSTACK(string);
          var object new_string = allocate_imm_s32string(len);
          string = popSTACK();
          if (len > 0)
            copy_32bit_32bit(&TheS32string(string)->data[offset],
                             &TheS32string(new_string)->data[0],len);
          return new_string;
          #else
          pushSTACK(string);
          var object new_string = allocate_imm_string(len);
          string = popSTACK();
          if (len > 0)
            copy_8bit_8bit(&TheSstring(string)->data[offset],
                           &TheSstring(new_string)->data[0],len);
          return new_string;
          #endif
        }
      default:
        break;
    }
  fehler_string(obj);
}
#endif

#ifdef HAVE_SMALL_SSTRING
/* UP: converts a string into a Normal-Simple-String.
 coerce_normal_ss(obj)
 > obj: Lisp-object, should be a string.
 < result: Normal-Simple-String with the same characters
 can trigger GC */
global object coerce_normal_ss (object obj)
{
  if (orecordp(obj))
   restart_it:
    switch (Record_type(obj)) {
      case Rectype_Imm_S32string:
      case Rectype_S32string:
        /* Normal-Simple-String, return unchanged */
        return obj;
      case Rectype_Imm_S8string:
      case Rectype_S8string:
      case Rectype_Imm_S16string:
      case Rectype_S16string:
      case Rectype_string:
        /* other string, copy it */
        return copy_string(obj);
      case Rectype_reallocstring:
        /* reallocated simple string */
        obj = TheSiarray(obj)->data;
        goto restart_it;
      default:
        break;
    }
  fehler_string(obj);
}
#endif

#if 0 /* unused */
#ifdef HAVE_SMALL_SSTRING
/* UP: converts a string into an immutable Normal-Simple-String.
 coerce_imm_normal_ss(obj)
 > obj: Lisp-object, should be a string.
 < result: immutable Normal-Simple-String with the same characters
 can trigger GC */
global object coerce_imm_normal_ss (object obj)
{
  if (orecordp(obj))
    switch (Record_type(obj)) {
      case Rectype_Imm_S32string:
        /* immutable Normal-Simple-String, return unchanged */
        return obj;
      case Rectype_Imm_S8string:
      case Rectype_Imm_S16string:
      case Rectype_S8string:
      case Rectype_S16string:
      case Rectype_S32string:
      case Rectype_reallocstring:
      case Rectype_string: { /* other string, copy it */
          var uintL len;
          var uintL offset;
          var object string = unpack_string_ro(obj,&len,&offset);
          pushSTACK(string);
          var object new_string = allocate_imm_string(len);
          string = popSTACK();
          if (len > 0) {
            SstringCase(string,
              { copy_8bit_32bit(&TheS8string(string)->data[offset],
                                &TheSstring(new_string)->data[0],len); },
              { copy_16bit_32bit(&TheS16string(string)->data[offset],
                                 &TheSstring(new_string)->data[0],len); },
              { copy_32bit_32bit(&TheS32string(string)->data[offset],
                                 &TheSstring(new_string)->data[0],len); });
          }
          return new_string;
        }
      default:
        break;
    }
  fehler_string(obj);
}
#endif
#endif

/* (SYS::STRING-INFO str) => char-len(8/16/32); immutable-p; realloc-p */
LISPFUNN(string_info,1) {
  var object str = popSTACK();
  if (stringp(str)) {
   #ifdef HAVE_SMALL_SSTRING
    if (Record_type(str) == Rectype_reallocstring) {
      value3 = T; simple_array_to_storage(str);
    } else value3 = NIL;
   #endif
    value2 = NIL;
    switch (Record_type(str)) {
     #ifdef TYPECODES
      case Array_type_sstring: value1 = fixnum(32); break;
     #else
      case Rectype_Imm_S32string: value2 = T; /*FALLTHROUGH*/
      case Rectype_S32string: value1 = fixnum(32); break;
      case Rectype_Imm_S16string: value2 = T; /*FALLTHROUGH*/
      case Rectype_S16string: value1 = fixnum(16); break;
      case Rectype_Imm_S8string: value2 = T; /*FALLTHROUGH*/
      case Rectype_S8string: value1 = fixnum(8); break;
     #endif
      default: NOTREACHED;
    }
  } else value1 = value2 = value3 = NIL;
  mv_count = 3;
}

/* UP: conversion of an object into a character
 coerce_char(obj)
 > obj: Lisp-object
 < result: Character or NIL */
global object coerce_char (object obj) {
  if (charp(obj)) {
    return obj; /* return character unchanged */
  } else if (symbolp(obj)) {
    /* obj is a symbol */
    obj = TheSymbol(obj)->pname; goto string;
  } else if (stringp(obj)) {
   string: /* obj is a string */
    var uintL len;
    var uintL offset;
    var object string = unpack_string_ro(obj,&len,&offset);
    /* at ptr are len characters */
    if (len==1)
      return code_char(schar(string,offset));
  } else if (nullpSv(coerce_fixnum_char_ansi) && posfixnump(obj)) {
    var uintL code = posfixnum_to_L(obj);
    if (code < char_code_limit)
      /* obj is a fixnum >=0, < char_code_limit */
      return code_char(as_chart(code));
  }
  /* was none of it -> can not be converted into a character */
  return NIL; /* NIL as result */
}

/* character-names:
 Only the characters with font 0 and bits 0 have names. Among these
 are all non-graphic characters and the space.
 The reader also accepts
 - the syntax #\A for the character A (etc. for all characters),
 - the syntax #\^A for the character 'A'-64 (etc. for all control-characters
   of the ASCII-charset) and
 - the syntax #\Code231 for the character with the code 231 (decimal)
 for all characters out of font 0. */

/* table of character-names:
 defined in CONSTOBJ.D, */
#ifdef AMIGA_CHARNAMES
  #define charname_table_length  45  /* length of the table */
  #define charname_table  ((object*)(&object_tab.charname_0)) /* table starts with charname_0 */
#endif
#ifdef MSDOS_CHARNAMES
  #define charname_table_length  13  /* length of the table */
  #define charname_table  ((object*)(&object_tab.charname_0)) /* table starts with charname_0 */
#endif
#ifdef WIN32_CHARNAMES
  #define charname_table_length  13  /* length of the table */
  #define charname_table  ((object*)(&object_tab.charname_0)) /* table starts with charname_0 */
#endif
#ifdef UNIX_CHARNAMES
  #define charname_table_length  46  /* length of the table */
  #define charname_table  ((object*)(&object_tab.charname_0bis)) /* table starts with charname_0bis */
#endif
/* table of codes for this name: */
local const uintB charname_table_codes [charname_table_length]
  #ifdef AMIGA_CHARNAMES
    = { 0,1,2,3,4,5,6,BEL,BS,TAB,NL,11,PG,CR,14,15,16,17,18,19,20,21,22,
        23,24,25,26,ESC,28,29,30,31,' ',127,7,8,9,LF,10,12,13,27,127,RUBOUT,
        155,
      };
  #endif
  #ifdef MSDOS_CHARNAMES
    = { 0,BEL,BS,TAB,NL,11,PG,CR,26,ESC,' ',RUBOUT,LF, };
  #endif
  #ifdef WIN32_CHARNAMES
    = { 0,BEL,BS,TAB,NL,11,PG,CR,26,ESC,' ',RUBOUT,LF, };
  #endif
  #ifdef UNIX_CHARNAMES
    = { 0,7,BS,TAB,NL,LF,PG,CR,27,32,RUBOUT,127,
        0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,
        20,21,22,23,24,25,26,27,28,29,30,31,32,127,
      };
  #endif
/* the code charname_table_codes[i] belongs to the name charname_table[i]
   (for 0 <= i < charname_table_length). */

#ifdef UNICODE

#include "uniname.h"
#include "uniname.c"

#endif

/* UP: return the name of a character
 char_name(code)
 > chart code: character code
 < result: simple-string (the name of the character) or NIL
 can trigger GC */
global object char_name (chart code) {
  var cint c = as_cint(code);
  {
    var const uintB* codes_ptr = &charname_table_codes[0];
    var object* strings_ptr = &charname_table[0];
    var uintC count;
    dotimesC(count,charname_table_length, {
      if (c == *codes_ptr++) /* compare code with charname_table_codes[i] */
        return *strings_ptr; /* return string charname_table[i] from the table */
      strings_ptr++;
    });
  }
  /* not found */
 #ifdef UNICODE
  /* Try to find the long name, from UnicodeData.txt. It is the second
     semicolon separated field from (sys::unicode-attributes-line c). */
  #ifdef AWFULLY_SLOW
  {
    pushSTACK(fixnum(c));
    funcall(S(unicode_attributes_line),1);
    var object line = value1;
    if (!nullp(line)) {
      var uintL len = Sstring_length(line);
      var uintL i1;
      var uintL i2;
      for (i1 = 0; i1 < len; i1++)
        if (chareq(TheSstring(line)->data[i1],ascii(';'))) {
          i1++;
          for (i2 = i1; i2 < len; i2++)
            if (chareq(TheSstring(line)->data[i2],ascii(';'))) {
              if (!chareq(TheSstring(line)->data[i1],ascii('<'))) {
                var object name = subsstring(line,i1,i2);
                /* Replace ' ' with '_': */
                var uintL count = i2-i1;
                if (count > 0) {
                  var chart* ptr = &TheSstring(name)->data[0];
                  dotimespL(count,count, {
                    if (chareq(*ptr,ascii(' ')))
                      *ptr = ascii('_');
                    ptr++;
                  });
                }
                return name;
              }
              break;
            }
          break;
        }
    }
  }
  #else
  /* Here is a much faster implementation. */
  {
    var char buf[UNINAME_MAX];
    if (unicode_character_name(c,buf)) {
      var char* ptr = buf;
      /* Turn the word separators into underscores. */
      while (*ptr != '\0') {
        if (*ptr == ' ')
          *ptr = '_';
        ptr++;
      }
      return n_char_to_string(buf,ptr-buf,Symbol_value(S(ascii)));
    }
  }
  #endif /* AWFULLY_SLOW */
  /* CLHS (glossary "name" 5) specifies that all non-graphic characters have
     a name. Let's give a name to all of them, it's more uniform (and avoids
     printer errors). */
  /* if (!graphic_char_p(code)) */
  {
    local char hex_table[] = "0123456789ABCDEF";
    if (c < 0x10000) {
      var object name = allocate_s8string(5);
      TheS8string(name)->data[0] = as_cint(ascii('U'));
      TheS8string(name)->data[1] = as_cint(ascii(hex_table[(c>>12)&0x0F]));
      TheS8string(name)->data[2] = as_cint(ascii(hex_table[(c>>8)&0x0F]));
      TheS8string(name)->data[3] = as_cint(ascii(hex_table[(c>>4)&0x0F]));
      TheS8string(name)->data[4] = as_cint(ascii(hex_table[c&0x0F]));
      return name;
    } else {
      var object name = allocate_s8string(9);
      TheS8string(name)->data[0] = as_cint(ascii('U'));
      TheS8string(name)->data[1] = as_cint(ascii('0'));
      TheS8string(name)->data[2] = as_cint(ascii('0'));
      TheS8string(name)->data[3] = as_cint(ascii(hex_table[(c>>20)&0x0F]));
      TheS8string(name)->data[4] = as_cint(ascii(hex_table[(c>>16)&0x0F]));
      TheS8string(name)->data[5] = as_cint(ascii(hex_table[(c>>12)&0x0F]));
      TheS8string(name)->data[6] = as_cint(ascii(hex_table[(c>>8)&0x0F]));
      TheS8string(name)->data[7] = as_cint(ascii(hex_table[(c>>4)&0x0F]));
      TheS8string(name)->data[8] = as_cint(ascii(hex_table[c&0x0F]));
      return name;
    }
  }
 #else /* no UNICODE */
  {
    var object name = allocate_string(1);
    TheSstring(name)->data[0] = ascii(c);
    return name;
  }
 #endif
  return NIL;
}

/* UP: find the character with the given name
 name_char(string)
 > string: String
 < result: character with the name, or NIL if does not exist */
global object name_char (object string) {
  {
    var const uintB* codes_ptr = &charname_table_codes[0];
    var object* strings_ptr = &charname_table[0];
    var uintC count;
    dotimesC(count,charname_table_length, {
      if (string_equal(string,*strings_ptr++)) /* compare string with charname_table[i] */
        return code_char(as_chart(*codes_ptr)); /* return Code charname_table_codes[i] from the table */
      codes_ptr++;
    });
  }
  /* no character with the name name found */
 #ifdef UNICODE
  {
    var uintL len;
    var uintL offset;
    string = unpack_string_ro(string,&len,&offset);
    if (len > 1 && len < UNINAME_MAX) {
      var const chart* charptr;
      unpack_sstring_alloca(string,len,offset, charptr=);
      /* Test for Uxxxx or Uxxxxxxxx syntax. */
      if ((len == 5 || len == 9)
          && (chareq(charptr[0],ascii('U'))
              || chareq(charptr[0],ascii('u')))) {
        /* decode a hexadecimal number: */
        var uintL code = 0;
        var uintL index = 1;
        var const chart* tmpcharptr = charptr+1;
        loop {
          var cint c = as_cint(*tmpcharptr++); /* next character */
          /* should be a hexadecimal digit: */
          if (c > 'f') break;
          if (c >= 'a') { c -= 'a'-'A'; }
          if (c < '0') break;
          if (c <= '9') { c = c - '0'; }
          else if ((c >= 'A') && (c <= 'F')) { c = c - 'A' + 10; }
          else break;
          code = 16*code + c; /* put in the digit */
          /* code should be < char_code_limit: */
          if (code >= char_code_limit) break; /* should not occur */
          index++;
          if (index == len) {
            /* Character name was "Uxxxx" with code = xxxx < char_code_limit.
               Its length should be 5 or 9, depending on xxxx < 0x10000. */
            if (!(len == (code < 0x10000 ? 5 : 9)))
              break;
            /* Don't test for graphic_char_p - see comment in char_name().
               This also avoids special-casing the #\Uxxxx syntax in io.d. */
            /* if (!graphic_char_p(as_chart(code))) */
            return code_char(as_chart(code));
          }
        }
      }
      { /* Test for word1_word2_... syntax. */
        var char buf[UNINAME_MAX];
        var char* ptr = buf;
        loop {
          var cint c = as_cint(*charptr++);
          if (!(c >= ' ' && c <= '~'))
            break;
          *ptr++ = (char)(c == '_' ? ' ' : c);
          if (--len == 0)
            goto filled_buf;
        }
        if (false) {
        filled_buf:
          *ptr = '\0';
          var cint32 code = unicode_name_character(buf);
          if (code != UNINAME_INVALID)
            return code_char(as_chart(code));
        }
      }
    }
  }
 #else /* no UNICODE */
  return coerce_char(string);
 #endif
  return NIL;
}

/* UP: checks a character that is to be inserted into a string
 test_char_arg()
 > STACK_0: argument
 > subr_self: caller (a SUBR)
 < result: argument as character
 increases STACK by 1 */
local object test_char_arg (void) {
  var object arg = popSTACK(); /* argument */
  if (charp(arg)) {
    return arg;
  } else
    fehler_char(arg);
}

LISPFUNN(standard_char_p,1) /* (STANDARD-CHAR-P char), CLTL p. 234 */
{ /* (standard-char-p char) ==
     (or (char= char #\Newline) (char<= #\Space char #\~))
 Standard-Chars have a code c, with
       $20 <= c <= $7E oder c = NL. */
  var object arg = test_char_arg();
  var chart ch = char_code(arg);
  var cint c = as_cint(ch);
  VALUES_IF((('~' >= c) && (c >= ' ')) || (c == NL));
}

LISPFUNN(graphic_char_p,1) /* (GRAPHIC-CHAR-P char), CLTL p. 234 */
{
  var object arg = test_char_arg();
  VALUES_IF(graphic_char_p(char_code(arg)));
}

LISPFUNN(char_width,1) /* (CHAR-WIDTH char) */
{
  var object arg = test_char_arg();
  VALUES1(fixnum(char_width(char_code(arg))));
}

LISPFUNN(string_char_p,1) /* (STRING-CHAR-P char), CLTL p. 235 */
{ /* all characters are string-chars. */
  var object arg = test_char_arg();
  VALUES1(T);
}

#if (base_char_code_limit < char_code_limit)
LISPFUNN(base_char_p,1) /* (SYSTEM::BASE-CHAR-P char) */
{
  var object arg = test_char_arg();
  VALUES_IF(as_cint(char_code(arg)) < base_char_code_limit);
}
#endif

LISPFUNN(alpha_char_p,1) /* (ALPHA-CHAR-P char), CLTL p. 235 */
{ /* Test with ALPHAP. */
  var object arg = test_char_arg();
  VALUES_IF(alphap(char_code(arg)));
}

LISPFUNN(upper_case_p,1) /* (UPPER-CASE-P char), CLTL p. 235 */
{ /* upper-case-characters are those with a code c with 0 <= c < $100, that
     are different from (downcase char) . */
  var object arg = test_char_arg();
  var chart ch = char_code(arg);
  VALUES_IF(!chareq(down_case(ch),ch));
}

LISPFUNN(lower_case_p,1) /* (LOWER-CASE-P char), CLTL p. 235 */
{ /* lower-case-characters are those with a code c with 0 <= c < $100, that
     are different from (upcase char) . */
  var object arg = test_char_arg();
  var chart ch = char_code(arg);
  VALUES_IF(!chareq(up_case(ch),ch));
}

LISPFUNN(both_case_p,1) /* (BOTH-CASE-P char), CLTL p. 235 */
{ /* (both-case-p char) == (or (upper-case-p char) (lower-case-p char))
     both-case-characters are those with a code c with 0 <= c < $100.
     For them (downcase char) and (upcase char) are different. */
  var object arg = test_char_arg();
  var chart ch = char_code(arg);
  VALUES_IF(!chareq(down_case(ch),up_case(ch)));
}

/* UP: Checks an optional radix-argument
 test_radix_arg()
 > STACK_0: argument, default is 10
 > subr_self: caller (a SUBR)
 < result: radix, an integer >=2, <=36
 increases STACK by 1 */
local uintWL test_radix_arg (void) {
  var object arg = popSTACK(); /* argument */
  if (!boundp(arg))
    return 10;
  if (posfixnump(arg)) {
    var uintL radix = posfixnum_to_L(arg);
    if ((2 <= radix) && (radix <= 36))
      return radix;
  }
  /* error */
  pushSTACK(arg); /* TYPE-ERROR slot DATUM */
  pushSTACK(O(type_radix)); /* TYPE-ERROR slot EXPECTED-TYPE */
  pushSTACK(arg); pushSTACK(TheSubr(subr_self)->name);
  fehler(type_error,GETTEXT("~: the radix must be an integer between 2 and 36, not ~"));
}

LISPFUN(digit_char_p,1,1,norest,nokey,0,NIL)
{ /* (DIGIT-CHAR-P char [radix]), CLTL p. 236
 method:
 test, if radix is an integer >=2 and <=36 .
 char must be a character <= 'z' , otherwise return NIL as result.
 if radix<=10: c must be >= '0' and < '0'+radix , else NIL.
 if radix>=10: c must be >= '0' and <= '9' or
                  (upcase c) must be >= 'A' and < 'A'-10+radix , else NIL. */
  var uintWL radix = test_radix_arg(); /* basis >=2, <=36 */
  var object arg = test_char_arg();
  var chart ch = char_code(arg);
  var cint c = as_cint(ch);
 #ifdef UNICODE
  switch (c >> 8) {
    case 0x00:
      if ((c >= 0x0030) && (c <= 0x0039)) { c -= 0x0030; break; }
      if ((c >= 0x0041) && (c <= 0x005a)) { c -= 0x0037; break; }
      if ((c >= 0x0061) && (c <= 0x007a)) { c -= 0x0057; break; }
      goto no;
    case 0x06:
      if ((c >= 0x0660) && (c <= 0x0669)) { c -= 0x0660; break; }
      if ((c >= 0x06f0) && (c <= 0x06f9)) { c -= 0x06f0; break; }
      goto no;
    case 0x09:
      if ((c >= 0x0966) && (c <= 0x096f)) { c -= 0x0966; break; }
      if ((c >= 0x09e6) && (c <= 0x09ef)) { c -= 0x09e6; break; }
      goto no;
    case 0x0A:
      if ((c >= 0x0a66) && (c <= 0x0a6f)) { c -= 0x0a66; break; }
      if ((c >= 0x0ae6) && (c <= 0x0aef)) { c -= 0x0ae6; break; }
      goto no;
    case 0x0B:
      if ((c >= 0x0b66) && (c <= 0x0b6f)) { c -= 0x0b66; break; }
      if ((c >= 0x0be7) && (c <= 0x0bef)) { c -= 0x0be6; break; }
      goto no;
    case 0x0C:
      if ((c >= 0x0c66) && (c <= 0x0c6f)) { c -= 0x0c66; break; }
      if ((c >= 0x0ce6) && (c <= 0x0cef)) { c -= 0x0ce6; break; }
      goto no;
    case 0x0D:
      if ((c >= 0x0d66) && (c <= 0x0d6f)) { c -= 0x0d66; break; }
      goto no;
    case 0x0E:
      if ((c >= 0x0e50) && (c <= 0x0e59)) { c -= 0x0e50; break; }
      if ((c >= 0x0ed0) && (c <= 0x0ed9)) { c -= 0x0ed0; break; }
      goto no;
    case 0x0F:
      if ((c >= 0x0f20) && (c <= 0x0f29)) { c -= 0x0f20; break; }
      goto no;
    case 0xFF:
      if ((c >= 0xff10) && (c <= 0xff19)) { c -= 0xff10; break; }
      goto no;
    default:
      goto no;
  }
 #else
  if (c > 'z') goto no; /* too big -> no */
  if (c >= 'a') { c -= 'a'-'A'; } /* convert character >='a',<='z' into uppercase letter */
  /* now: $00 <= ch <= $60. */
  if (c < '0') goto no;
  /* convert $30 <= c <= $60 into number value: */
  if (c <= '9') { c = c - '0'; }
  else if (c >= 'A') { c = c - 'A' + 10; }
  else goto no;
 #endif
  /* now, c is the number value of the digit, >=0, <=41. */
  if (c >= radix) goto no; /* only valid, if 0 <= c < radix. */
  /* return value as fixnum: */
  VALUES1(fixnum(c)); return;
 no: VALUES1(NIL); return;
}

LISPFUNN(alphanumericp,1) /* (ALPHANUMERICP char), CLTL p. 236 */
{ /* alphanumeric characters are the digits '0',...,'9' and the
     alphabetic characters. */
  var object arg = test_char_arg();
  VALUES_IF(alphanumericp(char_code(arg)));
}

/* comparison functions for characters:
 The comparisons CHAR=,... compare the entire oint (or equivalent,
 only the cint).
 The comparisons CHAR-EQUAL,... convert the codes into uppercase letters and
 compare those. */

/* UP: tests, if all argcount+1 arguments below args_pointer
 are characters. if not, Error.
 > argcount: number of arguments - 1
 > args_pointer: pointer to the arguments
 > subr_self: caller (a SUBR) */
local void test_char_args (uintC argcount, const object* args_pointer) {
  dotimespC(argcount,argcount+1, {
    var object arg = NEXT(args_pointer); /* next argument */
    if (!charp(arg)) /* must be a character */
      fehler_char(arg);
  });
}

/* UP: tests, if all argcount+1 arguments below args_pointer
 are characters. If not, error. Discards bits and font
 and transforms them into uppercase letters.
 > argcount: number of arguments - 1
 > args_pointer: pointer to the arguments
 > subr_self: caller (a SUBR) */
local void test_char_args_upcase (uintC argcount, object* args_pointer) {
  dotimespC(argcount,argcount+1, {
    var object* argptr = &NEXT(args_pointer);
    var object arg = *argptr; /* next argument */
    if (!charp(arg)) /* must be a character */
      fehler_char(arg);
    /* replace by uppercase letters: */
    *argptr = code_char(up_case(char_code(arg)));
  });
}

/* UP: (CHAR= char {char}) for checked arguments */
local Values char_gleich (uintC argcount, object* args_pointer) {
/* method:
 n+1 arguments Arg[0..n].
 x:=Arg[n].
 for i:=n-1 to 0 step -1 do ( if Arg[i]/=x then return(NIL) ), return(T). */
  var object x = popSTACK(); /* take last argument */
  dotimesC(argcount,argcount, {
    if (!eq(popSTACK(),x)) {
      goto no;
    }
  });
 yes:
  VALUES1(T); goto ok;
 no:
  VALUES1(NIL); goto ok;
 ok:
  set_args_end_pointer(args_pointer);
}

/* UP: (CHAR/= char {char}) for checked arguments */
local Values char_ungleich (uintC argcount, object* args_pointer) {
/* method:
 n+1 arguments Arg[0..n].
 for j:=n-1 to 0 step -1 do
   x:=Arg[j+1], for i:=j to 0 step -1 do
                   if Arg[i]=x then return(NIL),
 return(T). */
  var object* arg_j_ptr = args_end_pointer;
  var uintC j = argcount;
  while (j!=0) {
    var object x = BEFORE(arg_j_ptr); /* second last argument */
    /* compare with all previous arguments: */
    var object* arg_i_ptr = arg_j_ptr;
    var uintC i;
    dotimespC(i,j, {
      if (eq(BEFORE(arg_i_ptr),x))
        goto no;
    });
    j--;
  }
 yes: VALUES1(T); goto ok;
 no: VALUES1(NIL); goto ok;
 ok: set_args_end_pointer(args_pointer);
}

/* UP: (CHAR< char {char}) for checked arguments */
local Values char_kleiner (uintC argcount, object* args_pointer) {
  /* Method:
     n+1 Arguments Arg[0..n].
     for i:=n to 1 step -1 do
       x:=Arg[i], if x char<= Arg[i-1] then return(NIL),
     return(T). */
  dotimesC(argcount,argcount, {
    var object x = popSTACK();
    if (as_oint(x) <= as_oint(STACK_0))
      goto no;
  });
 yes: VALUES1(T); goto ok;
 no: VALUES1(NIL); goto ok;
 ok: set_args_end_pointer(args_pointer);
}

/* UP: (CHAR> char {char}) for checked arguments */
local Values char_groesser (uintC argcount, object* args_pointer)
/* method:
 n+1 arguments Arg[0..n].
 for i:=n to 1 step -1 do
    x:=Arg[i], if x char>= Arg[i-1] then return(NIL),
 return(T). */
{
  dotimesC(argcount,argcount, {
    var object x = popSTACK();
    if (as_oint(x) >= as_oint(STACK_0))
      goto no;
  });
 yes: VALUES1(T); goto ok;
 no: VALUES1(NIL); goto ok;
 ok: set_args_end_pointer(args_pointer);
}

/* UP: (CHAR<= char {char}) for checked arguments */
local Values char_klgleich (uintC argcount, object* args_pointer)
/* method:
 n+1 arguments Arg[0..n].
 for i:=n to 1 step -1 do
    x:=Arg[i], if x char< Arg[i-1] then return(NIL),
 return(T). */
{
  dotimesC(argcount,argcount, {
    var object x = popSTACK();
    if (as_oint(x) < as_oint(STACK_0))
      goto no;
  });
 yes: VALUES1(T); goto ok;
 no: VALUES1(NIL); goto ok;
 ok: set_args_end_pointer(args_pointer);
}

/* UP: (CHAR>= char {char}) for checked arguments */
local Values char_grgleich (uintC argcount, object* args_pointer)
/* method:
 n+1 arguments Arg[0..n].
 for i:=n to 1 step -1 do
    x:=Arg[i], if x char> Arg[i-1] then return(NIL),
 return(T). */
{
  dotimesC(argcount,argcount, {
    var object x = popSTACK();
    if (as_oint(x) > as_oint(STACK_0))
      goto no;
  });
 yes: VALUES1(T); goto ok;
 no: VALUES1(NIL); goto ok;
 ok: set_args_end_pointer(args_pointer);
}

LISPFUN(char_gleich,1,0,rest,nokey,0,NIL)
{ /* (CHAR= char {char}), CLTL p. 237 */
  var object* args_pointer = rest_args_pointer STACKop 1;
  test_char_args(argcount,args_pointer);
  return_Values char_gleich(argcount,args_pointer);
}

LISPFUN(char_ungleich,1,0,rest,nokey,0,NIL)
{ /* (CHAR/= char {char}), CLTL p. 237 */
  var object* args_pointer = rest_args_pointer STACKop 1;
  test_char_args(argcount,args_pointer);
  return_Values char_ungleich(argcount,args_pointer);
}

LISPFUN(char_kleiner,1,0,rest,nokey,0,NIL)
{ /* (CHAR< char {char}), CLTL p. 237 */
  var object* args_pointer = rest_args_pointer STACKop 1;
  test_char_args(argcount,args_pointer);
  return_Values char_kleiner(argcount,args_pointer);
}

LISPFUN(char_groesser,1,0,rest,nokey,0,NIL)
{ /* (CHAR> char {char}), CLTL p. 237 */
  var object* args_pointer = rest_args_pointer STACKop 1;
  test_char_args(argcount,args_pointer);
  return_Values char_groesser(argcount,args_pointer);
}

LISPFUN(char_klgleich,1,0,rest,nokey,0,NIL)
{ /* (CHAR<= char {char}), CLTL p. 237 */
  var object* args_pointer = rest_args_pointer STACKop 1;
  test_char_args(argcount,args_pointer);
  return_Values char_klgleich(argcount,args_pointer);
}

LISPFUN(char_grgleich,1,0,rest,nokey,0,NIL)
{ /* (CHAR>= char {char}), CLTL p. 237 */
  var object* args_pointer = rest_args_pointer STACKop 1;
  test_char_args(argcount,args_pointer);
  return_Values char_grgleich(argcount,args_pointer);
}

LISPFUN(char_equal,1,0,rest,nokey,0,NIL)
{ /* (CHAR-EQUAL char {char}), CLTL p. 239 */
  var object* args_pointer = rest_args_pointer STACKop 1;
  test_char_args_upcase(argcount,args_pointer);
  return_Values char_gleich(argcount,args_pointer);
}

LISPFUN(char_not_equal,1,0,rest,nokey,0,NIL)
{ /* (CHAR-NOT-EQUAL char {char}), CLTL p. 239 */
  var object* args_pointer = rest_args_pointer STACKop 1;
  test_char_args_upcase(argcount,args_pointer);
  return_Values char_ungleich(argcount,args_pointer);
}

LISPFUN(char_lessp,1,0,rest,nokey,0,NIL)
{ /* (CHAR-LESSP char {char}), CLTL p. 239 */
  var object* args_pointer = rest_args_pointer STACKop 1;
  test_char_args_upcase(argcount,args_pointer);
  return_Values char_kleiner(argcount,args_pointer);
}

LISPFUN(char_greaterp,1,0,rest,nokey,0,NIL)
{ /* (CHAR-GREATERP char {char}), CLTL p. 239 */
  var object* args_pointer = rest_args_pointer STACKop 1;
  test_char_args_upcase(argcount,args_pointer);
  return_Values char_groesser(argcount,args_pointer);
}

LISPFUN(char_not_greaterp,1,0,rest,nokey,0,NIL)
{ /* (CHAR-NOT-GREATERP char {char}), CLTL p. 239 */
  var object* args_pointer = rest_args_pointer STACKop 1;
  test_char_args_upcase(argcount,args_pointer);
  return_Values char_klgleich(argcount,args_pointer);
}

LISPFUN(char_not_lessp,1,0,rest,nokey,0,NIL)
{ /* (CHAR-NOT-LESSP char {char}), CLTL p. 239 */
  var object* args_pointer = rest_args_pointer STACKop 1;
  test_char_args_upcase(argcount,args_pointer);
  return_Values char_grgleich(argcount,args_pointer);
}

LISPFUNN(char_code,1)
{ /* (CHAR-CODE char), CLTL p. 239 */
  var object arg = test_char_arg();
  VALUES1(fixnum(as_cint(char_code(arg)))); /* ascii-code as fixnum */
}

LISPFUNN(code_char,1)
/* (CODE-CHAR code) */
{
  var object codeobj = popSTACK(); /* code-argument */
  if (!integerp(codeobj)) {
    /* code-argument is not an integer. */
    pushSTACK(codeobj); /* TYPE-ERROR slot DATUM */
    pushSTACK(S(integer)); /* TYPE-ERROR slot EXPECTED-TYPE */
    pushSTACK(codeobj); pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,
           GETTEXT("~: the code argument should be an integer, not ~"));
  }
  /* codeobj is now an integer. */
  var uintL code;
  /* test, if  0 <= code < char_code_limit : */
  if (posfixnump(codeobj) &&
      ((code = posfixnum_to_L(codeobj)) < char_code_limit)) {
    VALUES1(code_char(as_chart(code))); /* handicraft character */
  } else {
    VALUES1(NIL); /* else value NIL */
  }
}

LISPFUNN(character,1) /* (CHARACTER object), CLTL p. 241 */
{
  var object trial = coerce_char(STACK_0); /* convert argument into character */
  if (nullp(trial)) { /* unsuccessfully? */
    /* Argument still in STACK_0, TYPE-ERROR slot DATUM */
    pushSTACK(O(type_designator_character)); /* TYPE-ERROR slot EXPECTED-TYPE*/
    pushSTACK(STACK_1);
    pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,GETTEXT("~: cannot coerce ~ to a character"));
  } else {
    VALUES1(trial); skipSTACK(1);
  }
}

LISPFUNN(char_upcase,1) /* (CHAR-UPCASE char), CLTL p. 241 */
{
  var object arg = test_char_arg();
  VALUES1(code_char(up_case(char_code(arg)))); /* convert into uppercase letters */
}

LISPFUNN(char_downcase,1) /* (CHAR-DOWNCASE char), CLTL p. 241 */
{
  var object arg = test_char_arg();
  VALUES1(code_char(down_case(char_code(arg)))); /* convert into lowercase letters */
}

LISPFUN(digit_char,1,1,norest,nokey,0,NIL)
/* (DIGIT-CHAR weight [radix]), CLTL2 p. 384
 method:
 all arguments have to be integers, radix between 2 and 36.
 if 0 <= weight < radix, construct
     a character from '0',...,'9','A',...,'Z' with value weight.
 else value NIL. */
{
  var uintWL radix = test_radix_arg(); /* radix-argument, >=2, <=36 */
  var object weightobj = popSTACK(); /* weight-argument */
  if (!integerp(weightobj)) {
    /* weight-Argument is not an integer. */
    pushSTACK(weightobj); /* TYPE-ERROR slot DATUM */
    pushSTACK(S(integer)); /* TYPE-ERROR slot EXPECTED-TYPE */
    pushSTACK(weightobj); pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,
           GETTEXT("~: the weight argument should be an integer, not ~"));
  }
  /* weightobj is now an integer. */
  /* test, if 0<=weight<radix, else NIL: */
  var uintL weight;
  if (posfixnump(weightobj) &&
      ((weight = posfixnum_to_L(weightobj)) < radix)) {
    weight = weight + '0'; /* convert into digit */
    if (weight > '9')
      weight += 'A'-'0'-10; /* or turn it into a letter */
    VALUES1(ascii_char(weight)); /* handicraft character */
  } else {
    VALUES1(NIL);
  }
}

LISPFUNN(char_int,1) /* (CHAR-INT char), CLTL p. 242 */
{
  var object arg = test_char_arg();
  VALUES1(fixnum(as_cint(char_code(arg))));
}

LISPFUNN(int_char,1) /* (INT-CHAR integer), CLTL p. 242 */
{
  var object arg = popSTACK(); /* integer-Argument */
  if (integerp(arg)) {
    /* turn into a character if 0 <= arg < char_code_limit, else NIL */
    var uintL i;
    if ((posfixnump(arg)) && ((i = posfixnum_to_L(arg)) < char_code_limit)) {
      VALUES1(code_char(as_chart(i)));
    } else {
      VALUES1(NIL);
    }
  } else { /* arg not an integer -> error: */
    pushSTACK(arg); /* TYPE-ERROR slot DATUM */
    pushSTACK(S(integer)); /* TYPE-ERROR slot EXPECTED-TYPE */
    pushSTACK(arg); pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,GETTEXT("~: argument should be an integer, not ~"));
  }
}

LISPFUNN(char_name,1) /* (CHAR-NAME char), CLTL p. 242 */
{
  var object arg = test_char_arg();
  VALUES1(char_name(char_code(arg)));
}


/* error, if index-argument is not an integer. */
nonreturning_function(local, fehler_int, (object kw, object obj)) {
  pushSTACK(obj); /* TYPE-ERROR slot DATUM */
  pushSTACK(S(integer)); /* TYPE-ERROR slot EXPECTED-TYPE */
  pushSTACK(obj);
  if (eq(kw,nullobj)) {
    pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,GETTEXT("~: index should be an integer, not ~"));
  } else {
    pushSTACK(kw); pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,GETTEXT("~: ~-index should be an integer, not ~"));
  }
}

/* error, if index-argument is not an integer or NIL. */
nonreturning_function(local, fehler_int_null, (object kw, object obj)) {
  pushSTACK(obj); /* TYPE-ERROR slot DATUM */
  pushSTACK(O(type_end_index)); /* TYPE-ERROR slot EXPECTED-TYPE */
  pushSTACK(obj);
  if (eq(kw,nullobj)) {
    pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,GETTEXT("~: index should be NIL or an integer, not ~"));
  } else {
    pushSTACK(kw); pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,GETTEXT("~: ~-index should be NIL or an integer, not ~"));
  }
}

/* error, if index-argument is negative. */
nonreturning_function(local, fehler_posint, (object kw, object obj)) {
  pushSTACK(obj); /* TYPE-ERROR slot DATUM */
  pushSTACK(O(type_posinteger)); /* TYPE-ERROR slot EXPECTED-TYPE */
  pushSTACK(obj);
  if (eq(kw,nullobj)) {
    pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,GETTEXT("~: index should not be negative: ~"));
  } else {
    pushSTACK(kw); pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,GETTEXT("~: ~-index should not be negative: ~"));
  }
}

/* error, if index-argument is not <= limit. */
nonreturning_function(local, fehler_cmp_inclusive, (object kw, object obj,
                                                    uintL grenze)) {
  pushSTACK(obj); /* TYPE-ERROR slot DATUM */
  pushSTACK(NIL);
  pushSTACK(obj);
  {
    var object tmp;
    pushSTACK(S(integer)); pushSTACK(Fixnum_0); pushSTACK(UL_to_I(grenze));
    tmp = listof(3);
    STACK_1 = tmp; /* TYPE-ERROR slot EXPECTED-TYPE */
  }
  if (eq(kw,nullobj)) {
    pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,GETTEXT("~: index ~ should not be greater than the length of the string"));
  } else {
    pushSTACK(kw); pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,GETTEXT("~: ~-index ~ should not be greater than the length of the string"));
  }
}

/* error, if index-argument is not < limit. */
nonreturning_function(local, fehler_cmp_exclusive, (object kw, object obj,
                                                    uintL grenze)) {
  pushSTACK(obj); /* TYPE-ERROR slot DATUM */
  pushSTACK(NIL);
  pushSTACK(obj);
  {
    var object tmp;
    pushSTACK(S(integer)); pushSTACK(Fixnum_0); pushSTACK(UL_to_I(grenze));
    tmp = listof(1); pushSTACK(tmp); tmp = listof(3);
    STACK_1 = tmp; /* TYPE-ERROR slot EXPECTED-TYPE */
  }
  if (eq(kw,nullobj)) {
    pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,
           GETTEXT("~: index ~ should be less than the length of the string"));
  } else {
    pushSTACK(kw); pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,GETTEXT("~: ~-index ~ should be less than the length of the string"));
  }
}

/* Macro: checks an index-argument
 test_index(woher,wohin_zuweisung,def,default,vergleich,grenze,ucname,lcname)
 woher : expression, where the index (as object) comes from.
 wohin_zuweisung : assigns the result (as uintL) .
 def : 0 if we do not have to test for default values,
       1 if the default is set in on unbound,
       2 if the default is set in on unbound or NIL.
 default : expression, that serves as default value in this case.
 grenze : upper limit
 vergleich : comparison with upper limit
 kw : keyword, that identifies the index, or nullobj */
#define test_index(woher,wohin_zuweisung,def,default,vergleich,grenze,kw) \
  { var object index = woher; /* index-argument */                      \
    if (def && (!boundp(index) || (def == 2 && nullp(index))))          \
      { wohin_zuweisung default; }                                      \
    else { /* must be an integer: */                                    \
      if (!integerp(index))                                             \
        { if (def==2) fehler_int_null(kw,index); else fehler_int(kw,index); } \
      /* index is an integer. */                                        \
      if (!(positivep(index)))                                          \
        { fehler_posint(kw,index); }                                    \
      /* index is >=0. */                                               \
      if (!((posfixnump(index)) &&                                      \
            ((wohin_zuweisung posfixnum_to_L(index)) vergleich grenze))) { \
        if (0 vergleich 0)                                              \
          /* "<= grenze" - comparison not satisfied (grenze == limit) */ \
          { fehler_cmp_inclusive(kw,index,grenze); }                    \
        else                                                            \
          /* "< grenze" - comparison not satisfied (grenze == limit) */ \
          { fehler_cmp_exclusive(kw,index,grenze); }                    \
      }                                                                 \
    }}

/* UP: check the index argument for string functions
 > STACK_0: Argument
 > len: length of the strings (< array-total-size-limit)
 > subr_self: caller (a SUBR)
 < return: index in the string */
local uintL test_index_arg (uintL len)
{
  var uintL i;
  /* i := Index STACK_0, no default value, must be <len: */
  test_index(STACK_0,i=,0,0,<,len,nullobj);
  return i;
}

LISPFUNN(char,2) /* (CHAR string index), CLTL p. 300 */
{
  var object string = STACK_1;
  if (!stringp(string))
    fehler_string(string);
  var uintL len;
  var uintL offset = 0;
  /* Don't use unpack_string_ro() -- we need (array-dimension string 0),
     not (length string). */
  if (simple_string_p(string)) {
    simple_array_to_storage(string);
    len = Sstring_length(string);
  } else {
    len = TheIarray(string)->totalsize;
    string = iarray_displace_check(string,len,&offset);
  }
  var uintL index = test_index_arg(len);
  VALUES1(code_char(schar(string,offset+index)));
  skipSTACK(2);
}

LISPFUNN(schar,2) /* (SCHAR string integer), CLTL p. 300 */
{
  var object string = STACK_1;
  if (!simple_string_p(string))
    fehler_sstring(string);
  simple_array_to_storage(string);
  var uintL index = test_index_arg(Sstring_length(string));
  VALUES1(code_char(schar(string,index)));
  skipSTACK(2);
}

LISPFUNN(store_char,3)
/* (SYSTEM::STORE-CHAR string index newchar)
 = (SETF (CHAR string index) newchar), CLTL p. 300 */
{
  var object newchar = test_char_arg(); /* newchar-Argument */
  var object string = STACK_1; /* string-argument */
  if (!stringp(string)) /* must be a string */
    fehler_string(string);
  var uintL len;
  var uintL offset = 0;
  /* Don't use unpack_string_rw() -- we need (array-dimension string 0),
     not (length string). */
  if (simple_string_p(string)) {
    simple_array_to_storage(string);
    len = Sstring_length(string);
  } else {
    len = TheIarray(string)->totalsize;
    string = iarray_displace_check(string,len,&offset);
  }
  check_sstring_mutable(string);
  offset += test_index_arg(len); /* go to the element addressed by index */
  sstring_store(string,offset,char_code(newchar)); /* put in the character */
  VALUES1(newchar);
  skipSTACK(2);
}

LISPFUNN(store_schar,3)
/* (SYSTEM::STORE-SCHAR simple-string index newchar)
 = (SETF (SCHAR simple-string index) newchar), CLTL p. 300 */
{
  var object newchar = test_char_arg(); /* newchar-argument */
  var object string = STACK_1; /* string-argument */
  if (!simple_string_p(string)) /* must be a simple-string */
    fehler_sstring(string);
  simple_array_to_storage(string);
  check_sstring_mutable(string);
  var uintL offset = test_index_arg(Sstring_length(string)); /* go to the element addressed by index */
  sstring_store(string,offset,char_code(newchar)); /* put in the character */
  VALUES1(newchar);
  skipSTACK(2);
}

/* UP: checks the limits for a string-argument
 test_string_limits_ro(&arg)  [for read-only access]
 > STACK_2: string-argument
 > STACK_1: optional :start-argument
 > STACK_0: optional :end-argument
 > subr_self: caller (a SUBR)
 < stringarg arg: description of the argument
 < result: string-argument
 increases STACK by 3 */
global object test_string_limits_ro (stringarg* arg) {
  var uintL len;
  var uintL start;
  var uintL end;
  /* check string-argument: */
  var object string = STACK_2;
  if (!stringp(string))
    fehler_string(string);
  arg->string = unpack_string_ro(string,&len,&arg->offset);
  /* now, len is the length (<2^oint_data_len).
     check :START-argument:
     start := Index STACK_1, default value 0, must be <=len : */
  test_index(STACK_1,start=,1,0,<=,len,S(Kstart));
  /* start is now the value of the :START-argument.
     check :END-argument:
     end := Index STACK_0, default value len, musst be <=len : */
  test_index(STACK_0,end=,2,len,<=,len,S(Kend));
  /* end is now the value of the :END-argument.
     compare :START and :END arguments: */
  if (!(start <= end)) {
    pushSTACK(STACK_0); /* :END-Index */
    pushSTACK(STACK_2); /* :START-Index */
    pushSTACK(TheSubr(subr_self)->name);
    fehler(error,GETTEXT("~: :start-index ~ must not be greater than :end-index ~"));
  }
  skipSTACK(3);
  /* issue results: */
  arg->index = start; arg->len = end-start;
  return string;
}

/* UP: checks the limits for a string-argument
 test_string_limits_rw(&arg)  [for read-write access]
 > STACK_2: string-argument
 > STACK_1: optional :start-argument
 > STACK_0: optional :end-argument
 > subr_self: caller (a SUBR)
 < stringarg arg: description of the argument
 < result: string-argument
 increases STACK by 3 */
#ifdef TYPECODES
#define test_string_limits_rw(arg)  test_string_limits_ro(arg)
#else
local object test_string_limits_rw (stringarg* arg) {
  var object string = test_string_limits_ro(arg);
  if (arg->len > 0) {
    switch (Record_type(arg->string)) {
      case Rectype_Imm_S8string:
      case Rectype_Imm_S16string:
      case Rectype_Imm_S32string:
        fehler_sstring_immutable(string);
      case Rectype_S8string:
      case Rectype_S16string:
      case Rectype_S32string:
        break;
      default: NOTREACHED;
    }
  }
  return string;
}
#endif

/* UP: checks a string/symbol/character-argument
 > obj: argument
 > subr_self: caller (a SUBR)
 < ergebnis: argument as string
 can trigger GC */
local object test_stringsymchar_arg (object obj) {
  if (stringp(obj)) /* string: return unchanged */
    return obj;
  if (symbolp(obj)) /* symbol: user print name */
    return TheSymbol(obj)->pname;
  if (charp(obj)) { /* character: turn it into a one-element string: */
    var object new_string = allocate_string(1);
    TheSstring(new_string)->data[0] = char_code(obj);
    return new_string;
  }
  pushSTACK(obj); /* TYPE-ERROR slot DATUM */
  pushSTACK(O(type_stringsymchar)); /* TYPE-ERROR slot EXPECTED-TYPE */
  pushSTACK(obj); pushSTACK(TheSubr(subr_self)->name);
  fehler(type_error,GETTEXT("~: argument ~ should be a string, a symbol or a character"));
}

/* UP: checks the limits for 1 string/symbol-argument and copies it
 test_1_stringsym_limits(&string,&len)
 > STACK_2: string/symbol-argument
 > STACK_1: optional :start-argument
 > STACK_0: optional :end-argument
 > subr_self: caller (a SUBR)
 < object string: copy of the string
 < uintL offset: index of first affected character
 < uintL len: number of affected characters
 increases STACK by 3
 can trigger GC */
local void test_1_stringsym_limits (object* string_, uintL* offset_,
                                    uintL* len_) {
  var object string;
  var uintL len;
  var uintL start;
  var uintL end;
  /* check string/symbol-argument: */
  string = test_stringsymchar_arg(STACK_2);
  len = vector_length(string);
  /* now, len is the length (<2^oint_data_len).
     check :START-argument:
     start := Index STACK_1, default value 0, must be <=len : */
  test_index(STACK_1,start=,1,0,<=,len,S(Kstart));
  /* start is now the value of the :START-argument.
     check :END-argument:
     end := Index STACK_0, default value len, must be <=len : */
  test_index(STACK_0,end=,2,len,<=,len,S(Kend));
  /* end is now the value of the :END-argument.
     compare :START and :END arguments: */
  if (!(start <= end)) {
    pushSTACK(STACK_0); /* :END-Index */
    pushSTACK(STACK_2); /* :START-Index */
    pushSTACK(TheSubr(subr_self)->name);
    fehler(error,GETTEXT("~: :start-index ~ must not be greater than :end-index ~"));
  }
  skipSTACK(3);
  /* copy string and issue results: */
  *string_ = copy_string(string); /* copy string */
  *offset_ = start; *len_ = end-start;
}

/* UP: checks the limits for 2 string/symbol-arguments
 test_2_stringsym_limits(&arg1,&arg2)
 > STACK_5: string/symbol-argument1
 > STACK_4: string/symbol-argument2
 > STACK_3: optional :start1-argument
 > STACK_2: optional :end1-argument
 > STACK_1: optional :start2-argument
 > STACK_0: optional :end2-argument
 > subr_self: caller (a SUBR)
 < stringarg arg1: description of argument1
 < stringarg arg2: description of argument2
 increases STACK by 6 */
local void test_2_stringsym_limits (stringarg* arg1, stringarg* arg2) {
  var uintL len1;
  var uintL len2;
  { /* check string/symbol-argument1: */
    var object string1 = test_stringsymchar_arg(STACK_5);
    pushSTACK(string1); /* save string1 */
    /* check string/symbol-argument2: */
    var object string2 = test_stringsymchar_arg(STACK_(4+1));
    arg2->string = unpack_string_ro(string2,&len2,&arg2->offset);
    /* now, len2 is the length (<2^oint_data_len) of string2. */
    string1 = popSTACK(); /* restore string1 */
    arg1->string = unpack_string_ro(string1,&len1,&arg1->offset);
    /* now, len1 is the length (<2^oint_data_len) of string1. */
  }
  { /* check :START1 and :END1: */
    var uintL start1;
    var uintL end1;
    /* check :START1-argument:
       start1 := Index STACK_3, default value 0, must be <=len1: */
    test_index(STACK_3,start1=,1,0,<=,len1,S(Kstart1));
    /* start1 is now the value of the :START1-argument.
       check :END1-argument:
       end1 := Index STACK_2, default value len1, must be <=len1: */
    test_index(STACK_2,end1=,2,len1,<=,len1,S(Kend1));
    /* end1 is now the value of the :END1-argument.
       compare :START1 and :END1 arguments: */
    if (!(start1 <= end1)) {
      pushSTACK(STACK_2); /* :END1-Index */
      pushSTACK(STACK_4); /* :START1-Index */
      pushSTACK(TheSubr(subr_self)->name);
      fehler(error,GETTEXT("~: :start1-index ~ must not be greater than :end1-index ~"));
    }
    /* issue the results for string1: */
    arg1->index = start1; arg1->len = end1-start1;
  }
  { /* check :START2 and :END2: */
    var uintL start2;
    var uintL end2;
    /* check :START2-argument:
       start2 := Index STACK_1, default value 0, must be <=len2: */
    test_index(STACK_1,start2=,1,0,<=,len2,S(Kstart2));
    /* start2 is now the value of the :START2-argument.
       check :END2-argument:
       end2 := Index STACK_0, default value len2, must be <=len2: */
    test_index(STACK_0,end2=,2,len2,<=,len2,S(Kend2));
    /* end2 is now the value of the :END2-argument.
       compare :START2 and :END2 arguments: */
    if (!(start2 <= end2)) {
      pushSTACK(STACK_0); /* :END2-Index */
      pushSTACK(STACK_2); /* :START2-Index */
      pushSTACK(TheSubr(subr_self)->name);
      fehler(error,GETTEXT("~: :start2-index ~ must not be greater than :end2-index ~"));
    }
    /* issue the results for string2: */
    arg2->index = start2; arg2->len = end2-start2;
    /* done. */
    skipSTACK(6);
  }
}

/* UP: compares two strings of equal length for equality
 > string1,offset1: here are the addressed characters in string1
 > string2,offset2: here are the addressed characters in string2
 > len: number of addressed characters in String1 and in String2, > 0
 < result: true if equal, else false. */
global bool string_eqcomp (object string1, uintL offset1, object string2, uintL offset2, uintL len) {
  SstringDispatch(string1,X1, {
    var const cintX1* charptr1 = &((SstringX1)TheVarobject(string1))->data[offset1];
    SstringDispatch(string2,X2, {
      var const cintX2* charptr2 = &((SstringX2)TheVarobject(string2))->data[offset2];
      dotimespL(len,len, {
        if (!chareq(as_chart(*charptr1++),as_chart(*charptr2++)))
          goto no;
      });
    });
  });
  return true;
 no: return false;
}

/* UP: compares two strings
 > arg1: here are the addressed characters in string1
 > arg2: here are the addressed characters in string2
 < arg1.index: location of the first difference i string1
 < ergebnis: 0 if equal,
             -1 if string1 is genuinely lesser than string2,
             +1 if string1 is genuinely bigger than string2. */
local signean string_comp (stringarg* arg1, const stringarg* arg2){
  var uintL len1 = arg1->len;
  var uintL len2 = arg2->len;
  SstringCase(arg1->string, {
    var const cint8* charptr1_0 = &TheS8string(arg1->string)->data[arg1->offset];
    var const cint8* charptr1 = &charptr1_0[arg1->index];
    SstringDispatch(arg2->string,X2, {
      var const cintX2* charptr2 = &((SstringX2)TheVarobject(arg2->string))->data[arg2->offset+arg2->index];
      loop {
        /* one of the strings finished ? */
        if (len1==0) goto A_string1_end;
        if (len2==0) goto A_string2_end;
        /* compare next characters: */
        if (!chareq(as_chart(*charptr1++),as_chart(*charptr2++))) break;
        /* decrease both counters: */
        len1--; len2--;
      }
      /* two different characters are found */
      arg1->index = --charptr1 - charptr1_0;
      if (charlt(as_chart(*charptr1),as_chart(*--charptr2)))
        return signean_minus; /* string1 < string2 */
      else
        return signean_plus; /* string1 > string2 */
    });
  A_string1_end: /* string1 finished */
    arg1->index = charptr1 - charptr1_0;
    if (len2==0)
      return signean_null; /* string1 = string2 */
    else /* String1 is a genuine starting piece of string2 */
      return signean_minus;
  A_string2_end: /* string2 is finished, string1 is not yet finished */
    arg1->index = charptr1 - charptr1_0;
    return signean_plus; /* string2 is a genuine starting piece of string1 */
  }, {
    var const cint16* charptr1_0 = &TheS16string(arg1->string)->data[arg1->offset];
    var const cint16* charptr1 = &charptr1_0[arg1->index];
    SstringDispatch(arg2->string,X2, {
      var const cintX2* charptr2 = &((SstringX2)TheVarobject(arg2->string))->data[arg2->offset+arg2->index];
      loop {
        /* one of the strings finished ? */
        if (len1==0) goto B_string1_end;
        if (len2==0) goto B_string2_end;
        /* compare next characters: */
        if (!chareq(as_chart(*charptr1++),as_chart(*charptr2++))) break;
        /* decrease both counters: */
        len1--; len2--;
      }
      /* two different characters are found */
      arg1->index = --charptr1 - charptr1_0;
      if (charlt(as_chart(*charptr1),as_chart(*--charptr2)))
        return signean_minus; /* string1 < string2 */
      else
        return signean_plus; /* string1 > string2 */
    });
  B_string1_end: /* string1 finished */
    arg1->index = charptr1 - charptr1_0;
    if (len2==0)
      return signean_null; /* string1 = string2 */
    else /* String1 is a genuine starting piece of string2 */
      return signean_minus;
  B_string2_end: /* string2 is finished, string1 is not yet finished */
    arg1->index = charptr1 - charptr1_0;
    return signean_plus; /* string2 is a genuine starting piece of string1 */
  }, {
    var const cint32* charptr1_0 = &TheS32string(arg1->string)->data[arg1->offset];
    var const cint32* charptr1 = &charptr1_0[arg1->index];
    SstringDispatch(arg2->string,X2, {
      var const cintX2* charptr2 = &((SstringX2)TheVarobject(arg2->string))->data[arg2->offset+arg2->index];
      loop {
        /* one of the strings finished ? */
        if (len1==0) goto C_string1_end;
        if (len2==0) goto C_string2_end;
        /* compare next characters: */
        if (!chareq(as_chart(*charptr1++),as_chart(*charptr2++))) break;
        /* decrease both counters: */
        len1--; len2--;
      }
      /* two different characters are found */
      arg1->index = --charptr1 - charptr1_0;
      if (charlt(as_chart(*charptr1),as_chart(*--charptr2)))
        return signean_minus; /* string1 < string2 */
      else
        return signean_plus; /* string1 > string2 */
    });
  C_string1_end: /* string1 finished */
    arg1->index = charptr1 - charptr1_0;
    if (len2==0)
      return signean_null; /* string1 = string2 */
    else /* string1 is a genuine starting piece of string2 */
      return signean_minus;
  C_string2_end: /* string2 is finished, string1 is not yet finished */
    arg1->index = charptr1 - charptr1_0;
    return signean_plus; /* string2 is a genuine starting piece of string1 */
  });
}

LISPFUN(string_gleich,2,0,norest,key,4,
        (kw(start1),kw(end1),kw(start2),kw(end2)) )
{ /* (STRING= string1 string2 :start1 :end1 :start2 :end2), CLTL p. 300 */
  var stringarg arg1;
  var stringarg arg2;
  /* check arguments: */
  test_2_stringsym_limits(&arg1,&arg2);
  /* compare: */
  VALUES_IF((arg1.len==arg2.len)
            && ((arg1.len==0)
                || string_eqcomp(arg1.string,arg1.offset+arg1.index,
                                 arg2.string,arg2.offset+arg2.index,
                                 arg1.len)));
}

LISPFUN(string_ungleich,2,0,norest,key,4,
        (kw(start1),kw(end1),kw(start2),kw(end2)) )
{ /* (STRING/= string1 string2 :start1 :end1 :start2 :end2), CLTL p. 301 */
  var stringarg arg1;
  var stringarg arg2;
  /* check arguments: */
  test_2_stringsym_limits(&arg1,&arg2);
  /* compare: */
  VALUES1(string_comp(&arg1,&arg2)==0 ? NIL : fixnum(arg1.index));
}

LISPFUN(string_kleiner,2,0,norest,key,4,
        (kw(start1),kw(end1),kw(start2),kw(end2)) )
{ /* (STRING< string1 string2 :start1 :end1 :start2 :end2), CLTL p. 301 */
  var stringarg arg1;
  var stringarg arg2;
  /* check arguments: */
  test_2_stringsym_limits(&arg1,&arg2);
  /* compare: */
  VALUES1(string_comp(&arg1,&arg2)<0 ? fixnum(arg1.index) : NIL);
}

LISPFUN(string_groesser,2,0,norest,key,4,
        (kw(start1),kw(end1),kw(start2),kw(end2)) )
{ /* (STRING> string1 string2 :start1 :end1 :start2 :end2), CLTL p. 301 */
  var stringarg arg1;
  var stringarg arg2;
  /* check arguments: */
  test_2_stringsym_limits(&arg1,&arg2);
  /* compare: */
  VALUES1(string_comp(&arg1,&arg2)>0 ? fixnum(arg1.index) : NIL);
}

LISPFUN(string_klgleich,2,0,norest,key,4,
        (kw(start1),kw(end1),kw(start2),kw(end2)) )
{ /* (STRING<= string1 string2 :start1 :end1 :start2 :end2), CLTL p. 301 */
  var stringarg arg1;
  var stringarg arg2;
  /* check arguments: */
  test_2_stringsym_limits(&arg1,&arg2);
  /* compare: */
  VALUES1(string_comp(&arg1,&arg2)<=0 ? fixnum(arg1.index) : NIL);
}

LISPFUN(string_grgleich,2,0,norest,key,4,
        (kw(start1),kw(end1),kw(start2),kw(end2)) )
{ /* (STRING>= string1 string2 :start1 :end1 :start2 :end2), CLTL p. 301 */
  var stringarg arg1;
  var stringarg arg2;
  /* check arguments: */
  test_2_stringsym_limits(&arg1,&arg2);
  /* compare: */
  VALUES1(string_comp(&arg1,&arg2)>=0 ? fixnum(arg1.index) : NIL);
}

/* UP: compares two strings of equal length for equality, case-insensitive
 > string1,offset1: here are the addressed characters in string1
 > string2,offset2: here are the addressed characters in string2
 > len: number of addressed characters in String1 and in String2, > 0
 < result: true if equal, else false. */
global bool string_eqcomp_ci (object string1, uintL offset1, object string2,
                              uintL offset2, uintL len) {
  SstringDispatch(string1,X1, {
    var const cintX1* charptr1 = &((SstringX1)TheVarobject(string1))->data[offset1];
    SstringDispatch(string2,X2, {
      var const cintX2* charptr2 = &((SstringX2)TheVarobject(string2))->data[offset2];
      dotimespL(len,len, {
        if (!chareq(up_case(as_chart(*charptr1++)),up_case(as_chart(*charptr2++))))
          goto no;
      });
    });
  });
  return true;
 no: return false;
}

/* UP: compares two strings, case-insensitive
 > arg1: here are the addressed characters in string1
 > arg2: here are the addressed characters in string2
 < arg1.index: location of the first difference i string1
 < result: 0 if equal,
             -1 if string1 is genuinely lesser than string2,
             +1 if string1 is genuinely bigger than string2. */
local signean string_comp_ci (stringarg* arg1, const stringarg* arg2)
{
  var uintL len1 = arg1->len;
  var uintL len2 = arg2->len;
  SstringCase(arg1->string,{
    var const cint8* charptr1_0 = &TheS8string(arg1->string)->data[arg1->offset];
    var const cint8* charptr1 = &charptr1_0[arg1->index];
    var chart ch1;
    var chart ch2;
    SstringDispatch(arg2->string,X2, {
      var const cintX2* charptr2 = &((SstringX2)TheVarobject(arg2->string))->data[arg2->offset+arg2->index];
      loop {
        /* is one of the strings finished ? */
        if (len1==0) goto A_string1_end;
        if (len2==0) goto A_string2_end;
        /* compare next characters: */
        if (!chareq(ch1 = up_case(as_chart(*charptr1++)), ch2 = up_case(as_chart(*charptr2++)))) break;
        /* decrease both counters: */
        len1--; len2--;
      }
    });
    /* two different characters are found */
    arg1->index = --charptr1 - charptr1_0;
    if (charlt(ch1,ch2))
      return signean_minus; /* string1 < string2 */
    else
      return signean_plus; /* string1 > string2 */
   A_string1_end: /* string1 finished */
    arg1->index = charptr1 - charptr1_0;
    if (len2==0)
      return signean_null; /* string1 = string2 */
    else
      return signean_minus; /* string1 is a genuine starting piece of string2 */
   A_string2_end: /* string2 is finished, string1 is not yet finished */
    arg1->index = charptr1 - charptr1_0;
    return signean_plus; /* string2 is a genuine starting piece of string1 */
  },{
    var const cint16* charptr1_0 = &TheS16string(arg1->string)->data[arg1->offset];
    var const cint16* charptr1 = &charptr1_0[arg1->index];
    var chart ch1;
    var chart ch2;
    SstringDispatch(arg2->string,X2, {
      var const cintX2* charptr2 = &((SstringX2)TheVarobject(arg2->string))->data[arg2->offset+arg2->index];
      loop {
        /* is one of the strings finished ? */
        if (len1==0) goto B_string1_end;
        if (len2==0) goto B_string2_end;
        /* compare next characters: */
        if (!chareq(ch1 = up_case(as_chart(*charptr1++)), ch2 = up_case(as_chart(*charptr2++)))) break;
        /* decrease both counters: */
        len1--; len2--;
      }
    });
    /* two different characters are found */
    arg1->index = --charptr1 - charptr1_0;
    if (charlt(ch1,ch2))
      return signean_minus; /* string1 < string2 */
    else
      return signean_plus; /* string1 > string2 */
   B_string1_end: /* string1 finished */
    arg1->index = charptr1 - charptr1_0;
    if (len2==0)
      return signean_null; /* string1 = string2 */
    else
      return signean_minus; /* string1 is a genuine starting piece of string2 */
   B_string2_end: /* string2 is finished, string1 is not yet finished */
    arg1->index = charptr1 - charptr1_0;
    return signean_plus; /* string2 is a genuine starting piece of string1 */
  },{
    var const cint32* charptr1_0 = &TheS32string(arg1->string)->data[arg1->offset];
    var const cint32* charptr1 = &charptr1_0[arg1->index];
    var chart ch1;
    var chart ch2;
    SstringDispatch(arg2->string,X2, {
      var const cintX2* charptr2 = &((SstringX2)TheVarobject(arg2->string))->data[arg2->offset+arg2->index];
      loop {
        /* is one of the strings finished ? */
        if (len1==0) goto C_string1_end;
        if (len2==0) goto C_string2_end;
        /* compare next characters: */
        if (!chareq(ch1 = up_case(as_chart(*charptr1++)), ch2 = up_case(as_chart(*charptr2++)))) break;
        /* decrease both counters: */
        len1--; len2--;
      }
    });
    /* two different characters are found */
    arg1->index = --charptr1 - charptr1_0;
    if (charlt(ch1,ch2))
      return signean_minus; /* string1 < string2 */
    else
      return signean_plus; /* string1 > string2 */
   C_string1_end: /* String1 finished */
    arg1->index = charptr1 - charptr1_0;
    if (len2==0)
      return signean_null; /* string1 = string2 */
    else
      return signean_minus; /* string1 is a genuine starting piece of string2 */
   C_string2_end: /* string2 is finished, string1 is not yet finished */
    arg1->index = charptr1 - charptr1_0;
    return signean_plus; /* string2 is a genuine starting piece of string1 */
  });
}

LISPFUN(string_equal,2,0,norest,key,4,
        (kw(start1),kw(end1),kw(start2),kw(end2)) )
{ /* (STRING-EQUAL string1 string2 :start1 :end1 :start2 :end2), CLTL p. 301 */
  var stringarg arg1;
  var stringarg arg2;
  /* check arguments: */
  test_2_stringsym_limits(&arg1,&arg2);
  /* compare: */
  VALUES_IF((arg1.len==arg2.len)
            && ((arg1.len==0)
                || string_eqcomp_ci(arg1.string,arg1.offset+arg1.index,
                                    arg2.string,arg2.offset+arg2.index,
                                    arg1.len)));
}

LISPFUN(string_not_equal,2,0,norest,key,4,
        (kw(start1),kw(end1),kw(start2),kw(end2)) )
{ /* (STRING-NOT-EQUAL string1 string2 :start1 :end1 :start2 :end2),
     CLTL p. 302 */
  var stringarg arg1;
  var stringarg arg2;
  /* check arguments: */
  test_2_stringsym_limits(&arg1,&arg2);
  /* compare: */
  VALUES1(string_comp_ci(&arg1,&arg2)==0 ? NIL : fixnum(arg1.index));
}

LISPFUN(string_lessp,2,0,norest,key,4,
        (kw(start1),kw(end1),kw(start2),kw(end2)) )
{ /* (STRING-LESSP string1 string2 :start1 :end1 :start2 :end2), CLTL p. 302 */
  var stringarg arg1;
  var stringarg arg2;
  /* check arguments: */
  test_2_stringsym_limits(&arg1,&arg2);
  /* compare: */
  VALUES1(string_comp_ci(&arg1,&arg2)<0 ? fixnum(arg1.index) : NIL);
}

LISPFUN(string_greaterp,2,0,norest,key,4,
        (kw(start1),kw(end1),kw(start2),kw(end2)) )
{ /* (STRING-GREATERP string1 string2 :start1 :end1 :start2 :end2),
     CLTL p. 302 */
  var stringarg arg1;
  var stringarg arg2;
  /* check arguments: */
  test_2_stringsym_limits(&arg1,&arg2);
  /* compare: */
  VALUES1(string_comp_ci(&arg1,&arg2)>0 ? fixnum(arg1.index) : NIL);
}

LISPFUN(string_not_greaterp,2,0,norest,key,4,
        (kw(start1),kw(end1),kw(start2),kw(end2)) )
{ /* (STRING-NOT-GREATERP string1 string2 :start1 :end1 :start2 :end2),
     CLTL p. 302 */
  var stringarg arg1;
  var stringarg arg2;
  /* check arguments: */
  test_2_stringsym_limits(&arg1,&arg2);
  /* compare: */
  VALUES1(string_comp_ci(&arg1,&arg2)<=0 ? fixnum(arg1.index) : NIL);
}

LISPFUN(string_not_lessp,2,0,norest,key,4,
        (kw(start1),kw(end1),kw(start2),kw(end2)) )
{ /* (STRING-NOT-LESSP string1 string2 :start1 :end1 :start2 :end2),
     CLTL p. 302 */
  var stringarg arg1;
  var stringarg arg2;
  /* check arguments: */
  test_2_stringsym_limits(&arg1,&arg2);
  /* compare: */
  VALUES1(string_comp_ci(&arg1,&arg2)>=0 ? fixnum(arg1.index) : NIL);
}

/* UP: searches a string string1 in another string string2
 > arg1: here are the addressed characters in string1
 > arg2: here are the addressed characters in string2
 > eqcomp: comparison function, &string_eqcomp or &string_eqcomp_ci
 < result: NIL if not found,
             position in string2 (as fixnum) if found.
 let eqcomp_fun_t be the type of such a comparison function: */
typedef bool (*eqcomp_fun_t) (object string1, uintL offset1,
                              object string2, uintL offset2, uintL len);
local object string_search (const stringarg* arg1, const stringarg* arg2,
                            eqcomp_fun_t eqcomp)
{
  var uintL len1 = arg1->len;
  var uintL len2 = arg2->len;
  if (len1 > len2) goto notfound; /* Only if len1<=len2, can string1 occur in string2. */
  /* loop:
     for i=0..len2-len1:
     compare string1 with the len1 characters at charptr2[i].
     Thereto, pass through loop len2-len1+1 times,
     growing charptr2 and start2. */
  {
    var object string1 = arg1->string;
    var uintL offset1 = arg1->offset + arg1->index;
    var object string2 = arg2->string;
    var uintL offset2 = arg2->offset + arg2->index;
    var uintL count;
    if (len1==0) goto found;
    dotimespL(count,len2-len1+1, {
      if ((*eqcomp)(string1,offset1,string2,offset2,len1)) /* compare */
        goto found;
      offset2++;
    });
    goto notfound;
   found: return fixnum(offset2 - arg2->offset);
  }
 notfound: return NIL;
}

LISPFUN(search_string_gleich,2,0,norest,key,4,
        (kw(start1),kw(end1),kw(start2),kw(end2)) )
{ /* (SYS::SEARCH-STRING= string1 string2 [:start1] [:end1] [:start2] [:end2])
   = (search string1 string2 :test #'char= [:start1] [:end1] [:start2] [:end2]) */

  var stringarg arg1;
  var stringarg arg2;
  /* check arguments: */
  test_2_stringsym_limits(&arg1,&arg2);
  /* search string1 in string2: */
  VALUES1(string_search(&arg1,&arg2,&string_eqcomp));
}

LISPFUN(search_string_equal,2,0,norest,key,4,
        (kw(start1),kw(end1),kw(start2),kw(end2)) )
{ /* (SYS::SEARCH-STRING-EQUAL string1 string2 [:start1] [:end1] [:start2] [:end2])
   = (search string1 string2 :test #'char-equal [:start1] [:end1] [:start2] [:end2]) */
  var stringarg arg1;
  var stringarg arg2;
  /* check arguments: */
  test_2_stringsym_limits(&arg1,&arg2);
  /* search string1 in string2: */
  VALUES1(string_search(&arg1,&arg2,&string_eqcomp_ci));
}

LISPFUN(make_string,1,0,norest,key,2, (kw(initial_element),kw(element_type)) )
/* (MAKE-STRING size :initial-element :element-type) */
{
  var uintL size;
  /* check size: */
  if (!posfixnump(STACK_2)) { /* size must be fixnum >= 0 */
    pushSTACK(STACK_2); /* TYPE-ERROR slot DATUM */
    pushSTACK(O(type_posfixnum)); /* TYPE-ERROR slot EXPECTED-TYPE */
    pushSTACK(STACK_(2+2)); pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,
           GETTEXT("~: the string length ~ should be nonnegative fixnum"));
  }
  size = posfixnum_to_L(STACK_2);
  /* check element-type: */
  if (boundp(STACK_0)) {
    var object eltype = STACK_0;
    if (!eq(eltype,S(character))) {
      /* Verify (SUBTYPEP eltype 'CHARACTER): */
      pushSTACK(eltype); pushSTACK(S(character)); funcall(S(subtypep),2);
      if (nullp(value1)) {
        pushSTACK(STACK_0); /* eltype */
        pushSTACK(S(character)); /* CHARACTER */
        pushSTACK(S(Kelement_type)); /* :ELEMENT-TYPE */
        pushSTACK(S(make_string));
        fehler(error,GETTEXT("~: ~ argument must be a subtype of ~, not ~"));
      }
    }
  }
  var object new_string;
  /* maybe fill with initial-element: */
  var object initial_element = STACK_1;
  if (!boundp(initial_element)) {
    new_string = allocate_string(size);
  } else {
    if (!charp(initial_element)) { /* must be a character */
      pushSTACK(initial_element); /* TYPE-ERROR slot DATUM */
      pushSTACK(S(character)); /* TYPE-ERROR slot EXPECTED-TYPE */
      pushSTACK(S(character)); pushSTACK(initial_element);
      pushSTACK(S(Kinitial_element)); pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,GETTEXT("~: ~ ~ should be of type ~"));
    } else {
      var chart ch = char_code(initial_element);
     #ifdef HAVE_SMALL_SSTRING
      var cint c = as_cint(ch);
      if (c < cint8_limit) {
        new_string = allocate_s8string(size);
        if (size !=0) {
          var cint8* pdata = TheS8string(new_string)->data;
          dotimespL(size,size, { *pdata++ = c; } );
        }
      } else if (c < cint16_limit) {
        new_string = allocate_s16string(size);
        if (size !=0) {
          var cint16* pdata = TheS16string(new_string)->data;
          dotimespL(size,size, { *pdata++ = c; } );
        }
      } else {
        new_string = allocate_s32string(size);
        if (size !=0) {
          var cint32* pdata = TheS32string(new_string)->data;
          dotimespL(size,size, { *pdata++ = c; } );
        }
      }
     #else
      new_string = allocate_string(size);
      if (size!=0) {
        var chart* charptr = &TheSstring(new_string)->data[0];
        dotimespL(size,size, { *charptr++ = ch; } );
      }
     #endif
    }
  }
  VALUES1(new_string); skipSTACK(3);
}

LISPFUNN(string_both_trim,3)
/* (SYS::STRING-BOTH-TRIM character-bag-left character-bag-right string)
 basic function for
 STRING-TRIM, STRING-LEFT-TRIM, STRING-RIGHT-TRIM, CLTL p. 302
 method:
 (let ((l (length string)))
   (do ((i 0 (1+ i)))
       (nil)
     (when (or (= i l)
               (not (find (char string i) character-bag-left)))
       (do ((j l (1- j)))
           (nil)
         (when (or (= i j)
                   (not (find (char string (1- j)) character-bag-right)))
           (return (if (and (= i 0) (= j l)) string
                       (substring string i j)))))))) */
{
  var object string = test_stringsymchar_arg(popSTACK()); /* convert argument into string */
  pushSTACK(string); /* and back into stack again */
  pushSTACK(fixnum(vector_length(string))); /* length as fixnum into the stack */
  pushSTACK(Fixnum_0); /* i := 0 */
  /* stack layout: bag-left, bag-right, string, l, i */
  loop {
    if (eq(STACK_0,STACK_1)) break; /* for i = l (both fixnums): loop done */
    /* determine (char string i) : */
    pushSTACK(STACK_2); pushSTACK(STACK_1); funcall(L(char),2);
    /* determine (find (char ...) character-bag-left) : */
    pushSTACK(value1); pushSTACK(STACK_5); funcall(L(find),2);
    if (nullp(value1)) break; /* char not in character-bag-left -> loop done */
    STACK_0 = fixnum_inc(STACK_0,1); /* i := (1+ i) */
  }
  pushSTACK(STACK_1); /* j := l */
  /* stack layout: bag-left, bag-right, string, l, i, j */
  loop {
    if (eq(STACK_0,STACK_1)) break; /* for j = i (both fixnums): loop done */
    /* determine (char string (1- j)) : */
    pushSTACK(STACK_3); pushSTACK(fixnum_inc(STACK_1,-1)); funcall(L(char),2);
    /* determine (find (char ...) character-bag-right) : */
    pushSTACK(value1); pushSTACK(STACK_5); funcall(L(find),2);
    if (nullp(value1)) break; /* char not in character-bag-right -> loop done */
    STACK_0 = fixnum_inc(STACK_0,-1); /* j := (1- j) */
  }
  /* stack layout: bag-left, bag-right, string, l, i, j
     throw away the characters of the string with index <i or >=j : */
  var object j = popSTACK();
  var object i = popSTACK();
  var object l = popSTACK();
  string = popSTACK();
  skipSTACK(2);
  if (eq(i,Fixnum_0) && eq(j,l)) {
    value1 = string; /* for i=0 and j=l, nothing to do, string as value */
  } else {
    /* copy sub part of the indices >=i, <j :
       (substring string i j) as value */
    pushSTACK(string); pushSTACK(i); pushSTACK(j); funcall(L(substring),3);
  }
  mv_count=1;
}

LISPFUN(string_width,1,0,norest,key,2, (kw(start),kw(end)) )
{
  var stringarg arg;
  var object string = test_string_limits_ro(&arg);
  var uintL width = 0;
  var uintL len = arg.len;
  if (len > 0) {
    SstringDispatch(string,X, {
      var const cintX* charptr = &((SstringX)TheVarobject(arg.string))->data[arg.offset];
      dotimespL(len,len, {
        width += char_width(as_chart(*charptr)); charptr++;
      });
    });
  }
  /* width <= 2*arg.len. */
  VALUES1(UL_to_I(width));
}

/* UP: converts the characters of a string piece into uppercase letters
 nstring_upcase(dv,offset,len);
 > object dv: the character storage vector
 > uintL offset: index of first affected character
 > uintL len: number of affected characters
 can trigger GC */
global void nstring_upcase (object dv, uintL offset, uintL len) {
 restart_it:
  if (len > 0)
    SstringCase(dv,{
      do {
        dv = sstring_store(dv,offset,up_case(as_chart(TheS8string(dv)->data[offset])));
        offset++;
        len--;
        if (Record_type(dv) == Rectype_reallocstring) { /* has it been reallocated? */
          dv = TheSiarray(dv)->data;
          goto restart_it;
        }
      } while (len > 0);
    },{
      do {
        dv = sstring_store(dv,offset,up_case(as_chart(TheS16string(dv)->data[offset])));
        offset++;
        len--;
        if (Record_type(dv) == Rectype_reallocstring) { /* has it been reallocated? */
          dv = TheSiarray(dv)->data;
          goto restart_it;
        }
      } while (len > 0);
    },{
      var cint32* charptr = &TheS32string(dv)->data[offset];
      dotimespL(len,len, {
        *charptr = as_cint(up_case(as_chart(*charptr))); charptr++;
      });
    });
}

/* UP: converts a string into uppercase letters
 string_upcase(string)
 > string: string
 < ergebnis: new normal-simple-string, in uppercase letters
 can trigger GC */
global object string_upcase (object string) {
  string = copy_string(string); /* copy and turn into a normal-simple-string */
  pushSTACK(string);
  nstring_upcase(string,0,Sstring_length(string)); /* convert */
  string = popSTACK();
  simple_array_to_storage(string);
  return string;
}

LISPFUN(nstring_upcase,1,0,norest,key,2, (kw(start),kw(end)) )
{ /* (NSTRING-UPCASE string :start :end), CLTL p. 304 */
  var stringarg arg;
  var object string = test_string_limits_rw(&arg);
  pushSTACK(string);
  nstring_upcase(arg.string,arg.offset+arg.index,arg.len);
  VALUES1(popSTACK());
}

LISPFUN(string_upcase,1,0,norest,key,2, (kw(start),kw(end)) )
{ /* (STRING-UPCASE string :start :end), CLTL p. 303 */
  var object string;
  var uintL offset;
  var uintL len;
  test_1_stringsym_limits(&string,&offset,&len);
  pushSTACK(string);
  nstring_upcase(string,offset,len);
  string = popSTACK();
  simple_array_to_storage(string);
  VALUES1(string);
}

/* UP: converts the characters of a string piece into lowercase letters
 nstring_downcase(dv,offset,len);
 > object dv: the character storage vector
 > uintL offset: index of first affected character
 > uintL len: number of affected characters
 can trigger GC */
global void nstring_downcase (object dv, uintL offset, uintL len) {
 restart_it:
  if (len > 0)
    SstringCase(dv,{
      do {
        dv = sstring_store(dv,offset,down_case(as_chart(TheS8string(dv)->data[offset])));
        offset++;
        len--;
        if (Record_type(dv) == Rectype_reallocstring) { /* has it been reallocated? */
          dv = TheSiarray(dv)->data;
          goto restart_it;
        }
      } while (len > 0);
    },{
      do {
        dv = sstring_store(dv,offset,down_case(as_chart(TheS16string(dv)->data[offset])));
        offset++;
        len--;
        if (Record_type(dv) == Rectype_reallocstring) { /* has it been reallocated? */
          dv = TheSiarray(dv)->data;
          goto restart_it;
        }
      } while (len > 0);
    },{
      var cint32* charptr = &TheS32string(dv)->data[offset];
      dotimespL(len,len, {
              *charptr = as_cint(down_case(as_chart(*charptr))); charptr++;
      });
    });
}

/* UP: converts a string into lowercase letters
 string_downcase(string)
 > string: string
 < result: new normal-simple-string, in lowercase letters
 can trigger GC */
global object string_downcase (object string) {
  string = copy_string(string); /* copy and turn into a normal-simple-string */
  pushSTACK(string);
  nstring_downcase(string,0,Sstring_length(string)); /* convert */
  string = popSTACK();
  simple_array_to_storage(string);
  return string;
}

LISPFUN(nstring_downcase,1,0,norest,key,2, (kw(start),kw(end)) )
{ /* (NSTRING-DOWNCASE string :start :end), CLTL p. 304 */
  var stringarg arg;
  var object string = test_string_limits_rw(&arg);
  pushSTACK(string);
  nstring_downcase(arg.string,arg.offset+arg.index,arg.len);
  VALUES1(popSTACK());
}

LISPFUN(string_downcase,1,0,norest,key,2, (kw(start),kw(end)) )
{ /* (STRING-DOWNCASE string :start :end), CLTL p. 303 */
  var object string;
  var uintL offset;
  var uintL len;
  test_1_stringsym_limits(&string,&offset,&len);
  pushSTACK(string);
  nstring_downcase(string,offset,len);
  string = popSTACK();
  simple_array_to_storage(string);
  VALUES1(string);
}

/* UP: converts the words of a string piece into words, that
 that start with a capital and continue with lowercase letters.
 nstring_capitalize(dv,offset,len);
 > object dv: the character storage vector
 > uintL offset: index of first affected character
 > uintL len: number of affected characters
 method:
  alternately, seach for beginning of a word (and do not convert)
  resp. search for end of word (and do convert).
 can trigger GC */
global void nstring_capitalize (object dv, uintL offset, uintL len) {
  var chart ch;
  SstringCase(dv,{
    /* Search the start of a word. */
   search_wordstart_8:
    while (len!=0) {
      ch = as_chart(TheS8string(dv)->data[offset]);
      if (alphanumericp(ch))
        goto wordstart_8;
      offset++; len--;
    }
    return; /* len = 0 -> string terminated */
    /* Found the start of a word. */
   wordstart_8:
    dv = sstring_store(dv,offset,up_case(ch));
    loop {
      offset++;
      if (Record_type(dv) == Rectype_reallocstring) { /* has it been reallocated? */
        dv = TheSiarray(dv)->data;
        SstringCase(dv, abort();, goto in_word_16;, goto in_word_32; );
      }
     in_word_8:
      if (--len==0)
        break;
      ch = as_chart(TheS8string(dv)->data[offset]);
      if (!alphanumericp(ch))
        goto search_wordstart_8;
      dv = sstring_store(dv,offset,down_case(ch));
    }
    return; /* len = 0 -> string terminated */
  },{
    /* Search the start of a word. */
   search_wordstart_16:
    while (len!=0) {
      ch = as_chart(TheS16string(dv)->data[offset]);
      if (alphanumericp(ch))
        goto wordstart_16;
      offset++; len--;
    }
    return; /* len = 0 -> string terminated */
    /* Found the start of a word. */
   wordstart_16:
    dv = sstring_store(dv,offset,up_case(ch));
    loop {
      offset++;
      if (Record_type(dv) == Rectype_reallocstring) { /* has it been reallocated? */
        dv = TheSiarray(dv)->data;
        SstringCase(dv, abort();, abort();, goto in_word_32; );
      }
    in_word_16:
      if (--len==0)
        break;
      ch = as_chart(TheS16string(dv)->data[offset]);
      if (!alphanumericp(ch))
        goto search_wordstart_16;
      dv = sstring_store(dv,offset,down_case(ch));
    }
    return; /* len = 0 -> string terminated */
  },{
    /* Search the start of a word. */
               search_wordstart_32:
    while (len!=0) {
      ch = as_chart(TheS32string(dv)->data[offset]);
      if (alphanumericp(ch))
        goto wordstart_32;
      offset++; len--;
    }
    return; /* len = 0 -> string terminated */
    /* Found the start of a word. */
   wordstart_32:
    TheS32string(dv)->data[offset] = as_cint(up_case(ch));
    loop {
      offset++;
    in_word_32:
      if (--len==0)
        break;
      ch = as_chart(TheS32string(dv)->data[offset]);
      if (!alphanumericp(ch))
        goto search_wordstart_32;
      TheS32string(dv)->data[offset] = as_cint(down_case(ch));
    }
    return; /* len = 0 -> string terminated */
  });
}

LISPFUN(nstring_capitalize,1,0,norest,key,2, (kw(start),kw(end)) )
{ /* (NSTRING-CAPITALIZE string :start :end), CLTL p. 304 */
  var stringarg arg;
  var object string = test_string_limits_rw(&arg);
  pushSTACK(string);
  nstring_capitalize(arg.string,arg.offset+arg.index,arg.len);
  VALUES1(popSTACK());
}

LISPFUN(string_capitalize,1,0,norest,key,2, (kw(start),kw(end)) )
{ /* (STRING-CAPITALIZE string :start :end), CLTL p. 303 */
  var object string;
  var uintL offset;
  var uintL len;
  test_1_stringsym_limits(&string,&offset,&len);
  pushSTACK(string);
  nstring_capitalize(string,offset,len);
  string = popSTACK();
  simple_array_to_storage(string);
  VALUES1(string);
}

LISPFUNN(string,1) /* (STRING object), CLTL p. 304 */
{
  VALUES1(test_stringsymchar_arg(popSTACK()));
}

LISPFUNN(name_char,1) /* (NAME-CHAR name), CLTL p. 243 */
{
  /* convert argument into a string, search character with this name: */
  VALUES1(name_char(test_stringsymchar_arg(popSTACK())));
}

/* UP: Returns a substring of a simple-string.
 subsstring(string,start,end)
 > object string: a simple-string
 > uintL start: start index
 > uintL end: end index
 with 0 <= start <= end <= Sstring_length(string)
 < object result: (subseq string start end),
           a freshly created normal-simple-string */
global object subsstring (object string, uintL start, uintL end) {
  var uintL count = end - start;
  pushSTACK(string);
  var object new_string = allocate_string(count);
  string = popSTACK();
  if (count > 0) {
   #ifdef UNICODE
    SstringCase(string,
      { copy_8bit_32bit(&TheS8string(string)->data[start],
                        &TheS32string(new_string)->data[0],count); },
      { copy_16bit_32bit(&TheS16string(string)->data[start],
                         &TheS32string(new_string)->data[0],count); },
      { copy_32bit_32bit(&TheS32string(string)->data[start],
                         &TheS32string(new_string)->data[0],count); });
   #else
    copy_8bit_8bit(&TheSstring(string)->data[start],
                   &TheSstring(new_string)->data[0],count);
   #endif
  }
  return new_string;
}

LISPFUN(substring,2,1,norest,nokey,0,NIL)
{ /* (SUBSTRING string start [end]) like SUBSEQ, but only for strings */
  var object string;
  var uintL len;
  var uintL start;
  var uintL end;
  /* check string/symbol-argument: */
  string = test_stringsymchar_arg(STACK_2);
  len = vector_length(string);
  /* now, len is the length (<2^oint_data_len).
     check :START-argument:
     start := Index STACK_1, default value 0, must be <=len: */
  test_index(STACK_1,start=,1,0,<=,len,S(Kstart));
  /* start is now the value of the :START-argument.
     check :end-argument:
     end := Index STACK_0, default value len, must be <=len: */
  test_index(STACK_0,end=,2,len,<=,len,S(Kend));
  /* end is now the value of the :END-argument.
     compare :START and :END arguments: */
  if (start > end) {
    pushSTACK(STACK_0); /* :END-Index */
    pushSTACK(STACK_2); /* :START-Index */
    pushSTACK(TheSubr(subr_self)->name);
    fehler(error,GETTEXT("~: :start-index ~ must not be greater than :end-index ~"));
  }
  skipSTACK(3);
  /* extract substring: */
  pushSTACK(string); /* save old string */
  var uintL count = end-start; /* number of characters to be copied */
  var object new_string = allocate_string(count); /* new string */
  string = popSTACK(); /* old string */
  if (count > 0) {
    var uintL len; /* again the length of the old string */
    var uintL offset;
    string = unpack_string_ro(string,&len,&offset);
   #ifdef UNICODE
    SstringCase(string,
      { copy_8bit_32bit(&TheS8string(string)->data[offset+start],
                        &TheS32string(new_string)->data[0],count); },
      { copy_16bit_32bit(&TheS16string(string)->data[offset+start],
                         &TheS32string(new_string)->data[0],count); },
      { copy_32bit_32bit(&TheS32string(string)->data[offset+start],
                         &TheS32string(new_string)->data[0],count); });
   #else
    copy_8bit_8bit(&TheSstring(string)->data[offset+start],
                   &TheSstring(new_string)->data[0],count);
   #endif
  }
  VALUES1(new_string);
}

/* UP: concatenates several strings.
 string_concat(argcount)
 > uintC argcount: number of arguments
 > on the STACK: the arguments (should be strings)
 > subr_self: caller (a SUBR) (unnecessary, if all arguments are strings)
 < result: total string, freshly created
 < STACK: cleaned up
 can trigger GC */
global object string_concat (uintC argcount) {
  var object* args_pointer = (args_end_pointer STACKop argcount);
  /* args_pointer = pointer to the arguments
     check, if they are all strings, and add the lengths: */
  var uintL total_length = 0;
  if (argcount > 0) {
    var object* argptr = args_pointer;
    var uintC count;
    dotimespC(count,argcount, {
      var object arg = NEXT(argptr); /* next argument */
      if (!stringp(arg))
        fehler_string(arg);
      total_length += vector_length(arg);
    });
  }
  /* total_length is now the total length. */
  var object new_string = allocate_string(total_length); /* new string */
  if (argcount > 0) {
    var cint32* charptr2 = &TheS32string(new_string)->data[0];
    var object* argptr = args_pointer;
    do {
      var object arg = NEXT(argptr); /* next argument-string */
      var uintL len; /* its length */
      var uintL offset;
      var object string = unpack_string_ro(arg,&len,&offset);
      if (len > 0) { /* copy len characters from string to charptr2: */
       #ifdef UNICODE
        SstringCase(string,
          { copy_8bit_32bit(&TheS8string(string)->data[offset],
                            charptr2,len); },
          { copy_16bit_32bit(&TheS16string(string)->data[offset],
                             charptr2,len); },
          { copy_32bit_32bit(&TheS32string(string)->data[offset],
                             charptr2,len); });
       #else
        copy_8bit_8bit(&TheSstring(string)->data[offset],charptr2,len);
       #endif
        charptr2 += len;
      }
    } while (--argcount > 0);
  }
  set_args_end_pointer(args_pointer); /* clean up STACK */
  return new_string;
}

LISPFUN(string_concat,0,0,rest,nokey,0,NIL)
{ /* (STRING-CONCAT {string})
     creates a string by concatenating the arguments */
  VALUES1(string_concat(argcount));
}
