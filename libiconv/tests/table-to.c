/* Copyright (C) 2000 Free Software Foundation, Inc.
   This file is part of the GNU ICONV Library.

   The GNU ICONV Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Library General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   The GNU ICONV Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Library General Public License for more details.

   You should have received a copy of the GNU Library General Public
   License along with the GNU ICONV Library; see the file COPYING.LIB.  If not,
   write to the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
   Boston, MA 02111-1307, USA.  */

/* Create a table from Unicode to CHARSET. */

#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <libiconv.h>
#include <errno.h>

int main (int argc, char* argv[])
{
  const char* charset;
  iconv_t cd;

  if (argc != 2) {
    fprintf(stderr,"Usage: table-to charset\n");
    exit(1);
  }
  charset = argv[1];

  cd = iconv_open(charset,"UCS-2-INTERNAL");
  if (cd == (iconv_t)(-1)) {
    perror("iconv_open");
    exit(1);
  }

  {
    unsigned int i;
    unsigned char buf[10];
    for (i = 0; i < 0x10000; i++) {
      unsigned short in = i;
      const char* inbuf = (const char*) &in;
      size_t inbytesleft = sizeof(unsigned short);
      char* outbuf = (char*)buf;
      size_t outbytesleft = sizeof(buf);
      size_t result = iconv(cd,&inbuf,&inbytesleft,&outbuf,&outbytesleft);
      if (result == (size_t)(-1)) {
        if (errno != EILSEQ) {
          int saved_errno = errno;
          fprintf(stderr,"0x%02X: iconv error: ",i);
          errno = saved_errno;
          perror("");
          exit(1);
        }
      } else if (result == 0) /* ignore conversions with transliteration */ {
        unsigned int j, jmax;
        if (inbytesleft != 0 || outbytesleft == sizeof(buf)) {
          fprintf(stderr,"0x%02X: inbytes = %ld, outbytes = %ld\n",i,(long)(sizeof(unsigned short)-inbytesleft),(long)(sizeof(buf)-outbytesleft));
          exit(1);
        }
        jmax = sizeof(buf) - outbytesleft;
        printf("0x");
        for (j = 0; j < jmax; j++)
          printf("%02X",buf[j]);
        printf("\t0x%04X\n",i);
      }
    }
  }

  if (iconv_close(cd) < 0) {
    perror("iconv_close");
    exit(1);
  }

  if (ferror(stdin) || ferror(stdout)) {
    fprintf(stderr,"I/O error\n");
    exit(1);
  }

  exit(0);
}
