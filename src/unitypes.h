/* Elementary types for the GNU UniString library.
   Copyright (C) 2002 Free Software Foundation, Inc.

   This program is free software; you can redistribute it and/or modify it
   under the terms of the GNU Library General Public License as published
   by the Free Software Foundation; either version 2, or (at your option)
   any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Library General Public License for more details.

   You should have received a copy of the GNU Library General Public
   License along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307,
   USA.  */

#ifndef _UNITYPES_H
#define _UNITYPES_H

/* Get uint8_t, uint16_t, uint32_t.  */
#ifdef HAVE_STDINT_H
#  include <stdint.h>
#else
#  include "stdint.h"
#endif

/* Type representing a Unicode character.  */
typedef uint32_t ucs4_t;

/* Common macro.  */
#ifndef PARAMS
# if __STDC__ || defined __GNUC__ || defined __SUNPRO_C || defined __cplusplus || __PROTOTYPES
#  define PARAMS(Args) Args
# else
#  define PARAMS(Args) ()
# endif
#endif

/* Common macro, to avoid compilation errors when we use a GCC extension and
   GCC is run in pedantic mode.  */
#if __GNUC__ > 2 || (__GNUC__ == 2 && __GNUC_MINOR__ >= 8)
# define UC_GNUC_EXTENSION __extension__
#else
# define UC_GNUC_EXTENSION
#endif

#endif /* _UNITYPES_H */
