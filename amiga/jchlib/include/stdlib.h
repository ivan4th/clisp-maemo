/* Tiny GCC Library
 * stdlib.h
 * J�rg H�hle, 11-Jun-96
 */

#ifndef _STDLIB_H_
#define _STDLIB_H_

typedef unsigned long size_t;
extern void* malloc (size_t);
extern void free (void*);

typedef void __exit_t (int);
extern volatile __exit_t exit;

extern char *getenv (const char *);

#endif /* _STDLIB_H_ */
