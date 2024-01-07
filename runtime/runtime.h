#ifndef __LAMA_RUNTIME__
#define __LAMA_RUNTIME__

#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <limits.h>
#include <regex.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <time.h>

#define WORD_SIZE (CHAR_BIT * sizeof(int))

void failure (char *s, ...);

extern void *Belem (void *p, int i);
extern void *Bsta (void *v, int i, void *x);
extern void *Bstring (void *);
extern int   LtagHash (char *s);

extern int   Llength (void *p);
extern void *Lstring (void *p);

extern int Lread ();
extern int Lwrite (int n);

extern int Btag (void *d, int t, int n);
extern int Barray_patt (void *d, int n);
extern int Bstring_patt (void *x, void *y);
extern int Bclosure_tag_patt (void *x);
extern int Bboxed_patt (void *x);
extern int Bunboxed_patt (void *x);
extern int Barray_tag_patt (void *x);
extern int Bstring_tag_patt (void *x);
extern int Bsexp_tag_patt (void *x);

#endif
