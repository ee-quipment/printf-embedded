/******************************************************************************

    (c) Copyright 2018 ee-quipment.com

    printf-emb.h - A printf library targeted at embedded environments

    int  snprintf(char *s, size_t n, const char *fmt, ...)
    int  vsnprintf(char *s, size_t n, const char *fmt, va_list ap)

    int  saprintf(emb_printf_fn_alloc_t fn_alloc, char **s, const char *fmt, ...)
    int  vsaprintf(emb_printf_fn_alloc_t fn_alloc, char **s, const char *fmt, va_list ap)

    snprintf and vsnprintf are the equivalent of the same-named functions
    in the standard library with the exceptions and extensions noted below.

    saprintf and vsaprintf are equivalent to snprintf and vsnprintf except
    that they will compute the output string length and allocate a buffer
    using the supplied fn_alloc. The caller is responsible for freeing
    any memory allocated by fn_alloc.

    With saprintf and vsaprintf, if memory cannot be allocated that will hold
    the entire string the the buffer pointer *s will be set to NULL. The
    caller must check that *s is valid.

    What IS supported:
        All integer conversion specifiers: d, i, o, u, x, and X.
        The unsigned char specifier: c
        The pointer specifier: p.
        The string specifier: s.
        The % escape specifier: %.

        Length modifiers: hh, h, l, ll, z.

    What is NOT supported:
        Floating point conversion specifiers: e, E (see below), f, F, g, G, a, A.
        The number-of-characters specifier: n.
        Wide characters.
        Any other specifier not explicitly supported.

    Modifications / Extensions:
        The conversion specifiers e, E are supported, but for integer
        arguments in place of double. A length modifier may be associated
        with the argument.

        For e, the output is the same as if the argument as a double of the
        same value as the integer argument, where there is one digit to the
        left of the decimal point. The precision specifies the number of
        digits to the right of the decimal point.

        For E, the output is in engineering notation where there may be 1,
        2, or 3 digits to the left of the decimal point, and the exponent
        is always a multiple of three. The precision specifies the number
        of significant digits. If the precision is zero it is
        taken to be one.  A decimal point appears only if it is followed
        by at least one digit.

        Passing a double as an argument to an e, E specifier will result
        in undefined and most likely bad behavior.

 *****************************************************************************/


#ifndef _printf_emb_H_
#define _printf_emb_H_

#include <stddef.h>
#include <stdarg.h>

#pragma GCC diagnostic ignored "-Wformat"   // stop complaints about redefining e, E


typedef void * (*emb_printf_fn_alloc_t)(size_t);


int  snprintf(char *s, size_t n, const char *fmt, ...);
int  vsnprintf(char *s, size_t n, const char *fmt, va_list ap);

int  saprintf(emb_printf_fn_alloc_t fn_alloc, char **s, const char *fmt, ...);
int  vsaprintf(emb_printf_fn_alloc_t fn_alloc, char **s, const char *fmt, va_list ap);


#endif  /* _printf_emb_H_ */


