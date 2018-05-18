/******************************************************************************

    (c) Copyright 2018 ee-quipment.com

    printf-emb.c - printf type functions for an embedded environment.

    int  snprintf(char *s, size_t n, const char *fmt, ...)
    int  saprintf(char *s, size_t n, const char *fmt, ...)
    void sfprintf(char *s)

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


    For performance reasons no division operations (including modulo, etc) are performed.

    This implementation is recursive, and is called for every conversion
    specifier and string literal in the format string. For example, the
    format string "There are %d months and %d days left this year" will result
    in xprintf() being called 5 times. The recursion depth can be limited
    by the MACRO RECURSION_LIMIT. If the recursion limit is reached
    then the return string will be truncated at that point.

    The recursive implementation analyzes the entire string and determines
    the total length before writing to the output buffer. This allows buffer
    memory to be allocated after the string length is known.

    The implementation is targeted at a 32-bit ARM architecture that supports
    long long (64 bit) data types, has a 32 x 32 = 32 multiplier and treats
    int and long as the same data type.


 *****************************************************************************/


/*
 * Always optimize this file.
 */
#pragma GCC optimize ("O3")


#include <stddef.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include "printf-emb.h"

/*
 * Design by contract assertion macros are included as sanity checks in
 * the function calls. To activate them supply an appropriate assert()
 * function for your system.
 */
#define assert(test)
#define REQUIRE(test)     assert(test)
#define ENSURE(test)      assert(test)


#define RECURSION_LIMIT               14

#define ARG_OCT_DIGITS_MAX            22    // %llo 64-bit octal
#define ARG_DEC_DIGITS_MAX            20    // %lld 64-bit signed decimal including
#define ARG_STR_LEN_MAX              (ARG_OCT_DIGITS_MAX + 1)   // including '0' prefix


/*
 * One global_variable_t is allocated per printf() call.
 */
typedef struct {
    char *                output_buf;
    int                   output_buf_size;
    int                   output_str_len;
    int                   arg_str_pos;
    int                   recursion_depth;
    emb_printf_fn_alloc_t alloc;
    va_list               ap;
} global_variable_t;

/*
 * One arg_token_t variable is allocated (on the stack) per token found
 * in the format string, where a token is a converted argument or a
 * string segment.
 */
typedef struct {
    int16_t field_width;
    int16_t precision;
    int16_t arg_str_len;
    union {
        struct {
            uint8_t alt_form          :1;
            uint8_t arg_signed        :1;
            uint8_t sign_indicator    :1;
            uint8_t space_before_pos  :1;
            uint8_t left_justify      :1;
            uint8_t zero_padded       :1;
            uint8_t string_const      :1;
            uint8_t caps              :1;
        } flag;
        uint8_t flags;
    };
    union {
        long long          arg_LL;
        unsigned long long arg_ULL;
    };
    union {
        char          arg_as_str[ARG_STR_LEN_MAX];
        const char *  p_fixed_str;
    };
} arg_token_t;


#define PRECISION_UNDEFINED   -1
#define PRECISION_MAX         INT16_MAX
typedef enum { CONV_DECIMAL=0, CONV_OCTAL, CONV_HEX, CONV_EXP, CONV_CHAR, CONV_STRING, CONV_PERCENT } conversion_type_t;
typedef enum { ARG_CHAR=0, ARG_SHORT, ARG_INT, ARG_LONG, ARG_LONG_LONG, ARG_CHAR_POINTER, ARG_NUM_TYPES } arg_type_t;

#define SIZE_T_TYPE ((sizeof(size_t) == sizeof(unsigned int  )) ? ARG_INT  :         \
                     (sizeof(size_t) == sizeof(unsigned long )) ? ARG_LONG : ARG_LONG_LONG)


/*
 * Private functions
 */
static uint16_t _udiv_by_10(uint16_t *dividend);
static void     _getVararg(global_variable_t *p_g_var, arg_token_t *token, arg_type_t arg_type);
static void     _buildOutputString(global_variable_t *p_g_var, const arg_token_t *token);
static void     _parse(global_variable_t * p_g_var, const char *fmt);
static void     _flags(const char **p_fmt, arg_token_t *token);
static void     _fieldWidth(global_variable_t *p_g_var, const char **p_fmt, arg_token_t *token);
static void     _precision(global_variable_t *p_g_var, const char **p_fmt, arg_token_t *token);
static void     _lengthModifier(const char **p_fmt, const arg_token_t *token, arg_type_t *arg_type);
static void     _conversionSpecifier(const char **p_fmt, arg_token_t *token, conversion_type_t *conv_type);
static void     _convertDec(arg_token_t *token);
static void     _convertBin(arg_token_t *token, conversion_type_t radix);
static void     _convertExp(arg_token_t *token);
static void     _convertChar(arg_token_t *token);
static void     _convertString(arg_token_t *token);



/******************************************************************************
 *
 * Write at most n bytes (including the terminating '0' to s. Return the
 * number of characters printed, excluding the terminating nul. The
 * return value will be the same regardless of the value of n.
 *
 * Values of 0 for n and NULL for s are permitted. No output will be generated.
 *
 *****************************************************************************/
int  snprintf(char *s, size_t n, const char *fmt, ...) {
    int     n_chars;
    va_list ap;

    REQUIRE (fmt);

    va_start(ap, fmt);
    n_chars = vsnprintf(s, n, fmt, ap);
    va_end(ap);
    return (n_chars);
}


/******************************************************************************
 *
 * vsnprintf() is equivalent to snprintf(), except that it is called with
 * a va_list instead of a variable number of arguments.
 *
 * This function does not call the va_end macro. Because it invokes the
 * va_arg macro, the value of ap is undefined after the call.
 *
 *****************************************************************************/
int  vsnprintf(char *s, size_t n, const char *fmt, va_list ap) {
    global_variable_t  g_var;

    REQUIRE (fmt);

    g_var.output_buf      = s;
    g_var.output_buf_size = (int) n;
    g_var.output_str_len  = 0;
    g_var.recursion_depth = 0;
    g_var.ap              = ap;
    g_var.alloc           = NULL;

    if (*fmt) {
        _parse(&g_var, fmt);
    }
    return (g_var.output_str_len);
}


/******************************************************************************
 *
 * Determine the length of the output string and call fn_alloc() to allocate
 * a buffer of that size. Assign the buffer pointer to *s. If a buffer
 * cannot be allocated that will hold the entire output string then
 * set **s to NULL.
 *
 * The caller is responsible for freeing any memory allocated by fn_alloc.
 *
 *****************************************************************************/
int  saprintf(emb_printf_fn_alloc_t fn_alloc, char **s, const char *fmt, ...) {
    int     n_chars;
    va_list ap;

    REQUIRE (s);
    REQUIRE (fmt);

    va_start(ap, fmt);
    n_chars = vsaprintf(fn_alloc, s, fmt, ap);
    va_end(ap);
    return (n_chars);
}


/******************************************************************************
 *
 * vsaprintf() is equivalent to saprintf(), except that it is called with
 * a va_list instead of a variable number of arguments.
 *
 * This function does not call the va_end macro. Because it invokes the
 * va_arg macro, the value of ap is undefined after the call.
 *
 *****************************************************************************/
int vsaprintf(emb_printf_fn_alloc_t fn_alloc, char **s, const char *fmt, va_list ap) {
    global_variable_t  g_var;

    REQUIRE (s);
    REQUIRE (fmt);

    g_var.output_buf      = (char *) s;
    g_var.output_buf_size = INT32_MAX;  // buf not allocated yet, assume it's plenty big
    g_var.output_str_len  = 0;
    g_var.recursion_depth = 0;
    g_var.ap              = ap;
    g_var.alloc           = fn_alloc;

    if (*fmt) {
        _parse(&g_var, fmt);
    }
    return (g_var.output_str_len);
}


/******************************************************************************
 *
 * Unsigned integer divide by 10 using 16 x 16 = 32 multiplication. Modify the
 * dividend in place (dividend = INT(dividend / 10) and return the remainder.
 *
 *****************************************************************************/
static uint16_t _udiv_by_10(uint16_t *dividend) {
    const uint16_t recip_0pt8 = 0xcccd;
    uint32_t q;
    uint32_t d = (uint32_t) *dividend;

    /* divide the dividend by 10 in-place and return the remainder */
    q  = (d * recip_0pt8) >> 19;
    *dividend = (uint16_t) q;
    return ((uint16_t) (d - (10 * q)));
}


/******************************************************************************
 *
 * Retrieve an argument from the variable argument list. The ... operator
 * promotes all smaller parameters to int.
 *
 * If the argument is long or int, it is promoted (and sign extended) into the
 * long long argument.
 *
 * If the argument is a pointer to a string, it is promoted to unsigned
 * long long and stored in token->arg_ULL which is assumed large enough to
 * hold a pointer.
 *
 *****************************************************************************/
static void _getVararg(global_variable_t *p_g_var, arg_token_t *token, arg_type_t arg_type) {

    REQUIRE (p_g_var);
    REQUIRE (token);
    if (arg_type == ARG_LONG_LONG) {
        token->arg_LL = va_arg(p_g_var->ap, long long);   // works for signed or unsigned
    }
    else if (arg_type == ARG_CHAR_POINTER) {
        token->arg_ULL = (unsigned long long) ((unsigned long) va_arg(p_g_var->ap, char *));
    }
    else {
        if (token->flag.arg_signed) {
            if (arg_type == ARG_LONG) { token->arg_LL = (long long) va_arg(p_g_var->ap, long); }
            else {                      token->arg_LL = (long long) va_arg(p_g_var->ap, int);  }
        }
        else {
            if (arg_type == ARG_LONG) { token->arg_ULL = (unsigned long long) va_arg(p_g_var->ap, unsigned long); }
            else {                      token->arg_ULL = (unsigned long long) va_arg(p_g_var->ap, unsigned int);  }
        }
    }
}


/******************************************************************************
 *
 * Build up the final output string from individual token argument strings.
 * The string is built right to left as the procedure calls are unwound.
 * Truncate the string if the output buffer is insufficiently large.
 *
 * sob = pointer to location in output buffer to write token argument string
 * eob = pointer to location of last char written to output buffer
 *
 * The pointers sob and eob may be out of range of the output buffer, but they
 * are tested before dereferencing.
 *
 *****************************************************************************/
static void _buildOutputString(global_variable_t *p_g_var, const arg_token_t *token) {
    char *       sob;
    char *       eob;
    const char * arg_str;
    const char   pad_char = (token->flag.zero_padded) ? '0' : ' ';
    int          i;

    REQUIRE (p_g_var);
    REQUIRE (token);

    /*
     * End of buffer is either the start of the previous token string or
     * the terminating nul in the output buffer.
     */
    eob = &(p_g_var->output_buf[p_g_var->arg_str_pos]);
    if (&(p_g_var->output_buf[p_g_var->output_buf_size-1]) < eob) {
        eob = &(p_g_var->output_buf[p_g_var->output_buf_size-1]);
    }

    // decrement position index and initialize pointer to the start of where this token argument string will be written
    p_g_var->arg_str_pos -= (token->arg_str_len > token->field_width) ? token->arg_str_len : token->field_width;
    ENSURE (p_g_var->arg_str_pos >= 0); // shouldn't ever exceed lower bound of output buffer
    sob = &(p_g_var->output_buf[p_g_var->arg_str_pos]);

    if (token->flag.string_const) { arg_str = token->p_fixed_str; }
    else                          { arg_str = token->arg_as_str; }

    /*
     * If the string is right justified, left-pad if needed. If the pad char
     * is '0', pad between the minus sign (if present) and the number.
     * Truncate the string if it does not fit in the output buffer.
     */
    if (!token->flag.left_justify) {
        if (((token->field_width - token->arg_str_len) > 0) && (pad_char == '0') && (arg_str[0] == '-')) {
            *sob++ = *arg_str++;
        }
        for (i=0; i<(token->field_width - token->arg_str_len) && (sob < eob); ++i) {
            *sob++ = pad_char;
        }
    }

    // output token argument string, truncate if needed
    for (i=0; i<token->arg_str_len && (sob < eob); ++i) {
        *sob++ = *arg_str++;
    }

    // pad the remaining field with spaces
    while (sob < eob) { *sob++ = ' '; }
}


/******************************************************************************
 *
 * Parse the format string into tokens. A single token is generated every
 * time _parse() is called, whenever there is a string literal or a conversion
 * specifier.
 *
 *****************************************************************************/
static void _parse(global_variable_t *p_g_var, const char *fmt) {
    arg_token_t       token;
    arg_type_t        arg_type;
    conversion_type_t conv_type;

    REQUIRE (p_g_var);
    REQUIRE (fmt);

    token.flags = 0;
    ++p_g_var->recursion_depth;

    /* Fixed string to be copied to output */
    if (*fmt != '%') {
        token.flag.string_const = 1;
        token.p_fixed_str = fmt;
        token.field_width = 0;
        token.precision   = PRECISION_MAX;
        token.arg_str_len = 0;
        while (*fmt && (*fmt != '%')) {
            ++token.arg_str_len;
            ++p_g_var->output_str_len;
            ++fmt;
        }
    }

    /* Parse conversion specification % */
    else {
        _flags(&fmt, &token);
        _fieldWidth(p_g_var, &fmt, &token);
        _precision(p_g_var, &fmt, &token);
        _lengthModifier(&fmt, &token, &arg_type);
        _conversionSpecifier(&fmt, &token, &conv_type);

        // reconcile conflicting flags
        if (token.flag.zero_padded      && token.flag.left_justify)    { token.flag.zero_padded      = 0; }
        if (token.flag.space_before_pos && token.flag.sign_indicator)  { token.flag.space_before_pos = 0; }

        // convert the argument
        switch (conv_type) {
            case CONV_DECIMAL:
                _getVararg(p_g_var, &token, arg_type);
                _convertDec(&token);
                break;
            case CONV_OCTAL:
            case CONV_HEX:
                _getVararg(p_g_var, &token, arg_type);
                _convertBin(&token, conv_type);
                break;
            case CONV_EXP:
                _getVararg(p_g_var, &token, arg_type);
                _convertExp(&token);
                break;
            case CONV_CHAR:
                _getVararg(p_g_var, &token, arg_type);
                _convertChar(&token);
                break;
            case CONV_STRING:
                _getVararg(p_g_var, &token, ARG_CHAR_POINTER);
                _convertString(&token);
                break;
            case CONV_PERCENT:
                token.arg_str_len = 1;
                token.arg_as_str[0] = '%';
                break;
            default:
                assert (false);
        }

        // keep a running total of the length of the output string
        p_g_var->output_str_len += (token.arg_str_len > token.field_width) ? token.arg_str_len : token.field_width;
    }

    /*
     * Handle next portion of the format string by recursing, unless:
     *    The end of the format string has been reached, or
     *    The recursion depth limit has been reached, or
     *    The number of characters generated (incl trailing nul) has filled the output buffer
     */
    if (*fmt && (p_g_var->recursion_depth < RECURSION_LIMIT) && ((p_g_var->output_str_len + 1) <= p_g_var->output_buf_size)) {
        _parse(p_g_var, fmt);
    }

    // Recursion ended, prepare to unwind procedure calls. Allocate memory if needed
    else {
        if (p_g_var->alloc) {
            *((char **) p_g_var->output_buf) = p_g_var->alloc((size_t) (p_g_var->output_str_len + 1)); // set user's pointer to output string
            // dereference buf pointer and set size to look like a call to snprintf
            p_g_var->output_buf = *((char **) p_g_var->output_buf);
            p_g_var->output_buf_size = p_g_var->output_str_len + 1;
        }

        // return to caller if no output buffer is allocated
        if (p_g_var->output_buf == NULL) { return; }

        /*
         * Maintain an index to where the next token string should be put
         * in the output buffer. The pointer may exceed the bounds of the
         * buffer, indicating that the token string must be truncated.
         *
         * Upon entry the pointer will point to the last char written.
         */
        p_g_var->arg_str_pos = p_g_var->output_str_len; // terminating null goes here if buffer large enough
        if (p_g_var->arg_str_pos <= (p_g_var->output_buf_size - 1)) {
            p_g_var->output_buf[p_g_var->arg_str_pos] = '\0';
        }
        else { // otherwise terminate at the last buffer location
            p_g_var->output_buf[p_g_var->output_buf_size-1] = '\0';
        }
    }

    // as _parse() unwinds it returns here to construct string unless there is no buffer allocated
    if (p_g_var->output_buf != NULL) {
        _buildOutputString(p_g_var, &token);
    }
}


/******************************************************************************
 *
 * Parse the flag characters and set the token flags. *fmt == '%' on entry
 *
 *****************************************************************************/
static void _flags(const char **p_fmt, arg_token_t *token) {
    bool exit  = false;

    REQUIRE (token);
    REQUIRE (p_fmt);
    REQUIRE (*p_fmt);
    REQUIRE (**p_fmt == '%');

    do {
        ++*p_fmt;
        switch (**p_fmt) {
            case '#':
                token->flag.alt_form = 1;
                break;
            case '0':
                token->flag.zero_padded = 1;
                break;
            case '-':
                token->flag.left_justify = 1;
                break;
            case ' ':
                token->flag.space_before_pos = 1;
                break;
            case '+':
                token->flag.sign_indicator = 1;
                break;
            default:
                exit = true;
                break;
        }
    } while (!exit);
}


/******************************************************************************
 *
 * Parse the field width. Zero cannot be the first field width numeral or it
 * would have been interpreted as a flag. *fmt points to the (potential) first
 * numeral of the field width on entry.
 *
 *****************************************************************************/
static void _fieldWidth(global_variable_t * p_g_var, const char **p_fmt, arg_token_t *token) {
    int          fw  = 0;

    REQUIRE (p_g_var);
    REQUIRE (p_fmt);
    REQUIRE (*p_fmt);
    REQUIRE (token);
    if (**p_fmt == '*') {
        _getVararg(p_g_var, token, ARG_INT);
        fw = (int) token->arg_LL;
        if (fw < 0) { // a neg field width is taken as a '-' flag followed by a positive field width.
            token->flag.left_justify = 1;
            fw = -fw;
        }
        ++*p_fmt;
    }
    else {
        while ((**p_fmt >= '0') && **p_fmt <= '9') {
            fw *= 10;
            fw += **p_fmt - '0';
            ++*p_fmt;
        }
    }
    token->field_width = (int16_t) fw;
}


/******************************************************************************
 *
 * Parse the precision. *fmt points to the precision field
 * delimiter '.' (if present) on entry.
 *
 *****************************************************************************/
static void _precision(global_variable_t * p_g_var, const char **p_fmt, arg_token_t *token) {
    int16_t prec;
    bool    neg = false;

    REQUIRE (p_g_var);
    REQUIRE (p_fmt);
    REQUIRE (*p_fmt);
    REQUIRE (token);
    if (**p_fmt == '.') {
        prec = 0;
        ++*p_fmt;
        if (**p_fmt == '*') {
            _getVararg(p_g_var, token, ARG_INT);
            prec = (int16_t) token->arg_LL;
            if (prec < 0) {
                prec = PRECISION_UNDEFINED; // negative precision not allowed
            }
            ++*p_fmt;
        }
        else {
            if (**p_fmt == '-') {
                neg = true;
                ++*p_fmt;
            }
            while ((**p_fmt >= '0') && **p_fmt <= '9') {
                prec *= 10;
                prec += **p_fmt - '0';
                ++*p_fmt;
            }
            if (neg) {
                prec = PRECISION_UNDEFINED; // negative precision not allowed
            }
        }
    }
    else {
        prec = PRECISION_UNDEFINED;
    }
    token->precision = prec;
}


/******************************************************************************
 *
 * Parse the length modifier and set the arg_type.  *fmt points to the first
 * character of the modifier (if present) on entry.
 *
 *****************************************************************************/
static void _lengthModifier(const char **p_fmt, const arg_token_t *token, arg_type_t *arg_type) {

    REQUIRE (p_fmt);
    REQUIRE (*p_fmt);
    REQUIRE (token);
    REQUIRE (arg_type);

    *arg_type = ARG_INT;

    if (**p_fmt == 'h') {           //  'h'
        *arg_type = ARG_SHORT;
        ++*p_fmt;
        if (**p_fmt == 'h') {       //  'hh'
            *arg_type = ARG_CHAR;
            ++*p_fmt;
        }
    }
    else if (**p_fmt == 'l') {
        *arg_type = ARG_LONG;       //  'l'
        ++*p_fmt;
        if (**p_fmt == 'l') {       //  'll'
            *arg_type = ARG_LONG_LONG;
            ++*p_fmt;
        }
    }
    else if (**p_fmt == 'z') {
        *arg_type = SIZE_T_TYPE;
        ++*p_fmt;
    }
}


/******************************************************************************
 *
 * Parse the conversion specifier and set the flag.arg_signed flag and the conversion
 * type.  *fmt points to the conversion specifier on entry.
 *
 *****************************************************************************/
static void _conversionSpecifier(const char **p_fmt, arg_token_t *token, conversion_type_t *conv_type) {

    REQUIRE (p_fmt);
    REQUIRE (*p_fmt);
    REQUIRE (token);
    REQUIRE (conv_type);

    if ((**p_fmt == 'd') || (**p_fmt == 'i')) {
        *conv_type = CONV_DECIMAL;
        token->flag.arg_signed = 1;
    }
    else if (**p_fmt == 'c') {
        *conv_type = CONV_CHAR;
    }
    else if (**p_fmt == 's') {
        *conv_type = CONV_STRING;
        if (token->precision == PRECISION_UNDEFINED) {
            token->precision = PRECISION_MAX;
        }
    }
    else if (**p_fmt == 'u') {
        *conv_type = CONV_DECIMAL;
    }
    else if (**p_fmt == 'o') {
        *conv_type = CONV_OCTAL;
    }
    else if ((**p_fmt == 'X') || (**p_fmt == 'x')) {
        *conv_type = CONV_HEX;
        if (**p_fmt == 'X') { token->flag.caps = 1; }
    }
    else if (**p_fmt == 'p') {
        *conv_type = CONV_HEX;
        token->flag.alt_form = 1;
    }
    else if ((**p_fmt == 'e') || (**p_fmt == 'E')) {
        *conv_type = CONV_EXP;
        token->flag.arg_signed = 1;
        if (token->precision == PRECISION_UNDEFINED) { token->precision = 6; }
        if (**p_fmt == 'E') { token->flag.caps = 1; }
    }
    else { // **p_fmt == '%' or any unrecognized conversion specifier
        *conv_type = CONV_PERCENT;
    }

    /*
     * If a precision is given with a numeric conversion, the '0' flag is
     * ignored.
     */
    if ((**p_fmt == 'd') || (**p_fmt == 'i') || (**p_fmt == 'o') || (**p_fmt == 'u') || (**p_fmt == 'x') || (**p_fmt == 'X')) {
        if (token->precision != PRECISION_UNDEFINED) {
            token->flag.zero_padded = 0;
        }
    }

    /* Default precision for everything except s, e, E */
    if (token->precision == PRECISION_UNDEFINED) { token->precision = 1; }

    (*p_fmt)++;
}


/******************************************************************************
 *
 * The (optionally signed) value in token->arg_(U)LL is converted to a decimal string
 * in token->arg_as_str.
 *
 * Algorithm derived from Douglas Jones
 *    http://homepage.cs.uiowa.edu/~jones/bcd/decimal.html
 *
 *****************************************************************************/
#define r_10000     ((((1LL << 32) << 13) / 10000) + 1) // (1 / 10000) << 45
static void _convertDec(arg_token_t *token) {
    uint64_t n;
    uint32_t d4, d3, d2, d1, d0, q;
    int sign = 1;

    REQUIRE (token);

    /*
     * If the precision == 0 and the argument == 0 then output an empty string
     * or a single space if token->flag.space_before_pos is set and the
     * conversion type is signed.
     */
    if (token->precision == 0 && (token->arg_ULL == 0)) {
        token->arg_str_len = 0;
        token->field_width = 0;
        if ((token->flag.arg_signed) && (token->flag.space_before_pos)) {
            token->arg_str_len = 1;
            token->arg_as_str[0] = ' ';
        }
        return;
    }

    n = token->arg_ULL;
    if ((token->flag.arg_signed) && (token->arg_LL < 0)) {
        n = (uint64_t) -((int64_t) n);
        sign = -1;
    }

    d0 = n       & 0xFFFF;
    d1 = (n>>16) & 0xFFFF;
    d2 = (n>>32) & 0xFFFF;
    d3 = (n>>48) & 0xFFFF;

    d0 = 656 * d3 + 7296 * d2 + 5536 * d1 + d0;
    //  q = d0 / 10000;
    // d0 = d0 % 10000;
    q  = (d0 * r_10000) >> 45;
    d0 = d0 - (q * 10000);

    d1 = q + 7671 * d3 + 9496 * d2 + 6 * d1;
    //  q = d1 / 10000;
    // d1 = d1 % 10000;
    q  = (d1 * r_10000) >> 45;
    d1 = d1 - (q * 10000);

    d2 = q + 4749 * d3 + 42 * d2;
    //  q = d2 / 10000;
    // d2 = d2 % 10000;
    q  = (d2 * r_10000) >> 45;
    d2 = d2 - (q * 10000);

    d3 = q + 281 * d3;
    //  q = d3 / 10000;
    // d3 = d3 % 10000;
    q  = (d3 * r_10000) >> 45;
    d3 = d3 - (q * 10000);

    d4 = q;


    /*
     * Create output string backwards, least significant digit first,
     * creating all 20 digits. p_dec_str always points to a valid char.
     */
    char * p_dec_str = &(token->arg_as_str[ARG_STR_LEN_MAX]);
    uint16_t  d0_16 = (uint16_t) d0;
    uint16_t  d1_16 = (uint16_t) d1;
    uint16_t  d2_16 = (uint16_t) d2;
    uint16_t  d3_16 = (uint16_t) d3;
    uint16_t  d4_16 = (uint16_t) d4;
    for (int i=0; i<4; ++i) { *--p_dec_str = (char) ('0' + _udiv_by_10(&d0_16)); }
    for (int i=0; i<4; ++i) { *--p_dec_str = (char) ('0' + _udiv_by_10(&d1_16)); }
    for (int i=0; i<4; ++i) { *--p_dec_str = (char) ('0' + _udiv_by_10(&d2_16)); }
    for (int i=0; i<4; ++i) { *--p_dec_str = (char) ('0' + _udiv_by_10(&d3_16)); }
    for (int i=0; i<4; ++i) { *--p_dec_str = (char) ('0' + _udiv_by_10(&d4_16)); }

    // trim string len to max of precision or sig digits
    token->arg_str_len = ARG_DEC_DIGITS_MAX;
    while (token->arg_str_len>token->precision && (*p_dec_str == '0')) {
        --token->arg_str_len;
        ++p_dec_str;
    }

    /*
     * Add the sign indicator (or space) for signed conversions if negative
     * or required by the flags.
     */
    if (token->flag.arg_signed) {
        if (sign == -1)                        { *--p_dec_str = '-'; ++token->arg_str_len;}
        else if (token->flag.sign_indicator)   { *--p_dec_str = '+'; ++token->arg_str_len;}
        else if (token->flag.space_before_pos) { *--p_dec_str = ' '; ++token->arg_str_len;}
    }

    // move characters from right justified to left justified
    for (int i=0; i<token->arg_str_len; ++i) {
        token->arg_as_str[i] = *p_dec_str++;
    }
}


/******************************************************************************
 *
 * The value in token->arg_ULL is converted to an octal or hex string
 * in token->arg_as_str.
 *
 *****************************************************************************/
static void _convertBin(arg_token_t *token, conversion_type_t radix) {
    char *  p_hex_str;
    int     shift_cnt;
    uint8_t char_mask;

    REQUIRE (token);
    REQUIRE ((radix == CONV_OCTAL) || (radix == CONV_HEX));

    token->arg_str_len = 0;
    p_hex_str = &(token->arg_as_str[ARG_STR_LEN_MAX]);  // create backwards, least significant digit first (pointer is predecremented in loop)
    if (radix == CONV_OCTAL) {
        shift_cnt = 3;    // convert this many bits at a time
        char_mask = 0x07; // 3 bits makes one octal char
    }
    else {  // radix == CONV_HEX
        shift_cnt = 4;
        char_mask = 0x0f;
    }

    // precision == 0 and argument == 0 must output a null string
    if (token->precision == 0 && (token->arg_ULL == 0)) {
        token->arg_str_len = 0;
        token->field_width = 0;
        return;
    }

    // precision == 1 and argument == 0 output a '0' with no preceding '0x'
    if (token->precision == 1 && (token->arg_ULL == 0)) {
        token->arg_str_len = 1;
        token->arg_as_str[0] = '0';
        return;
    }

    // repeat until argument is exhausted and at least precision digits
    int prec = token->precision;
    while ((prec-- > 0) || token->arg_ULL) {
        --p_hex_str;  // decrement here so that it will point to valid char on exit
        *p_hex_str = (char) ((token->arg_ULL & char_mask) + '0');
        if (*p_hex_str > '9') {
            if (token->flag.caps) { *p_hex_str += 'A' - ('9' + 1); }
            else                  { *p_hex_str += 'a' - ('9' + 1); }
        }
        ++token->arg_str_len;
        token->arg_ULL >>= shift_cnt;
    }

    // add preceding zero (octal) or '0x' or '0X' if required
    if (token->flag.alt_form) {
        if (radix == CONV_HEX) {
            if (token->flag.caps) { *--p_hex_str = 'X'; }
            else                  { *--p_hex_str = 'x'; }
            ++token->arg_str_len;
        }
        if (*p_hex_str != '0') {    // also takes care of alt form radix==CONV_OCTAL when first octal digit isn't a zero
            *--p_hex_str = '0';
            ++token->arg_str_len;
        }
    }

    // move characters from right justified to left justified
    for (int i=0; i<token->arg_str_len; ++i) {
        token->arg_as_str[i] = *p_hex_str++;
    }
}


/******************************************************************************
 *
 * The signed integer value in token->arg_LL is converted to a
 * decimal string in token->arg_as_str.
 *
 * The argument is rounded and converted in the style [-][d][d]d.ddde+dd.
 *
 * Because the input argument is an integer, the exponent will always be positive.
 *
 * If the conversion specifier is e, there will always be one and only one
 * digit before the decimal point. The precision specifies the number of
 * digits following the decimal point.
 *
 * If the conversion specifier is E, the exponent will be divisible by 3,
 * there will be one, two, or three digits before the decimal point, and
 * zero or more digits after the decimal point. The number of significant
 * digits is equal to the precision. The least significant digit is rounded. If
 * the precision is less than the number of digits to the left of the
 * decimal point, the remaining digits will appear as zero.
 *
 *
 *****************************************************************************/
#define EXP_MAX_STR_LEN   (ARG_DEC_DIGITS_MAX + 6)    // extra chars: sign, dec pt, e+dd
static void _convertExp(arg_token_t *token) {
    char *    p_dec_str;
    uint32_t  dec_chars_rem;
    uint32_t  exp;
    uint32_t  integer_digits;
    char      e_str[EXP_MAX_STR_LEN];
    char *    p_e_str = e_str;

    REQUIRE (token);

    /*
     * Convert the integer argument to a decimal string with a precision of
     * one in order to get all of the significant digits without any leading
     * zeros, then massage the decimal string into e format.
     *
     * If the format is 'E' then the precision specifies the number of
     * significant digits which must be at least one.
     */
    int16_t e_precision = token->precision;
    token->precision = 1;
    _convertDec(token);
    token->precision = e_precision;
    if (token->precision == 0 && token->flag.caps) {
        token->precision = 1;
    }

    /*
     * If the argument is zero and the precision is zero, _convertDec will
     * return "" or " ", but in e, E format this should be printed as "0".
     *
     * Fix up the output string and return.
     */
    if (token->precision == 0 && (token->arg_ULL == 0)) {
        token->arg_str_len = 1;
        token->arg_as_str[0] = '0';
        return;
    }

    p_dec_str     = token->arg_as_str;
    dec_chars_rem = (uint32_t) (int) (token->arg_str_len);    // convoluted cast to silence lint

    // preserve leading sign and spaces
    if ((*p_dec_str == '+') || (*p_dec_str == '-') || (*p_dec_str == ' ')) {
        *p_e_str++ = *p_dec_str++;
        --dec_chars_rem;
    }

    /*
     * All that's left in the string are digits. Based on the conversion
     * specifier (e or E) determine the number of digits in the integer part
     * and from that, the value of the exponent.
     */
    if (!token->flag.caps) {  // e conversion specifier - one digit in integer part
        integer_digits = 1;
    }
    else {  // E conversion specifier - 1, 2, or 3 digits in integer part
        integer_digits = dec_chars_rem - (3 * ((((unsigned) dec_chars_rem) * 0xaaab) >> 17)); // dec_chars_rem % 3, 0xaaab = 2/3 * 2^16
        if (integer_digits == 0 ) { integer_digits = 3; }
    }
    exp = dec_chars_rem - integer_digits;


    // round if there are undisplayed digits
    int32_t rnd_digit_idx = (token->precision); // first unseen digit (zero-based) if 'E', precision is number of sig digits
    if (!token->flag.caps) { rnd_digit_idx += 1; }                // first unseen digit if 'e', precision is number of digits after decimal
    uint32_t carry = (p_dec_str[rnd_digit_idx] >= '5') ? 1 : 0;   // won't use if indexed char is garbage
    if ((dec_chars_rem > ((uint32_t) rnd_digit_idx)) && carry) {
        while (--rnd_digit_idx >= 0) {
            p_dec_str[rnd_digit_idx] += 1;
            carry = (p_dec_str[rnd_digit_idx] > '9') ? 1 : 0;
            if (carry) { p_dec_str[rnd_digit_idx] = '0'; }
            else       { break; }
        }
    }

    /*
     * Build string starting with the integer part. If rounding overflowed the
     * number then add a '1' at the front and fix up the number of digits
     * in the integer part and the exponent value.
     */
    if (carry) {
        *p_e_str++ = '1';           // add first integer digit to output string
        if (!token->flag.caps) {    // e conversion specifier, print only 1 integer digit
            --integer_digits;
            ++exp;
        }
        else {                      // E conversion specifier
            --(token->precision);   // remaining significant digits, already printed the first one
            if (integer_digits == 3) {  // E conversion specifier, keep exp at a multiple of 3
                integer_digits = 0;
                exp += 3;
            }
        }
    }
    while (integer_digits--) {
        if ((token->precision > 0) || (!token->flag.caps)) { // 'e' always prints the integer part
            *p_e_str++ = *p_dec_str++;
            if (token->flag.caps) {   // 'E' precision is sig digits
                --token->precision;
            }
        }
        else { *p_e_str++ = '0'; }

        --dec_chars_rem;
    }

    // decimal point only if there are more digits or # flag
    int exp_chars_rem = token->precision;
    if (exp_chars_rem || token->flag.alt_form) {
        *p_e_str++ = '.';
        while (exp_chars_rem) {
            if (dec_chars_rem) {
                *p_e_str++ = *p_dec_str++;
                --dec_chars_rem;
            }
            else {
                *p_e_str++ = '0';
            }
            --exp_chars_rem;
        }
    }

    /*
     * Generate exponent portion 'e+00', exponent is always positive.
     * If the value is zero and the precision is zero print '0' without
     * any exponent.
     */
    uint16_t exp_16 = (uint16_t) exp;
    if ((token->precision != 0) || (token->arg_ULL != 0)) {
        *p_e_str++ = 'e';
        *p_e_str++ = '+';
        p_e_str[1] = (char) (_udiv_by_10(&exp_16) + '0'); // remainder, one's digit
        p_e_str[0] = (char) (exp_16 + '0');  // divisor, tens digit
        p_e_str   += 2;
    }

    // compute length of string
    token->arg_str_len = (int16_t) (p_e_str - e_str);

    // replace token decimal string with exponent string
    for (int i=0; i<token->arg_str_len; ++i) {
        token->arg_as_str[i] = e_str[i];
    }
}


/******************************************************************************
 *
 * The value in token->arg_ULL is converted to a single character at token->arg_as_str[0].
 *
 *****************************************************************************/
static void _convertChar(arg_token_t *token) {

    REQUIRE (token);
    token->arg_str_len = 1;
    token->arg_as_str[0] = (char) token->arg_ULL;
}


/******************************************************************************
 *
 * The value in token->arg_ULL is converted to a pointer to a char string,
 * the string length is determined, and the results are stored in token.
 *
 *****************************************************************************/
static void _convertString(arg_token_t *token) {

    REQUIRE (token);
    token->p_fixed_str = (const char *) ((unsigned long) token->arg_ULL);
    token->flag.string_const = 1;

    /* compute string length */
    token->arg_str_len=0;
    while ((token->p_fixed_str[token->arg_str_len] != '\0')  &&
           (token->arg_str_len < INT16_MAX)                  &&
            token->arg_str_len < token->precision) {
        ++token->arg_str_len;
    }
}



#ifdef UNIT_TEST

#include <string.h>

#define TEST(cond)  failed |= !(cond)

int printf_emb_UNIT_TEST (void) {
  char buf[128];
  bool failed = false;

  /* truncation and return value */
  TEST (snprintf (buf, 0, "abc") == 3);
  TEST (snprintf (NULL, 0, "abc") == 3);
  TEST (snprintf (buf, 5, "")    == 0);
  TEST (snprintf (buf, 5, "abc") == 3);
  TEST (snprintf (buf, 1, "abc") == 3 && buf[0] == '\0' && !strcmp (buf, ""));
  TEST (snprintf (buf, 2, "abc") == 3 && buf[1] == '\0' && !strcmp (buf, "a"));
  TEST (snprintf (buf, 3, "abc") == 3 && buf[2] == '\0' && !strcmp (buf, "ab"));
  TEST (snprintf (buf, 4, "abc") == 3 && buf[3] == '\0' && !strcmp (buf, "abc"));
  TEST (snprintf (buf, 5, "abc") == 3 && buf[3] == '\0' && !strcmp (buf, "abc"));

  /* %d, basic formatting */
  TEST (snprintf (buf, 128, "%d", 5) == 1 && !strcmp (buf, "5"));
  TEST (snprintf (buf, 128, "%d", 0) == 1 && !strcmp (buf, "0"));
  TEST (snprintf (buf, 128, "%.0d", 0) == 0 && !strcmp (buf, ""));
  TEST (snprintf (buf, 128, "%5.0d", 0) == 0 && !strcmp (buf, ""));
  TEST (snprintf (buf, 128, "%.0d", 1) == 1 && !strcmp (buf, "1"));
  TEST (snprintf (buf, 128, "%.d", 2) == 1 && !strcmp (buf, "2"));
  TEST (snprintf (buf, 128, "%d", -1) == 2 && !strcmp (buf, "-1"));
  TEST (snprintf (buf, 128, "%.3d", 5) == 3 && !strcmp (buf, "005"));
  TEST (snprintf (buf, 128, "%.3d", -5) == 4 && !strcmp (buf, "-005"));
  TEST (snprintf (buf, 128, "%5.3d", 5) == 5 && !strcmp (buf, "  005"));
  TEST (snprintf (buf, 128, "%5.3d", -5) == 5 && !strcmp (buf, " -005"));
  TEST (snprintf (buf, 128, "%05.3d", -5) == 5 && !strcmp (buf, " -005"));
  TEST (snprintf (buf, 128, "%-5.3d", -5) == 5 && !strcmp (buf, "-005 "));
  TEST (snprintf (buf, 128, "%-5.-3d", -5) == 5 && !strcmp (buf, "-5   "));

  /* %d, length modifiers */
  TEST (snprintf (buf, 128, "%hhd", (signed char)        -5) == 2 && !strcmp (buf, "-5"));
  TEST (snprintf (buf, 128, "%hhd", (unsigned char)       5) == 1 && !strcmp (buf, "5"));
  TEST (snprintf (buf, 128, "%hd",  (short)              -5) == 2 && !strcmp (buf, "-5"));
  TEST (snprintf (buf, 128, "%hd",  (unsigned short)      5) == 1 && !strcmp (buf, "5"));
  TEST (snprintf (buf, 128, "%ld",  (long)               -5) == 2 && !strcmp (buf, "-5"));
  TEST (snprintf (buf, 128, "%ld",  (unsigned long)       5) == 1 && !strcmp (buf, "5"));
  TEST (snprintf (buf, 128, "%lld", (long long)          -5) == 2 && !strcmp (buf, "-5"));
  TEST (snprintf (buf, 128, "%lld", (unsigned long long)  5) == 1 && !strcmp (buf, "5"));
  TEST (snprintf (buf, 128, "%zd",  (size_t)              5) == 1 && !strcmp (buf, "5"));

  /* %d, flags */
  TEST (snprintf (buf, 128, "%-d", 5) == 1 && !strcmp (buf, "5"));
  TEST (snprintf (buf, 128, "%-+d", 5) == 2 && !strcmp (buf, "+5"));
  TEST (snprintf (buf, 128, "%+-d", 5) == 2 && !strcmp (buf, "+5"));
  TEST (snprintf (buf, 128, "%+d", -5) == 2 && !strcmp (buf, "-5"));
  TEST (snprintf (buf, 128, "% d", 5) == 2 && !strcmp (buf, " 5"));
  TEST (snprintf (buf, 128, "% .0d", 0) == 1 && !strcmp (buf, " "));
  TEST (snprintf (buf, 128, "% +d", 5) == 2 && !strcmp (buf, "+5"));
  TEST (snprintf (buf, 128, "%03d", 5) == 3 && !strcmp (buf, "005"));
  TEST (snprintf (buf, 128, "%-03d", -5) == 3 && !strcmp (buf, "-5 "));
  TEST (snprintf (buf, 128, "%3d", -5) == 3 && !strcmp (buf, " -5"));
  TEST (snprintf (buf, 128, "%03d", -5) == 3 && !strcmp (buf, "-05"));

  /* %o, basic formatting */
  TEST (snprintf (buf, 128, "%o", 5) == 1 && !strcmp (buf, "5"));
  TEST (snprintf (buf, 128, "%o", 8) == 2 && !strcmp (buf, "10"));
  TEST (snprintf (buf, 128, "%o", 0) == 1 && !strcmp (buf, "0"));
  TEST (snprintf (buf, 128, "%#o", 5) == 2 && !strcmp (buf, "05"));
  TEST (snprintf (buf, 128, "%#o", 05) == 2 && !strcmp (buf, "05"));
  TEST (snprintf (buf, 128, "%.0o", 0) == 0 && !strcmp (buf, ""));
  TEST (snprintf (buf, 128, "%.0o", 1) == 1 && !strcmp (buf, "1"));
  TEST (snprintf (buf, 128, "%.3o", 5) == 3 && !strcmp (buf, "005"));
  TEST (snprintf (buf, 128, "%.3o", 8) == 3 && !strcmp (buf, "010"));
  TEST (snprintf (buf, 128, "%5.3o", 5) == 5 && !strcmp (buf, "  005"));

  /* %u, basic formatting */
  TEST (snprintf (buf, 128, "%u", 5) == 1 && !strcmp (buf, "5"));
  TEST (snprintf (buf, 128, "%u", 0) == 1 && !strcmp (buf, "0"));
  TEST (snprintf (buf, 128, "%.0u", 0) == 0 && !strcmp (buf, ""));
  TEST (snprintf (buf, 128, "%5.0u", 0) == 0 && !strcmp (buf, ""));
  TEST (snprintf (buf, 128, "%.0u", 1) == 1 && !strcmp (buf, "1"));
  TEST (snprintf (buf, 128, "%.3u", 5) == 3 && !strcmp (buf, "005"));
  TEST (snprintf (buf, 128, "%5.3u", 5) == 5 && !strcmp (buf, "  005"));

  /* %x, basic formatting */
  TEST (snprintf (buf, 128, "%x", 5) == 1 && !strcmp (buf, "5"));
  TEST (snprintf (buf, 128, "%x", 31) == 2 && !strcmp (buf, "1f"));
  TEST (snprintf (buf, 128, "%x", 0) == 1 && !strcmp (buf, "0"));
  TEST (snprintf (buf, 128, "%.0x", 0) == 0 && !strcmp (buf, ""));
  TEST (snprintf (buf, 128, "%5.0x", 0) == 0 && !strcmp (buf, ""));
  TEST (snprintf (buf, 128, "%.0x", 1) == 1 && !strcmp (buf, "1"));
  TEST (snprintf (buf, 128, "%.3x", 5) == 3 && !strcmp (buf, "005"));
  TEST (snprintf (buf, 128, "%.3x", 31) == 3 && !strcmp (buf, "01f"));
  TEST (snprintf (buf, 128, "%5.3x", 5) == 5 && !strcmp (buf, "  005"));

  /* %x, flags */
  TEST (snprintf (buf, 128, "%-x", 5) == 1 && !strcmp (buf, "5"));
  TEST (snprintf (buf, 128, "%-3x", 5) == 3 && !strcmp (buf, "5  "));
  TEST (snprintf (buf, 128, "%03x", 5) == 3 && !strcmp (buf, "005"));
  TEST (snprintf (buf, 128, "%#x", 31) == 4 && !strcmp (buf, "0x1f"));
  TEST (snprintf (buf, 128, "%#x", 0) == 1 && !strcmp (buf, "0"));

  /* %X, basic formatting */
  TEST (snprintf (buf, 128, "%X", 5) == 1 && !strcmp (buf, "5"));
  TEST (snprintf (buf, 128, "%X", 31) == 2 && !strcmp (buf, "1F"));
  TEST (snprintf (buf, 128, "%X", 0) == 1 && !strcmp (buf, "0"));
  TEST (snprintf (buf, 128, "%.0X", 0) == 0 && !strcmp (buf, ""));
  TEST (snprintf (buf, 128, "%5.0X", 0) == 0 && !strcmp (buf, ""));
  TEST (snprintf (buf, 128, "%.0X", 1) == 1 && !strcmp (buf, "1"));
  TEST (snprintf (buf, 128, "%.3X", 5) == 3 && !strcmp (buf, "005"));
  TEST (snprintf (buf, 128, "%.3X", 31) == 3 && !strcmp (buf, "01F"));
  TEST (snprintf (buf, 128, "%5.3X", 5) == 5 && !strcmp (buf, "  005"));

  /* %X, flags */
  TEST (snprintf (buf, 128, "%-X", 5) == 1 && !strcmp (buf, "5"));
  TEST (snprintf (buf, 128, "%03X", 5) == 3 && !strcmp (buf, "005"));
  TEST (snprintf (buf, 128, "%#X", 31) == 4 && !strcmp (buf, "0X1F"));
  TEST (snprintf (buf, 128, "%#X", 0) == 1 && !strcmp (buf, "0"));

  /* %p, basic formatting */
  TEST (snprintf (buf, 128, "%p", 1234) == 5 && !strcmp (buf, "0x4d2"));
  TEST (snprintf (buf, 128, "%.8p", 1234) == 10 && !strcmp (buf, "0x000004d2"));
  TEST (snprintf (buf, 128, "%p", 0x20001ffc) == 10 && !strcmp (buf, "0x20001ffc"));
  TEST (snprintf (buf, 128, "%.8p", 0) == 10 && !strcmp (buf, "0x00000000"));
  TEST (snprintf (buf, 128, "%.6p", -1) == 10 && !strcmp (buf, "0xffffffff"));

  /* %e, basic formatting */
  TEST (snprintf (buf, 128, "%e",   314159265) == 12 && !strcmp (buf, "3.141593e+08"));
  TEST (snprintf (buf, 128, "%.8e", 314159265) == 14 && !strcmp (buf, "3.14159265e+08"));
  TEST (snprintf (buf, 128, "%.0e", 314159265) == 5 && !strcmp (buf, "3e+08"));
  TEST (snprintf (buf, 128, "%.0e", 0) == 1 && !strcmp (buf, "0"));
  TEST (snprintf (buf, 128, "%.1e", 0) == 7 && !strcmp (buf, "0.0e+00"));

  /* %e, flags */
  TEST (snprintf (buf, 128, "%+e",    314159265) == 13 && !strcmp (buf, "+3.141593e+08"));
  TEST (snprintf (buf, 128, "% e",    314159265) == 13 && !strcmp (buf, " 3.141593e+08"));
  TEST (snprintf (buf, 128, "%#.0e",  314159265) == 6  && !strcmp (buf, "3.e+08"));
  TEST (snprintf (buf, 128, "%e",    -314159265) == 13 && !strcmp (buf, "-3.141593e+08"));
  TEST (snprintf (buf, 128, "%09.2e", 314159265) == 9 && !strcmp (buf, "03.14e+08"));
  TEST (snprintf (buf, 128, "%.2e",   9999) == 8 && !strcmp (buf, "1.00e+04"));
  TEST (snprintf (buf, 128, "%.2e",   12) == 8 && !strcmp (buf, "1.20e+01"));
  TEST (snprintf (buf, 128, "%.3E",   1234)    == 8 && !strcmp (buf, "1.23e+03"));
  TEST (snprintf (buf, 128, "%.4E",   12345)   == 9 && !strcmp (buf, "12.35e+03"));
  TEST (snprintf (buf, 128, "%.5E",   123456)  == 10 && !strcmp (buf, "123.46e+03"));
  TEST (snprintf (buf, 128, "%E",     123456)  == 11 && !strcmp (buf, "123.456e+03"));
  TEST (snprintf (buf, 128, "%.0E",   123456)  == 7 && !strcmp (buf, "100e+03"));
  TEST (snprintf (buf, 128, "%.1E",   123456)  == 7 && !strcmp (buf, "100e+03"));
  TEST (snprintf (buf, 128, "%#.1E",  123456)  == 8 && !strcmp (buf, "100.e+03"));
  TEST (snprintf (buf, 128, "%.2E",   123456)  == 7 && !strcmp (buf, "120e+03"));
  TEST (snprintf (buf, 128, "%.3E",   123567)  == 7 && !strcmp (buf, "124e+03"));
  TEST (snprintf (buf, 128, "%.2E",   1234567) == 7 && !strcmp (buf, "1.2e+06"));
  TEST (snprintf (buf, 128, "%.2E",   99999) == 7 && !strcmp (buf, "100e+03"));
  TEST (snprintf (buf, 128, "%.3E",   99999) == 7 && !strcmp (buf, "100e+03"));
  TEST (snprintf (buf, 128, "%.2E",   999999) == 7 && !strcmp (buf, "1.0e+06"));

  /* %c */
  TEST (snprintf (buf, 128, "%c", 'a') == 1 && !strcmp (buf, "a"));

  /* %s */
  TEST (snprintf (buf, 128, "%.2s", "abc") == 2 && !strcmp (buf, "ab"));
  TEST (snprintf (buf, 128, "%.6s", "abc") == 3 && !strcmp (buf, "abc"));
  TEST (snprintf (buf, 128, "%5s", "abc") == 5 && !strcmp (buf, "  abc"));
  TEST (snprintf (buf, 128, "%-5s", "abc") == 5 && !strcmp (buf, "abc  "));
  TEST (snprintf (buf, 128, "%5.2s", "abc") == 5 && !strcmp (buf, "   ab"));
  TEST (snprintf (buf, 128, "%*s", 5, "abc") == 5 && !strcmp (buf, "  abc"));
  TEST (snprintf (buf, 128, "%*s", -5, "abc") == 5 && !strcmp (buf, "abc  "));
  TEST (snprintf (buf, 128, "%*.*s", 5, 2, "abc") == 5 && !strcmp (buf, "   ab"));
  TEST (snprintf (buf, 128-5, "%s + cat_text", buf) == 16 && !strcmp (buf, "   ab + cat_text")); // this is allowed in contravention to the spec
  TEST (snprintf (buf, 128, "%*.*s", 5, 2, "abc") == 5 && !strcmp (buf, "   ab"));
  TEST (snprintf (buf, 128-5, "cat_text + %s", buf) == 16 && !strcmp (buf, "cat_text +    ab")); // this is allowed in contravention to the spec

  /* %% and unrecognized conversion specifier*/
  TEST (snprintf (buf, 128, "%%") == 1 && !strcmp (buf, "%"));
  TEST (snprintf (buf, 128, "%?") == 1 && !strcmp (buf, "%"));

  /* 64 bit support */
  TEST (snprintf (buf, 128, "%lli",  (int64_t)  123456) == 6 && !strcmp (buf, "123456"));
  TEST (snprintf (buf, 128, "%lli",  (int64_t) -123456) == 7 && !strcmp (buf, "-123456"));
  TEST (snprintf (buf, 128, "%llu",  (uint64_t) 123456) == 6 && !strcmp (buf, "123456"));
  TEST (snprintf (buf, 128, "%llo",  (int64_t)  123456) == 6 && !strcmp (buf, "361100"));
  TEST (snprintf (buf, 128, "%#llo", (int64_t)  123456) == 7 && !strcmp (buf, "0361100"));
  TEST (snprintf (buf, 128, "%llx",  (int64_t)  123456) == 5 && !strcmp (buf, "1e240"));
  TEST (snprintf (buf, 128, "%#llx", (int64_t)  123456) == 7 && !strcmp (buf, "0x1e240"));
  TEST (snprintf (buf, 128, "%llX",  (int64_t)  123456) == 5 && !strcmp (buf, "1E240"));
  TEST (snprintf (buf, 128, "%llx",  -1ll) == 16 && !strcmp (buf, "ffffffffffffffff"));
  TEST (snprintf (buf, 128, "%lld",  -1ll) == 2 && !strcmp (buf, "-1"));
  TEST (snprintf (buf, 128, "%llu",  -1ll) == 20 && !strcmp (buf, "18446744073709551615"));
  TEST (snprintf (buf, 128, "%lle",  -1ll) == 13 && !strcmp (buf, "-1.000000e+00"));
  TEST (snprintf (buf, 128, "%.3llE", 1234567890123456789ll)  == 8 && !strcmp (buf, "1.23e+18"));
  TEST (snprintf (buf, 128, "%.3llE", -1234567890123456789ll) == 9 && !strcmp (buf, "-1.23e+18"));
  TEST (snprintf (buf, 128, "%.3llE", 99953577184ll) == 7 && !strcmp (buf, "100e+09"));
  TEST (snprintf (buf, 128, "%.3llE", 999535771840ll) == 8 && !strcmp (buf, "1.00e+12"));


  return (failed);
}

#endif /* UNIT_TEST */

