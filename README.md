### Overview
A printf library for embedded environments.

- Compiles to about 3.5K of object code.
- Integer numbers only - no floating point support.
- Converts 64 bit numbers.
- Scientific notation and engineering notation both supported.
- Number conversion to decimal does not perform any divide operations.

Only safe conversions to a character buffer are supported. The output string
is constructed on the stack and copied to the output buffer and will be truncated
if the buffer is unable to contain the entire string.

A duplicate (non-standard) set of function calls is provided which will
call a user-supplied memory allocation function once the string is constructed.
This allows an exact-sized buffer to be used, ensuring the string will not
be truncated without having to speculatively allocate an oversized buffer.

A NULL buffer pointer may also be passed for the side effect of determining how
long the string will be, without generating the actual string output.


### API
```C
int  snprintf(char *s, size_t n, const char *fmt, ...);
int  vsnprintf(char *s, size_t n, const char *fmt, va_list ap);

int  saprintf(emb_printf_fn_alloc_t fn_alloc, char **s, const char *fmt, ...);
int  vsaprintf(emb_printf_fn_alloc_t fn_alloc, char **s, const char *fmt, va_list ap);
```

`snprintf()` and `vsnprintf()` are the equivalent of the same-named functions
in the standard library with the exceptions and extensions noted below.

`saprintf()` and `vsaprintf()` are equivalent to `snprintf()` and `vsnprintf()`
except that they will compute the output string length and allocate a buffer
using the supplied fn_alloc. The caller is responsible for freeing
any memory allocated by fn_alloc.

With `saprintf()` and `vsaprintf()` if memory cannot be allocated that will hold
the entire string the the buffer pointer *s will be set to NULL. The
caller must check that *s is valid.

### What IS Supported
- All integer conversion specifiers: d, i, o, u, x, and X.
- The unsigned char specifier: c
- The pointer specifier: p.
- The string specifier: s.
- The % escape specifier: %.
- Length modifiers: hh, h, l, ll, z.

### What is NOT Supported
- Floating point conversion specifiers: e, E (see below), f, F, g, G, a, A.
- The number-of-characters specifier: n.
- Wide characters.
- Any other specifier not explicitly supported.

### Modifications and Extensions
The conversion specifiers e, E are supported, but for integer
arguments in place of double. A length modifier may be associated
with the argument.

For e, the output is the same as if the argument was a double of the
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

### Implementation Details
The code was written to be easily understood. No particular emphasis was
put on code size or performance with the exception of eliminating all
division operations (including modulo, etc).

This implementation is recursive, and is called for every conversion
specifier and string literal in the format string. For example, the
format string "There are %d months and %d days left this year" will result
in xprintf() being called 5 times, once for each %d format specifier and
three times for the strings in between. The recursion depth can be limited
by the macro RECURSION_LIMIT. If the recursion limit is reached
then the return string will be truncated at that point.

The recursive implementation analyzes the entire string and determines
the total length before writing to the output buffer. This allows buffer
memory to be allocated after the string length is known.

For applications with complex format strings or limited stack space the string
can be built up incrementally with multiple calls that include the previous string.
Although the printf specification does not allow the output buffer to
also be used for the input string, it will in fact work fine.

```C
snprintf (out_buf, length, "first_string");
snprintf (out_buf, length, "%s + second_string", out_buf)
out_buf --> "first_string + second_string"

snprintf (out_buf, length, "first_string");
snprintf (out_buf, length, "second_string + %s", out_buf)
out_buf --> "second_string + first_string"
```
##### Example Stack Usage
```C
total_chars = snprintf(out_buf, length, "%#llx in hex; %lld in decimal; %lle in scientific notation; %llE in engineering notation.", 0x1234567890abcdefll, 0x1234567890abcdefll, 0x1234567890abcdefll, 0x1234567890abcdefll);
total_chars --> 132, stack usage 792 bytes

total_chars = snprintf(out_buf, length, "The secret number is %d", 47);
total_chars --> 23, stack usage 312 bytes
```

### Compilation Target and Test
The implementation is targeted at a 32-bit ARM architecture that supports
long long (64 bit) data types, has a 32 x 32 = 32 multiplier and treats
int and long as the same data type.

A comprehensive unit test is appended to the end of the source file.

