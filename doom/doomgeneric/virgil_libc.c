#ifdef VIRGIL_SDL2
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdint.h>
#include <limits.h>
#include <string.h>
#include <ctype.h>
#include <math.h>
#else
typedef unsigned char uint8_t;
typedef unsigned short uint16_t;
typedef unsigned int uint32_t;
typedef long int64_t;
typedef long intptr_t;
typedef unsigned long size_t;
typedef void FILE;
typedef void *va_list;

#define NULL 0
#define EISDIR 17
FILE *stdout = (FILE *) 0;
FILE *stderr = (FILE *) 1;
#define INT_MAX 2147483647
#define INT_MIN -2147483648
#define SHRT_MAX 32767
#define SHRT_MIN -32768

#define VIRGIL_SYS_DEBUG 0
#define VIRGIL_SYS_PIXEL 1
#define VIRGIL_SYS_MALLOC 2

void *memset(void *dest, int c, size_t n) {
    uint8_t *s = (uint8_t *) dest;
    for (size_t i = 0; i < n; ++i) *(s + i) = c;
    return dest;
}

void *memcpy(void *dest, void *src, size_t n) {
    uint8_t *d = (uint8_t *) dest;
    uint8_t *s = (uint8_t *) src;
    for (size_t i = 0; i < n; ++i)
        *(d + i) = *(s + i);
    return dest;
}

void *memmove(void *dest, void *src, size_t n) {
    uint8_t *d = (uint8_t *) dest;
    uint8_t *s = (uint8_t *) src;
    uint8_t *temp = (uint8_t *) malloc(n);
    for (size_t i = 0; i < n; ++i)
        *(temp + i) = *(s + i);
    for (size_t i = 0; i < n; ++i)
        *(dest + i) = *(temp + i);
    free(temp);
    return dest;
}

void *malloc(size_t n) {
    return syscall(SYSCALL_MALLOC, n);
}
void free(void *p) {}
void *realloc(void *base, size_t n) {}
void *calloc(size_t nmemb, size_t sz) {
    size_t len = nmemb * sz;
    void *ret = malloc(len);
    memset(ret, 0, len);
    return ret;
}

#endif

#include "wad.h"
