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
#endif

#include "wad.h"
