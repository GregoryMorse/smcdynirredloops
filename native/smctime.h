/* Portable helpers of the native drivers (AES, RSA, ECDSA): a monotonic clock in seconds, the number of timing iterations
   (default 1000 as in Tables 1-2; the environment variable SMC_ITERATIONS lowers it, e.g. for the portability tests of CI) and
   a heap replacement of the MSVC-only _malloca. */
#ifndef SMCTIME_H
#define SMCTIME_H
#include <stdlib.h>
#ifdef _WIN32
#include <windows.h>
#include <malloc.h>
static double smc_now(void)
{
	LARGE_INTEGER f, c;
	QueryPerformanceFrequency(&f);
	QueryPerformanceCounter(&c);
	return (double)c.QuadPart / (double)f.QuadPart;
}
#else
#include <time.h>
#define _malloca(n) malloc(n)
static double smc_now(void)
{
	struct timespec t;
	clock_gettime(CLOCK_MONOTONIC, &t);
	return (double)t.tv_sec + (double)t.tv_nsec * 1e-9;
}
#endif
static int smc_iterations(void)
{
	const char* s = getenv("SMC_ITERATIONS");
	int n = s ? atoi(s) : 1000;
	return n > 0 ? n : 1000;
}
#endif
