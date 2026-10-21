#include "smctime.h"
#include <stdint.h>
#include "stdio.h"

typedef const unsigned int L;
//extern unsigned char scrtchaes256[];
//#pragma pack(push, 1)
/*typedef struct VMO { unsigned char o; unsigned short l; const void* a; } VMO;
typedef struct SG { L* ip; L* op; const VMO* v; unsigned char* d; unsigned long l; } SG;
typedef struct SS { L* p; L* ip; unsigned long il; L* op; unsigned long ol; const SG* sg; unsigned long r; } SS;*/
//typedef struct VMO { unsigned char o; unsigned short l; L a; } VMO;
//typedef struct SG { L ip; L op; L iop; L v; unsigned long l; } SG;
//typedef struct SS { L p; L ip; unsigned long il; L op; unsigned long ol; L sg; unsigned long r; } SS;
//#pragma pack(pop)

/*void load_input(unsigned char* in, unsigned long ins, L* inpmap, unsigned char* d)
{
	for (unsigned long i = 0; i < ins; i++) {
		for (int j = 0; j < 8; j++) {
			d[inpmap[((i * 8 + j) * 2) + ((in[i] & (1 << j)) != 0 ? 0 : 1)]]++;
		}
	}
}
void read_output(unsigned char* out, unsigned long outs, L* outp, unsigned char* d)
{
	for (unsigned long i = 0; i < outs; i++) {
		for (int j = 0; j < 8; j++) {
			if ((d[outp[(i * 8 + j) * 2]] & 1) != 0) out[i] |= (1 << j);
		}
	}
}
int all_of(unsigned long l, L* a, unsigned char* d)
{
	for (unsigned long i = 0; i < l; i++) {
		if (!d[a[i]]) return 0;
	}
	return 1;
}
int any_of(unsigned long l, L* a, unsigned char* d)
{
	for (unsigned long i = 0; i < l; i++) {
		if (d[a[i]]) return 1;
	}
	return 0;
}
int count_of(unsigned long l, L* a, unsigned char* d)
{
	int c = 0;
	for (unsigned long i = 0; i < l; i++) {
		c += d[a[i]]; //if (d[a[i]]) c++;		
	}
	return c;
}
void zm(unsigned char* m, unsigned long c)
{
	while (c--) *(m++) = 0;
}
void run_vm(int vmi, int vml, const VMO* vmo, unsigned char* d, L* e, const SG* sg, const SS* ss, int scrtch)
{
	const VMO* pvm = &vmo[vmi];
	for (int i = 0; i < vml; i++) {
		unsigned short l = pvm->l;
		switch (pvm->o) {
		case 1:
			if (l != 0 && d[vmi + i] == 0) d[vmi+i] = all_of(l, &e[pvm->a], d);
			break;
		case 4:
			if (l != 0) d[vmi + i] = any_of(l, &e[pvm->a], d);
			break;
		case 2:
			d[vmi + i] = count_of(l, &e[pvm->a], d) & 1;
			break;
		case 3:
			d[vmi + i] = (count_of(l, &e[pvm->a], d) & 1) == 0;
			break;
		case 5:
		{
			const SS* a = &ss[pvm->a];
			if (count_of(l, &e[a->p], d) == (l >> 1)) { //(a->il >> 1)) {
				zm(&d[sg[a->sg].v], sg[a->sg].l);
				for (unsigned long j = 0; j < a->il; j++) {
					if (d[e[a->ip+j]] != 0)
						d[e[sg[a->sg].ip + j]]++;
				}
				run_vm(sg[a->sg].v, sg[a->sg].l, vmo, d, e, sg, ss, scrtch);
				for (unsigned long k = 0; k < a->r; k++) {
					for (unsigned long j = 0; j < a->ol; j++) {
						d[scrtch+j] = d[e[sg[a->sg].op+j]];
					}
					zm(&d[sg[a->sg].v], sg[a->sg].l);
					for (unsigned long j = 0; j < a->il; j++) {
						if (d[scrtch+j] != 0)
							d[e[sg[a->sg].ip+j]]++;
					}
					run_vm(sg[a->sg].v, sg[a->sg].l, vmo, d, e, sg, ss, scrtch);
				}
				for (unsigned long j = 0; j < a->ol; j++) {
					if (e[a->op+j] != ~0U && d[e[sg[a->sg].op+j]] != 0)
						d[e[a->op+j]]++;
				}
			}
			break;
		}
		}
		pvm++;
	}
}*/
/*void run_vm(int vml, const VMO* vmo, unsigned char* d)
{
	const VMO* pvm = vmo;
	for (int i = 0; i < vml; i++) {
		unsigned short l = pvm->l;
		const void* a = pvm->a;
		switch (pvm->o) {
		case 1:
			if (l != 0 && d[i] == 0) d[i] = all_of(l, (L*)a, d);
			break;
		case 4:
			if (l != 0) d[i] = any_of(l, (L*)a, d);
			break;
		case 2:
			d[i] = count_of(l, (L*)a, d) & 1;
			break;
		case 3:
			d[i] = (count_of(l, (L*)a, d) & 1) == 0;
			break;
		case 5:
			if (count_of(l, ((SS*)a)->p, d) == (l >> 1)) { //(((SS*)a)->il >> 1)) {
				zm(((SS*)a)->sg->d, ((SS*)a)->sg->l);
				for (unsigned long j = 0; j < ((SS*)a)->il; j++) {
					if (d[((SS*)a)->ip[j]] != 0)
						((SS*)a)->sg->d[((SS*)a)->sg->ip[j]]++;
				}
				run_vm(((SS*)a)->sg->l, ((SS*)a)->sg->v, ((SS*)a)->sg->d);
				for (unsigned long k = 0; k < ((SS*)a)->r; k++) {
					for (unsigned long j = 0; j < ((SS*)a)->ol; j++) {
						scrtchaes256[j] = ((SS*)a)->sg->d[((SS*)a)->sg->op[j]];
					}
					zm(((SS*)a)->sg->d, ((SS*)a)->sg->l);
					for (unsigned long j = 0; j < ((SS*)a)->il; j++) {
						if (scrtchaes256[j] != 0)
							((SS*)a)->sg->d[((SS*)a)->sg->ip[j]]++;
					}
					run_vm(((SS*)a)->sg->l, ((SS*)a)->sg->v, ((SS*)a)->sg->d);
				}
				for (unsigned long j = 0; j < ((SS*)a)->ol; j++) {
					if (((SS*)a)->op[j] != ~0U && ((SS*)a)->sg->d[((SS*)a)->sg->op[j]] != 0)
						d[((SS*)a)->op[j]]++;
				}
			}
			break;
		}
		pvm++;
	}
}*/
void load_input(const unsigned char* in, unsigned long ins, L* inpmap, unsigned char* d)
{
	for (unsigned long i = 0; i < ins; i++) {
		for (unsigned long j = 0; j < 8; j++) {
			d[inpmap[i * 8 + j]] = (in[i] & (1 << j)) != 0;
		}
	}
}
void read_output(unsigned char* out, unsigned long outs, L* outp, unsigned char* d)
{
	for (unsigned long i = 0; i < outs; i++) {
		for (unsigned long j = 0; j < 8; j++) {
			out[i] |= (((d[outp[i * 8 + j]] & 1) != 0) << j);
		}
	}
}
static inline unsigned long co(const unsigned long l, L* __restrict a, const unsigned char* const __restrict d)
{
	unsigned long c = 0;
	L* __restrict f = a + l;
	if (l != 0) { do { c += d[*(a++)]; } while (a != f); }
	return c;
}
void zm(unsigned char* __restrict m, unsigned long c)
{
	while (c--) *(m++) = 0;
}
void run_vm(unsigned long vmi, unsigned long vml, L* const vmo, unsigned char* const __restrict d, L* e, L* sg, L* ss, unsigned long scrtch)
{
	L* __restrict pvm = &vmo[vmi << 1];
	unsigned char* pd = &d[vmi];
	L* __restrict pvf = pvm + vml + vml;
	for (; pvm != pvf; ) {
		unsigned long l = *(pvm++);
		switch (l & 7) {
		case 1:
			l >>= 3;
			*pd = (*pd != 0 && l == 0) || (l != 0 && co(l, &e[*pvm], d) == l); pd++, pvm++;
			continue;
		case 4:
			*(pd++) = co(l >> 3, &e[*(pvm++)], d) != 0;
			continue;
		case 2:
			*(pd++) = co(l >> 3, &e[*(pvm++)], d) & 1;
			continue;
		case 3:
			*(pd++) = (co(l >> 3, &e[*(pvm++)], d) & 1) == 0;
			continue;
		case 5:
		{
			L* const __restrict a = &ss[*(pvm++) * 7];
			L* const __restrict s = &sg[a[5] * 5];
			if (co(l >> 3, &e[a[0]], d) == 1) { //(l >> 4)) {
				zm(&d[s[3]], s[4]);
				{
					L* __restrict eip = &e[s[0]]; L* __restrict eaip = &e[a[1]];
					L* const __restrict efp = eip + a[2];
					do {
						d[*(eip++)] = d[*(eaip++)];
					} while (efp != eip);
				}
				run_vm(s[3], s[4], vmo, d, e, sg, ss, scrtch);
				for (unsigned long k = a[6]; k != 0; k--) {
					if (a[6] == ~0U && !d[*(&e[s[1]] + a[4])]) break;
					{
						unsigned char* __restrict ds = &d[scrtch];
						L* __restrict eip = &e[s[0]]; L* __restrict eop = &e[s[1]];
						L* __restrict efp = eop + a[4];
						do {
							*(ds++) = d[*(eop++)];
						} while (eop != efp);
						zm(&d[s[3]], s[4]);
						efp = eip + a[2];
						L* __restrict eiop = &e[s[2]]; ds = &d[scrtch];
						do {
							d[*(eip++)] = ds[*(eiop++)];
							//d[*(eip++)] = d[eop[*eiop++]];
						} while (eip != efp);
					}
					run_vm(s[3], s[4], vmo, d, e, sg, ss, scrtch);
				}
				{
					L* __restrict eop = &e[s[1]]; L* __restrict eaop = &e[a[3]];
					L* const __restrict efp = eop + a[4];
					for (; eop != efp; ) {
						unsigned int x = *(eaop++);
						if (x != ~0U) d[x] = d[*(eop++)];
						else eop++;
					}
				}
			}
			pd++;
			continue;
		}
		case 6:
		{
			L* const __restrict a = &e[*(pvm++)];
			l >>= 3;
			if (co(l, &e[*a], d) == l) {
				unsigned long c = 0;
				L* __restrict eip = &e[a[2]];
				L* __restrict eaip = &e[a[3]];
				for (unsigned long k = a[1]; k != 0; ) {
					unsigned long i = 0, b = 32 ^ ((k ^ 32) & -(k < 32));
					unsigned int x = 0;
					do {
						x |= (unsigned int)d[*(eip++)] << i;
					} while (++i != b);
					k -= b;
					c |= x & *(eaip++);
				}
				*pd = c != 0;
			}
			pd++;
			continue;
		}
		}
	}
}

#ifdef _MSC_VER
#define SMC_ALIGNED_STRUCT(name) __declspec(align(16)) struct name
#else
#define SMC_ALIGNED_STRUCT(name) struct __attribute__((aligned(16))) name
#endif
SMC_ALIGNED_STRUCT(aes_key_struct) { //must 16-byte align for intrinsics; 32-bit words (unsigned long is 64-bit on LP64 hosts)
	uint32_t rd_key[60];
	int rounds;
};

typedef struct aes_key_struct AES_KEY;
AES_KEY intrin_key;
AES_KEY intrin_key192;
AES_KEY intrin_key256;
typedef uint32_t u32;

const unsigned char userKey[16] = { 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12 };
const unsigned char userKey192[24+8] = { 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12,
									0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12 };
const unsigned char userKey256[32] = { 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12,
									0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12, 0x12 };


#if defined(__x86_64__) || defined(_M_X64) || defined(__i386__) || defined(_M_IX86)
#define SMC_AESNI 1
#endif
#ifdef SMC_AESNI

#ifdef _MSC_VER
#include <intrin.h>
#include <emmintrin.h>
#pragma optimize("gt",on)
#else
#include <x86intrin.h>
#endif
//https://www.intel.com.br/content/dam/doc/white-paper/advanced-encryption-standard-new-instructions-set-paper.pdf
#define AES_128_key_exp(k, rcon) aes_128_key_expansion(k, _mm_aeskeygenassist_si128(k, rcon))
#define AES_192_key_exp(k, rcon, a) aes_192_key_expansion(k, _mm_aeskeygenassist_si128(*a, rcon), a)
#define AES_256_key_expn(k, rcon, a) aes_128_key_expansion(a, _mm_aeskeygenassist_si128(k, rcon))
#define AES_256_key_exp(k, a) aes_256_key_expansion(a, _mm_aeskeygenassist_si128(k, 0))

static __m128i aes_128_key_expansion(__m128i key, __m128i keygened) {
	keygened = _mm_shuffle_epi32(keygened, _MM_SHUFFLE(3, 3, 3, 3));
	key = _mm_xor_si128(key, _mm_slli_si128(key, 4));
	key = _mm_xor_si128(key, _mm_slli_si128(key, 4));
	key = _mm_xor_si128(key, _mm_slli_si128(key, 4));
	return _mm_xor_si128(key, keygened);
}
static __m128i aes_192_key_expansion(__m128i key, __m128i keygened, __m128i *alt) {
	keygened = _mm_shuffle_epi32(keygened, _MM_SHUFFLE(1, 1, 1, 1));
	key = _mm_xor_si128(key, _mm_slli_si128(key, 4));
	key = _mm_xor_si128(key, _mm_slli_si128(key, 4));
	key = _mm_xor_si128(key, _mm_slli_si128(key, 4));
	key = _mm_xor_si128(key, keygened);
	keygened = _mm_shuffle_epi32(key, _MM_SHUFFLE(3, 3, 3, 3));
	*alt = _mm_xor_si128(*alt, _mm_slli_si128(*alt, 4));
	*alt = _mm_xor_si128(*alt, keygened);
	return key;
}
static __m128i aes_256_key_expansion(__m128i key, __m128i keygened) {
	keygened = _mm_shuffle_epi32(keygened, _MM_SHUFFLE(2, 2, 2, 2));
	key = _mm_xor_si128(key, _mm_slli_si128(key, 4));
	key = _mm_xor_si128(key, _mm_slli_si128(key, 4));
	key = _mm_xor_si128(key, _mm_slli_si128(key, 4));
	return _mm_xor_si128(key, keygened);
}

int AES_set_encrypt_key_intrin(const unsigned char* userKey, const int bits,
	AES_KEY* key) {
	if (bits == 128) {
		key->rounds = 10;
		*((__m128i*) & key->rd_key[0]) = _mm_loadu_si128((const __m128i*) userKey);
		*((__m128i*) & key->rd_key[4]) = AES_128_key_exp(*((__m128i*) & key->rd_key[0]), 0x01);
		*((__m128i*) & key->rd_key[8]) = AES_128_key_exp(*((__m128i*) & key->rd_key[4]), 0x02);
		*((__m128i*) & key->rd_key[12]) = AES_128_key_exp(*((__m128i*) & key->rd_key[8]), 0x04);
		*((__m128i*) & key->rd_key[16]) = AES_128_key_exp(*((__m128i*) & key->rd_key[12]), 0x08);
		*((__m128i*) & key->rd_key[20]) = AES_128_key_exp(*((__m128i*) & key->rd_key[16]), 0x10);
		*((__m128i*) & key->rd_key[24]) = AES_128_key_exp(*((__m128i*) & key->rd_key[20]), 0x20);
		*((__m128i*) & key->rd_key[28]) = AES_128_key_exp(*((__m128i*) & key->rd_key[24]), 0x40);
		*((__m128i*) & key->rd_key[32]) = AES_128_key_exp(*((__m128i*) & key->rd_key[28]), 0x80);
		*((__m128i*) & key->rd_key[36]) = AES_128_key_exp(*((__m128i*) & key->rd_key[32]), 0x1B);
		*((__m128i*) & key->rd_key[40]) = AES_128_key_exp(*((__m128i*) & key->rd_key[36]), 0x36);
	}
	else if (bits == 192) {
		key->rounds = 12;
		*((__m128i*) & key->rd_key[0]) = _mm_loadu_si128((const __m128i*) userKey);
		__m128i s = _mm_loadu_si128((const __m128i*) (userKey+16));		
		_mm_storeu_si128(((__m128i*) & key->rd_key[4]), s); //*((__m128i*) & key->rd_key[4]) = s;
		__m128i t = AES_192_key_exp(*((__m128i*) & key->rd_key[0]), 0x01, &s);
		*((__m128i*) & key->rd_key[4]) = _mm_castpd_si128(_mm_shuffle_pd(*((__m128d*) & key->rd_key[4]), _mm_castsi128_pd(t), 0));
		*((__m128i*) & key->rd_key[8]) = _mm_castpd_si128(_mm_shuffle_pd(_mm_castsi128_pd(t), _mm_castsi128_pd(s), 1));
		*((__m128i*) & key->rd_key[12]) = AES_192_key_exp(t, 0x02, &s);
		_mm_storeu_si128(((__m128i*) & key->rd_key[16]), s); //*((__m128i*) & key->rd_key[16]) = s;
		t = AES_192_key_exp(*((__m128i*) & key->rd_key[12]), 0x04, &s);
		*((__m128i*) & key->rd_key[16]) = _mm_castpd_si128(_mm_shuffle_pd(*((__m128d*) & key->rd_key[16]), _mm_castsi128_pd(t), 0));
		*((__m128i*) & key->rd_key[20]) = _mm_castpd_si128(_mm_shuffle_pd(_mm_castsi128_pd(t), _mm_castsi128_pd(s), 1));
		*((__m128i*) & key->rd_key[24]) = AES_192_key_exp(t, 0x08, &s);
		_mm_storeu_si128(((__m128i*) & key->rd_key[28]), s); //*((__m128i*) & key->rd_key[28]) = s;
		t = AES_192_key_exp(*((__m128i*) & key->rd_key[24]), 0x10, &s);
		*((__m128i*) & key->rd_key[28]) = _mm_castpd_si128(_mm_shuffle_pd(*((__m128d*) & key->rd_key[28]), _mm_castsi128_pd(t), 0));
		*((__m128i*) & key->rd_key[32]) = _mm_castpd_si128(_mm_shuffle_pd(_mm_castsi128_pd(t), _mm_castsi128_pd(s), 1));
		*((__m128i*) & key->rd_key[36]) = AES_192_key_exp(t, 0x20, &s);
		_mm_storeu_si128(((__m128i*) & key->rd_key[40]), s); //*((__m128i*) & key->rd_key[40]) = s;
		t = AES_192_key_exp(*((__m128i*) & key->rd_key[36]), 0x40, &s);
		*((__m128i*) & key->rd_key[40]) = _mm_castpd_si128(_mm_shuffle_pd(*((__m128d*) & key->rd_key[40]), _mm_castsi128_pd(t), 0));
		*((__m128i*) & key->rd_key[44]) = _mm_castpd_si128(_mm_shuffle_pd(_mm_castsi128_pd(t), _mm_castsi128_pd(s), 1));
		*((__m128i*) & key->rd_key[48]) = AES_192_key_exp(t, 0x80, &s);
	}
	else if (bits == 256) {
		key->rounds = 14;
		*((__m128i*) & key->rd_key[0]) = _mm_loadu_si128((const __m128i*) userKey);
		*((__m128i*) & key->rd_key[4]) = _mm_loadu_si128((const __m128i*) (userKey + 16));
		*((__m128i*) & key->rd_key[8]) = AES_256_key_expn(*((__m128i*) & key->rd_key[4]), 0x01, *((__m128i*) & key->rd_key[0]));
		*((__m128i*) & key->rd_key[12]) = AES_256_key_exp(*((__m128i*) & key->rd_key[8]), *((__m128i*) & key->rd_key[4]));
		*((__m128i*) & key->rd_key[16]) = AES_256_key_expn(*((__m128i*) & key->rd_key[12]), 0x02, *((__m128i*) & key->rd_key[8]));
		*((__m128i*) & key->rd_key[20]) = AES_256_key_exp(*((__m128i*) & key->rd_key[16]), *((__m128i*) & key->rd_key[12]));
		*((__m128i*) & key->rd_key[24]) = AES_256_key_expn(*((__m128i*) & key->rd_key[20]), 0x04, *((__m128i*) & key->rd_key[16]));
		*((__m128i*) & key->rd_key[28]) = AES_256_key_exp(*((__m128i*) & key->rd_key[24]), *((__m128i*) & key->rd_key[20]));
		*((__m128i*) & key->rd_key[32]) = AES_256_key_expn(*((__m128i*) & key->rd_key[28]), 0x08, *((__m128i*) & key->rd_key[24]));
		*((__m128i*) & key->rd_key[36]) = AES_256_key_exp(*((__m128i*) & key->rd_key[32]), *((__m128i*) & key->rd_key[28]));
		*((__m128i*) & key->rd_key[40]) = AES_256_key_expn(*((__m128i*) & key->rd_key[36]), 0x10, *((__m128i*) & key->rd_key[32]));
		*((__m128i*) & key->rd_key[44]) = AES_256_key_exp(*((__m128i*) & key->rd_key[40]), *((__m128i*) & key->rd_key[36]));
		*((__m128i*) & key->rd_key[48]) = AES_256_key_expn(*((__m128i*) & key->rd_key[44]), 0x20, *((__m128i*) & key->rd_key[40]));
		*((__m128i*) & key->rd_key[52]) = AES_256_key_exp(*((__m128i*) & key->rd_key[48]), *((__m128i*) & key->rd_key[44]));
		*((__m128i*) & key->rd_key[56]) = AES_256_key_expn(*((__m128i*) & key->rd_key[52]), 0x40, *((__m128i*) & key->rd_key[48]));
	}
	return 0;
}

void AES_encrypt_intrin(const unsigned char* in, unsigned char* out,
	const AES_KEY* key) {
	const u32* rk = key->rd_key;
	__m128i m = _mm_loadu_si128((__m128i*)in);
	m = _mm_xor_si128(m, *((__m128i*) & rk[0]));
	m = _mm_aesenc_si128(m, *((__m128i*) & rk[4]));
	m = _mm_aesenc_si128(m, *((__m128i*) & rk[8]));
	m = _mm_aesenc_si128(m, *((__m128i*) & rk[12]));
	m = _mm_aesenc_si128(m, *((__m128i*) & rk[16]));
	m = _mm_aesenc_si128(m, *((__m128i*) & rk[20]));
	m = _mm_aesenc_si128(m, *((__m128i*) & rk[24]));
	m = _mm_aesenc_si128(m, *((__m128i*) & rk[28]));
	m = _mm_aesenc_si128(m, *((__m128i*) & rk[32]));
	m = _mm_aesenc_si128(m, *((__m128i*) & rk[36]));
	if (key->rounds == 10) {
		m = _mm_aesenclast_si128(m, *((__m128i*) & rk[40]));
	} else {
		m = _mm_aesenc_si128(m, *((__m128i*) & rk[40]));
		m = _mm_aesenc_si128(m, *((__m128i*) & rk[44]));
		if (key->rounds == 12) {
			m = _mm_aesenclast_si128(m, *((__m128i*) & rk[48]));
		} else {
			m = _mm_aesenc_si128(m, *((__m128i*) & rk[48]));
			m = _mm_aesenc_si128(m, *((__m128i*) & rk[52]));
			m = _mm_aesenclast_si128(m, *((__m128i*) & rk[56]));
		}
	}
	_mm_storeu_si128((__m128i*)out, m);
}
void AES_intrin_fix_keys()
{
	AES_set_encrypt_key_intrin(userKey, 128, &intrin_key);
	AES_set_encrypt_key_intrin(userKey192, 192, &intrin_key192);
	AES_set_encrypt_key_intrin(userKey256, 256, &intrin_key256);
}

void AES_128_encrypt_intrin(unsigned char* out, unsigned char* in) {
	//AES_set_encrypt_key_intrin(userKey, 128, &intrin_key);
	AES_encrypt_intrin(in, out, &intrin_key);
}
void AES_192_encrypt_intrin(unsigned char* out, unsigned char* in) {
	//AES_set_encrypt_key_intrin(userKey192, 192, &intrin_key192);
	AES_encrypt_intrin(in, out, &intrin_key192);
}
void AES_256_encrypt_intrin(unsigned char* out, unsigned char* in) {
	//AES_set_encrypt_key_intrin(userKey256, 256, &intrin_key256);
	AES_encrypt_intrin(in, out, &intrin_key256);
}
#else
/* no AES-NI on this architecture (e.g. arm64): the 'Intrinsics' column falls back to the C reference implementation */
extern void AES_128_encrypt(unsigned char* out, unsigned char* in);
extern void AES_192_encrypt(unsigned char* out, unsigned char* in);
extern void AES_256_encrypt(unsigned char* out, unsigned char* in);
void AES_intrin_fix_keys() {}
void AES_128_encrypt_intrin(unsigned char* out, unsigned char* in) { AES_128_encrypt(out, in); }
void AES_192_encrypt_intrin(unsigned char* out, unsigned char* in) { AES_192_encrypt(out, in); }
void AES_256_encrypt_intrin(unsigned char* out, unsigned char* in) { AES_256_encrypt(out, in); }
#endif

extern void AES_128_obf_virt_encrypt(unsigned char* out, unsigned char* in);
extern void AES_128_obf_encrypt(unsigned char* out, unsigned char* in);
extern void AES_192_obf_virt_encrypt(unsigned char* out, unsigned char* in);
extern void AES_192_obf_encrypt(unsigned char* out, unsigned char* in);
extern void AES_256_obf_virt_encrypt(unsigned char* out, unsigned char* in);
extern void AES_256_obf_encrypt(unsigned char* out, unsigned char* in);
extern void AES_fix_keys();
extern void AES_128_encrypt(unsigned char* out, unsigned char* in);
extern void AES_192_encrypt(unsigned char* out, unsigned char* in);
extern void AES_256_encrypt(unsigned char* out, unsigned char* in);

typedef struct aesbitfuncs {
	int bits;
	const unsigned char* key;
	void(*f[4])(unsigned char*, unsigned char*);
} aesbitfuncs;

const char* aesstrs[] = { "C. Ref Encryption", "Instrinsics Encryption", "Graph Encryption", "Graph VM Encryption" };

aesbitfuncs aesfuncs[] = {
	{128, userKey, {AES_128_encrypt, AES_128_encrypt_intrin, AES_128_obf_encrypt, AES_128_obf_virt_encrypt}},
	{192, userKey192, {AES_192_encrypt, AES_192_encrypt_intrin, AES_192_obf_encrypt, AES_192_obf_virt_encrypt}},
	{256, userKey256, {AES_256_encrypt, AES_256_encrypt_intrin, AES_256_obf_encrypt, AES_256_obf_virt_encrypt}}
};

void verify(aesbitfuncs f)
{
	char inp[16] = "Hello world!!!!";
	unsigned char out[4][16] = {0};
	for (int i = 0; i < 4; i++)
		f.f[i](out[i], (unsigned char*)inp);
	printf("%d %d %d\n", memcmp(out[0], out[1], 16), memcmp(out[0], out[2], 16), memcmp(out[0], out[3], 16));
}

void timing(aesbitfuncs f)
{
	unsigned char out[16] = { 0 };
	char inp[16] = "Hello world!!!!";
	for (int c = 0; c < 4; c++) {
		double start = smc_now();
		for (int i = 0; i < smc_iterations(); i++)
			f.f[c](out, (unsigned char*)inp);
		double stop = smc_now();
		printf("AES-%u %s: %lf seconds\n", f.bits, aesstrs[c], stop - start);
	}
}

void test()
{
	AES_intrin_fix_keys();
	AES_fix_keys();
	for (int i = 0; i < 3; i++) {
		verify(aesfuncs[i]);
		timing(aesfuncs[i]);
	}
}

#include <stdio.h>
int main(int argc, char** argv)
{
	test();
	int i;
	unsigned char out[16] = { 0 };
	char inp[16] = "Hello world!!!!";
	if (argc == 2) {
		for (i = 0; i < 32; i++) {
			if ((i & 1) == 0) inp[i >> 1] = 0;
			inp[i >> 1] |= (argv[1][i] - (argv[1][i] > '9' ? ('a' - 10) : '0')) << ((i & 1) != 0 ? 0 : 4);
		}
	}
	AES_128_encrypt(out, (unsigned char*)inp);
	//AES_192_encrypt(out, (unsigned char*)inp);
	//AES_256_encrypt(out, (unsigned char*)inp);
	//AES_128_obf_virt_encrypt(out, (unsigned char*)inp);
	//AES_128_obf_encrypt(out, (unsigned char*)inp);
	for (i = 0; i < 16; i++) {
		putchar((((out[i] & 0xf0) >> 4) >= 10 ? 'a' - 10 : '0') + ((out[i] & 0xf0) >> 4));
		putchar(((out[i] & 0xf) >= 10 ? 'a' - 10 : '0') + (out[i] & 0xf));
	}
	putchar('\n');
	//getchar();
	return 0;
}