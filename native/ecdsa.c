typedef const unsigned int L;
//extern unsigned char scrtchecdsa256[];
extern void ECDSA_256_obf_virt_encrypt(unsigned char* out, const unsigned char* inp);
/*typedef struct VMO { unsigned char o; unsigned short l; const void* a; } VMO;
typedef struct SG { L* ip; L* op; const VMO* v; unsigned char* d; unsigned long l; } SG;
typedef struct SS { L* p; L* ip; unsigned long il; L* op; unsigned long ol; const SG* sg; unsigned long r; } SS;*/
//typedef struct VMO { L ol; L a; } VMO;
//typedef struct SG { L ip; L op; L iop; L v; L l; } SG;
//typedef struct SS { L p; L ip; L il; L op; L ol; L sg; L r; } SS;
/*
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
void run_vm(int vml, const VMO* vmo, unsigned char* d)
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
						scrtchecdsa256[j] = ((SS*)a)->sg->d[((SS*)a)->sg->op[j]];
					}
					zm(((SS*)a)->sg->d, ((SS*)a)->sg->l);
					for (unsigned long j = 0; j < ((SS*)a)->il; j++) {
						if (scrtchecdsa256[j] != 0)
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
}
void load_input(const unsigned char* in, unsigned long ins, L* inpmap, unsigned char* d)
{
	for (unsigned long i = 0; i < ins; i++) {
		for (unsigned long j = 0; j < 8; j++) {
			d[inpmap[((i * 8 + j) * 2) + ((in[ins - 1 - i] & (1 << j)) != 0 ? 1 : 0)]] = 0;
			d[inpmap[((i * 8 + j) * 2) + ((in[ins - 1 - i] & (1 << j)) != 0 ? 0 : 1)]] = 1;
		}
	}
}
void read_output(unsigned char* out, unsigned long outs, L* outp, unsigned char* d)
{
	for (unsigned long i = 0; i < outs; i++) {
		for (unsigned long j = 0; j < 8; j++) {
			out[outs - 1 - i] |= (((d[outp[(i * 8 + j) * 2]] & 1) != 0) << j);
		}
	}
}*/
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#define GETU32(x) x
#else
typedef unsigned int u32;
unsigned int getu32(unsigned char* p)
{
	return (((u32)(p)[3]) ^ ((u32)(p)[2] << 8) ^ ((u32)(p)[1] << 16) ^ ((u32)(p)[0] << 24));
}
#define GETU32(x) getu32(x)
#endif
void load_input(const unsigned char* in, unsigned long ins, L* inpmap, unsigned char* d)
{
	for (unsigned long i = 0; i < ins; i++) {
		for (unsigned long j = 0; j < 8; j++) {
			d[inpmap[i * 8 + j]] = (in[ins - 1 - i] & (1 << j)) != 0;
		}
	}
}
void read_output(unsigned char* out, unsigned long outs, L* outp, unsigned char* d)
{
	for (unsigned long i = 0; i < outs; i++) {
		for (unsigned long j = 0; j < 8; j++) {
			out[outs - 1 - i] |= (((d[outp[i * 8 + j]] & 1) != 0) << j);
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
	L* __restrict pvm = &vmo[vmi<<1];
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
			L* const __restrict a = &ss[*(pvm++)*7];
			L* const __restrict s = &sg[a[5]*5];
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

void vm_ECDSA_256_sign(unsigned char sig[64], const unsigned char hash[32])
{
	unsigned char out[64] = { 0 };
	ECDSA_256_obf_virt_encrypt(out, hash);
	for (unsigned long i = 0; i < 32; i++) sig[i] = out[i + 32], sig[i + 32] = out[i];
}

/*void vm_ECDSA_256_sign(unsigned char sig[64], const unsigned char hash[32])
{
	unsigned char out[65] = { 1 };
	unsigned char inp[32+32];
	for (unsigned long i = 0; i < 32; i++) inp[i + 32] = hash[i];
	unsigned int loop_counter = 0;
	while (out[0]) {
		zm(out, 65);
		*((unsigned int*)&inp[0]) = loop_counter++;
		ECDSA_256_obf_virt_encrypt(out, inp);
	}
	for (unsigned long i = 0; i < 32; i++) sig[i] = out[i+32+1], sig[i + 32] = out[i + 1];
}*/