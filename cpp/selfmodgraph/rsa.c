//pip install conan
//conanfile.txt: [requires] gmp/6.2.1 [generators] cmake
//"C:\Program Files\Python38\Scripts\conan" profile new default --detect
//mkdir build
//"C:\Program Files\Python38\Scripts\conan" install ..
//%UserProfile%\.conan\data\gmp\6.2.1\_\_\package\c1430fa7339501202f6eff5c00c1be2706543a7c\lib
//https://github.com/ShiftMediaProject/gmp/releases
// rsa.cpp : This file contains the 'main' function. Program execution begins and ends there.
//

#include <Windows.h>

#include <stdio.h>
#include <malloc.h>

typedef const unsigned int L;
//extern unsigned char scrtchrsa256[];
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
			d[inpmap[((i * 8 + j) * 2) + ((in[ins-1-i] & (1 << j)) != 0 ? 0 : 1)]]++;
		}
	}
}
void read_output(unsigned char* out, unsigned long outs, L* outp, unsigned char* d)
{
	for (unsigned long i = 0; i < outs; i++) {
		for (int j = 0; j < 8; j++) {
			if ((d[outp[(i * 8 + j) * 2]] & 1) != 0) out[outs-1-i] |= (1 << j);
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
			if (l != 0 && d[vmi + i] == 0) d[vmi + i] = all_of(l, &e[pvm->a], d);
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
					if (d[e[a->ip + j]] != 0)
						d[e[sg[a->sg].ip + j]]++;
				}
				run_vm(sg[a->sg].v, sg[a->sg].l, vmo, d, e, sg, ss, scrtch);
				for (unsigned long k = 0; k < a->r; k++) {
					for (unsigned long j = 0; j < a->ol; j++) {
						d[scrtch + j] = d[e[sg[a->sg].op + j]];
					}
					zm(&d[sg[a->sg].v], sg[a->sg].l);
					for (unsigned long j = 0; j < a->il; j++) {
						if (d[scrtch + j] != 0)
							d[e[sg[a->sg].ip + j]]++;
					}
					run_vm(sg[a->sg].v, sg[a->sg].l, vmo, d, e, sg, ss, scrtch);
				}
				for (unsigned long j = 0; j < a->ol; j++) {
					if (e[a->op + j] != ~0U && d[e[sg[a->sg].op + j]] != 0)
						d[e[a->op + j]]++;
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
			if (l != 0 && d[i]==0) d[i] = all_of(l, (L*)a, d);
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
						scrtchrsa256[j] = ((SS*)a)->sg->d[((SS*)a)->sg->op[j]];
					}
					zm(((SS*)a)->sg->d, ((SS*)a)->sg->l);
					for (unsigned long j = 0; j < ((SS*)a)->il; j++) {
						if (scrtchrsa256[j] != 0)
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
					unsigned long i = 0, x = 0, b = 32 ^ ((k ^ 32) & -(k < 32));
					do {
						x |= d[*(eip++)] << i;
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

#pragma warning (disable : 4146)
#include <gmp.h>

#define n32_str "A53AC651"
#define e32_str "36FE9B11"
#define d32_str "3B86D58D"
//const char* p32_str = "C15B";
//const char* q32_str = "DAC3";
//const char* phi32_str = "A5392A34";
//const char* lambda32_str = "529C951A";

#define n64_str "84BB8647D193A629"
#define e64_str "33CF97157F1B2C71"
#define d64_str "2876A60FE36123C7"
//const char* p64_str = "FEA476F3";
//const char* q64_str = "8570AD73";
//const char* phi64_str = "84BB86464D7E81C4";
//const char* lambda64_str = "425DC32326BF40E2";

#define n128_str "EA0D13A0EFF6F45C57E6EC379DB0278D"
#define e128_str "6F5621FF5E78D15EC7F23CBBC7064F9F"
#define d128_str "730883C2426CF0D8C970C914CC3D678D"
//const char* p128_str = "F907D8627EFD7777";
//const char* q128_str = "F099E96F28CF621B";
//const char* phi128_str = "EA0D13A0EFF6F45A6E452A65F5E34DFC";
//const char* lambda128_str = "750689D077FB7A2D37229532FAF1A6FE";

#define n256_str "9FDA35FBB1472593855EA39CBD628F0D2C4F3D8F1B6514B92F0011649BED567D"
#define e256_str "451573601F714778C1F5134B96F86617A68F2F80BCE8975FB1D8CE9D86AB23DB"
#define d256_str "1A65AAB3EE3ADC4434ECBC741F04482B9A08D477E09075482A925105A00663C9"
//const char* p256_str = "D98616B04C12E6D7F3A7E46E580067FF";
//const char* q256_str = "BC20A56C3B0EE3FBE30AF949DFAFE183";
//const char* phi256_str = "9FDA35FBB1472593855EA39CBD628F0B96A88172944349E5584D33AC643D0CFC";
//const char* lambda256_str = "4FED1AFDD8A392C9C2AF51CE5EB14785CB5440B94A21A4F2AC2699D6321E867E";

#define n512_str "B84AD133A82C5D2F4BCF853C3B176952394D4DC1E7FD800609AC3CE028616121D14F4C42D9CD69E836742FF4E06CF99399BFC03CE9E497EDD5DEF0FC10FC1209"
#define e512_str "07052AD629C30247103294189056BF5A320BD32AF16B717483BFADDB1B71FCA30C70CFEFFBBE12E3B231E48A011D3FDCB82D0AD3459E05D6DC129852372EBA49"
#define d512_str "4D71D969C5F58EBCC628765FBF9B68DCF5388C4D1439A42E0C26CF521C180E4C8299B1848A01EC49F559C348BA736D237D5B6EAD95C33E914C23D67FF63C9F65"
//const char* p512_str = "CA2D22806E5CBC9AA3E964C43E0BFCCF43A8803FAF7E1650DB6642691206D22F";
//const char* q512_str = "E95AD5E7D25F262FA9BE6FAA02CC8AC85D6510E9813BE479511565DC7525E947";
//const char* phi512_str = "B84AD133A82C5D2F4BCF853C3B176952394D4DC1E7FD800609AC3CE0286161201DC753DA9911871DE8CC5B869F9471FBF8B22F13B92A9D23A96348B689CF5694";
//const char* lambda512_str = "5C256899D4162E97A5E7C29E1D8BB4A91CA6A6E0F3FEC00304D61E701430B0900EE3A9ED4C88C38EF4662DC34FCA38FDFC591789DC954E91D4B1A45B44E7AB4A";

#define RSABITSIZE 1024
#define RSABYTESIZE (RSABITSIZE / 8)
#define SHA256BITSIZE 256
#define SHA256BYTESIZE (SHA256BITSIZE / 8)

#define n1024_str "94EC34827E8621B2ED0E72D7F36E87570E8E6763CFF83AC2366B9D676C98AF2B13EF30675E13AD0540CD568645A9BDE5038B5DA952EC84DE43027E391FBA4568A9ADB941FDE36545E208F24A8985F8238FE932EF0D2A680B5955152E4480D4982A63547E3C40303E45F089E43142532C61A82B5C87250EBCE952CE643F4CB9C9"
#define e1024_str "279F242F809787C1E57066E22F0C08C69C2F647A7F8B1A1E80884CB79D512E80CC90E3B3DECC740341928CF63D1FBCF67F41878E5DAD39E3E3099325D8995460C6D8367E64239539F6032E9DAE204CF3CF305497B935CB6042E4B1417006085DD347EF18E81A18B79AE1375867A341B704877F55309C81666A741A328CF66C8B"
#define d1024_str "2CBF49B38FCF723BAAD2C7F9CAD55D40034A3320A52D7D76EC78C259633CA7275BF0C748F675419019EFA7EDA1C3AEAFF9B4B899DD0B3FC0094EE85BFDFA81A2FF2054AF264BB67B46AE083107795767A5B8561C61BA8E56A5C5195CADC059E514A63AF2B79106D6E4624A63540692C9630BBAC6D3AB9CF2BF50B22D10F853BD"
//const char* p1024_str = "96910779A158F76217BFE38739196805EA37638EFE0B32C42EEBFD62590EA38E20608D1A2BC62580537FDA95DAB76F52F52F86A181FF66351F5320470EFA2A2F";
//const char* q1024_str = "FD347EF218CBDECFFABD6EDE0FDEC31F00A0EFDAB2D020C0E835EA86EA426DCDC8EAB6C6E8757D34B0AF673729FD1F25703208DC8D5A95AC3B057C924C377587";
//const char* phi1024_str = "94EC34827E8621B2ED0E72D7F36E87570E8E6763CFF83AC2366B9D676C98AF2B13EF30675E13AD0540CD568645A9BDE5038B5DA952EC84DE43027E391FBA456715E832D643BE8F13CF8B9FE5408DCCFEA510DF855C4F148642332D45012FC33C4118109D28048D8941C148172C8DC4B3FC469BDE77CB12DB8EFA318AE41B1A14";
//const char* lambda1024_str = "4A761A413F4310D97687396BF9B743AB874733B1E7FC1D611B35CEB3B64C579589F79833AF09D682A066AB4322D4DEF281C5AED4A976426F21813F1C8FDD22B38AF4196B21DF4789E7C5CFF2A046E67F52886FC2AE278A43211996A28097E19E208C084E940246C4A0E0A40B9646E259FE234DEF3BE5896DC77D18C5720D8D0A";

void encode_pkcs(unsigned char* pkcs, unsigned char* in, int msize, int bytes)
{
	memset(pkcs, 0, bytes);
	pkcs[1] = 2;
	int i;
	for (i = 0; i < bytes - msize - 3; i++) {
		pkcs[i + 2] = 0x1; //random
	}
	for (int i = 0; i < msize; i++) {
		pkcs[i + bytes - msize] = in[i];
	}
}

void rsa_encrypt(unsigned char* out, unsigned char* in, int msize, int bytes, const char* n_str, const char* e_str)
{
	unsigned char* pkcs = (unsigned char*)_malloca(bytes);
	encode_pkcs(pkcs, in, msize, bytes);
	mpz_t m, e, n;
	mpz_inits(m, e, n, NULL);
	mpz_init_set_str(n, n_str, 16);
	mpz_init_set_str(e, e_str, 16);
	mpz_import(m, bytes, 1, 1, 1, 0, pkcs);
	mpz_powm(m, m, e, n);
	mpz_export(out, NULL, 1, bytes, 1, 0, m);

	mpz_clears(m, e, n, NULL);
	//for (int i = 0; i < bytes; i++) out[i] = pkcs[i];
}

int pkcs_decode(unsigned char* out, unsigned char* pkcs, int byteSize, int minpad) //minpad=8
{
	int good = 1; int idx = 0;
	for (int i = 0; i < byteSize; i++) {
		if (i == 0) good &= pkcs[i] == 0;
		else if (i == 1) good &= pkcs[i] == 2;
		else if (i < 2 + minpad) good &= pkcs[i] != 0;
		else {
			int val = (pkcs[i] == 0) && (idx == 0);
			idx = i * val + idx * (1 - val);
		}
	}
	good &= idx != 0;
	if (good) {
		for (int i = idx + 1; i < byteSize; i++) {
			out[i - idx - 1] = pkcs[i];
		}
		return byteSize - idx - 1;
	}
	else return -1;
}

int rsa_decrypt(unsigned char* out, unsigned char* in, int bytes, const char* n_str, const char* d_str)
{
	mpz_t m, d, n;
	mpz_inits(m, d, n, NULL);
	mpz_init_set_str(n, n_str, 16);
	mpz_init_set_str(d, d_str, 16);
	mpz_import(m, bytes, 1, 1, 1, 0, in);
	mpz_powm(m, m, d, n);
	unsigned char* pkcs = (unsigned char*)_malloca(bytes);
	mpz_export(pkcs, NULL, 1, bytes, 1, 0, m);

	mpz_clears(m, d, n, NULL);
	return pkcs_decode(out, pkcs, bytes, 0);
}

void encode_pkcs_sign(unsigned char* pkcs, unsigned char* in, int bytes)
{
	memset(pkcs, 0, bytes);
	pkcs[1] = 1;
	//SHA256 OID "2.16.840.1.101.3.4.2.1"
	//DER encoding of DerSequence([DerSequence([DerObjectID(SHA256 OID), DerNull()]), DerOctetString(in)])) where length of in is 32 bytes
	char der[] = "010\r\x06\t`\x86H\x01" "e\x03\x04\x02\x01\x05\x00\x04 ";
	int i;
	for (i = 0; i < bytes - SHA256BYTESIZE - (sizeof(der) - 1) - 3; i++) {
		pkcs[i + 2] = 0xff;
	}
	for (int i = 0; i < sizeof(der) - 1; i++) {
		pkcs[i + bytes - SHA256BYTESIZE - (sizeof(der) - 1)] = der[i];
	}
	for (int i = 0; i < SHA256BYTESIZE; i++) {
		pkcs[i + bytes - SHA256BYTESIZE] = in[i];
	}
}

void rsa_sign(unsigned char* out, unsigned char* in, int bytes, const char* n_str, const char* d_str)
{
	unsigned char* pkcs = (unsigned char*)_malloca(bytes);
	encode_pkcs_sign(pkcs, in, bytes);
	mpz_t m, d, n;
	mpz_inits(m, d, n, NULL);
	mpz_init_set_str(n, n_str, 16);
	mpz_init_set_str(d, d_str, 16);
	mpz_import(m, bytes, 1, 1, 1, 0, pkcs);
	mpz_powm(m, m, d, n);
	mpz_export(out, NULL, 1, bytes, 1, 0, m);

	mpz_clears(m, d, n, NULL);
	//for (int i = 0; i < bytes; i++) out[i] = pkcs[i];
}

int pkcs_verify(unsigned char* sig, unsigned char* pkcs, int bytes)
{
	if (pkcs[0] != 0 || pkcs[1] != 1) return 0;
	char der[] = "010\r\x06\t`\x86H\x01" "e\x03\x04\x02\x01\x05\x00\x04 ";
	for (int i = 0; i < bytes - SHA256BYTESIZE - (sizeof(der) - 1) - 3; i++) {
		if (pkcs[i + 2] != 0xff) return 0;
	}
	if (memcmp(der, &pkcs[bytes - SHA256BYTESIZE - (sizeof(der) - 1)], sizeof(der) - 1) != 0) return 0;
	return memcmp(sig, &pkcs[bytes - SHA256BYTESIZE], SHA256BYTESIZE) == 0;
}

int rsa_sign_verify(unsigned char* in, unsigned char* sig, int bytes, const char* n_str, const char* e_str)
{
	unsigned char* pkcs = (unsigned char*)_malloca(bytes);
	mpz_t m, e, n;
	mpz_inits(m, e, n, NULL);
	mpz_init_set_str(n, n_str, 16);
	mpz_init_set_str(e, e_str, 16);
	mpz_import(m, bytes, 1, 1, 1, 0, sig);
	mpz_powm(m, m, e, n);
	mpz_export(pkcs, NULL, 1, bytes, 1, 0, m);
	mpz_clears(m, e, n, NULL);
	return pkcs_verify(in, pkcs, bytes);
}

//extern int rsa_decrypt_obf(unsigned char* out, unsigned char* in);
//extern int rsa_decrypt_obf_il(unsigned char* out, unsigned char* in);

typedef struct rsabitfuncs {
	const int bits;
	const int padSize;
	const char* n;
	const char* e;
	const char* d;
	const int(*f[3])(unsigned char*, unsigned char*);
} rsabitfuncs;

const char* rsasignstrs[] = { "GMP Signature", "Graph Signature", "Irreducible Loop Graph Signature" };

const char* rsastrs[] = { "GMP Decryption", "Graph Decryption", "Irreducible Loop Graph Decryption" };

extern void RSA_32_obf_virt_encrypt(unsigned char* out, unsigned char* in);
extern void RSA_64_obf_virt_encrypt(unsigned char* out, unsigned char* in);
extern void RSA_128_obf_virt_encrypt(unsigned char* out, unsigned char* in);
extern void RSA_256_obf_virt_encrypt(unsigned char* out, unsigned char* in);
extern void RSA_512_obf_virt_encrypt(unsigned char* out, unsigned char* in) {}
extern void RSA_1024_obf_virt_encrypt(unsigned char* out, unsigned char* in) {}
extern int RSA_32_obf_virt_encryptw(unsigned char* out, unsigned char* in) {
	unsigned char pkcs[32 / 8] = {0};
	RSA_32_obf_virt_encrypt(pkcs, in);
	return pkcs_decode(out, pkcs, 32 / 8, 0); }
extern int RSA_64_obf_virt_encryptw(unsigned char* out, unsigned char* in) {
	unsigned char pkcs[64 / 8] = {0};
	RSA_64_obf_virt_encrypt(pkcs, in);
	return pkcs_decode(out, pkcs, 64 / 8, 0); }
extern int RSA_128_obf_virt_encryptw(unsigned char* out, unsigned char* in) {
	unsigned char pkcs[128 / 8] = {0};
	RSA_128_obf_virt_encrypt(pkcs, in);
	return pkcs_decode(out, pkcs, 128 / 8, 0); }
extern int RSA_256_obf_virt_encryptw(unsigned char* out, unsigned char* in) {
	unsigned char pkcs[256/ 8] = {0};
	RSA_256_obf_virt_encrypt(pkcs, in);
	return pkcs_decode(out, pkcs, 256 / 8, 0); }
extern int RSA_512_obf_virt_encryptw(unsigned char* out, unsigned char* in) {
	unsigned char pkcs[512 / 8] = {0};
	RSA_512_obf_virt_encrypt(pkcs, in);
	return pkcs_decode(out, pkcs, 512 / 8, 0); }
extern int RSA_1024_obf_virt_encryptw(unsigned char* out, unsigned char* in) {
	unsigned char pkcs[1024 / 8] = {0};
	RSA_1024_obf_virt_encrypt(pkcs, in);
	return pkcs_decode(out, pkcs, 1024 / 8, 0); }
int rsa32_decrypt(unsigned char* out, unsigned char* in) {
	return rsa_decrypt(out, in, 32 / 8, n32_str, d32_str);
}
int rsa64_decrypt(unsigned char* out, unsigned char* in) {
	return rsa_decrypt(out, in, 64 / 8, n64_str, d64_str);
}
int rsa128_decrypt(unsigned char* out, unsigned char* in) {
	return rsa_decrypt(out, in, 128 / 8, n128_str, d128_str);
}
int rsa256_decrypt(unsigned char* out, unsigned char* in) {
	return rsa_decrypt(out, in, 256 / 8, n256_str, d256_str);
}
int rsa512_decrypt(unsigned char* out, unsigned char* in) {
	return rsa_decrypt(out, in, 512 / 8, n512_str, d512_str);
}
int rsa1024_decrypt(unsigned char* out, unsigned char* in) {
	return rsa_decrypt(out, in, 1024 / 8, n1024_str, d1024_str);
}


const rsabitfuncs rsafuncs[] = {
	{32, 3, n32_str, e32_str, d32_str, {rsa32_decrypt, RSA_32_obf_virt_encryptw}},
	{64, 3, n64_str, e64_str, d64_str, {rsa64_decrypt, RSA_64_obf_virt_encryptw}},
	{128, 11, n128_str, e128_str, d128_str, {rsa128_decrypt, RSA_128_obf_virt_encryptw}},
	{256, 11, n256_str, e256_str, d256_str, {rsa256_decrypt, RSA_256_obf_virt_encryptw}},
	{512, 11, n512_str, e512_str, d512_str, {rsa512_decrypt, RSA_512_obf_virt_encryptw}},
	{1024, 11, n1024_str, e1024_str, d1024_str, {rsa1024_decrypt, RSA_1024_obf_virt_encryptw}},
};

void verify_sign()
{
	unsigned char out[RSABYTESIZE] = {0};
	char inp[SHA256BYTESIZE] = "Hello world!!!!";
	rsa_sign(out, (unsigned char*)inp, RSABYTESIZE, n1024_str, d1024_str);
	for (int i = 0; i < RSABYTESIZE; i++) {
		putchar((((out[i] & 0xf0) >> 4) >= 10 ? 'a' - 10 : '0') + ((out[i] & 0xf0) >> 4));
		putchar(((out[i] & 0xf) >= 10 ? 'a' - 10 : '0') + (out[i] & 0xf));
	}
	putchar('\n');

	printf("%d\n", rsa_sign_verify((unsigned char*)inp, out, RSABYTESIZE, n1024_str, e1024_str));
}

void verify(rsabitfuncs f)
{
	char* inp = (char*)_malloca(2 * (f.bits / 8 - f.padSize));
	if (inp == NULL) return;
	for (int i = 0; i < f.bits / 8 - f.padSize; i++) inp[i] = 1;
	unsigned char* out = (unsigned char*)_malloca(f.bits / 8);
	rsa_encrypt(out, (unsigned char*)inp, f.bits / 8 - f.padSize, f.bits / 8, f.n, f.e);
	int res[2] = {0};
	for (int i = 0; i < 2; i++)
		res[i] = f.f[i]((unsigned char*)&inp[i * (f.bits / 8 - f.padSize)], out);
	int chk = 0;
	for (int i = 0; i < f.bits / 8 - f.padSize; i++) chk = chk | (inp[i] != 1);
	printf("%d %d %d %d\n", res[0] != f.bits / 8 - f.padSize, res[0] != res[1], chk, memcmp(inp, &inp[f.bits / 8 - f.padSize], f.bits / 8 - f.padSize));
}

void timing(rsabitfuncs f)
{
	char* inp = (char*)_malloca(f.bits / 8 - f.padSize);
	if (inp == NULL) return;
	for (int i = 0; i < f.bits / 8 - f.padSize; i++) inp[i] = 1;
	unsigned char* out = (unsigned char*)_malloca(f.bits / 8);
	rsa_encrypt(out, (unsigned char*)inp, f.bits / 8 - f.padSize, f.bits / 8, f.n, f.e);
	LARGE_INTEGER start;
	LARGE_INTEGER stop;
	LARGE_INTEGER frequency;
	QueryPerformanceFrequency(&frequency);
	for (int c = 0; c < 2; c++) {
		QueryPerformanceCounter(&start);
		for (int i = 0; i < 1000; i++)
			f.f[c]((unsigned char*)inp, out);
		QueryPerformanceCounter(&stop);
		printf("RSA-%u %s: %lf seconds\n", f.bits, rsastrs[c], (double)(stop.QuadPart - start.QuadPart) / (double)frequency.QuadPart);
	}
}

void test()
{
	verify_sign();
	for (int i = 0; i < 6; i++) {
		verify(rsafuncs[i]);
		timing(rsafuncs[i]);
	}
}

int main(int argc, char** argv)
{
	test();
	unsigned char out[RSABYTESIZE] = {0};
	char inp[SHA256BYTESIZE] = {0};
	while (!feof(stdin)) {
		size_t l = fread(inp, SHA256BYTESIZE, 1, stdin);
		if (l != 1) break;

		rsa_sign(out, (unsigned char*)inp, RSABYTESIZE, n1024_str, d1024_str);

		l = fwrite(out, RSABYTESIZE, 1, stdout);
		if (l != 1) break;
	}
	return 0;
}
