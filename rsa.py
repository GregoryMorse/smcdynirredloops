import random
#Could use Fermat's primality test first to potentially save time
#https://en.wikipedia.org/wiki/Safe_and_Sophie_Germain_primes
def is_safe_prime(n, k):
  #if (n % 3) != 2: return False #if (n % 6) != 5: return False
  if (n % 12) != 11: return False #n > 7
  #assert jacobi(3, n) == 1 and jacobi(12, n) == 1
  return is_all_prime([(n - 1) >> 1, n], [k >> 2, k >> 1])
  #return is_prime((n - 1) >> 1, k >> 2) and is_prime(n, k >> 1)
#https://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test
def is_all_prime(nl, kl): #Miller-Rabin test for k rounds
  if any(n < 3 or (n & 1) == 0 for n in nl): return False
  r, d, idxs = [1 for _ in nl], [n - 1 for n in nl], [i for i in range(len(nl))]
  for i in idxs:
    while d[i] & 1 == 0: #write n as 2^r*d where d odd
      r[i] += 1; d[i] >>= 1
  while len(idxs) != 0:
    if any(not miller_rabin(nl[i], d[i], r[i]) for i in idxs): return False
    for i in idxs: kl[i] -= 1
    idxs = [i for i in idxs if kl[i] != 0]
  return True #probably prime
def is_prime(n, k): #Miller-Rabin test for k rounds
  return is_all_prime([n], [k])
  if n < 3 or (n & 1) == 0: return False
  r, d = 1, n - 1
  while d & 1 == 0:
    r += 1; d >>= 1
  while k != 0:
    k -= 1
    if not miller_rabin(n, d, r): return False
  return True #probably prime
def miller_rabin(n, d, r):
  a = random.randint(2, n - 2)
  x = pow(a, d, n)
  if x == 1 or x == n - 1: return True
  for _ in range(r - 1):
    x = pow(x, 2, n)
    if x == n - 1: return True
  else: return False #composite
def find_prime(slambda, tester=is_prime):
  while True:
    p = random.randint(1 << slambda, 1 << (slambda+1))
    if tester(p, slambda): return p

def prime(x):
  import math
  for n in range(2, x):
    i = 2 #suggested k = math.isqrt(n)+1
    while (i < (math.isqrt(n)+1)) and (n % i) != 0:
      i += 1
    if (i >= (math.isqrt(n)+1)): yield n
def get_factors(x):
    factors = []
    for i in prime(x):
        if (x % i) == 0: factors.append(i); x //= i
        if x == 1: break
    return factors
#https://people.math.sc.edu/filaseta/ConsecutiveDigitallyDelicatePrimes2021.pdf
def find_cover(b): #An+B+d*b^k
    fact = get_factors(10)
    useprime = {}
    dset = {9} #{x for x in range(-b+1, 0)} | {x for x in range(1, b)}
    dprimes = {z: [] for z in dset}
    for z in prime(400):
        if z in fact: continue
        for d in list(dset):
            for k in range(1, 100):
                for offs in range(k):
                    bk = pow(b, offs, z)
                    db = (d * bk) % z
                    if db != 0 and (db * pow(b, k, z)) % z == db:
                        if not z in useprime: useprime[z] = db
                        if z in useprime and db == useprime[z]:
                            dprimes[d].append((z, offs, k))
                            if k == 1: dset.remove(d)
                            #break
                else: continue
                break
    print(dprimes, useprime)
#find_cover(2)
#find_cover(10)


import virt

def rsa32_params():
  p, q, e = 49499, 56003, 922655505
  n, phi, lbda = 2772092497, 2771986996, 1385993498
  d = 998692237
  return (e, n), (p, q, n, phi, lbda, e, d)
def rsa64_params():
  p, q, e = 4272191219, 2238754163, 3733368734696025201
  n, phi, lbda = 9564385876668294697, 9564385870157349316, 4782192935078674658
  d = 2915700395938489287
  return (e, n), (p, q, n, phi, lbda, e, d)
def rsa128_params():
  p, q, e = 17944549157829965687, 17337144904174756379, 147991534613895669455462982569179893663
  n, phi, lbda = 311107248989385205742476773349154367373, 311107248989385205707195079287149645308, 155553624494692602853597539643574822654
  d = 152905430276612922144768171953314686861
  return (e, n), (p, q, n, phi, lbda, e, d)
def rsa256_params():
  p, q, e = 289138703045082005708695539141295761407, 250064371879541069820815615080275108227, 31247486632901769226056358866015564630442511951876829452439547335197879641051
  n, phi, lbda = 72303288163033580603837904103026181713848958306456742618739602196963294795389, 72303288163033580603837904103026181713309755231532119543210091042741723925756, 36151644081516790301918952051513090856654877615766059771605045521370861962878
  d = 11939763764505489918510862380373093883334881403862563327789508654249642714057
  return (e, n), (p, q, n, phi, lbda, e, d)
def rsa512_params():
  p, q, e = 91446941653606303784098164498632228032931481827096111170892490426653602140719, 105549386277605392928996501630878979300579448809124650803557417258617686845767, 367676916253194814015086157899021841236851361100532580880251072843320650917946638859948564976479926691240298255018707972136376586438656312122115672160841
  n, phi, lbda = 9652168568502134220045432883256647288368230990384095935197969409129281931879808018361300632926941184105864705294605999472071198882366422699931277983486473, 9652168568502134220045432883256647288368230990384095935197969409129281931879611022033369421230228089439735194087272488541434978120391972792246006694499988, 4826084284251067110022716441628323644184115495192047967598984704564640965939805511016684710615114044719867597043636244270717489060195986396123003347249994
  d = 4056109299669358201498474142679216484708049838114760445574777369862909764129372415103891701823705292449878800503576908036395519856967382275541302503055205
  return (e, n), (p, q, n, phi, lbda, e, d)
def rsa1024_params():
  p = 7885808535207301034239713607139608507148672928247309074107137459938276543434170084679880437454084706535402300359854240247729931066619960244141783378438703
  q = 13261425151126008028299487639637729481078394556559634154160515703215248258278422035101537385794542447190282959934633182274277843734320286961025493304309127
  e = 27823265946233292894901223417581703022669104896270694389660105976150907656698268172739569336828831478808894284262700053001070636319480799679670822433266101056275827994012054027760345563873385744460227062280327794024603042487598911017166199651780517587871217509827192379587627893810273820860541524805946862731
  n, phi, lbda = 104577059645762246119363592952129339763263440023056136287410471974814114617050234573597054426416959663303203242631541454497672128231585522384724591861976252788848829346039485843197870312888602354516740679682283330110114809846836907137173661846754548627739151730796999030612553482840296261811084971371332942281, 104577059645762246119363592952129339763263440023056136287410471974814114617050234573597054426416959663303203242631541454497672128231585522384724591861976231641615143012730423303996623535550614127449255872739055062456951656322035194545053880428931300000585426045536704543190031475065495321563879804094650194452, 52288529822881123059681796476064669881631720011528068143705235987407057308525117286798527213208479831651601621315770727248836064115792761192362295930988115820807571506365211651998311767775307063724627936369527531228475828161017597272526940214465650000292713022768352271595015737532747660781939902047325097226
  d = 31422565321001067726008304050244872153428876571586233622513194036694831120322168272322165719693835678542672518998058962521108005504610529627915240508876113482793831978665892801462737571507798910257461176270711590198226046225469339438998231191974839280314092545146423775072931097360534624146462550199264367549
  #n, phi, lbda = gen_n_phi_lbda(p, q)
  #d = gen_d(e, lbda)
  return (e, n), (p, q, n, phi, lbda, e, d)
def print_rsa_params(slambda, pub, priv):
  print("RSA modulus size: %d" % (slambda * 2))
  print(("RSA Modulus: %0" + str(slambda * 2*2 // 8) + "X (%d)") % (pub[1], pub[1]))
  print(("Public key: %0" + str(slambda * 2*2 // 8) + "X (%d)") % (pub[0], pub[0]))
  print(("Private key: %0" + str(slambda * 2*2 // 8) + "X (%d)") % (priv[6], priv[6]))
  print(("p: %0" + str(slambda*2 // 8) + "X (%d)") % (priv[0], priv[0]))
  print(("q: %0" + str(slambda*2 // 8) + "X (%d)") % (priv[1], priv[1]))
  print(("phi: %0" + str(slambda * 2*2 // 8) + "X (%d)") % (priv[3], priv[3]))
  print(("lambda: %0" + str(slambda * 2*2 // 8) + "X (%d)") % (priv[4], priv[4]))

def gen_rsa_params(slambda):
  #RSA - generate 2 safe/Sophie Germain primes
  while True:
    p = find_prime(slambda-1, is_safe_prime)
    #print(p, virt.getBitSize(p))
    q = find_prime(slambda-1, is_safe_prime)
    #print(q, virt.getBitSize(q), virt.getBitSize(p*q))
    n, phi, lbda = gen_n_phi_lbda(p, q)
    if virt.getBitSize(n) == slambda * 2: break
  #e having a short bit-length and small Hamming weight results in more efficient encryption
  import math
  while True:
    e = random.randint(2, lbda-1)
    if math.gcd(e, lbda) == 1: break
  #e = 65537
  d = gen_d(e, lbda)
  lcm = phi // math.gcd(p-1, q-1)
  assert e * d % lcm == 1, e * d % lcm
  return (e, n), (p, q, n, phi, lbda, e, d)
def gen_n_phi_lbda(p, q):
  import math
  n = p * q
  #https://en.wikipedia.org/wiki/Euler%27s_totient_function#Computing_Euler's_totient_function
  phi = (p - 1) * (q - 1)
  lbda = phi//math.gcd(p-1, q-1)
  return n, phi, lbda
def gen_d(e, lbda):
  #d = (e ** (totient(phi)-1)) % phi #factoring phi is not reasonable
  #d = mul_inv(e, phi)
  #d = pow(e, totient(lbda)-1, lbda) #factoring lbda is not reasonable
  d = mul_inv(e, lbda)
  return d
def test_rsa_params():
  p, q, e = 61, 53, 17 #wikipedia
  #p, q, e = 
  n, phi, lbda = gen_n_phi_lbda(p, q)
  d = gen_d(e, lbda)
  return (e, n), (p, q, n, phi, lbda, e, d)
def run_modexp_virtual(inp, m, op, g, inpmap, outp, subg):
  inp %= m
  accepting = virt.run_virtual(op, g, 1, [inpmap[i] for i, x in enumerate(virt.zero_extend_num(virt.constant_to_virtual(inp), virt.getBitSize(m))) if x], inpmap, outp, subg)
  outv = virt.virtual_to_constant([x in accepting for x in outp])
  return outv
def rsa_encrypt(m, pub):
  e, n = pub
  randfunc = lambda i: b'\x01'*i #Random.get_random_bytes
  encsize = (virt.getBitSize(n)+7)//8
  pkcs = rsa_pkcs_1_15_pad(m, encsize, randfunc)
  res = virt.modexp(int.from_bytes(pkcs, 'big'), e, n)
  return res.to_bytes((virt.getBitSize(res)+7)//8, 'big')
def rsa_decrypt(c, priv):
  p, q, n, phi, lbda, e, d = priv
  #res = virt.modexp(int.from_bytes(c, 'big'), d, n) #pow(int.from_bytes(c, 'big'), d, n)
  B, R, Np, R2 = virt.toMontgomery(n)
  #res = virt.montgomeryREDC(virt.modexpMontgomery(virt.montgomeryREDC(int.from_bytes(c, 'big') * R2, B, R, n, Np), d, n, B, R, Np, R2), B, R, n, Np)
  node, g, op, subg = virt.make_graph()
  inp = virt.make_input(n.bit_length(), node, g, op)
  outp = virt.modexp_virtual(inp, d, n, node, g, op, subg)
  res = run_modexp_virtual(int.from_bytes(c, 'big'), n, op, g, inp, outp, subg)
  print(res, virt.montgomeryREDC(int.from_bytes(c, 'big') * R2, B, R, n, Np))
  #res = modexp_montgomery_ladder(int.from_bytes(c, 'big'), d, n)
  encsize = (virt.getBitSize(priv[2])+7)//8
  #res = modexp_crt(int.from_bytes(c, 'big'), d, p, q)
  #res = chinese_remainder([p,q], [virt.modexp(int.from_bytes(c, 'big'), d % (p-1), p), virt.modexp(int.from_bytes(c, 'big'), d % (q-1), q)])
  return pkcs1_decode(int.to_bytes(res, encsize, 'big'), encsize, 0)
#https://github.com/Legrandin/pycryptodome/blob/master/lib/Crypto/Util/asn1.py
def encode_oid(oid):
  comps = [int(x) for x in oid.split(".")]
  payload = bytes([40*comps[0]+comps[1]])
  for v in comps[2:]:
    if v == 0: enc = [0]
    else: 
      enc = []
      while v:
        enc.insert(0, (v & 0x7F) | 0x80)
        v >>= 7
      enc[-1] &= 0x7F
    payload += bytes(enc)
  return b'\x06' + payload
def encode_octet_string(s): return b'\x04' + s
def encode_null(): return b'\x05'
def encode_len(x): return bytes([x[0], len(x)-1, *x[1:]]) #works only for 7 bit lengths
def encode_sequence(seq, constructed=True):
  #0x20 C/Constructed=1, 0x40/0x80 Universal=0/0,Application=1/0,Context-Spec=0/1,Private=1/1
  return (b'\x10' if not constructed else b'\x30') + b''.join(encode_len(x) for x in seq)
def rsa_sig_pkcs_1_15_pad(data, bits):
  #https://datatracker.ietf.org/doc/html/rfc8017#section-9.2
  #DerSequence(DerSequence(DerObjectId(oid) + optional DerNull) + DerOctetString(data))
  #joint-iso-itu-t(2) country(16) us(840) organization(1)
  #gov(101) csor(3) nistalgorithm(4) hashAlgs(2)
  sha256_oid = "2.16.840.1.101.3.4.2.1" #https://en.wikipedia.org/wiki/X.690#DER_encoding
  digestInfo = encode_len(encode_sequence([encode_sequence([encode_oid(sha256_oid), encode_null()]), encode_octet_string(data)]))
  if bits < len(digestInfo) + 11: assert False
  return b'\x00\x01' + b'\xff'*(bits-len(digestInfo)-3) + b'\x00' + digestInfo
def rsa_sign_lib(c, pub, priv):
  assert len(c) == 256 // 8
  from Crypto.Signature import pkcs1_15
  from Crypto.Hash import SHA256
  from Crypto.PublicKey import RSA
  h = SHA256.new(); h.digest = lambda: c #h.update(c) #(virt.getBitSize(c) + 7) // 8
  crtq = mul_inv(priv[0], priv[1]) #p^-1 mod q
  signature = pkcs1_15.new(RSA.construct(rsa_components=(pub[1], pub[0], priv[6], priv[0], priv[1], crtq))).sign(h)
  encsize = (virt.getBitSize(pub[1])+7)//8
  pkcs = pkcs1_15._EMSA_PKCS1_V1_5_ENCODE(h, encsize)
  assert rsa_sig_pkcs_1_15_pad(h.digest(), encsize) == pkcs
  assert signature == int.to_bytes(pow(int.from_bytes(pkcs, 'big'), priv[6], pub[1]), encsize, 'big')
  return signature
def rsa_verify_lib(c, sig, pub, priv):
  from Crypto.Signature import pkcs1_15
  from Crypto.Hash import SHA256
  from Crypto.PublicKey import RSA
  h = SHA256.new(); h.digest = lambda: c #h.update(c)
  crtq = mul_inv(priv[0], priv[1]) #p^-1 mod q
  res = True
  try:
    pkcs1_15.new(RSA.construct(rsa_components=(pub[1], pub[0], priv[6], priv[0], priv[1], crtq))).verify(h, sig)
  except ValueError: res = False
  encsize = (virt.getBitSize(pub[1])+7)//8
  assert res == (rsa_sig_pkcs_1_15_pad(h.digest(), encsize) == int.to_bytes(pow(int.from_bytes(sig, 'big'), pub[0], pub[1]), encsize, 'big'))
  return res
def rsa_pkcs_1_15_pad(data, bits, randfunc):
  ps = []
  while len(ps) != bits - len(data) - 3:
    new_byte = randfunc(1)
    if new_byte == b'\x00': continue
    ps.append(new_byte)
  return b'\x00\x02' + b''.join(ps) + b'\x00' + data
#https://github.com/Legrandin/pycryptodome/blob/master/lib/Crypto/Cipher/PKCS1_v1_5.py
def rsa_encrypt_lib(c, pub, priv):
  from Crypto.PublicKey import RSA
  from Crypto.Cipher import PKCS1_v1_5
  crtq = mul_inv(priv[0], priv[1]) #p^-1 mod q
  randfunc = lambda i: b'\x01'*i #Random.get_random_bytes
  cipher_rsa = PKCS1_v1_5.new(RSA.construct(rsa_components=(pub[1], pub[0], priv[6], priv[0], priv[1], crtq)), randfunc=randfunc)
  #c = c.to_bytes((virt.getBitSize(c) + 7) // 8, 'big')
  enc = cipher_rsa.encrypt(c)
  encsize = (virt.getBitSize(pub[1])+7)//8
  pkcs = rsa_pkcs_1_15_pad(c, encsize, randfunc)
  assert enc == int.to_bytes(pow(int.from_bytes(pkcs, 'big'), pub[0], pub[1]), encsize, 'big')
  return enc
def pkcs1_decode(pkcs, encsize, minpad=8):
  #this needs to be constant-time
  assert len(pkcs) == encsize
  good, idx = True, 0
  for i in range(0, encsize):
    if i == 0: good &= pkcs[i] == 0
    elif i == 1: good &= pkcs[i] == 2
    elif i < 2+minpad: good &= pkcs[i] != 0
    else: val = (pkcs[i] == 0) & (idx == 0); idx = i*val+idx*(1-val)
  good &= idx != 0
  #good = pkcs[0] == 0 and pkcs[1] == 2 and all(pkcs[x] != 0 for x in pkcs[2:10]) and b'\x00' in pkcs[10:]
  #if good: idx = pkcs[10:].index(b'\x00')+10
  return pkcs[idx+1:] if good else None
def rsa_decrypt_lib(c, pub, priv):
  from Crypto.PublicKey import RSA
  from Crypto.Cipher import PKCS1_v1_5
  crtq = mul_inv(priv[0], priv[1]) #p^-1 mod q
  cipher_rsa = PKCS1_v1_5.new(RSA.construct(rsa_components=(pub[1], pub[0], priv[6], priv[0], priv[1], crtq)))
  #c = c.to_bytes((virt.getBitSize(c) + 7) // 8, 'big')
  dec = cipher_rsa.decrypt(c, None)
  encsize = (virt.getBitSize(pub[1])+7)//8
  res = pkcs1_decode(int.to_bytes(pow(int.from_bytes(c, 'big'), priv[6], pub[1]), encsize, 'big'), encsize)
  assert dec == res
  return dec
def save_rsa_virtual(op, g, inpmap, outp, subg, bits):
  virt.virt_to_c("rsa" + str(bits), "RSA_" + str(bits), op, g, 10+1, inpmap, outp, subg)
def gen_rsa(bits, pub, priv):
  p, q, n, phi, lbda, e, d = priv
  #res = virt.modexp(int.from_bytes(c, 'big'), d, n) #pow(int.from_bytes(c, 'big'), d, n)
  B, R, Np, R2 = virt.toMontgomery(n)
  #res = virt.montgomeryREDC(virt.modexpMontgomery(virt.montgomeryREDC(int.from_bytes(c, 'big') * R2, B, R, n, Np), d, n, B, R, Np, R2), B, R, n, Np)
  node, g, op, subg = virt.make_graph()
  inp = virt.make_input(n.bit_length(), node, g, op)
  outp = virt.modexp_virtual(inp, d, n, node, g, op, subg)
  save_rsa_virtual(op, g, inp, outp, subg, bits)
def rsa_sec():
  #for secbits in (32, 64, 128, 256, 512, 1024):
  #  print_rsa_params(secbits // 2, *gen_rsa_params(secbits // 2))
  #minimum RSA encryption per PKCS is 2+8+1 + 1 encrypted byte = 12 bytes or 96 bits
  #minimum RSA signature depends on hash scheme for SHA256, it is 2+8+1 + 19 bytes DER encoding + 32 bytes = 62 bytes or 496 bits (RSA-150)
  for secbits, f in ((32, rsa32_params), (64, rsa64_params), (128, rsa128_params), (256, rsa256_params), (512, rsa512_params), (1024, rsa1024_params)):
    #print_rsa_params(secbits // 2, *f())
    m = b'\x01' * (secbits // 8 - 3)
    pub, priv = f()
    gen_rsa(secbits, pub, priv)
    c = rsa_encrypt(m, pub)
    assert m == rsa_decrypt(c, priv)
    #print(virt.getBitSize(pub[1]))
  #print("%0128X" % int.from_bytes(rsa_encrypt_lib(m, pub, priv), 'big'))

  pub, priv = rsa1024_params()
  m=b'Hello world!!!!\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'
  assert m == rsa_decrypt_lib(rsa_encrypt_lib(m, pub, priv), pub, priv)
  #print("%0128X" % int.from_bytes(rsa_sign_lib(m, pub, priv), 'big'))
  assert rsa_verify_lib(m, rsa_sign_lib(m, pub, priv), pub, priv)
rsa_sec()