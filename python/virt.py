import graph
import os, random
if os.environ.get('SMCIRRED_SEED'): random.seed(int(os.environ['SMCIRRED_SEED'])) #optional reproducible graph regeneration (L05)

def getBitSize(num): return num.bit_length()
def countSetBits(n):
  count = 0
  while n != 0: n, count = n & (n-1), count+1
  return count
#https://web.ece.ucsb.edu/~parhami/pubs_folder/parh88-ieeetc-add-recoded-bsd.pdf
def to_bsd(num): #binary signed digit
  if num < 0:
    return [1 if ((1 << i) & num) != 0 else 0 for i in range(getBitSize(-num))] + [-1]
  else:
    return [1 if ((1 << i) & num) != 0 else 0 for i in range(getBitSize(num))]
def from_bsd(bsd):
  a, borrow = [], False
  for x in bsd:
    if x == -1: a.append(0 if borrow else 1); borrow = True
    elif x == 0: a.append(1 if borrow else 0)
    else: a.append(0 if borrow else 1); borrow = False
  num = 0
  for i, x in enumerate(a):
    if borrow and i == len(a) - 1: num -= (1 << i)
    elif x: num += (1 << i)
  return num
def bsd_neg(bsd): return [-x for x in bsd]
def to_rbsd(bsd): #recoded binary signed digit for carry-free addition
  enc1 = {-1: 0, (0, -1): 0, (0, 0): 1, (0, 1): 1, 1: 1}
  enc2 = {-1: -1, (0, -1): -1, (0, 0): 0, (0, 1): 0, 1: 0}
  enc3 = {-1: 1, 0: -1, 1: -1}
  recoding = ((enc1, enc3, enc2),
              (enc2, 0, enc1),
              (enc1, enc3, enc2))
  i3, i2, i1 = 0, 0, 0
  a = []
  for i in bsd + [0]:
    l = recoding[i+1][i1+1]
    if isinstance(l, int): a.append(l)
    elif i2 in l: a.append(l[i2])
    else: a.append(l[(i2, i3)])
    i3, i2, i1 = i2, i1, i
  return a
def add_rbsd(num1, num2, issub=False):
  table = (
    ({0: 0, (1, 0): 0, (1, 1): 1}, {0: -1, (1, -1): -1, (1, 0): -1, (1, 1): 0}, 0),
    ({(None, 0): -1, (-1, 1): -1, (0, 1): -1, (1, 1): 0},
     {(-1, -1): -1, (None, 0): 0, (-1, 1): 0, 0: 0, (1, -1): 0, (1, 1): 1},
     {(-1, -1): 0, (None, 0): 1, (0, -1): 1, (1, -1): 1}),
    (0, {(-1, -1): 0, (-1, 0): 1, (-1, 1): 1, 0: 1}, {(-1, -1): -1, (-1, 0): 0, 0: 0}))
  x1, y1 = 0, 0
  if issub: num2 = bsd_neg(num2)
  a = []
  for i in range(max(len(num1), len(num2))+1):
    x = num1[i] if i < len(num1) else 0
    y = num2[i] if i < len(num2) else 0
    l = table[x+1][y+1]
    if isinstance(l, int): a.append(l)
    elif x1 in l: a.append(l[x1])
    elif (None, y1) in l: a.append(l[(None, y1)])
    else: a.append(l[(x1, y1)])
    x1, y1 = x, y
  return a
def get_consec_ones(num):
  i = 0
  pos = []
  while num != 0:
    while (num & 1) == 0: i+=1; num >>= 1
    j = 0
    while (num & 1) == 1: i+=1; j+=1; num >>= 1
    if j == 1: pos.append(i)
    else: pos.append(j-i-1); pos.append(i+1)
  return tuple(pos)
def consec_ones_to_num(pos):
  num = 0
  for i in pos:
    if i >= 0: num += 1 << (i-1)
    else: num += -(1 << (-i-1))
  return num
def str_consec_ones(pos):
  s = ""
  for i in reversed(pos):
    if i >= 0: s += "+2^" + str(i-1)
    else: s += "-2^" + str(-i-1)
  return s
def addition(num1, num2, bits, issub=False):
  #return num1+num2
  doop = (lambda a, b, c: a+b+c) if not issub else (lambda a, b, c: a-b-c)
  tblsize = 4
  addtables = [[doop(a, b, 0) for b in range(1 << tblsize)] for a in range(1 << tblsize)]
  addtablesc = [[[doop(a, b, c) for c in range(2)] for b in range(1 << tblsize)] for a in range(1 << tblsize)]
  if bits <= tblsize:
    assert addtables[num1][num2] == doop(num1, num2, 0)
    return addtables[num1][num2]
  else:
    result = 0
    mask = (1 << tblsize) - 1
    carry = 0
    for i in range(0, bits, tblsize):
      if i == 0: res = addtables[(num1 & mask) >> i][(num2 & mask) >> i]
      else: res = addtablesc[(num1 & mask) >> i][(num2 & mask) >> i][carry]
      carry = res >> tblsize
      result |= (res << i) & mask
      mask <<= tblsize
    if carry: result |= carry << bits
    assert result == doop(num1, num2, 0)
    return result

def _extended_gcd(a, b):
    """
    Division in integers modulus p means finding the inverse of the
    denominator modulo p and then multiplying the numerator by this
    inverse (Note: inverse of A is B such that A*B % p == 1) this can
    be computed via extended Euclidean algorithm
    http://en.wikipedia.org/wiki/Modular_multiplicative_inverse#Computation
    """
    x = 0
    last_x = 1
    y = 1
    last_y = 0
    while b != 0:
        quot = a // b
        a, b = b, a % b
        x, last_x = last_x - quot * x, x
        y, last_y = last_y - quot * y, y
    return last_x, last_y
def _divmod(num, den, p):
    """Compute num / den modulo prime p

    To explain what this means, the return value will be such that
    the following is true: den * _divmod(num, den, p) % p == num
    """
    inv, _ = _extended_gcd(den, p)
    return num * inv
#https://rosettacode.org/wiki/Chinese_remainder_theorem#Python_3.6
def chinese_remainder(n, a):
    from functools import reduce
    sum = 0
    prod = reduce(lambda a, b: a*b, n)
    for n_i, a_i in zip(n, a):
        p = prod // n_i
        sum += a_i * mul_inv(p, n_i) * p
    return sum % prod
def max_mul_inv(a, b):
  if a == 1: return 0# or b == 1: return 0
  import math
  m = max(a, b)
  return (1 if a < b else 0) + math.floor(math.log(m, (1 + math.sqrt(5)) / 2))
def mul_inv_rounds(a, b):
    #if b == 1: return 0
    if a < 0: a %= b
    b0 = b
    x0, x1 = 0, 1
    rounds = 0
    while a > 1: #need to know the precise maximum number of times this loop can execute log_phi b
        q = a // b
        a, b = b, a%b
        x0, x1 = x1 - q * x0, x0
        rounds += 1
    return rounds
#https://link.springer.com/content/pdf/10.1007%2F3-540-36400-5_6.pdf
def mul_inv_bin_rounds(a, p): #only for prime p!
  if a == 1: return 0
  u, v, r, s, k, rounds = p, a, 0, 1, 0, 0
  while v > 0:
    while (u & 1) == 0: #max getBitSize(p)-1 iterations
      if (r & 1) == 0: r >>= 1
      else: r = (r+p) >> 1
      u, k = u >> 1, k+1
    while (v & 1) == 0: #max getBitSize(p)-1 iterations
      if (s & 1) == 0: s >>= 1
      else: s = (s+p) >> 1
      v, k = v >> 1, k+1
    x = u - v #max getBitSize(p) iterations
    if x > 0:
      u, r = x, r - s
      if r < 0: r += p
    else:
      v, s = -x, s - r
      if s < 0: s += p
    rounds += 1
  #if r > p: r -= p
  #if r < 0: r += p
  return rounds #n <= k <= n+n
def mul_inv_bin(a, p): #only for prime p!
  if a == 1: return 1
  u, v, r, s, k = p, a, 0, 1, 0
  while v > 0:
    while (u & 1) == 0:
      if (r & 1) == 0: r >>= 1
      else: r = (r+p) >> 1
      u, k = u >> 1, k+1; continue
    while (v & 1) == 0:
      if (s & 1) == 0: s >>= 1
      else: s = (s+p) >> 1
      v, k = v >> 1, k+1; continue
    x = u - v
    if x > 0:
      u, r = x, r - s
      if r < 0: r += p
    else:
      v, s = -x, s - r
      if s < 0: s += p
  #if r > p: r -= p
  #if r < 0: r += p
  return r #n <= k <= n+n

def mul_inv(a, b):
    #if b == 1: return 0
    if a < 0: a %= b
    b0 = b
    x0, x1 = 0, 1
    while a > 1: #need to know the precise maximum number of times this loop can execute log_phi b
        q = a // b
        a, b = b, a%b
        x0, x1 = x1 - q * x0, x0
    if x1 < 0: x1 += b0
    return x1
def mul_invMontgomery(a, b, B, R, Np, R2):
  R3 = montgomeryREDC(R2 * R2, B, R, b, Np) #(R*R*R) % b
  return montgomeryREDC(mul_inv(a, b)*R3, B, R, b, Np)
def mul_inv_almostMontgomery(a, p, inpm=False, outm=True):
  u, v, r, s, k = p, a, 0, 1, 0
  while v > 0:
    if (u & 1) == 0:
      u, s = u >> 1, s << 1
    elif (v & 1) == 0:
      v, r = v >> 1, r << 1
    else:
      x = v - u
      if x < 0: u, r, s = (-x) >> 1, r + s, s << 1
      else: v, s, r = x >> 1, r + s, r << 1
    k += 1
  if r >= p: r -= p
  r = p - r
  if inpm and outm:
    #B, R, Np, R2 = toMontgomery(p)
    #return montgomeryREDC(montgomeryREDC(r*R2, B, R, p, Np) << (2*getBitSize(p)-k), B, R, p, Np)
    for i in range(2*getBitSize(p)-k):
      r <<= 1
      if r >= p: r -= p
  else:
    for i in range(k - getBitSize(p) if inpm or outm else k):
      if (r & 1) == 0: r >>= 1
      else: r = (r + p) >> 1
  return r
#https://eprint.iacr.org/2020/972.pdf
#https://github.com/pornin/bingcd
def mul_inv_eff(y, m, k=32):
  a, u, b, v = y, 1, m, 0
  for i in range(1, ((m.bit_length()<<1)-1+k-1)//k+1):
    n = max(k << 1, a.bit_length(), b.bit_length())
    abar = (a & ((1 << (k-1))-1)) + ((a >> (n-k-1)) << (k-1))
    bbar = (b & ((1 << (k-1))-1)) + ((b >> (n-k-1)) << (k-1))
    f0, g0, f1, g1 = 1, 0, 0, 1
    for j in range(1, k):
      if (abar & 1) == 0: abar >>= 1
      else:
        if abar < bbar:
          abar, bbar, f0, g0, f1, g1 = bbar, abar, f1, g1, f0, g0
        abar = (abar - bbar) >> 1
        f0, g0 = f0 - f1, g0 - g1
      f1 <<= 1; g1 <<= 1
    a, b = (a*f0+b*g0) >> (k-1), (a*f1+b*g1) >> (k-1)
    if a < 0: a, f0, g0 = -a, -f0, -g0
    if b < 0: b, f1, g1 = -b, -f1, -g1
    u, v = (u * f0 + v * g0) % m, (u * f1 + v * g1) % m
  v = (v * mul_inv((1 << (k-1)*(((m.bit_length()<<1)-1+k-2) // (k-1))) % m, m)) % m
  if b != 1: return 0
  return v
#https://www.rookieslab.com/posts/extended-euclid-algorithm-to-find-gcd-bezouts-coefficients-python-cpp-code
def extended_euclid_gcd(a, b):
    """
    Returns a list `result` of size 3 where:
    Referring to the equation ax + by = gcd(a, b)
        result[0] is gcd(a, b)
        result[1] is x
        result[2] is y 
    """
    s = 0; old_s = 1
    t = 1; old_t = 0
    r = b; old_r = a

    while r != 0:
        quotient = old_r//r # In Python, // operator performs integer or floored division
        # This is a pythonic way to swap numbers
        # See the same part in C++ implementation below to know more
        old_r, r = r, old_r - quotient*r
        old_s, s = s, old_s - quotient*s
        old_t, t = t, old_t - quotient*t
    return [old_r, old_s, old_t]
def montgomeryBound(T, N, issub=False):
  return (T + N if T < 0 else T) if issub else (T - N if T >= N else T)
#https://en.wikipedia.org/wiki/Montgomery_modular_multiplication
def montgomeryREDC(T, B, R, N, Np):
  #REDC algorithm
  if B == 0:
    m = ((T % R) * Np) % R
    t = (T + m * N) // R
  else:
    m = ((T & (R-1)) * Np) & (R-1)
    t = (T + m * N) >> B
  return montgomeryBound(t, N) #t - N if t >= N else t
def montgomeryREDC_eff(T, B, R, N, Np):
  x = T
  for i in range(B):
    x = (x + (N if (1 & x) != 0 else 0)) >> 1
  return montgomeryBound(x, N)
def montgomeryREDC_mul_eff(T0, T1, B, R, N, Np): #1990 Dusse and Kaliski
  #Rp = mul_inv(R, N)
  x = 0
  #n0p = 1 #-mul_inv(N & 1, 2) % 2 #R, N are coprime and R is power of 2 so N always odd, e.g. fix this at 1
  for i in range(B):
    x += T1 if ((T0 >> i) & 1) == 1 else 0
    #y = n0p & x
    x = (x + (N if (1 & x) != 0 else 0)) >> 1
  #print((T0 * T1 * mul_inv(R, N)) % N, x)
  return montgomeryBound(x, N)
def toMontgomery(m):
  B = getBitSize(m)
  R = 1 << B
  Rp, Np = extended_euclid_gcd(R, m)[1:]
  Np = -Np % R
  R2 = (R*R) % m
  return B, R, Np, R2
def modexpMontgomery(b, e, m, B, R, Np, R2):
  assert (m & 1) != 0 #coprime only if non-even modulus
  if m == 1: return 0
  result = montgomeryREDC(R2, B, R, m, Np)
  #modmul = lambda a, b, m: montgomeryREDC(a * b, B, R, m, Np)
  while e > 0:
    if (e & 1) != 0: result = montgomeryREDC(result * b, B, R, m, Np)
    e >>= 1
    b = montgomeryREDC(b * b, B, R, m, Np)
  return result
def modexpMontgomeryWindow(b, e, m, B, R, Np, R2):
  assert (m & 1) != 0 #coprime only if non-even modulus
  if m == 1: return 0
  res = montgomeryREDC(R2, B, R, m, Np)
  #scalar products B, window reduction to ((B+w-1) // w)+(1<<w)-2 scalar products, transition points at 2,6,27,103,333,976
  w = min((((B+w-1) // w)+(1<<w)-2, w) for w in range(1, B.bit_length()))[1] #3 for 64, 4 for 128/256, 5 for 512, 6 for 1024/2048, 7 for 4096
  tbl = {0: res, 1: b}
  for j in range(2, 1<<w):
    if (j & 1) == 0 and (j >> 1) in tbl: tbl[j] = montgomeryREDC(tbl[j>>1]*tbl[j>>1], B, R, m, Np)
    else: tbl[j] = montgomeryREDC(tbl[j-1] * b, B, R, m, Np)
  for j in range(((B+w-1) // w)-1, -1, -1):
    res = montgomeryREDC(tbl[e >> (j * w) & ((1 << w)-1)] * res, B, R, m, Np)
    if j == 0: break
    for i in range(w):
      res = montgomeryREDC(res * res, B, R, m, Np)
  return res
def mulKaratsuba(num1, num2, num1bits, num2bits):
  m = min(num1bits, num2bits)
  m2 = m >> 1
  m2shift = (1 << m2) - 1
  low1 = num1 & m2shift
  low2 = num2 & m2shift
  high1 = num1 >> m2
  high2 = num2 >> m2
  z0 = doBigMul(low1, low2, m2, m2)
  z2 = doBigMul(high1, high2, num1bits - m2, num2bits - m2)
  if num1 == num2:
    z1 = doBigMul(low1, high1, m2, num1bits - m2)
    return ((z2 << (m2 << 1)) | z0) + (z1 << (m2+1))
  else:
    lowhigh1, lowhigh2 = low1 + high1, low2 + high2
    z1 = doBigMul(lowhigh1, lowhigh2, num1bits - m2 + 1, num2bits - m2 + 1)
    return ((z2 << (m2 << 1)) | z0) + ((z1 - z0 - z2) << m2)
def doBigMul(num1, num2, num1bits, num2bits):
  if (num1 <= 0xFFFFFFFF and num2 <= 0xFFFFFFFF):
    return num1 * num2
  if (num1 <= 0xFFFFFFFF or num2 <= 0xFFFFFFFF or
      num1bits <= 4096 or num2bits <= 4096): return num1 * num2 #experimentally determined threshold 8192 is next best
                                                                #if (num1bits >= 1728 * 64 and num2bits >= 1728 * 64)
                                                                #return mulSchonhageStrassen(num1, num2, num1bits, num2bits)
  return mulKaratsuba(num1, num2, num1bits, num2bits)
def bigMul(num1, num2):
  signum = (-1 if num1 < 0 else 1) * (-1 if num2 < 0 else 1)
  if (num1 < 0): num1 = -num1
  if (num2 < 0): num2 = -num2
  res = doBigMul(num1, num2, getBitSize(num1), getBitSize(num2))
  return -res if signum < 0 else res

def modmul(a, b, m):
  #return (a*b)%m
  d, mp2 = 0, m >> 1
  if a >= m or a < 0: a %= m
  if b >= m or b < 0: b %= m
  bits = getBitSize(a)
  if bits == 0: return 0
  check = 1 << (bits - 1)
  for i in range(bits):
    d = (d << 1) - m if (d > mp2) else d << 1
    if (a & check) != 0: d += b
    if d >= m: d -= m
    a <<= 1
  return d
  
#https://en.wikipedia.org/wiki/Modular_exponentiation
def modexp(b, e, m):
  if m == 1: return 0
  result = 1
  b = b % m
  while e > 0:
    if (e & 1) != 0: result = modmul(result, b, m)
    e >>= 1
    b = modmul(b, b, m)
  return result
def modexp_montgomery_ladder(b, e, m):
  x1, x2 = b, modmul(b, b, m)
  for i in range(getBitSize(e)-2, -1, -1):
    if (e & (1 << i)) == 0: x2, x1 = modmul(x1, x2, m), modmul(x1, x1, m)
    else: x1, x2 = modmul(x1, x2, m), modmul(x2, x2, m)
  return x1
def modexp_crt(b, d, p, q):
  if p == 1 or q == 1: return 0
  dp, dq = d % (p-1), d % (q-1)
  qinv = mul_inv(q, p)
  m1 = modexp(b, dp, p)
  m2 = modexp(b, dq, q)
  h = (qinv * (m1 - m2)) % p
  return (m2 + h * q) % (p * q)
  
FLOW_OP, ADD_OP, ADDNEG_OP, ANY_OP, SUBG_OP, TBL_OP = 1, 2, 3, 4, 5, 6 #AND, XOR, XNOR, OR, reusable unit, compressed constant selection
THRESHOLD = 4096
BITSZ = 1
def reduce_graph(op, pred, g, inp, outp):
  s = set()
  for x in g:
    if x in outp or x in inp: continue
    if len(g[x]) == 0: s.add(x)
  while len(s) != 0:
    x = s.pop()
    for y in pred[x]: #duplicate successors possible
      while x in g[y]:
        g[y].remove(x)
      if len(g[y]) == 0 and not y in outp and not y in inp: s.add(y)      
    del op[x]
    del pred[x]
    del g[x]
def subg_to_virt_c(f, pre, funcname, op, g, inpmap, outmap, s):
  pred = graph.succ_to_pred(g)
  #deporder, levels = graph.topo_kahn_levels(g)
  deporder = graph.topo_kahn(g, randomize=True)
  mp = {}; ct = 0#; inp = set(inpmap)
  for x in deporder:
    mp[x] = ct; ct += 1
  f.write("S inpmap" + str(pre) + "[] = { " + ",".join(str(mp[z]) for z in inpmap) + " };\n")
  f.write("S outp" + str(pre) + "[] = { " + ",".join(str(mp[z]) for z in outmap) + " };\n")
  repeatmap = {}
  for x in g:
    if len(pred[x]) != 0:
      if not frozenset(pred[x]) in repeatmap:
        repeatmap[frozenset(pred[x])] = "g" + str(pre) + "_" + hex(x)[2:]
        f.write("S g" + str(pre) + "_" + hex(x)[2:] + "[]={" + ",".join(str(mp[y]) for y in pred[x]) + "};\n")
      if type(op[x]) is tuple:
        f.write("S gi" + str(pre) + "_" + str(x) + "[] = {" + ",".join(str(mp[y]) for y in op[x][2]) + "};\n")
        f.write("S go" + str(pre) + "_" + str(x) + "[] = {" + ",".join(str(mp[y]) if y in mp else "~0UL" for y in op[x][3]) + "};\n")
        for y in op[x][3]:
          if y in pred: repeatmap[frozenset(pred[y])] = ""
        #f.write("const SS ss" + str(pre) + "_" + str(x) + " = {gi" + str(pre) + "_" + str(x) + ", sizeof(gi" + str(pre) + "_" + str(x) + ")/sizeof(L), go" + str(pre) + "_" + str(x) + ", sizeof(go" + str(pre) + "_" + str(x) + ")/sizeof(L), &s" + str(s[op[x][1]]) + "};\n")
        f.write("static const SS ss" + str(pre) + "_" + str(x) + " = {" + repeatmap[frozenset(pred[x])] + ", gi" + str(pre) + "_" + str(x) + ", " + str(len(op[x][2])) + ", go" + str(pre) + "_" + str(x) + ", " + str(len(op[x][3])) + ", &s" + str(s[op[x][1]]) + ", " + str(op[x][4]) + "};\n")
  f.write("static const VMO g_" + str(pre) + "[] = {" + ",".join("{" + str(op[x][0] if type(op[x]) is tuple else op[x]) + "," + str(len(pred[x]) if len(pred[x]) != 0 and repeatmap[frozenset(pred[x])] != "" else 0) + "," + (("&ss" + str(pre) + "_" + str(x) if type(op[x]) is tuple else repeatmap[frozenset(pred[x])]) if len(pred[x]) != 0 else "") + "}" + ("\n\t" if (i % 50) == 49 else "") for i, x in enumerate(deporder)) + "};\n")
  f.write("unsigned char d" + funcname + str(pre) + "[" + str(len(g)) + "] = {0};\n")
  f.write("static const SG s" + str(pre) + " = { inpmap" + str(pre) + ", outp" + str(pre) + ", g_" + str(pre) + ", d" + funcname + str(pre) + ", sizeof(d" + funcname + str(pre) + ") };\n")

def graph_to_virt_c(fname, funcname, op, g, pred, deporder, inpmap, outp, subg):
  mp = {}; ct = 0#; inp = set(inpmap)
  for x in deporder:
    mp[x] = ct; ct += 1
  with open(fname + "vm.c", "w") as f:
    f.write("#define S static L\n")
    f.write("typedef const unsigned int L;\n")
    f.write("void zm(unsigned char*, unsigned long);\n")
    f.write("void load_input(const unsigned char*, unsigned long, L*, unsigned char*);\n")
    f.write("void read_output(unsigned char*, unsigned long, L*, unsigned char*);\n")
    if not subg is None:
      f.write("#pragma pack(push, 1)\n")
      f.write("typedef struct VMO { unsigned char o; unsigned short l; const void* a; } VMO;\n")
      f.write("typedef struct SG { L* ip; L* op; const VMO* v; unsigned char* d; unsigned long l; } SG;\n")
      f.write("typedef struct SS { L* p; L* ip; unsigned long il; L* op; unsigned long ol; const SG* sg; unsigned long r; } SS;\n")
      f.write("#pragma pack(pop)\n")
      s = {}; ct = 0
      for x in subg:
        s[x] = ct; ct += 1
      for x in subg:
        subg_to_virt_c(f, s[x], funcname, subg[x][1], subg[x][0], subg[x][2], subg[x][3], s)
    else:
      f.write("#pragma pack(push, 1)\n")
      f.write("typedef struct VMO { unsigned char o; unsigned short l; L* a; } VMO;\n")
      f.write("#pragma pack(pop)\n")
    f.write("void run_vm(unsigned long, const VMO*, unsigned char*);\n")
    f.write("S inpmap[] = { " + ",".join(str(mp[z]) for z in inpmap) + " };\n")
    f.write("S outmap[] = { " + ",".join(str(mp[z]) for z in outp) + " };\n")
    repeatmap = {}
    for x in g:
      if len(pred[x]) != 0:
        if not frozenset(pred[x]) in repeatmap:
          repeatmap[frozenset(pred[x])] = "g" + hex(x)[2:]
          f.write("S g" + hex(x)[2:] + "[]={" + ",".join(str(mp[y]) for y in pred[x]) + "};\n")
        if type(op[x]) is tuple:
          f.write("S gi" + str(x) + "[] = {" + ",".join(str(mp[y]) for y in op[x][2]) + "};\n")
          f.write("S go" + str(x) + "[] = {" + ",".join(str(mp[y]) if y in mp else "~0U" for y in op[x][3]) + "};\n")
          for y in op[x][3]:
            if y in pred: repeatmap[frozenset(pred[y])] = ""
          #f.write("const SS ss" + str(x) + " = {gi" + str(x) + ", sizeof(gi" + str(x) + ")/sizeof(L), go" + str(x) + ", sizeof(go" + str(x) + ")/sizeof(L), &s" + str(s[op[x][1]]) + "};\n")
          f.write("static const SS ss" + str(x) + " = {" + repeatmap[frozenset(pred[x])] + ", gi" + str(x) + ", " + str(len(op[x][2])) + ", go" + str(x) + ", " + str(len(op[x][3])) + ", &s" + str(s[op[x][1]]) + ", " + str(op[x][4]) + "};\n")
    f.write("static const VMO g[] = {" + ",".join("{" + str(op[x][0] if type(op[x]) is tuple else op[x]) + "," + str(len(pred[x]) if len(pred[x]) != 0 and repeatmap[frozenset(pred[x])] != "" else 0) + "," + (("&ss" + str(x) if type(op[x]) is tuple else repeatmap[frozenset(pred[x])]) if len(pred[x]) != 0 else "") + "}" + ("\n\t" if (i % 50) == 49 else "") for i, x in enumerate(deporder)) + "};\n")
    f.write("unsigned char d" + funcname + "[" + str(len(g)) + "] = {0};\n")
    if not subg is None:
      f.write("unsigned char scrtch"+fname+"[" + str(max(max(len(subg[x][2]), len(subg[x][3])) for x in subg)) + "] = {0};\n")
    f.write("void " + funcname + "_obf_virt_encrypt(unsigned char* out, const unsigned char* in)\n{\n")
    f.write("\tzm(d" + funcname + ", sizeof(d" + funcname + "));\n")
    f.write("\tload_input(in, " + str(len(inpmap)//BITSZ//8) + ", inpmap, d" + funcname + ");\n")
    f.write("\trun_vm(sizeof(d" + funcname + "), g, d" + funcname + ");\n")
    f.write("\tread_output(out, " + str(len(outp)//BITSZ//8) + ", outmap, d" + funcname + ");\n")
    f.write("}\n")
def subg_to_virt_c_opt(f, pre, funcname, op, g, inpmap, outmap, iomap, s, nodetable, edgetable, subgraphtable, subgmaptable):
  pred = graph.succ_to_pred(g)
  #deporder, levels = graph.topo_kahn_levels(g)
  deporder = graph.topo_kahn(g, randomize=True)
  mp = {}; ct = 0#; inp = set(inpmap)
  for x in deporder:
    mp[x] = ct; ct += 1
  base = len(nodetable)
  nodetable.extend([None] * len(g))
  edgeinpmap = len(edgetable)
  edgetable += [base+mp[z] for z in inpmap]
  edgeoutmap = len(edgetable)
  edgetable += [base+mp[z] for z in outmap]
  edgeiomap = len(edgetable)
  edgetable += iomap
  repeatmap = {}
  for x in g:
    if len(pred[x]) != 0:
      if not frozenset(pred[x]) in repeatmap:
        repeatmap[frozenset(pred[x])] = len(edgetable)
        edgetable += [base+mp[y] for y in pred[x]]
      if type(op[x]) is tuple and op[x][0] == SUBG_OP:
        gi = len(edgetable)
        edgetable += [base+mp[y] for y in op[x][2]]
        go = len(edgetable)
        edgetable += [base+mp[y] if y in mp else -1 for y in op[x][3]]
        for y in op[x][3]:
          if y in pred: repeatmap[frozenset(pred[y])] = -1
        subgmaptable.append((repeatmap[frozenset(pred[x])], gi, len(op[x][2]), go, len(op[x][3]), s[op[x][1]], op[x][4]))
      elif type(op[x]) is tuple and op[x][0] == TBL_OP:
        sels = [y[0] for y in op[x][1]]
        if not tuple(sels) in repeatmap:
          gi = len(edgetable)
          edgetable += [base+mp[y[0]] for y in op[x][1]]
          repeatmap[tuple(sels)] = gi
        else: gi = repeatmap[tuple(sels)]
        gmap = len(edgetable)
        inttbl = [x for y in op[x][2] for x in y]
        edgetable += [virtual_to_constant(inttbl[i*32*BITSZ:(i+1)*32*BITSZ]) for i in range((len(inttbl)//BITSZ+31)//32)]
        tbli = len(edgetable)
        edgetable += [repeatmap[frozenset(pred[x])], len(op[x][1]), gi, gmap]
    nodetable[base+mp[x]] = ((op[x][0] if type(op[x]) is tuple else op[x]) | (len(pred[x]) if len(pred[x]) != 0 and repeatmap[frozenset(pred[x])] != -1 else 0) << 3, (len(subgmaptable)-1 if type(op[x]) is tuple and op[x][0] == SUBG_OP else (tbli if type(op[x]) is tuple and op[x][0] == TBL_OP else repeatmap[frozenset(pred[x])])) if len(pred[x]) != 0 else 0)
  subgraphtable.append((edgeinpmap, edgeoutmap, edgeiomap, base, len(g)))
def c_escape():
  import string
  mp = []
  for c in range(256):
    if c == ord('\\'): mp.append("\\\\")
    elif c == ord('?'): mp.append("\\?")
    elif c == ord('\''): mp.append("\\'")
    elif c == ord('"'): mp.append("\\\"")
    elif c == ord('\a'): mp.append("\\a")
    elif c == ord('\b'): mp.append("\\b")
    elif c == ord('\f'): mp.append("\\f")
    elif c == ord('\n'): mp.append("\\n")
    elif c == ord('\r'): mp.append("\\r")
    elif c == ord('\t'): mp.append("\\t")
    elif c == ord('\v'): mp.append("\\v")
    elif chr(c) in string.printable: mp.append(chr(c))
    else:
      x = "\\%03o" % c
      mp.append(x if c>=64 else (("\\%%0%do" % (1+c>=8)) % c, x))
  return mp
  
def graph_to_virt_c_opt(fname, funcname, op, g, pred, deporder, inpmap, outp, subg, isstr=True):
  mp = {}; ct = 0#; inp = set(inpmap)
  for x in deporder:
    mp[x] = ct; ct += 1
  nodetable, edgetable, subgraphtable, subgmaptable = [], [], [], []
  with open(fname + "vm" + ("str" if isstr else "") + ".c", "wb") as f:
    f.write("#pragma GCC optimize (\"O3\")\n".encode('ascii'))
    f.write("typedef const unsigned int L;\n".encode('ascii'))
    f.write("void zm(unsigned char*, unsigned long);\n".encode('ascii'))
    f.write("void load_input(const unsigned char*, unsigned long, L*, unsigned char*);\n".encode('ascii'))
    f.write("void read_output(unsigned char*, unsigned long, L*, unsigned char*);\n".encode('ascii'))
    if not subg is None:
      s = {}; ct = 0
      for x in subg:
        s[x] = ct; ct += 1
      for x in subg:
        subg_to_virt_c_opt(f, s[x], funcname, subg[x][1], subg[x][0], subg[x][2], subg[x][3], subg[x][6], s, nodetable, edgetable, subgraphtable, subgmaptable)
    f.write("void run_vm(unsigned long, unsigned long, L* const, unsigned char* const __restrict, L*, L*, L*, unsigned long);\n".encode('ascii'))
    base = len(nodetable)
    nodetable.extend([None] * len(g))
    edgeinpmap = len(edgetable)
    edgetable += [base+mp[z] for z in inpmap]
    edgeoutmap = len(edgetable)
    edgetable += [base+mp[z] for z in outp]
    repeatmap = {}
    for x in g:
      if len(pred[x]) != 0:
        if not frozenset(pred[x]) in repeatmap:
          repeatmap[frozenset(pred[x])] = len(edgetable)
          edgetable += [base+mp[y] for y in pred[x]]
        if type(op[x]) is tuple and op[x][0] == SUBG_OP:
          gi = len(edgetable)
          edgetable += [base+mp[y] for y in op[x][2]]
          go = len(edgetable)
          edgetable += [base+mp[y] if y in mp else -1 for y in op[x][3]]
          for y in op[x][3]:
            if y in pred: repeatmap[frozenset(pred[y])] = -1
          subgmaptable.append((repeatmap[frozenset(pred[x])], gi, len(op[x][2]), go, len(op[x][3]), s[op[x][1]], op[x][4])) 
        elif type(op[x]) is tuple and op[x][0] == TBL_OP:
          sels = [y[0] for y in op[x][1]]
          if not tuple(sels) in repeatmap:
            gi = len(edgetable)
            edgetable += [base+mp[y[0]] for y in op[x][1]]
            repeatmap[tuple(sels)] = gi
          else: gi = repeatmap[tuple(sels)]
          gmap = len(edgetable)
          inttbl = [x for y in op[x][2] for x in y]
          edgetable += [virtual_to_constant(inttbl[i*32*BITSZ:(i+1)*32*BITSZ]) for i in range((len(inttbl)//BITSZ+31)//32)]
          tbli = len(edgetable)
          edgetable += [repeatmap[frozenset(pred[x])], len(op[x][1]), gi, gmap]
      nodetable[base+mp[x]] = ((op[x][0] if type(op[x]) is tuple else op[x]) | (len(pred[x]) if len(pred[x]) != 0 and repeatmap[frozenset(pred[x])] != -1 else 0) << 3, (len(subgmaptable)-1 if type(op[x]) is tuple and op[x][0] == SUBG_OP else (tbli if type(op[x]) is tuple and op[x][0] == TBL_OP else repeatmap[frozenset(pred[x])])) if len(pred[x]) != 0 else 0)
    #vals = ["~0U" if x == -1 else str(x) for i, x in enumerate(edgetable)] + [str(y) for i, x in enumerate(subgraphtable) for y in x] + [str(y) for i, x in enumerate(subgmaptable) for y in x] + [str(y) for i, x in enumerate(nodetable) for y in x]
    #f.write("L sg[] = {" + ",\n\t".join(",".join(str(y) for y in x) for x in subgraphtable) + "};\n")
    #f.write("L ss[] = {" + ",\n\t".join(",".join(str(y) for y in x) for x in subgmaptable) + "};\n")
    #f.write("static L e[] = {" + ",".join(("~0U" if x == -1 else str(x)) + ("\n\t" if (i % 50) == 49 else "") for i, x in enumerate(edgetable)) + "};\n")
    #f.write("static L g[] = {" + ",".join(",".join(str(y) for y in x) + ("\n\t" if (i % 50) == 49 else "") for i, x in enumerate(nodetable)) + "};\n")
    #at 1000000, the "0x" prefix hex is equal length to decimal, no benefit though until 1000000000000
    #mp = c_escape()
    vals = [x for i, x in enumerate(edgetable)] + [y for i, x in enumerate(subgraphtable) for y in x] + [y for i, x in enumerate(subgmaptable) for y in x] + [y for i, x in enumerate(nodetable) for y in x]
    if isstr:
      bytearr = [z for i, x in enumerate(vals) for z in x.to_bytes(4, 'little', signed=x<0)]
      #gcc combines sequences of \r and then changes \r or \r\n to \n
      #gcc cannot handle a backslash \\ some binary zeros \0 then a new line \n 5c 00 00 00 0a, 5c 00 00 0a, 5c 00 00 00 00 0a, 5c 09 00 0a, 5c 0c 0a
      #spacechars = [b'\x00', b'\x09', b'\x0b', b'\x0c', b' ']
      import re
      bytearr = re.sub(b"(\\\\[\x00\t\v\f ]+)(\n)", b"\\g<1>)|||\" R\"|||(\\g<2>", bytes(bytearr))
      f.write("static const char* ee = ".encode('ascii') + b' "\\r" '.join("R\"|||(".encode('ascii') + seq + ")|||\"".encode('ascii') for seq in bytearr.split(b'\r')) + ";\n".encode('ascii'))
      #f.write("static const char* e = \"" + "".join(mp[x] if not type(mp[x]) is tuple else mp[x][1 if not i == len(bytearr)-1 and bytearr[i+1] in list(range(ord('0'), ord('7')+1)) else 0] + ("\"\n\t\"" if (i % 50) == 49 else "") for i, x in enumerate(bytearr)) + "\";\n")
    else:
      f.write(("static L e[] = {" + ",".join(str(x) + ("\n\t" if (i % 2000) == 1999 else "") for i, x in enumerate(vals)) + "};\n").encode('ascii'))
    if not subg is None:
      scrtch = max(max(len(subg[x][2]), len(subg[x][3])) for x in subg)
    else: scrtch = 0
    f.write(("static unsigned char d[" + str(len(nodetable)+scrtch) + "];\n").encode('ascii'))
    f.write(("void " + funcname + "_obf_virt_encrypt(unsigned char* out, const unsigned char* in)\n{\n").encode('ascii'))
    if isstr: f.write(("\tL* e = (L*)ee;\n").encode('ascii'))
    f.write(("\tzm(&d[" + str(base) + "], " + str(len(g)) + ");\n").encode('ascii'))
    f.write(("\tload_input(in, " + str(len(inpmap)//BITSZ//8) + ", &e[" + str(edgeinpmap) + "], d);\n").encode('ascii'))
    f.write(("\trun_vm(" + str(base) + ", " + str(len(g)) + ", &e[" + str(len(edgetable)+len(subgraphtable)*5+len(subgmaptable)*7) + "], d, e, &e[" + str(len(edgetable)) + "], &e[" + str(len(edgetable)+len(subgraphtable)*5) + "], " + str(len(nodetable)) + ");\n").encode('ascii'))
    f.write(("\tread_output(out, " + str(len(outp)//BITSZ//8) + ", &e[" + str(edgeoutmap) + "], d);\n").encode('ascii'))
    f.write("}\n".encode('ascii'))
def graph_to_c(fname, funcname, op, g, pred, deporder, inpmap, outp, subg):
  mp = {}; ct = 0; inp = set(inpmap)
  for x in g:
    mp[x] = ct; ct += 1
  with open(fname + "graph.c", "w") as f:
    f.write("void load_input(unsigned char* in, unsigned long* inpmap, unsigned char* d);\n")
    f.write("void read_output(unsigned char* out, unsigned long* outp, unsigned char* d);\n")
    f.write("void " + funcname + "_obf_encrypt(unsigned char* out, unsigned char* in)\n{\n")
    f.write("\tunsigned long inpmap[] = { " + ",".join(str(mp[z]) for z in inpmap) + " };\n")
    f.write("\tunsigned long outp[] = { " + ",".join(str(mp[z]) for z in outp) + " };\n")
    f.write("\tunsigned char d[" + str(len(g)) + "] = {};\n")
    f.write("\tload_input(in, inpmap, d);\n")
    for i, x in enumerate(deporder):
      if i != 0: f.write("l" + str(x) + ":\n")
      nx = deporder[i+1] if i != len(deporder) - 1 else 0
      if op[x] == FLOW_OP:
        f.write("\tif (d[" + str(mp[x]) + "]!=" + str(1 if x in inp else len(pred[x])) + ") goto l" + str(nx) + ";\n")
      elif op[x] == ANY_OP:
        f.write("\tif (!d[" + str(mp[x]) + "]) goto l" + str(nx) + ";\n")
      elif op[x] == ADD_OP:
        f.write("\tif (!(d[" + str(mp[x]) + "]&1)) goto l" + str(nx) + ";\n")
      elif op[x] == ADDNEG_OP:
        f.write("\tif (d[" + str(mp[x]) + "]&1) goto l" + str(nx) + ";\n")
      for y in g[x]:
        f.write("\td[" + str(mp[y]) + "]++;\n")
    f.write("l" + str(0) + ":\n")
    f.write("\tread_output(out, outp, d);\n")
    f.write("}\n")
def virt_to_c(fname, funcname, op, g, rounds, inpmap, outmap=None, subg=None):
  #emit C code
  reduce_all(op, g, inpmap, outmap, subg)
  pred = graph.succ_to_pred(g)
  #deporder, levels = graph.topo_kahn_levels(g)
  deporder = graph.topo_kahn(g, randomize=True)
  #graph_to_c(fname, funcname, op, g, pred, deporder, inpmap, outmap, subg)
  graph_to_virt_c_opt(fname, funcname, op, g, pred, deporder, inpmap, outmap, subg, isstr=False)
  graph_to_virt_c_opt(fname, funcname, op, g, pred, deporder, inpmap, outmap, subg)
def reduce_all(op, g, inpmap, outmap, subg=None):
  outp = None
  if not outmap is None: outp = set(outmap)
  pred = graph.succ_to_pred(g)
  tn, te = len(g), sum(len(g[x]) for x in g)
  print("Graph nodes: ", tn, "Graph edges: ", te)
  if not outp is None:
    reduce_graph(op, pred, g, set(inpmap), outp) #trim the graph
  tn, te = len(pred), sum(len(pred[x]) for x in g)
  print("Reduced graph nodes: ", tn, "Reduced graph edges: ", te)
  if not subg is None:
    for x in subg:
      n, e = reduce_all(subg[x][1], subg[x][0], subg[x][2], subg[x][3], None)
      tn += n; te += e
    print("Total graph nodes: ", tn, "Total graph edges: ", te)
  return tn, te
  #relabel the graph
  #import random
  #lbls = [x for x in g]
  #random.shuffle(lbls)
def show_stats(stats):
  totalnodes, totaledges, total = 0, 0, 0
  for x in stats:
    if x is None: totalnodes += stats[x][0]; totaledges += stats[x][1]; total += stats[x][0] + stats[x][1]
    else: totalnodes += stats[x][0][0] * stats[x][1]; totaledges += stats[x][0][1] * stats[x][1]; total += (stats[x][0][0] + stats[x][0][1]) * stats[x][1]
  print("Total Nodes:", totalnodes, "Total Edges:", totaledges, "Total:", total)
  for x in stats:
    if x is None: print(stats[x], 100 * stats[x][0] / totalnodes, 100 * stats[x][1] / totaledges, 100 * (stats[x][0] + stats[x][1]) / total)
    else: print(x, stats[x], 100 * stats[x][0][0] * stats[x][1] / totalnodes, 100 * stats[x][0][1] * stats[x][1] / totaledges, 100 * (stats[x][0][0] + stats[x][0][1]) * stats[x][1] / total)
def run_virtual(op, g, rounds, inp, inpmap, outmap=None, subg=None):
  import graph
  reduce_all(op, g, inpmap, outmap, subg)
  result, stats = do_run_virtual(op, g, rounds, inp, inpmap, outmap, subg)
  show_stats(stats)
  return result
def do_run_virtual(op, g, rounds, inp, inpmap, outmap=None, subg=None):
  import graph
  if not outmap is None: outp = set(outmap)
  pred = graph.succ_to_pred(g)
  #dependency order the graph
  deporder = graph.topo_kahn(g, randomize=True)
  for x in inp: pred[x].add(0)
  import graph
  accepting = {0}
  i = 0
  stats, edgecount = {}, 0
  while (i != rounds) if outp is None else (len(accepting.intersection(outp)) != len(outp)//BITSZ):
    for x in deporder: #pred:
      edgecount += len(pred[x])
      #if x in accepting: continue
      if (op[x] == FLOW_OP) and len(pred[x]) != 0 and accepting.issuperset(pred[x]):
        accepting.add(x)
      elif (op[x] == FLOW_OP) and len(pred[x]) != 0 and x in accepting and not accepting.issuperset(pred[x]):
        pass #accepting.remove(x)
      elif (op[x] == ANY_OP) and len(pred[x]) != 0 and len(accepting.intersection(pred[x])) != 0:
        accepting.add(x)
      elif (op[x] == ANY_OP) and len(pred[x]) != 0 and x in accepting and len(accepting.intersection(pred[x])) == 0:
        accepting.remove(x)
      elif op[x] == ADD_OP and (len(accepting.intersection(pred[x])) & 1) != 0:
        accepting.add(x)
      elif op[x] == ADD_OP and x in accepting and (len(accepting.intersection(pred[x])) & 1) == 0:
        accepting.remove(x)
      elif op[x] == ADDNEG_OP and (len(accepting.intersection(pred[x])) & 1) == 0:
        accepting.add(x)
      elif op[x] == ADDNEG_OP and x in accepting and (len(accepting.intersection(pred[x])) & 1) != 0:
        accepting.remove(x)
      elif type(op[x]) is tuple and op[x][0] == SUBG_OP and (len(accepting.intersection(pred[x])) == (1 if BITSZ == 1  else len(pred[x]) // BITSZ)):
        z, subgstats = do_run_virtual(subg[op[x][1]][1], subg[op[x][1]][0], 0, [subg[op[x][1]][2][j] for j, y in enumerate(op[x][2]) if y in accepting], subg[op[x][1]][2], subg[op[x][1]][3], subg)
        for st in subgstats:
          if st is None:
            if not op[x][1] in stats: stats[op[x][1]] = [subgstats[st], 1]
            else: stats[op[x][1]][1] += 1          
          elif not st in stats: stats[st] = subgstats[st]
          else: stats[st][1] += subgstats[st][1]
        for i in range(op[x][4] if op[x][4] != -1 else 0xFFFFFFFF):
          if len(subg[op[x][1]][3]) != len(subg[op[x][1]][2]) and not subg[op[x][1]][3][-BITSZ] in z: break
          z, subgstats = do_run_virtual(subg[op[x][1]][1], subg[op[x][1]][0], 0, [y for j, y in enumerate(subg[op[x][1]][2]) if subg[op[x][1]][3][subg[op[x][1]][6][j]] in z], subg[op[x][1]][2], subg[op[x][1]][3], subg)
          #z = do_run_virtual(subg[op[x][1]][1], subg[op[x][1]][0], 0, [subg[op[x][1]][2][j] for j, y in enumerate(subg[op[x][1]][3]) if y in z], subg[op[x][1]][2], subg[op[x][1]][3], subg)
          for st in subgstats:
            if st is None: stats[op[x][1]][1] += 1
            elif not st in stats: stats[st] = subgstats[st]
            else: stats[st][1] += subgstats[st][1]
        accepting |= {y for j, y in enumerate(op[x][3]) if subg[op[x][1]][3][j] in z}
      elif type(op[x]) is tuple and op[x][0] == TBL_OP and accepting.issuperset(pred[x]):
        for i, y in enumerate(op[x][1]):
          if y[0] in accepting and op[x][2][i][0] is True: accepting.add(x); break
    i+=1
    break
  stats[None] = (len(pred), edgecount)
  #print(len(accepting.intersection(outp)))
  return accepting, stats

def make_graph():
  return [1], {}, {}, {}
def get_false(): return [False, True] if BITSZ == 2 else [False]
def get_true(): return [True, False] if BITSZ == 2 else [True]
def make_input(bits, node, g, op):
  inp = [node[0] + ix for ix in range(bits*BITSZ)]; node[0] += bits*BITSZ
  for ix in range(bits*BITSZ): op[inp[ix]] = FLOW_OP; g[inp[ix]] = []
  return inp
def isconst(x): return x[0] is True or x[0] is False
def isallconst(x): return all(isconst(x[i*BITSZ:(i+1)*BITSZ]) for i in range(len(x)//BITSZ))
def not_to_virtual(num, node, g, op):
  if BITSZ == 2: return [num[1], num[0]]
  outp = node[0]; node[0] += 1
  op[outp] = ADDNEG_OP; g[outp] = []
  g[num[0]].append(outp)
  return [outp]
def multi_not_to_virtual(num, node, g, op):
  return [x for y in [not_to_virtual(num[i*BITSZ:(i+1)*BITSZ], node, g, op) for i in range(len(num)//BITSZ)] for x in y]
  #return [num[i ^ 1] for i in range(len(num))]
def xor_to_virtual(nums, node, g, op):
  if all(isconst(x) for x in nums):
    return get_true() if (sum(x[0] for x in nums) & 1) != 0 else get_false()
  isflip = (sum(x[0] for x in nums if isconst(x)) & 1) != 0
  nums = [x for x in nums if not isconst(x)]
  newnums = set()
  for x in nums:
    if tuple(x) in newnums: newnums.remove(tuple(x))
    elif BITSZ == 2 and tuple(not_to_virtual(x, node, g, op)) in nums: newnums.remove(tuple(x)); isflip = not isflip
    else: newnums.add(tuple(x))
  nums = newnums
  if len(nums) == 1: return not_to_virtual(next(iter(nums)), node, g, op) if isflip else list(next(iter(nums)))
  if len(nums) == 0: return get_true() if isflip else get_false()
  outp0 = node[0]; node[0] += 1
  op[outp0] = ADDNEG_OP if isflip and (BITSZ == 1 or len(nums) > THRESHOLD) else ADD_OP
  g[outp0] = []
  if BITSZ == 2:
    outp1 = node[0]; node[0] += 1
    op[outp1] = ADDNEG_OP
    g[outp1] = []
  for x in nums:
    if BITSZ == 1 or len(nums) <= THRESHOLD:
      g[x[0]].append(outp0)
      if BITSZ == 2: g[x[0]].append(outp1)
    else:
      g[x[0]].append(outp1 if isflip else outp0)
  if BITSZ == 2 and len(nums) > THRESHOLD: g[outp1 if isflip else outp0].append(outp0 if isflip else outp1)
  return ([outp1, outp0] if isflip else [outp0, outp1]) if BITSZ == 2 else [outp0]
def and_to_virtual(nums, node, g, op):
  if all(isconst(x) for x in nums):
    return get_true() if all(x[0] for x in nums) else get_false()
  if any(isconst(x) and x[0] is False for x in nums):
    return get_false()
  nums = [x for x in nums if not isconst(x)]
  nums = set(tuple(x) for x in nums)
  for x in nums:
    if BITSZ == 2 and tuple(not_to_virtual(x, node, g, op)) in nums: return get_false()
  if len(nums) == 1: return list(next(iter(nums)))
  outp0 = node[0]; node[0] += 1
  op[outp0] = FLOW_OP; g[outp0] = []
  if BITSZ == 2:
    outp1 = node[0]; node[0] += 1
    op[outp1] = ADDNEG_OP if len(nums) > THRESHOLD else ANY_OP
    g[outp1] = []
  for x in nums:
    g[x[0]].append(outp0)
    if BITSZ == 2 and len(nums) <= THRESHOLD: g[x[1]].append(outp1)
  if BITSZ == 2 and len(nums) > THRESHOLD: g[outp0].append(outp1)
  return [outp0, outp1] if BITSZ == 2 else [outp0]
def or_to_virtual(nums, node, g, op):
  if all(isconst(x) for x in nums):
    return get_true() if any(x[0] for x in nums) else get_false()
  if any(isconst(x) and x[0] is True for x in nums):
    return get_true()
  nums = [x for x in nums if not isconst(x)]
  nums = set(tuple(x) for x in nums)
  for x in nums:
    if BITSZ == 2 and tuple(not_to_virtual(x, node, g, op)) in nums: return get_true()
  if len(nums) == 1: return list(next(iter(nums)))
  outp0 = node[0]; node[0] += 1
  op[outp0] = ANY_OP; g[outp0] = []
  if BITSZ == 2:
    outp1 = node[0]; node[0] += 1
    op[outp1] = ADDNEG_OP if len(nums) > THRESHOLD else FLOW_OP
    g[outp1] = []
  for x in nums:
    g[x[0]].append(outp0)
    if BITSZ == 2 and len(nums) <= THRESHOLD: g[x[1]].append(outp1)
  if BITSZ == 2 and len(nums) > THRESHOLD: g[outp0].append(outp1)
  return [outp0, outp1] if BITSZ == 2 else [outp0]
def get_bit_len(num): return len(num)//BITSZ
def get_bit_range(num, start, end): return num[start*BITSZ:end*BITSZ if not end is None else None]
def set_bit_range(num, start, end, replace): num[start*BITSZ:end*BITSZ if not end is None else None] = replace
def zero_extend_num(num, bits):
  return num + get_false() * (bits - (len(num)//BITSZ))
def zero_extend_virtual(nums):
  mlen = max(len(x) for x in nums)//BITSZ
  return mlen, [x if len(x)//BITSZ == mlen else (x + get_false() * (mlen - (len(x)//BITSZ))) for x in nums]
def sign_extend_virtual(nums):
  mlen = max(len(x) for x in nums)//BITSZ
  return mlen, [x if len(x)//BITSZ == mlen else (x + x[-BITSZ:] * (mlen - (len(x)//BITSZ))) for x in nums]
def multi_to_virtual(nums, f, node, g, op, subg=None):
  mlen, nums = zero_extend_virtual(nums)
  return [y for x in [f([x[i*BITSZ:(i+1)*BITSZ] for x in nums], node, g, op) for i in range(mlen)] for y in x]
def cmp_zero_to_virtual(num, nz, node, g, op):
  #(x | -x) >> (len(x)-1)
  #return multi_to_virtual([num, neg_to_virtual(num, node, g, op)[:-2]], or_to_virtual, node, g, op)[-BITSZ:]
  if len(num) == 0: return get_false() if nz else get_true()
  #return multi_to_virtual([num[i*BITSZ:(i+1)*BITSZ] if nz else not_to_virtual(num[i*BITSZ:(i+1)*BITSZ], node, g, op) for i in range(len(num)//BITSZ)], or_to_virtual if nz else and_to_virtual, node, g, op)
  x = multi_to_virtual([num[i*BITSZ:(i+1)*BITSZ] for i in range(len(num)//BITSZ)], or_to_virtual, node, g, op)
  return x if nz else not_to_virtual(x, node, g, op)
def constant_to_virtual(num):
  outp = []
  for ix in range(num.bit_length()):
    isoff = (num & (1 << ix)) == 0
    outp.extend(get_false() if isoff else get_true())
  return outp
def virtual_to_constant(num, issigned=False):
  x = 0
  for i in range(len(num)//BITSZ):
    if num[i*BITSZ]:
      if issigned and i == (len(num)//BITSZ) - 1:
        x |= -(1 << i)
      else: x |= (1 << i)
  return x
def selection_to_virtual(selector, num1, num2, node, g, op):
  return multi_to_virtual([num1, num2], lambda nums, node, g, op: multi_selection_to_virtual([selector, not_to_virtual(selector, node, g, op)], nums, node, g, op), node, g, op)
def multi_bit_selection_to_virtual(selectors, nums, node, g, op):
  return multi_to_virtual(nums, lambda nums, node, g, op: multi_selection_to_virtual(selectors, nums, node, g, op), node, g, op)
def multi_bit_selection_to_table_virtual(selectors, nums, node, g, op):
  prednode = node[0]; node[0] += 1
  op[prednode] = ANY_OP; g[prednode] = []
  for x in selectors: g[x[0]].append(prednode)
  shufarr = list(range(len(selectors)))
  import random
  random.shuffle(shufarr)
  return multi_to_virtual(nums, lambda nums, node, g, op: multi_selection_to_table_virtual(selectors, nums, node, g, op, prednode, shufarr), node, g, op)
def multi_selection_to_table_virtual(selectors, nums, node, g, op, pred, shufarr):
  assert all(isconst(x) for x in nums)
  outp = node[0]; node[0] += 1
  selectors = [selectors[i] for i in shufarr]
  nums = [nums[i] for i in shufarr]
  op[outp] = (TBL_OP, selectors, nums); g[outp] = []
  g[pred].append(outp)
  if BITSZ == 1: return [outp]
  outpn = node[0]; node[0] += 1
  op[outpn] = ADDNEG_OP; g[outpn] = []
  g[outp].append(outpn)
  return [outp, outpn]
def multi_selection_to_virtual(selectors, nums, node, g, op):
  inps = []
  for i in range(len(selectors)):
    if isconst(selectors[i]):
      if selectors[i][0] is False: continue
      elif selectors[i][0] is True: return nums[i]
    if isconst(nums[i]):
      if nums[i][0] is True: inps.append(selectors[i])
      else: continue
    else:
      inps.append(and_to_virtual([selectors[i], nums[i]], node, g, op))
  if len(inps) == 0: return get_false()
  return multi_to_virtual(inps, xor_to_virtual, node, g, op)
def table_lookup_virtual(inp, table, node, g, op, subg=None):
  """
  from pyeda.inter import ttvars, truthtable, espresso_tts
  X = ttvars('x', len(inp)//BITSZ)
  mlen = max(len(x)//BITSZ for x in table)
  f = [truthtable(X, "".join("1" if len(table[i]) > j*BITSZ and table[i][j*BITSZ] is True else "0" for i in range(len(table)))) for j in range(0, mlen)]
  fm = espresso_tts(*f)
  """
  if not subg is None:
    return multi_bit_selection_to_virtual(split_bits(subg_virtual(decoder_shift_to_virtual, inp, (), node, g, op, subg)), table, node, g, op)
  else:
    return multi_bit_selection_to_virtual(split_bits(decoder_shift_to_virtual(inp, node, g, op)), table, node, g, op)
def decoder_shift_to_virtual(shift, node, g, op): #2*2^n nodes, 2 predecessors per node
  num = constant_to_virtual(1)
  if len(shift) == 0: return num
  for i in range(len(shift)//BITSZ):
    num = multi_to_virtual([num, not_to_virtual(shift[i*BITSZ:(i+1)*BITSZ], node, g, op) * (len(num)//BITSZ)], and_to_virtual, node, g, op) + multi_to_virtual([num, shift[i*BITSZ:(i+1)*BITSZ] * (len(num)//BITSZ)], and_to_virtual, node, g, op)
  return num
def split_bits(num):
  return [num[i*BITSZ:(i+1)*BITSZ] for i in range(len(num)//BITSZ)]
def decoder_to_virtual(shift, node, g, op): #2^n nodes, n predecessors per node
  return [x for y in [cmp_zero_to_virtual(multi_to_virtual([constant_to_virtual(i), shift], xor_to_virtual, node, g, op), False, node, g, op) for i in range(1 << ((len(shift)//BITSZ)))] for x in y]
def test_virtual(inpbits, inp, outp, node, g, op, subg=None, issigned=False):
  accepting = run_virtual(op, g, 0, [inp[i] for i, x in enumerate(inpbits) if x], inp, [x for x in outp if not x is True and not x is False], subg)
  return virtual_to_constant([x is True or not x is False and x in accepting for x in outp], issigned=issigned)
def get_virtual(inpbits, f):
  node, g, op, subg = make_graph()
  inp = make_input(inpbits, node, g, op)
  return inp, f(inp, node, g, op, subg), node, g, op, subg
def mbinop_test(i, j, ival, jval, f, doop):
  res = test_virtual(ival, *get_virtual(len(ival)//BITSZ, lambda inp, node, g, op, subg: multi_to_virtual([inp, jval], f, node, g, op, subg)))
  assert doop(i, j) == res, (i, j, doop(i, j), res)
  res = test_virtual(ival, *get_virtual(len(ival)//BITSZ, lambda inp, node, g, op, subg: multi_to_virtual([jval, inp], f, node, g, op, subg)))
  assert doop(i, j) == res, (i, j, doop(i, j), res)
  res = test_virtual(ival + jval, *get_virtual((len(ival)+len(jval))//BITSZ, lambda inp, node, g, op, subg: multi_to_virtual([inp[:len(ival)], inp[len(ival):]], f, node, g, op, subg)))
  assert doop(i, j) == res, (i, j, doop(i, j), res)
def binop_test(i, j, ival, jval, f, doop, issigned=False, revargs=True):
  if revargs:
    res = test_virtual(ival, *get_virtual(len(ival)//BITSZ, lambda inp, node, g, op, subg: f(jval, inp, node, g, op, subg)), issigned=issigned)
    assert doop(j, i) == res, (i, j, doop(j, i), res)
  res = test_virtual(ival, *get_virtual(len(ival)//BITSZ, lambda inp, node, g, op, subg: f(inp, jval, node, g, op, subg)), issigned=issigned)
  assert doop(i, j) == res, (i, j, doop(i, j), res)
  res = test_virtual(ival + jval, *get_virtual((len(ival)+len(jval))//BITSZ, lambda inp, node, g, op, subg: f(inp[:len(ival)], inp[len(ival):], node, g, op, subg)), issigned=issigned)
  assert doop(i, j) == res, (i, j, doop(i, j), res)
def unaryop_test(i, ival, f, doop, issigned=False):
  res = test_virtual(ival, *get_virtual(len(ival)//BITSZ, lambda inp, node, g, op, subg: f(inp, node, g, op, subg)), issigned=issigned)
  assert doop(i) == res, (i, doop(i), res)
def addition_bit_to_virtual(num1, num2, carry, node, g, op, issub=False, need_carry=True):
  #S=A^B^carry_in, carry_out = (A&B)|(carry_in&(A^B))==(A&B)^(carry_in&(A^B))
  #borrow_out = (!A&B)|(borrow_in&!(A^B))==(!A&B)^(borrow_in&!(A^B))
  #borrow_out=True -> !A&B^!(A^B)==!A&B^!(A&!B|!A&B)==!A&B|(!A|B)&(A|!B)==!A|B
  #carry_in=True -> A|B
  if not need_carry: return xor_to_virtual([num1, num2, carry], node, g, op)
  if issub is False or issub is True: issub = [issub, not issub]
  num1sub = xor_to_virtual([issub, num1], node, g, op)
  if not isconst(carry) and (isconst(num1) and num1sub[0] is True and not isconst(num2) or not isconst(num1) and isconst(num2) and num2[0] is True):
    result = xor_to_virtual([num1, num2, carry], node, g, op)
    carry = or_to_virtual([and_to_virtual([num1sub, num2], node, g, op), carry], node, g, op)   
  else:
    s = xor_to_virtual([num1, num2], node, g, op)
    result = xor_to_virtual([carry, s], node, g, op)
    if isconst(carry) and carry[0] is True:
      carry = or_to_virtual([num1sub, num2], node, g, op)
    else:
      c = and_to_virtual([carry, xor_to_virtual([issub, s], node, g, op)], node, g, op)
      carry = xor_to_virtual([and_to_virtual([num1sub, num2], node, g, op), c], node, g, op)
  return result, carry
def addition_to_virtual(num1, num2, node, g, op, issub=False, need_carry=True):
  mlen = max(len(num1), len(num2))//BITSZ
  if len(num1)//BITSZ != mlen: num1 = num1 + get_false() * (mlen - (len(num1)//BITSZ))
  if len(num2)//BITSZ != mlen: num2 = num2 + get_false() * (mlen - (len(num2)//BITSZ))
  carry = get_false()
  result = []
  for i in range(mlen):
    if i == mlen-1:
      if need_carry:
        r, carry = addition_bit_to_virtual(num1[i*BITSZ:(i+1)*BITSZ], num2[i*BITSZ:(i+1)*BITSZ], carry, node, g, op, issub)
        result.extend(r + carry)
      else:
        r = addition_bit_to_virtual(num1[i*BITSZ:(i+1)*BITSZ], num2[i*BITSZ:(i+1)*BITSZ], carry, node, g, op, issub, False)
        result.extend(r)
    else:
      r, carry = addition_bit_to_virtual(num1[i*BITSZ:(i+1)*BITSZ], num2[i*BITSZ:(i+1)*BITSZ], carry, node, g, op, issub)
      result.extend(r)
  return result
def multi_addition_to_virtual(nums, node, g, op, need_carry=True):
  #carry-save adder reduction to add parallelism and help with constants
  #use a Wallace tree strategy
  if len(nums) == 0: return get_false()
  if len(nums) == 1: return nums[0]
  maxlen = max(len(x) for x in nums)//BITSZ
  nextnums = []
  finalnums = []
  for i in range(maxlen):
    nextnums += [x[i*BITSZ:(i+1)*BITSZ] for x in nums if (len(x)//BITSZ) > i]
    curbits = [x for x in nextnums if not isconst(x)]
    curconsts = [x for x in nextnums if isconst(x) and x[0] is True]
    nextnums = []
    while len(curconsts) >= 2:
      nextnums.append(get_true())
      del curconsts[:2]
    curbits += curconsts
    while len(curbits) >= 3:
      r, carry = addition_bit_to_virtual(curbits[0], curbits[1], curbits[2], node, g, op, False, True)
      del curbits[:3]
      curbits.append(r)
      nextnums.append(carry)
    finalnums.append(curbits)
  nums = ([y for x in finalnums for y in (x[0] if len(x) >= 1 else get_false())],
          [y for x in finalnums for y in (x[1] if len(x) == 2 else get_false())])
  return addition_to_virtual(nums[0], nums[1], node, g, op, False, need_carry)
  """
  while len(nums) >= 3:
    nums = list(sorted(nums, key=lambda x: len(x)))
    mlen, curnums = zero_extend_virtual(nums[:3])
    del nums[:3]
    nums += [[z for y in x for z in y] for x in zip(*[addition_bit_to_virtual(curnums[0][i*BITSZ:(i+1)*BITSZ], curnums[1][i*BITSZ:(i+1)*BITSZ], curnums[2][i*BITSZ:(i+1)*BITSZ], node, g, op, False, True) for i in range(mlen)])]
    nums[-1] = (get_false() + nums[-1])[:(maxlen+1 if need_carry else maxlen)*BITSZ]
  return addition_to_virtual(nums[0], nums[1], node, g, op, False, False) #len(nums) == 2
  """
def neg_to_virtual(num, node, g, op): #must already have a sign bit
  return addition_to_virtual(get_false(), num, node, g, op, True, need_carry=False)
  #return addition_to_virtual(multi_not_to_virtual(num, node, g, op), get_true(), node, g, op, need_carry=False)
def bound_to_virtual(t, N, node, g, op, issub=False, needcmp=False):
  if issub: #no sign bit assumed
    if len(t) < len(N): return t
    res = addition_to_virtual(t, N, node, g, op, True)
    if needcmp: return selection_to_virtual(res[-BITSZ:], t[:len(N)], res[:len(N)], node, g, op), not_to_virtual(res[-BITSZ:], node, g, op)
    return selection_to_virtual(res[-BITSZ:], t[:len(N)], res[:len(N)], node, g, op)
  else: #must already have sign bit!
    if len(t) <= BITSZ or len(N) <= BITSZ: return t
    return addition_to_virtual(t[:-BITSZ], multi_to_virtual([N, t[-BITSZ:]*((len(t)//BITSZ)-1)], and_to_virtual, node, g, op), node, g, op, need_carry=False)
def montgomeryREDC_to_virtual_mul_eff_subg(num, B, R, N, Np, node, g, op, subg):
  return montgomeryREDC_to_virtual_mul_eff(num[:len(num)//2], num[len(num)//2:], B, R, N, Np, node, g, op, subg)
def montgomeryREDC_to_virtual_mul_eff_sqr(num, B, R, N, Np, node, g, op, subg):
  return montgomeryREDC_to_virtual_mul_eff(num, num, B, R, N, Np, node, g, op, subg)
def montgomeryREDC_to_virtual_mul_eff_const(T1, T0, B, R, N, Np, node, g, op, subg):
  if T0 == 1:
    m = T1
  else:
    T0f = get_consec_ones(T0)
    print(B, len(T0f))
    if len(T0f) > (B >> 2):
      m = subg_virtual(mulKaratsuba_to_virtual_subg, zero_extend_num(T1, B) + zero_extend_num(constant_to_virtual(T0), B), (), node, g, op, subg, True)
      #m = mulKaratsuba_to_virtual(T1, constant_to_virtual(T0), node, g, op)
    else:
      #custom multiplication based on addition/subtraction sequences
      m = mul_consec_ones_virtual(T1, T0f, node, g, op)
  #m = mul_consec_ones_virtual(T1, T0f, node, g, op)
  return subg_virtual(montgomeryREDC_to_virtual, m, (B, R, N, Np), node, g, op, subg, True)
def montgomeryREDC_to_virtual_mul_eff(T1, T0, B, R, N, Np, node, g, op, subg):
  if T1 == T0:
    m = subg_virtual(mulKaratsuba_to_virtual_sqr, T1, (), node, g, op, subg, True)
    return subg_virtual(montgomeryREDC_to_virtual, m, (B, R, N, Np), node, g, op, subg, True)
  else:
    m = subg_virtual(mulKaratsuba_to_virtual_subg, T1 + T0, (), node, g, op, subg, True)
  #  m = mulKaratsuba_to_virtual(T1, T0, node, g, op)
    return subg_virtual(montgomeryREDC_to_virtual, m, (B, R, N, Np), node, g, op, subg, True)
  """
  if len(T1) == 0 or len(T0) == 0: return get_false()
  Nconst = constant_to_virtual(N)
  T1, T0 = zero_extend_virtual([T1, T0])[1]
  x = get_false()
  #NpT1 = addition_to_virtual(T1, Nconst, node, g, op)
  for i in range(B):
    #addboth = xor_to_virtual([x[:BITSZ], and_to_virtual([T0[i*BITSZ:(i+1)*BITSZ], T1[:BITSZ]], node, g, op)], node, g, op)
    x = addition_to_virtual(x, multi_to_virtual([T1, T0[i*BITSZ:(i+1)*BITSZ]*(len(T1)//BITSZ)], and_to_virtual, node, g, op), node, g, op)
    x = addition_to_virtual(x, multi_to_virtual([Nconst, x[:BITSZ]*B], and_to_virtual, node, g, op), node, g, op)
    x = x[BITSZ:] #n/n+1 bits
    if len(x) > (B+1) * BITSZ: x = x[:(B+1)*BITSZ] #n+1 maximum bits to carry over
  return bound_to_virtual(x, Nconst, node, g, op, True)
  """
def mulKaratsuba_to_virtual_sqr(num, node, g, op, subg): return mulKaratsuba_to_virtual(num, num, node, g, op, subg)
def mulKaratsuba_to_virtual_subg(num, node, g, op, subg): return mulKaratsuba_to_virtual(num[:len(num)//2], num[len(num)//2:], node, g, op, subg)
#https://gmplib.org/manual/Karatsuba-Multiplication
def mulKaratsuba_to_virtual(num1, num2, node, g, op, subg):
  mlen = max(len(num1), len(num2))//BITSZ
  if len(num1)//BITSZ != mlen: num1 = num1 + get_false() * (mlen - (len(num1)//BITSZ))
  if len(num2)//BITSZ != mlen: num2 = num2 + get_false() * (mlen - (len(num2)//BITSZ))
  n1const = sum(1 for i in range(len(num1)//BITSZ) if isconst(num1[i*BITSZ:(i+1)*BITSZ]))
  n2const = sum(1 for i in range(len(num2)//BITSZ) if isconst(num2[i*BITSZ:(i+1)*BITSZ]))
  if mlen <= 18 or (len(num1)//BITSZ)-n1const <= 18 or (len(num2)//BITSZ)-n2const <= 18 or num1==num2 and mlen <= 18:
    x = constant_to_virtual(0)
    if num1 == num2:
      #for i in range((len(num1)//BITSZ)-1, -1, -1):
      #  x = num1[i*BITSZ:(i+1)*BITSZ] + get_false() + addition_to_virtual(multi_to_virtual([num1[i*BITSZ:(i+1)*BITSZ]*((len(num1)//BITSZ)-i-1), num1[(i+1)*BITSZ:]], and_to_virtual, node, g, op), x, node, g, op)
      x = multi_addition_to_virtual([get_false() * i*2 + num1[i*BITSZ:(i+1)*BITSZ] + get_false() + multi_to_virtual([num1[i*BITSZ:(i+1)*BITSZ]*((len(num1)//BITSZ)-i-1), num1[(i+1)*BITSZ:]], and_to_virtual, node, g, op) for i in range((len(num1)//BITSZ)-1, -1, -1)], node, g, op)
    else:
      if n2const < n1const: num1, num2 = num2, num1
      #for i in range(len(num1)//BITSZ):
      #  x = addition_to_virtual(get_false() * i + multi_to_virtual([num1[i*BITSZ:(i+1)*BITSZ]*(len(num2)//BITSZ), num2], and_to_virtual, node, g, op), x, node, g, op)
      x = multi_addition_to_virtual([get_false() * i + multi_to_virtual([num1[i*BITSZ:(i+1)*BITSZ]*(len(num2)//BITSZ), num2], and_to_virtual, node, g, op) for i in range(len(num1)//BITSZ)], node, g, op)
    return x[:mlen*2*BITSZ]
  elif num1 == num2: #x*y=(x1*y1*2^(2B)+(x1*y0+x0*y1)*2^B+x0*y0
    m2 = mlen >> 1
    low1, high1 = num1[:m2*BITSZ], num1[m2*BITSZ:]
    z0 = subg_virtual(mulKaratsuba_to_virtual_sqr, low1, (), node, g, op, subg, True)
    #z0 = mulKaratsuba_to_virtual(low1, low1, node, g, op)
    z2 = subg_virtual(mulKaratsuba_to_virtual_sqr, high1, (), node, g, op, subg, True)
    #z2 = mulKaratsuba_to_virtual(high1, high1, node, g, op)
    #z1 = mulKaratsuba_to_virtual(low1, high1, node, g, op)
    #return z0[:(m2+1)*BITSZ] + addition_to_virtual(z0[(m2+1)*BITSZ:] + z2, z1, node, g, op, need_carry=False) #2*(bits - m2)+m2*2 - m2
    #(x1-x0)^2==(x1-x0)*(x1-x0)=x1^2-2*x1*x0+x0^2
    z1 = addition_to_virtual(high1, low1, node, g, op, True, need_carry=True)
    #abs(x) = (x < 0) ^ x - (x < 0)
    z1 = addition_to_virtual(multi_to_virtual([z1[-BITSZ:] * ((len(z1)//BITSZ)-1), z1[:-BITSZ]], xor_to_virtual, node, g, op), z1[-BITSZ:], node, g, op, False, need_carry=False)
    #assert len(z1) == len(low1), (len(z1), len(low1))
    #z1 = selection_to_virtual(z1[-BITSZ:], neg_to_virtual(z1, node, g, op)[:-BITSZ], z1[:-BITSZ], node, g, op)
    z1 = subg_virtual(mulKaratsuba_to_virtual_sqr, z1, (), node, g, op, subg, True)
    #z1 = mulKaratsuba_to_virtual(z1, z1, node, g, op)
    #big + small - medium
    #big - (medium - small)
    z0z2 = addition_to_virtual(z0[m2*BITSZ:], z2[:m2*BITSZ], node, g, op, need_carry=True)
    if len(z0) == len(z2):
      return z0[:m2*BITSZ] + addition_to_virtual(multi_addition_to_virtual([z0z2, get_false() * m2 + z0z2, z0[:m2*BITSZ] + z2[m2*BITSZ:] + z2[m2*BITSZ:]], node, g, op, need_carry=False), z1, node, g, op, True, need_carry=False)
    else: return z0[:m2*BITSZ] + addition_to_virtual(multi_addition_to_virtual([z0z2, get_false() * m2 + z0z2, z0[:m2*BITSZ] + z2[m2*BITSZ:], get_false()*(m2*2)+ z2[m2*BITSZ:]], node, g, op, need_carry=False), z1, node, g, op, True, need_carry=False)
    #return z0[:m2*BITSZ] + addition_to_virtual(addition_to_virtual(addition_to_virtual(z2, z0, node, g, op, need_carry=True), z0[m2*BITSZ:] + z2, node, g, op, need_carry=False), z1, node, g, op, True, need_carry=False)
  else:
    m2 = mlen >> 1
    low1, low2 = num1[:m2*BITSZ], num2[:m2*BITSZ]
    high1, high2 = num1[m2*BITSZ:], num2[m2*BITSZ:]
    if mlen > 1:
      z0 = subg_virtual(mulKaratsuba_to_virtual_subg, low1 + low2, (), node, g, op, subg, True)
    else:
      z0 = mulKaratsuba_to_virtual(low1, low2, node, g, op, subg)
    if mlen > 1:
      z2 = subg_virtual(mulKaratsuba_to_virtual_subg, high1 + high2, (), node, g, op, subg, True)
    else:
      z2 = mulKaratsuba_to_virtual(high1, high2, node, g, op, subg)
    #lowhigh1 = addition_to_virtual(low1, high1, node, g, op)
    #lowhigh2 = addition_to_virtual(low2, high2, node, g, op)
    #z1 = subg_virtual(mulKaratsuba_to_virtual_subg, lowhigh1 + lowhigh2, (), node, g, op, subg, True)
    #z1 = mulKaratsuba_to_virtual(lowhigh1, lowhigh2, node, g, op)
    #z1 = addition_to_virtual(z1, z0, node, g, op, True, need_carry=False)
    #z1 = addition_to_virtual(z1, z2, node, g, op, True, need_carry=False)
    #return z0[:m2*BITSZ] + addition_to_virtual(z0[m2*BITSZ:] + z2, z1, node, g, op, need_carry=False) #2*(bits - m2)+m2*2 - m2
    lowhigh1 = addition_to_virtual(high1, low1, node, g, op, True, need_carry=True)
    lowhigh2 = addition_to_virtual(high2, low2, node, g, op, True, need_carry=True)
    issub = not_to_virtual(xor_to_virtual([lowhigh1[-BITSZ:], lowhigh2[-BITSZ:]], node, g, op), node, g, op)
    lowhigh1 = addition_to_virtual(multi_to_virtual([lowhigh1[-BITSZ:] * ((len(lowhigh1)//BITSZ)-1), lowhigh1[:-BITSZ]], xor_to_virtual, node, g, op), lowhigh1[-BITSZ:], node, g, op, False, need_carry=False)
    lowhigh2 = addition_to_virtual(multi_to_virtual([lowhigh2[-BITSZ:] * ((len(lowhigh2)//BITSZ)-1), lowhigh2[:-BITSZ]], xor_to_virtual, node, g, op), lowhigh2[-BITSZ:], node, g, op, False, need_carry=False)
    if mlen > 1:
      z1 = subg_virtual(mulKaratsuba_to_virtual_subg, lowhigh1 + lowhigh2, (), node, g, op, subg, True)
    else:
      z1 = mulKaratsuba_to_virtual(lowhigh1, lowhigh2, node, g, op, subg)
    z0z2 = addition_to_virtual(z0[m2*BITSZ:], z2[:m2*BITSZ], node, g, op, need_carry=True)
    if len(z0) == len(z2):
      return z0[:m2*BITSZ] + addition_to_virtual(multi_addition_to_virtual([z0z2, get_false() * m2 + z0z2, z0[:m2*BITSZ] + z2[m2*BITSZ:] + z2[m2*BITSZ:]], node, g, op, need_carry=False), z1, node, g, op, issub, need_carry=False)
    else: return z0[:m2*BITSZ] + addition_to_virtual(multi_addition_to_virtual([z0z2, get_false() * m2 + z0z2, z0[:m2*BITSZ] + z2[m2*BITSZ:], get_false()*(m2*2)+ z2[m2*BITSZ:]], node, g, op, need_carry=False), z1, node, g, op, issub, need_carry=False)
    #return z0[:m2*BITSZ] + addition_to_virtual(addition_to_virtual(addition_to_virtual(z2, z0, node, g, op, need_carry=True), z0[m2*BITSZ:] + z2, node, g, op, need_carry=False), z1, node, g, op, issub, need_carry=False)
def trim_const(x):
  while len(x) != 0 and x[-BITSZ] is False: x = x[:-BITSZ]
  return x
def mul_consec_ones_virtual(num, pos, node, g, op):
  x = constant_to_virtual(0)
  i = 0
  while i != len(pos):
    z = pos[i]
    if z >= 0:
      x = addition_to_virtual(get_false() * (z-1) + num, x, node, g, op)
    else:
      x = addition_to_virtual(get_false() * (pos[i+1]-1) + num, x, node, g, op)
      x = addition_to_virtual(x, get_false() * (-z-1) + num, node, g, op, True)
      i += 1
    i += 1
  return trim_const(x)
def montgomeryREDC_to_virtual(T, B, R, N, Np, node, g, op, subg):
  Nconst = constant_to_virtual(N)
  Nf, Npf = get_consec_ones(N), get_consec_ones(Np)
  if len(Npf) > (B >> 2):
    #mul_const_window(None, Np, node, g, op)
    #m = mulKaratsuba_to_virtual(T[:B*BITSZ], constant_to_virtual(Np), node, g, op)[:B*BITSZ]
    m = subg_virtual(mulKaratsuba_to_virtual_subg, zero_extend_num(T[:B*BITSZ], B) + zero_extend_num(constant_to_virtual(Np), B), (), node, g, op, subg, True)[:B*BITSZ]
  else:
    #custom multiplication based on addition/subtraction sequences
    m = mul_consec_ones_virtual(T[:B*BITSZ], Npf, node, g, op)[:B*BITSZ]
    #m = mul_consec_ones_virtual(T[:B*BITSZ], Npf, node, g, op)[:B*BITSZ]
  if len(Nf) > (B >> 2):
    #m = mulKaratsuba_to_virtual(m, Nconst, node, g, op)[:B*2*BITSZ]
    m = subg_virtual(mulKaratsuba_to_virtual_subg, zero_extend_num(m, B) + zero_extend_num(constant_to_virtual(N), B), (), node, g, op, subg, True)
  else:
    m = mul_consec_ones_virtual(m, Nf, node, g, op)
  #m = mul_consec_ones_virtual(m, Nf, node, g, op)
  t = addition_to_virtual(T, m, node, g, op)[B*BITSZ:]
  """
  t, carry = T, []
  for i in range(B):
    res = addition_to_virtual(t[:(B+1)*BITSZ], multi_to_virtual([Nconst, t[:BITSZ]*B], and_to_virtual, node, g, op) + carry, node, g, op, need_carry=True)
    if len(t) > (B+1) * BITSZ:
      t, carry = res[:-BITSZ] + t[(B+1)*BITSZ:], res[-BITSZ:]
    else: t, carry = res, []
    t = t[BITSZ:] #n/n+1 bits
    #if len(t) > (B+1) * BITSZ: t = t[:(B+1)*BITSZ] #n+1 maximum bits to carry over
  """
  return bound_to_virtual(t, Nconst, node, g, op, True)
def modexp_window_to_virtual(e, m, num, B, R, Np, R2, node, g, op, subg):
  res = constant_to_virtual(montgomeryREDC(R2, B, R, m, Np))
  w = min((((B+w-1) // w)+(1<<w)-2, w) for w in range(1, B.bit_length()))[1] #3 for 64, 4 for 128/256, 5 for 512, 6 for 1024/2048, 7 for 4096
  tbl = {0: res + get_false() * ((len(num)//BITSZ)-(len(res)//BITSZ)), 1: num}
  usedvals = set()
  #for j in range(((B+w-1) // w)-1, -1, -1):
  #  usedvals.add(e >> (j * w) & ((1 << w)-1))
  for j in range(2, 1<<w):
    if (j & 1) == 0 and (j >> 1) in tbl: tbl[j] = subg_virtual(montgomeryREDC_to_virtual_mul_eff_sqr, tbl[j>>1], (B, R, m, Np), node, g, op, subg, True)
    else: tbl[j] = subg_virtual(montgomeryREDC_to_virtual_mul_eff_subg, tbl[j-1] + num, (B, R, m, Np), node, g, op, subg, True)
  for j in range(((B+w-1) // w)-1, -1, -1):
    if isallconst(res):
      res = montgomeryREDC_to_virtual_mul_eff_const(tbl[e >> (j * w) & ((1 << w)-1)], virtual_to_constant(res), B, R, m, Np, node, g, op, subg)
    else:
      res = subg_virtual(montgomeryREDC_to_virtual_mul_eff_subg, tbl[e >> (j * w) & ((1 << w)-1)] + res, (B, R, m, Np), node, g, op, subg, True)  
    if j == 0: break
    #for i in range(w):
    res = subg_virtual(montgomeryREDC_to_virtual_mul_eff_sqr, res, (B, R, m, Np), node, g, op, subg, True, repetition=w-1)
  return res
def modexp_to_virtual(e, m, num, B, R, Np, R2, node, g, op, subg):
  #assert (m & 1) != 0
  result = constant_to_virtual(montgomeryREDC(R2, B, R, m, Np))
  while e > 0:
    if (e & 1) != 0:
      if isallconst(result):
        result = montgomeryREDC_to_virtual_mul_eff_const(num, virtual_to_constant(result), B, R, m, Np, node, g, op, subg)
      else:
        result = subg_virtual(montgomeryREDC_to_virtual_mul_eff_subg, num + result + get_false() * ((len(num)//BITSZ)-(len(result)//BITSZ)), (B, R, m, Np), node, g, op, subg, True)
    e >>= 1
    if e == 0: break
    if isallconst(num):
      num = constant_to_virtual(montgomeryREDC_mul_eff(virtual_to_constant(num), virtual_to_constant(num), B, R, m, Np))
    else:
      num = subg_virtual(montgomeryREDC_to_virtual_mul_eff_sqr, num, (B, R, m, Np), node, g, op, subg, True)
  return result
def modexp_virtual(num, e, m, node, g, op, subg):
  B, R, Np, R2 = toMontgomery(m)
  bits = getBitSize(m)
  if m == 1: return constant_to_virtual(0)
  if e == 0: return constant_to_virtual(1)
  #print(len(g))
  #num = subg_virtual(montgomeryREDC_to_virtual_mul_eff_const_subg, num, (R2, B, R, m, Np), node, g, op, subg)
  num = montgomeryREDC_to_virtual_mul_eff_const(num, R2, B, R, m, Np, node, g, op, subg)
  num = modexp_window_to_virtual(e, m, num, B, R, Np, R2, node, g, op, subg)
  #return subg_virtual(montgomeryREDC_to_virtual_mul_eff_const, num, (1, B, R, m, Np), node, g, op, subg)
  return montgomeryREDC_to_virtual_mul_eff_const(num, 1, B, R, m, Np, node, g, op, subg)
def mul_inv_bin_to_virtual_subg(num, node, g, op, subg):
  return mul_inv_bin_to_virtual(num[:len(num)//2], num[len(num)//2:], node, g, op, subg)
def montgomery_div_step_subg(num, B, node, g, op):
  r, k = montgomery_div_step(num[:B*BITSZ], num[B*BITSZ:B*2*BITSZ], num[B*2*BITSZ:], node, g, op)
  return num[:B*BITSZ] + r + k
def montgomery_div_step(p, r, k, node, g, op):
  isend = cmp_zero_to_virtual(k, False, node, g, op)
  r = selection_to_virtual(isend, r, bound_to_virtual(get_false() + r, p, node, g, op, True), node, g, op)
  #Omura's method does not appear to work if the number is greater than the modulus
  #r = selection_to_virtual(isend, r, bound_to_virtual(get_false() + r, p, node, g, op), node, g, op)
  k = addition_to_virtual(k, not_to_virtual(isend, node, g, op), node, g, op, issub=True, need_carry=False)
  return r, k
def mul_inv_bin_gcd_step_subg(num, B, subk, node, g, op):
  if subk:
    u, v, r, s, k = mul_inv_bin_gcd_step(num[:B*BITSZ], num[B*BITSZ:B*2*BITSZ], num[B*2*BITSZ:B*2*BITSZ+(B+1)*BITSZ], num[B*2*BITSZ+(B+1)*BITSZ:B*2*BITSZ+(B+1)*2*BITSZ], B, node, g, op, num[B*2*BITSZ+(B+1)*2*BITSZ:])
    return u + v + r + s + k
  else:
    u, v, r, s = mul_inv_bin_gcd_step(num[:B*BITSZ], num[B*BITSZ:B*2*BITSZ], num[B*2*BITSZ:B*2*BITSZ+(B+1)*BITSZ], num[B*2*BITSZ+(B+1)*BITSZ:], B, node, g, op)
    return u + v + r + s
def mul_inv_bin_gcd_step(u, v, r, s, B, node, g, op, k=None):
  isend = cmp_zero_to_virtual(v, False, node, g, op) #s == 0 => v == 0
  x = addition_to_virtual(v, u, node, g, op, issub=True)
  y = addition_to_virtual(r, s, node, g, op, issub=False)
  selsu = []
  selsu.append(not_to_virtual(and_to_virtual([not_to_virtual(isend, node, g, op), u[:BITSZ]], node, g, op), node, g, op))
  selsu.append(not_to_virtual(and_to_virtual([v[:BITSZ], x[-BITSZ:]], node, g, op), node, g, op))
  selsu.append(and_to_virtual([u[:BITSZ], selsu[1], not_to_virtual(isend, node, g, op)], node, g, op))
  selsu.append(and_to_virtual([u[:BITSZ], v[:BITSZ], x[-BITSZ:]], node, g, op))
  newu = multi_bit_selection_to_virtual([selsu[0], selsu[2], selsu[3]], [u[BITSZ:], u, neg_to_virtual(x, node, g, op)[:-BITSZ][BITSZ:]], node, g, op)[:B*BITSZ]
  selsv = []
  selsv.append(and_to_virtual([u[:BITSZ], not_to_virtual(v[:BITSZ], node, g, op)], node, g, op))
  selsv.append(and_to_virtual([v[:BITSZ], x[-BITSZ:]], node, g, op))
  selsv.append(not_to_virtual(and_to_virtual([u[:BITSZ], not_to_virtual(selsv[1], node, g, op)], node, g, op), node, g, op))
  selsv.append(and_to_virtual([u[:BITSZ], v[:BITSZ], not_to_virtual(x[-BITSZ:], node, g, op)], node, g, op))
  newv = multi_bit_selection_to_virtual([selsv[0], selsv[2], selsv[3]], [v[BITSZ:], v, x[BITSZ:]], node, g, op)[:B*BITSZ]
  r = multi_bit_selection_to_virtual([selsu[0], selsu[2], selsu[3]], [r, get_false() + r, y], node, g, op)[:(B+1)*BITSZ]
  s = multi_bit_selection_to_virtual([selsv[0], selsv[2], selsv[3]], [s, get_false() + s, y], node, g, op)[:(B+1)*BITSZ]
  u, v = newu, newv
  if k is None:
    return u, v, r, s
  else: return u, v, r, s, addition_to_virtual(k, not_to_virtual(isend, node, g, op), node, g, op, issub=True, need_carry=False)
def mul_inv_bin_to_virtual(a, p, node, g, op, subg): #only for prime p!
  u, v = p, a
  r, s = constant_to_virtual(0), constant_to_virtual(1)
  B = len(p) // BITSZ
  k = constant_to_virtual(B)
  #could terminate with s when u==v to save one round for B+B-1
  uvrs = subg_virtual(mul_inv_bin_gcd_step_subg, u + zero_extend_num(v, B) + zero_extend_num(r, B+1) + zero_extend_num(s, B+1), (B, False), node, g, op, subg, False, B-1)
  uvrsk = subg_virtual(mul_inv_bin_gcd_step_subg, uvrs + k, (B, True), node, g, op, subg, False, B-1)
  r = uvrsk[B*2*BITSZ:B*2*BITSZ+(B+1)*BITSZ]
  k = uvrsk[B*2*BITSZ+(B+1)*2*BITSZ:]
  """
  for i in range(B + B):
    #some invariants: u and v are at most B bits until final B rounds where they are at most 2B-i bits
    #r and s are at most i+1/i+2 bits until final B rounds where they are at most B+1 bits
    uvbits = min(B, B+B-i)
    sbits = min(B+1, i+2); rbits = min(B+1, i+1)
    isend = cmp_zero_to_virtual(v, False, node, g, op) #s == 0 => v == 0
    x = addition_to_virtual(v, u, node, g, op, issub=True)
    y = addition_to_virtual(r, s, node, g, op, issub=False)
    selsu = []
    selsu.append(not_to_virtual(and_to_virtual([not_to_virtual(isend, node, g, op), u[:BITSZ]], node, g, op), node, g, op))
    selsu.append(not_to_virtual(and_to_virtual([v[:BITSZ], x[-BITSZ:]], node, g, op), node, g, op))
    selsu.append(and_to_virtual([u[:BITSZ], selsu[1], not_to_virtual(isend, node, g, op)], node, g, op))
    selsu.append(and_to_virtual([u[:BITSZ], v[:BITSZ], x[-BITSZ:]], node, g, op))
    newu = multi_bit_selection_to_virtual([selsu[0], selsu[2], selsu[3]], [u[BITSZ:], u, neg_to_virtual(x, node, g, op)[:-BITSZ][BITSZ:]], node, g, op)[:uvbits*BITSZ]
    selsv = []
    selsv.append(and_to_virtual([u[:BITSZ], not_to_virtual(v[:BITSZ], node, g, op)], node, g, op))
    selsv.append(and_to_virtual([v[:BITSZ], x[-BITSZ:]], node, g, op))
    selsv.append(not_to_virtual(and_to_virtual([u[:BITSZ], not_to_virtual(selsv[1], node, g, op)], node, g, op), node, g, op))
    selsv.append(and_to_virtual([u[:BITSZ], v[:BITSZ], not_to_virtual(x[-BITSZ:], node, g, op)], node, g, op))
    newv = multi_bit_selection_to_virtual([selsv[0], selsv[2], selsv[3]], [v[BITSZ:], v, x[BITSZ:]], node, g, op)[:uvbits*BITSZ]
    r = multi_bit_selection_to_virtual([selsu[0], selsu[2], selsu[3]], [r, get_false() + r, y], node, g, op)[:rbits*BITSZ]
    s = multi_bit_selection_to_virtual([selsv[0], selsv[2], selsv[3]], [s, get_false() + s, y], node, g, op)[:sbits*BITSZ]
    u, v = newu, newv
    if i >= B:
      k = addition_to_virtual(k, not_to_virtual(isend, node, g, op), node, g, op, issub=True, need_carry=False)
  """
  r = addition_to_virtual(p, bound_to_virtual(r, p, node, g, op, True), node, g, op, issub=True, need_carry=False)
  """
  for i in range(B):
    isend = cmp_zero_to_virtual(k, False, node, g, op)
    r = selection_to_virtual(isend, r, bound_to_virtual(get_false() + r, p, node, g, op, True), node, g, op)
    k = addition_to_virtual(k, not_to_virtual(isend, node, g, op), node, g, op, issub=True, need_carry=False)[:(B-i).bit_length()*2]
  """
  r = subg_virtual(montgomery_div_step_subg, p + r + k, (B,), node, g, op, subg, False, B-1)[B*BITSZ:B*2*BITSZ]
  return r
def const_to_var(num, node, g, op):
  varidx = [i for i in range(len(num)//BITSZ) if not isconst(num[i*BITSZ:(i+1)*BITSZ])]
  assert len(varidx) != 0
  if len(varidx) == len(num)//BITSZ: return num
  newnum = []
  import random
  for i in range(len(num)//BITSZ):
    if isconst(num[i*BITSZ:(i+1)*BITSZ]):
      newbit = [node[0]]; node[0] += 1
      op[newbit[0]] = ANY_OP if num[i*BITSZ] is True else FLOW_OP
      g[newbit[0]] = []
      if BITSZ == 2:
        newbit.append(node[0]); node[0] += 1
        op[newbit[1]] = FLOW_OP if num[i*BITSZ] is True else ANY_OP
        g[newbit[1]] = []
      idx = random.choice(varidx) #varidx[0]
      g[num[idx*BITSZ]].append(newbit[0])
      if BITSZ == 1:        
        g[xor_to_virtual([get_true(), [num[idx*BITSZ]]], node, g, op)[0]].append(newbit[0])
      else:
        g[num[idx*BITSZ+1]].append(newbit[0])
        g[num[idx*BITSZ]].append(newbit[1]); g[num[idx*BITSZ+1]].append(newbit[1])
      newnum.extend(newbit)
    else: newnum.extend(num[i*BITSZ:(i+1)*BITSZ])
  return newnum
def subg_virtual(func, num, spc, node, g, op, subg, recurse=False, repetition=0, gated=None):
  if isallconst(num):
    return func(num, *spc, node, g, op, *([subg] if recurse else []))
  num = const_to_var(num, node, g, op)
  tag = (func, len(num), spc)
  if not tag in subg:
    nodenew, opnew, gnew = [1], {}, {}
    numnew = [nodenew[0] + ix for ix in range(len(num))]; nodenew[0] += len(num)
    for ix in range(len(num)): opnew[numnew[ix]] = FLOW_OP; gnew[numnew[ix]] = []
    outpnew = func(numnew, *spc, nodenew, gnew, opnew, *([subg] if recurse else []))
    if isallconst(outpnew): return outpnew
    outpnew = const_to_var(outpnew, nodenew, gnew, opnew)
    imap = list(range(len(numnew)))
    omap = list(range(len(outpnew)-(BITSZ if gated is True else 0)))
    import random
    random.shuffle(imap); random.shuffle(omap)
    subg[tag] = (gnew, opnew, [numnew[x] for x in imap], [outpnew[x] for x in omap] + (outpnew[-BITSZ:] if gated is True else []), imap, omap, [])
  if repetition != 0 and subg[tag][6] == []:
    revdicto = {y: j for j, y in enumerate(subg[tag][5])}
    subg[tag][6].extend([revdicto[y] for y in subg[tag][4]])  
  outp = [node[0] + ix for ix in range(len(subg[tag][3])+1)]; node[0] += len(subg[tag][3])+1
  op[outp[0]] = (SUBG_OP, tag, [num[x] for x in subg[tag][4]], [outp[1+x] for x in subg[tag][5]], repetition); g[outp[0]] = outp[1:]
  if BITSZ == 1:
    tiein = xor_to_virtual(split_bits(num), node, g, op)
    nottiein = xor_to_virtual([get_true(), tiein], node, g, op)
    if not gated is None and not gated is True:
      g[and_to_virtual([gated, or_to_virtual([tiein, nottiein], node, g, op)], node, g, op)[0]].append(outp[0])
    else:
      g[or_to_virtual([tiein, nottiein], node, g, op)[0]].append(outp[0])
  elif not gated is None and not gated is True:
    gatefalse = node[0]; node[0] += 1
    op[gatefalse] = FLOW_OP; g[gatefalse] = []
    g[gated[0]].append(gatefalse); g[gated[1]].append(gatefalse)
    g[gated[0]].append(outp[0]); g[gatefalse].append(outp[0])
  if BITSZ == 2:
    for ix in range(len(num)):
      g[num[ix]].append(outp[0])
  for ix in range(1, len(subg[tag][3])+1): op[outp[ix]] = FLOW_OP; g[outp[ix]] = []
  return outp[1:] #return func(num, *spc, node, g, op)
def test_ops():
  import random
  tbl = [constant_to_virtual(random.randint(0, (1 << 256) - 1)) for j in range(256)]
  for i in range(1<<64, 1<<65):
    ival = constant_to_virtual(i)
    #unaryop_test(i, ival, lambda num, node, g, op, subg: multi_bit_selection_to_virtual(split_bits(decoder_to_virtual(num, node, g, op)), tbl, node, g, op), lambda a: virtual_to_constant(tbl[a]))
    #unaryop_test(i, ival, lambda num, node, g, op, subg: mulKaratsuba_to_virtual(num, num, node, g, op, subg), lambda a: a * a)
    #unaryop_test(i, ival, lambda num, node, g, op, subg: decoder_shift_to_virtual(num, node, g, op), lambda a: 1 << a)
    #unaryop_test(i, ival, lambda num, node, g, op, subg: decoder_to_virtual(num, node, g, op), lambda a: 1 << a)
    #unaryop_test(i, ival + get_false(), lambda num, node, g, op, subg, issigned=True: neg_to_virtual(num, node, g, op), lambda a: -a, issigned=True)
    #unaryop_test(i, ival, lambda num, node, g, op, subg: cmp_zero_to_virtual(num, False, node, g, op), lambda a: a == 0)
    #unaryop_test(i, ival, lambda num, node, g, op, subg: cmp_zero_to_virtual(num, True, node, g, op), lambda a: a != 0)
    for j in range(1, 256):
      jval = constant_to_virtual(j)
      #mbinop_test(i, j, ival, jval, xor_to_virtual, lambda a, b: a ^ b)
      #mbinop_test(i, j, ival, jval, and_to_virtual, lambda a, b: a & b)
      #mbinop_test(i, j, ival, jval, or_to_virtual, lambda a, b: a | b)
      #binop_test(i, j, ival, jval, lambda num1, num2, node, g, op, subg: addition_to_virtual(num1, num2, node, g, op), lambda a, b: a + b)
      #binop_test(i, j, ival, jval, lambda num1, num2, node, g, op, subg: mulKaratsuba_to_virtual(num1, num2, node, g, op, subg), lambda a, b: a * b)
      #binop_test(i, j, ival, jval, lambda num1, num2, node, g, op, subg, need_carry=True: addition_to_virtual(num1, num2, node, g, op, True, need_carry=need_carry), lambda a, b: a - b, issigned=True)
  for k in range(1, 256, 2):
    for i in range(k):
      ival = constant_to_virtual(i)
      #for j in range(k):
        #unaryop_test(i, ival, lambda num, node, g, op, subg: modexp_virtual(num, j, k, node, g, op, subg), lambda a: pow(i, j, k))

  for i in range(16):
    ival = constant_to_virtual(i)
    for j in range(2*i):
      jval = constant_to_virtual(j)
      #binop_test(i, j, ival, jval, lambda num1, num2, node, g, op, subg: bound_to_virtual(num1, num2, node, g, op, True), lambda a, b: a - b if a >= b else a, issigned=False)
      #binop_test(i, j, ival, jval, lambda num1, num2, node, g, op, subg: bound_to_virtual(num1 + get_false(), num2, node, g, op), lambda a, b: a + b if a < 0 else a, issigned=False)
  for k in range(1, 16):
    B, R, Np, R2 = toMontgomery(k)
    for i in range(k):
      ival = constant_to_virtual(i)
      for j in range(k):
        jval = constant_to_virtual(j)
        #print(i, j, k)
        #binop_test(i, j, ival, jval, lambda num1, num2, node, g, op, subg: montgomeryREDC_to_virtual_mul_eff(num1, num2, B, R, k, Np, node, g, op, subg), lambda a, b: montgomeryREDC(a * b, B, R, k, Np)) #montgomeryREDC_mul_eff(a, b, B, R, k, Np) only works if k is odd or prime
  from rsa import prime
  for j in prime(16):
    if j<5: continue
    B, R, Np, R2 = toMontgomery(j)
    jval = constant_to_virtual(j)
    for i in range(1, j):
      ival = constant_to_virtual(i)
      binop_test(i, j, ival, jval, lambda num1, num2, node, g, op, subg: mul_inv_bin_to_virtual(num1, num2, node, g, op, subg), lambda a, b: mul_inv_almostMontgomery(a, b, True, True), revargs=False)
#test_ops()
  
def test_mod_exp():
  for c in range(1022+1, 1022+1024, 2):
    B, R, Np, R2 = toMontgomery(c)
    for b in range(10):
      b = (1 << b) - 1
      #if (c & 1) != 0: virt = modexp_virtual(b, c)
      for a in range(20, 21):
        p = pow(a, b, c)
        assert p == montgomeryREDC(modexpMontgomeryWindow(montgomeryREDC((a%c)*R2, B, R, c, Np), b, c, B, R, Np, R2), B, R, c, Np), (a, b, c)
        assert p == modexp(a, b, c)
        if (c & 1) != 0:
          print(p, a, b, c)
          assert p == montgomeryREDC(modexpMontgomery(montgomeryREDC((a%c)*R2, B, R, c, Np), b, c, B, R, Np, R2), B, R, c, Np), (a, b, c, p)
          #res = run_modexp_virtual(a, c, virt)
          #assert p == res, (p, res, a, b, c)
def test_mod_inv():
  import math
  a = 1; b = 1
  while a < 1<<1024: #Fibonacci sequence is worst case
    a, b = b + a, a
    assert max_mul_inv(b, a) == mul_inv_rounds(b, a)
    assert max_mul_inv(a, b) == mul_inv_rounds(a, b), (a, b, max_mul_inv(a, b), mul_inv_rounds(a, b))
  for b in range(1, 256):
    for a in range(1, b):
      if math.gcd(a, b) != 1: continue
      assert (a * mul_inv(a, b)) % b == 1, (a, b, mul_inv(a, b))
      if b > 2 and (b & 1) != 0: assert mul_inv(a, b) == mul_inv_eff(a, b), (a, b, mul_inv(a, b), mul_inv_eff(a, b))
      continue
      if b <= 3 or b > 4 and is_prime(b, 5):
        assert mul_inv(a, b) == mul_inv_bin(a, b), (a, b, mul_inv(a, b), mul_inv_bin(a, b))
        B, R, Np, R2 = toMontgomery(b)
        assert getBitSize(b) >= mul_inv_bin_rounds(a, b), (a, b, max_mul_inv(a, b), mul_inv_rounds(a, b), mul_inv_bin_rounds(a, b))
        if b != 2: assert mul_invMontgomery(montgomeryREDC(a * R2, B, R, b, Np), b, B, R, Np, R2) == montgomeryREDC(mul_inv_almostMontgomery(montgomeryREDC(a * R2, B, R, b, Np), b) * R2, B, R, b, Np)
        if b != 2: assert mul_invMontgomery(montgomeryREDC(a * R2, B, R, b, Np), b, B, R, Np, R2) == mul_inv_almostMontgomery(montgomeryREDC(montgomeryREDC(a * R2, B, R, b, Np), B, R, b, Np), b)
        if b != 2: assert mul_inv(a, b) == mul_inv_almostMontgomery(montgomeryREDC(a * R2, B, R, b, Np), b, True, False)
        if b != 2: assert mul_inv(a, b) == montgomeryREDC(mul_inv_almostMontgomery(montgomeryREDC(a * R2, B, R, b, Np), b, True, True), B, R, b, Np)
        if b != 2: assert mul_inv(a, b) == montgomeryREDC(mul_inv_almostMontgomery(a, b, False, True), B, R, b, Np)
        if b != 2: assert mul_inv(a, b) == mul_inv_almostMontgomery(a, b, False, False)
        if b != 2: assert mul_inv(a, b) == montgomeryREDC(mul_invMontgomery(montgomeryREDC(a * R2, B, R, b, Np), b, B, R, Np, R2), B, R, b, Np), (a, b, mul_inv(a, b), mul_invMontgomery(montgomeryREDC(a * R2, B, R, b, Np), b, B, R, Np, R2), montgomeryREDC(mul_invMontgomery(montgomeryREDC(a * R2, B, R, b, Np), b, B, R, Np, R2), B, R, b, Np))
      assert max_mul_inv(a, b) >= mul_inv_rounds(a, b), (a, b, max_mul_inv(a, b), mul_inv_rounds(a, b))
      assert (mul_inv(a, b) * a) % b == 1 % b, (a, b)
def testMath():
  for a in range(5, 256+256):
    #addition_virtual(a, 0, ismul=False, isconst=False, makeconst=True)
    #addition_virtual(a, 0, ismul=False, isconst=False, isneg=True)
    #addition_virtual(-a, 0, ismul=False, isconst=False, isneg=True)
    for b in range(a+6, a + 100):
      if a != 0 and a < b and (b <= 3 or b > 4 and is_prime(b, 5)):
        #print(a, b, mul_inv(a, b), mul_inv_bin(a, b))
        addition_virtual(a, b, ismul=False, isconst=True, ismulinv=True)
      #addition_virtual(a, b, ismul=False, isconst=False, issub=False, isand=True)
      #addition_virtual(a, b, ismul=False, isconst=False, issub=False, isor=True)
      #addition_virtual(a, b, ismul=False, isconst=False, issub=False, isxor=True)
      #addition_virtual(a, b, ismul=False, isconst=False, issub=False, iscmpz=[True])
      #addition_virtual(a, b, ismul=False, isconst=False, issub=False, iscmpz=[False])
      addition_virtual(a, b, ismul=False, isconst=False, issub=False)
      addition_virtual(a, b, ismul=False, isconst=False, issub=True)
      addition_virtual(a, b, ismul=False, isconst=True, issub=False)
      addition_virtual(a, b, ismul=False, isconst=True, issub=True)
      #addition_virtual(a, b, ismul=True, isconst=False)
      #addition_virtual(b, b, ismul=True, isconst=False)
      #assert mulKaratsuba(b, b, getBitSize(b), getBitSize(b)) == b * b
      #addition_virtual(a, b, ismul=True, isconst=True)
      #addition(a, b, max(getBitSize(a), getBitSize(b)))
      #addition(a, b, max(getBitSize(a), getBitSize(b)), True)
def testMontgomery():
  #a, b = 7, 15
  #N, R, B = 17, 100, 100
  #N, R, B = 17, 10, 10
  a, b = 314, 271
  N = 997 #R, B = 1000, 10
  B, R, Np, R2 = toMontgomery(N)
  am = montgomeryREDC(a*R2, B, R, N, Np)
  #Rp = mul_inv(R, N)
  assert am == montgomeryREDC_mul_eff(a, R2, B, R, N, Np), am
  bm = montgomeryREDC(b*R2, B, R, N, Np)
  assert bm == montgomeryREDC_mul_eff(b, R2, B, R, N, Np)
  res = montgomeryREDC(am*bm, B, R, N, Np)
  assert res == montgomeryREDC_mul_eff(am, bm, B, R, N, Np)
  assert montgomeryREDC(res, B, R, N, Np) == (a * b) % N
def test_rbsd():
  for x in range(-2048, 2048):
    assert x == from_bsd(to_rbsd(to_bsd(x))), x
    assert x == from_bsd(to_bsd(x)), x
    assert -x == from_bsd(to_rbsd(bsd_neg(to_bsd(x)))), x
    assert -x == from_bsd(bsd_neg(to_rbsd(to_bsd(x)))), x
  for x in range(-128, 128):
    for y in range(-128, 128):
      assert x+y==from_bsd(to_rbsd(add_rbsd(to_rbsd(to_bsd(x)), to_rbsd(to_bsd(y)))))
      assert x-y==from_bsd(to_rbsd(add_rbsd(to_rbsd(to_bsd(x)), to_rbsd(to_bsd(y)), True)))
  print(from_bsd(add_rbsd(to_rbsd(to_bsd(26)), to_rbsd(to_bsd(26)))))#test_ecdsa()
def test_consec_ones():
  for i in range(1024):
    assert consec_ones_to_num(get_consec_ones(i)) == i
#test_consec_ones()
#test_rbsd()
test_mod_inv()
#test_mod_exp()
#testMath()
#testMontgomery()