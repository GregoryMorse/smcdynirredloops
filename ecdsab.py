#https://contest2021.whibox.io/rules
#https://github.com/whibox/whibox-contest-2021_supplementary-materials/blob/main/dECDSA.c
import virt
def is_point_on_curve(P, a, p, use_montgomery):
  b = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
  if use_montgomery is None:
    assert (P[1] * P[1]) % p == (((((P[0] * P[0]) % p + a) % p) * P[0]) % p + b) % p
  else:
    B, R, Np, R2 = use_montgomery
    b = virt.montgomeryREDC_mul_eff(b, R2, B, R, p, Np)
    assert virt.montgomeryREDC_mul_eff(P[1], P[1], B, R, p, Np) == virt.montgomeryBound(virt.montgomeryREDC_mul_eff(virt.montgomeryBound(virt.montgomeryREDC_mul_eff(P[0], P[0], B, R, p, Np) + a, p), P[0], B, R, p, Np) + b, p)
def point_add(P, Q, a, p, use_montgomery):
  if P == (0, 0): return Q
  if Q == (0, 0): return P
  #is_point_on_curve(P, a, p, use_montgomery)
  if use_montgomery is None:    
    if P[0] == Q[0] and P[1] == -Q[1] % p: return (0, 0)
    if P == Q:
      lbda = ((P[0] * P[0]) % p) * 3 + a
      denom = virt.mul_inv(P[1] * 2, p) #pow(P[1]*2, p-2, p)
    else:
      lbda = Q[1] - P[1]
      denom = virt.mul_inv(Q[0] - P[0], p) #pow(Q[0]-P[0], p-2, p)
    lbda = (lbda * denom) % p
    Rx = ((lbda * lbda) % p - P[0] - Q[0]) % p
    return (Rx, ((lbda * (P[0] - Rx)) % p - P[1]) % p)
  else:
    if P[0] == Q[0] and P[1] == virt.montgomeryBound(-Q[1], p, True): return (0, 0)
    B, R, Np, R2 = use_montgomery
    if P == Q:
      lbda = virt.montgomeryREDC_mul_eff(P[0], P[0], B, R, p, Np)
      lbda = virt.montgomeryBound(virt.montgomeryBound(virt.montgomeryBound(lbda << 1, p)+lbda, p)+a, p)
      denom = virt.montgomeryBound(P[1] << 1, p)
    else:
      lbda = virt.montgomeryBound(Q[1] - P[1], p, True)
      denom = virt.montgomeryBound(Q[0] - P[0], p, True)
    lbda = virt.montgomeryREDC_mul_eff(lbda, virt.mul_invMontgomery(denom, p, B, R, Np, R2), B, R, p, Np)
    #lbda = montgomeryREDC_mul_eff(lbda, modexpMontgomery(denom, p-2, p, B, R, Np, R2), B, R, p, Np)
    Rx = virt.montgomeryBound(virt.montgomeryBound(virt.montgomeryREDC_mul_eff(lbda, lbda, B, R, p, Np) - P[0], p, True) - Q[0], p, True)
    return (Rx, virt.montgomeryBound(virt.montgomeryREDC_mul_eff(lbda, virt.montgomeryBound(P[0] - Rx, p, True), B, R, p, Np) - P[1], p, True))
def is_point_on_curve_projective_affinex(P, a, p, use_montgomery):
  b = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
  if use_montgomery is None:
    Z2 = (P[2] * P[2]) % p; Z6 = (((Z2 * Z2) % p) * Z2) % p
    assert (P[1] * P[1]) % p == (((((((P[0] * P[0]) % p + a) % p) * P[0]) % p + b) % p) * Z6) % p
  else:
    B, R, Np, R2 = use_montgomery
    b = virt.montgomeryREDC_mul_eff(b, R2, B, R, p, Np)
    Z2 = virt.montgomeryREDC_mul_eff(P[2], P[2], B, R, p, Np); Z6 = virt.montgomeryREDC_mul_eff(virt.montgomeryREDC_mul_eff(Z2, Z2, B, R, p, Np), Z2, B, R, p, Np)
    assert virt.montgomeryREDC_mul_eff(P[1], P[1], B, R, p, Np) == virt.montgomeryREDC_mul_eff(virt.montgomeryBound(virt.montgomeryREDC_mul_eff(virt.montgomeryBound(virt.montgomeryREDC_mul_eff(P[0], P[0], B, R, p, Np) + a, p), P[0], B, R, p, Np) + b, p), Z6, B, R, p, Np)
def point_add_projective_affine(P, Q, p, use_montgomery): #P in projective, Q in affine except for doubling
  infty = (0, 0, 1) if use_montgomery is None else (0, 0, virt.montgomeryREDC_eff(use_montgomery[3], use_montgomery[0], use_montgomery[1], p, use_montgomery[2]))
  if P == infty: return Q if len(Q) == 3 else (Q[0], Q[1], infty[2])
  if Q == (0, 0) or Q == infty: return P
  if P == Q:
    if Q[1] == 0: return infty
    if use_montgomery is None:
      P2 = (P[1] * P[1]) % p
      A = (((P[0] * P2) % p) << 2) % p #S
      B = (((P2 * P2) % p) << 3) % p
      Z2 = (P[2] * P[2]) % p #optimized for a=p-3 of NIST-P256 curve or Z2=1 if from affine
      C = (((P[0] - Z2) % p) * ((P[0] + Z2) % p)) % p; C = (C + (C << 1) % p) % p
      X3 = (p - ((A << 1) % p) + (C * C) % p) % p
      return X3, ((C * (A - X3) % p) % p - B) % p, (((P[1] * P[2]) % p) << 1) % p #(P[1] << 1) % p
    else:
      B, R, Np, R2 = use_montgomery
      P2 = virt.montgomeryREDC_mul_eff(P[1], P[1], B, R, p, Np)
      A = virt.montgomeryBound(virt.montgomeryBound(virt.montgomeryREDC_mul_eff(P[0], P2, B, R, p, Np) << 1, p) << 1, p) #S
      Bb = virt.montgomeryBound(virt.montgomeryBound(virt.montgomeryBound(virt.montgomeryREDC_mul_eff(P2, P2, B, R, p, Np) << 1, p) << 1, p) << 1, p)
      Z2 = virt.montgomeryREDC_mul_eff(P[2], P[2], B, R, p, Np) #optimized for a of NIST-P256 curve
      C = virt.montgomeryREDC_mul_eff(virt.montgomeryBound(P[0] - Z2, p, True), virt.montgomeryBound(P[0] + Z2, p), B, R, p, Np)
      if P[2] == infty[2]:
        assert C == virt.montgomeryBound(virt.montgomeryREDC_mul_eff(P[0], P[0], B, R, p, Np) - infty[2], p, True)
      C = virt.montgomeryBound(C + virt.montgomeryBound(C << 1, p), p)
      X3 = virt.montgomeryBound(p - virt.montgomeryBound(A << 1, p) + virt.montgomeryREDC_mul_eff(C, C, B, R, p, Np), p)
      return X3, virt.montgomeryBound(virt.montgomeryREDC_mul_eff(C, virt.montgomeryBound(A - X3, p, True), B, R, p, Np) - Bb, p, True), virt.montgomeryBound(virt.montgomeryREDC_mul_eff(P[1], P[2], B, R, p, Np) << 1, p)
  else:
    assert len(Q) == 2
    if use_montgomery is None:
      Z2 = (P[2] * P[2]) % p
      A = (Q[0] * Z2) % p #U2
      B = (((Q[1] * Z2) % p) * P[2]) % p #S2
      if A == P[0]:
        if B != P[1]: return infty
        return point_add_projective_affine((Q[0], Q[1], infty[2]), (Q[0], Q[1], infty[2]), p, use_montgomery)
      C = (A - P[0]) % p; D = (B - P[1]) % p
      C2 = (C * C) % p; C3 = (C2 * C) % p
      P0C2 = (P[0] * C2) % p
      X3 = ((D * D) % p - (C3 + (P0C2 << 1) % p) % p) % p
      return X3, ((D * ((P0C2 - X3) % p)) % p - (P[1] * C3) % p) % p, (P[2] * C) % p
    else:
      B, R, Np, R2 = use_montgomery
      Z2 = virt.montgomeryREDC_mul_eff(P[2], P[2], B, R, p, Np)
      A = virt.montgomeryREDC_mul_eff(Q[0], Z2, B, R, p, Np) #U2
      Bb = virt.montgomeryREDC_mul_eff(virt.montgomeryREDC_mul_eff(Q[1], Z2, B, R, p, Np), P[2], B, R, p, Np) #S2
      if A == P[0]:
        if Bb != P[1]: return infty
        return point_add_projective_affine((Q[0], Q[1], infty[2]), (Q[0], Q[1], infty[2]), p, use_montgomery)
      C = virt.montgomeryBound(A - P[0], p, True); D = virt.montgomeryBound(Bb - P[1], p, True)
      C2 = virt.montgomeryREDC_mul_eff(C, C, B, R, p, Np); C3 = virt.montgomeryREDC_mul_eff(C2, C, B, R, p, Np)
      P0C2 = virt.montgomeryREDC_mul_eff(P[0], C2, B, R, p, Np)
      X3 = virt.montgomeryBound(virt.montgomeryREDC_mul_eff(D, D, B, R, p, Np) - virt.montgomeryBound(C3 + virt.montgomeryBound(P0C2 << 1, p), p), p, True)
      return X3, virt.montgomeryBound(virt.montgomeryREDC_mul_eff(D, virt.montgomeryBound(P0C2 - X3, p, True), B, R, p, Np) - virt.montgomeryREDC_mul_eff(P[1], C3, B, R, p, Np), p, True), virt.montgomeryREDC_mul_eff(P[2], C, B, R, p, Np)
def projective_to_affine(Q, p, use_montgomery):
  if use_montgomery is None:
    R2 = (Q[2] * Q[2]) % p
    return (Q[0] * virt.mul_inv(R2, p)) % p, (Q[1] * virt.mul_inv((R2 * Q[2]) % p, p)) % p
  else:
    B, R, Np, R2 = use_montgomery
    R2 = virt.montgomeryREDC_mul_eff(Q[2], Q[2], B, R, p, Np)
    return virt.montgomeryREDC_mul_eff(Q[0], virt.mul_inv_almostMontgomery(R2, p, True, True), B, R, p, Np), virt.montgomeryREDC_mul_eff(Q[1], virt.mul_inv_almostMontgomery(virt.montgomeryREDC_mul_eff(R2, Q[2], B, R, p, Np), p, True, True), B, R, p, Np)
def point_scalar_projective(P, scalar, num_bits, a, p, use_montgomery):
  if use_montgomery:
    use_montgomery = virt.toMontgomery(p)
    B, Rm, Np, R2 = use_montgomery
    P = (virt.montgomeryREDC_mul_eff(P[0], R2, B, Rm, p, Np), virt.montgomeryREDC_mul_eff(P[1], R2, B, Rm, p, Np))
    a = virt.montgomeryREDC_mul_eff(a, R2, B, Rm, p, Np)
    R = (0, 0, virt.montgomeryREDC_eff(R2, B, Rm, p, Np))
  else: use_montgomery = None; R = (0, 0, 1)
  for i in range(num_bits-1, -1, -1):
    R = point_add_projective_affine(R, R, p, use_montgomery)
    if (scalar & (1 << i)) != 0:
      R = point_add_projective_affine(R, P, p, use_montgomery)
  oldR = R
  R = projective_to_affine(R, p, use_montgomery)
  is_point_on_curve_projective_affinex((R[0], oldR[1], oldR[2]), a, p, use_montgomery)
  return R if use_montgomery is None else (virt.montgomeryREDC_eff(R[0], B, Rm, p, Np), virt.montgomeryREDC_eff(R[1], B, Rm, p, Np))
def point_scalar(P, scalar, num_bits, a, p, use_montgomery):
  R = (0, 0)
  if use_montgomery:
    use_montgomery = virt.toMontgomery(p)
    B, Rm, Np, R2 = use_montgomery
    P = (virt.montgomeryREDC_mul_eff(P[0], R2, B, Rm, p, Np), virt.montgomeryREDC_mul_eff(P[1], R2, B, Rm, p, Np))
    a = virt.montgomeryREDC_mul_eff(a, R2, B, Rm, p, Np)
  else: use_montgomery = None
  for i in range(num_bits-1, -1, -1):
    R = point_add(R, R, a, p, use_montgomery)
    if (scalar & (1 << i)) != 0:
      R = point_add(R, P, a, p, use_montgomery)
    """
    if (scalar & (1 << i)) == 0: #montgomery ladder
      P = point_add(R, P, a, p, use_montgomery)
      R = point_add(R, R, a, p, use_montgomery)
    else:
      R = point_add(R, P, a, p, use_montgomery)
      P = point_add(P, P, a, p, use_montgomery)
    """
  return R if use_montgomery is None else (virt.montgomeryREDC_eff(R[0], B, Rm, p, Np), virt.montgomeryREDC_eff(R[1], B, Rm, p, Np))
def get_naf(d, w, tot):
  dis = []
  while len(dis) != tot: # d > 0:
    if len(dis) == tot - 1: dis.append(d); break
    #if (d & 1) == 1:
    di = d & ((1 << w) - 1)
    di = di - (1 << w) if (di & (1 << (w-1))) != 0 else di
    d -= di
    #else: di = 0
    d >>= w#1
    dis.append(di)
  return dis
def eff_precompute_points(P, pts, num_bits, a, p, use_montgomery):
  ptdict = {}
  for vals in pts:
    for j in vals:
      x = vals[j]
      if x == 0: ptdict[x] = (0, 0)#, 1 if use_montgomery is None else virt.montgomeryREDC_eff(use_montgomery[3], use_montgomery[0], use_montgomery[1], p, use_montgomery[2]))
      if x == 1: ptdict[x] = P
      elif (x & 1) == 0 and (x >> 1) in ptdict: ptdict[x] = point_add(ptdict[x>>1], ptdict[x>>1], a, p, use_montgomery)
      else: ptdict[x] = point_add(ptdict[(x//j)*(j-1)], ptdict[(x//j)], a, p, use_montgomery)      
      #if use_montgomery is None: assert ptdict[x] == point_scalar(P, x, x.bit_length(), a, p)
  return [{x: ptdict[vals[x]] for x in vals} for vals in pts]
def precompute_point_scalar(P, scalar, num_bits, a, p, w=4, use_montgomery=False):
  d = (num_bits + (w-1)) // w
  #jb = ((1 << (w+1)) - (2 if (w & 1) == 0 else 1)) // 3
  if use_montgomery:
    use_montgomery = virt.toMontgomery(p)
    B, Rm, Np, R2 = use_montgomery
    P = (virt.montgomeryREDC_mul_eff(P[0], R2, B, Rm, p, Np), virt.montgomeryREDC_mul_eff(P[1], R2, B, Rm, p, Np))
    a = virt.montgomeryREDC_mul_eff(a, R2, B, Rm, p, Np)
    A = (0, 0, virt.montgomeryREDC_eff(R2, B, Rm, p, Np))
  else: use_montgomery = None; A = (0, 0, 1)
  Pt = eff_precompute_points(P, [{j: (1 << (w*i)) * j for j in range(1, (1 << (w-1 if i != d-1 else (num_bits % w if (num_bits % w) != 0 else w)+1))+1)} for i in range(d)], num_bits, a, p, use_montgomery)
  knaf = get_naf(scalar, w, d)
  for i in range(d):
    j = knaf[i] #k += j * (1 << (w*i))
    if j != 0:
      A = point_add_projective_affine(A, Pt[i][j] if j >= 0 else (Pt[i][-j][0], (p-Pt[i][-j][1])), p, use_montgomery)
  A = projective_to_affine(A, p, use_montgomery)
  return A if use_montgomery is None else (virt.montgomeryREDC_eff(A[0], B, Rm, p, Np), virt.montgomeryREDC_eff(A[1], B, Rm, p, Np))
def ecdsa_sign(G_x, G_y, n, p, z, d, use_montgomery=False):
  G = (G_x, G_y)
  a = p - 3
  k = z
  loop_counter = 0
  if use_montgomery:
    B, R, Np, R2 = virt.toMontgomery(n)
    dm = virt.montgomeryREDC_mul_eff(d, R2, B, R, n, Np)
    zm = virt.montgomeryREDC_mul_eff(z, R2, B, R, n, Np)
  while True:
    k += loop_counter
    k %= n
    if k == 0: loop_counter += 1; continue
    Q = point_scalar(G, k, 256, a, p, use_montgomery)
    if Q[0] == 0: loop_counter += 1; continue
    if use_montgomery:
      r = virt.montgomeryREDC_mul_eff(Q[0], R2, B, R, n, Np)
      k_inv = virt.mul_invMontgomery(virt.montgomeryREDC_mul_eff(k, R2, B, R, n, Np), n, B, R, Np, R2)
      #k_inv = virt.modexpMontgomery(virt.montgomeryREDC_mul_eff(k, R2, B, R, n, Np), n-2, n, B, R, Np, R2)
      #R3 = virt.montgomeryREDC_mul_eff(R2, R2, B, R, n, Np) #(R * R * R) % n
      #assert k_inv == virt.montgomeryREDC_mul_eff(virt.mul_inv(k, n), R2, B, R, n, Np)
      #assert k_inv == virt.montgomeryREDC_mul_eff(virt.mul_inv(virt.montgomeryREDC_mul_eff(k, R2, B, R, n, Np), n), R3, B, R, n, Np)
      s = virt.montgomeryREDC_mul_eff(virt.montgomeryBound(virt.montgomeryREDC_mul_eff(r, dm, B, R, n, Np) + zm, n), k_inv, B, R, n, Np)
      r = virt.montgomeryREDC_eff(r, B, R, n, Np)
      s = virt.montgomeryREDC_eff(s, B, R, n, Np)
    else:
      r = Q[0] % n
      k_inv = virt.mul_inv(k, n) #pow(k, n-2, n)
      s = (((((r * d) % n) + z) % n) * k_inv) % n
    if s == 0: loop_counter += 1; continue
    return r, s
def point_add_virtual(P, Q, a, p, B, Rm, Np, node, g, op, subg):
  pconst = virt.constant_to_virtual(p)
  pzero = virt.cmp_zero_to_virtual(P[0] + P[1], False, node, g, op)
  qzero = virt.cmp_zero_to_virtual(Q[0] + Q[1], False, node, g, op)
  pqloweq = virt.cmp_zero_to_virtual(virt.multi_to_virtual([P[0], Q[0]], virt.xor_to_virtual, node, g, op), False, node, g, op)
  pqhighinv = virt.cmp_zero_to_virtual(virt.multi_to_virtual([P[1], virt.addition_to_virtual(pconst, Q[1], node, g, op, True, need_carry=False)], virt.xor_to_virtual, node, g, op), False, node, g, op)
  pqhigheq = virt.cmp_zero_to_virtual(virt.multi_to_virtual([P[1], Q[1]], virt.xor_to_virtual, node, g, op), False, node, g, op)
  notpzero = virt.not_to_virtual(pzero, node, g, op)
  notqzero = virt.not_to_virtual(qzero, node, g, op)
  pqinv = virt.and_to_virtual([pqloweq, pqhighinv, notpzero, notqzero], node, g, op)
  notpqinv = virt.not_to_virtual(pqinv, node, g, op)
  pqeq = virt.and_to_virtual([pqloweq, pqhigheq, notpzero, notqzero], node, g, op)
  pqnzinv = virt.and_to_virtual([notpzero, notqzero, notpqinv], node, g, op)
  lbda = virt.montgomeryREDC_to_virtual_mul_eff_sqr(P[0], B, Rm, p, Np, node, g, op, subg)
  lbda = virt.selection_to_virtual(pqeq, virt.bound_to_virtual(virt.addition_to_virtual(virt.bound_to_virtual(virt.addition_to_virtual(virt.bound_to_virtual(virt.get_false() + lbda, pconst, node, g, op, True), lbda, node, g, op), pconst, node, g, op, True), virt.constant_to_virtual(a), node, g, op), pconst, node, g, op, True), virt.bound_to_virtual(virt.addition_to_virtual(Q[1], P[1], node, g, op, True), pconst, node, g, op), node, g, op)
  denom = virt.selection_to_virtual(pqeq, virt.bound_to_virtual(virt.get_false() + P[1], pconst, node, g, op, True), virt.bound_to_virtual(virt.addition_to_virtual(Q[0], P[0], node, g, op, True), pconst, node, g, op), node, g, op)
  lbda = virt.montgomeryREDC_to_virtual_mul_eff(lbda, virt.mul_inv_bin_to_virtual(denom, pconst, node, g, op), B, Rm, p, Np, node, g, op, subg)
  Rx = virt.bound_to_virtual(virt.addition_to_virtual(virt.bound_to_virtual(virt.addition_to_virtual(virt.montgomeryREDC_to_virtual_mul_eff_sqr(lbda, B, Rm, p, Np, node, g, op, subg), P[0], node, g, op, True), pconst, node, g, op), Q[0], node, g, op, True), pconst, node, g, op)
  Ry = virt.bound_to_virtual(virt.addition_to_virtual(virt.montgomeryREDC_to_virtual_mul_eff(lbda, virt.bound_to_virtual(virt.addition_to_virtual(P[0], Rx, node, g, op, True), pconst, node, g, op), B, Rm, p, Np, node, g, op, subg), P[1], node, g, op, True), pconst, node, g, op)
  return virt.multi_bit_selection_to_virtual([pzero, qzero, pqinv, pqnzinv], [Q[0], P[0], virt.constant_to_virtual(0), Rx], node, g, op), virt.multi_bit_selection_to_virtual([pzero, qzero, pqinv, pqnzinv], [Q[1], P[1], virt.constant_to_virtual(0), Ry], node, g, op)
def point_double_affine_projective_virtual(Q, p, B, Rm, Np, R2, node, g, op, subg):
  #following point doubling code assumes P[2]==montgomery reduction of 1
  pconst = virt.constant_to_virtual(p)
  P2 = virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_sqr, Q[1], (B, Rm, p, Np), node, g, op, subg, True)
  A = virt.bound_to_virtual(virt.get_false() + virt.bound_to_virtual(virt.get_false() + virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_subg, Q[0] + P2, (B, Rm, p, Np), node, g, op, subg, True), pconst, node, g, op, True), pconst, node, g, op, True) #S
  Bb = virt.bound_to_virtual(virt.get_false() + virt.bound_to_virtual(virt.get_false() + virt.bound_to_virtual(virt.get_false() + virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_sqr, P2, (B, Rm, p, Np), node, g, op, subg, True), pconst, node, g, op, True), pconst, node, g, op, True), pconst, node, g, op, True)
  #doubling optimized for a=p-3 of NIST-P256 curve
  #(x-1)*(x+1)=x^2-1
  C = virt.bound_to_virtual(virt.addition_to_virtual(virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_sqr, Q[0], (B, Rm, p, Np), node, g, op, subg, True), virt.constant_to_virtual(virt.montgomeryREDC_eff(R2, B, Rm, p, Np)), node, g, op, True), pconst, node, g, op)
  #C = virt.montgomeryREDC_to_virtual_mul_eff(virt.bound_to_virtual(virt.addition_to_virtual(Q[0], Z2, node, g, op, True), pconst, node, g, op), virt.bound_to_virtual(virt.addition_to_virtual(Q[0], Z2, node, g, op), pconst, node, g, op, True), B, Rm, p, Np, node, g, op, subg)
  C = virt.bound_to_virtual(virt.addition_to_virtual(C, virt.bound_to_virtual(virt.get_false() + C, pconst, node, g, op, True), node, g, op), pconst, node, g, op, True)
  X3d = virt.bound_to_virtual(virt.addition_to_virtual(virt.addition_to_virtual(pconst, virt.bound_to_virtual(virt.get_false() + A, pconst, node, g, op, True), node, g, op, True, need_carry=False), virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_sqr, C, (B, Rm, p, Np), node, g, op, subg, True), node, g, op), pconst, node, g, op, True)
  Y3d, Z3d = virt.bound_to_virtual(virt.addition_to_virtual(virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_subg, C + virt.bound_to_virtual(virt.addition_to_virtual(A, X3d, node, g, op, True), pconst, node, g, op), (B, Rm, p, Np), node, g, op, subg, True), Bb, node, g, op, True), pconst, node, g, op), virt.bound_to_virtual(virt.get_false() + Q[1], pconst, node, g, op, True) #virt.montgomeryREDC_to_virtual_mul_eff(Q[1], Q[2], B, Rm, p, Np, node, g, op, subg)
  return X3d, Y3d, Z3d
def point_double_affine_projective_virtual_subg(num, p, B, Rm, Np, R2, node, g, op, subg):
  Q = point_double_affine_projective_virtual((virt.get_bit_range(num, 0, B), virt.get_bit_range(num, B, None)), p, B, Rm, Np, R2, node, g, op, subg)
  return Q[0] + Q[1] + Q[2]
def point_add_projective_affine_virtual_subg(num, p, B, Rm, Np, R2, node, g, op, subg):
  Q = point_add_projective_affine_virtual((virt.get_bit_range(num, 0, B), virt.get_bit_range(num, B, B*2), virt.get_bit_range(num, B*2, B*3)), (virt.get_bit_range(num, B*3, B*4), virt.get_bit_range(num, B*4, None)), p, B, Rm, Np, R2, node, g, op, subg)
  return Q[0] + Q[1] + Q[2]
def point_add_projective_affine_virtual(P, Q, p, B, Rm, Np, R2, node, g, op, subg):
  pconst = virt.constant_to_virtual(p)
  pzero = virt.cmp_zero_to_virtual(P[0] + P[1], False, node, g, op)
  qzero = virt.cmp_zero_to_virtual(Q[0] + Q[1], False, node, g, op)
  Z2 = virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_sqr, P[2], (B, Rm, p, Np), node, g, op, subg, True)
  A = virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_subg, Q[0] + Z2, (B, Rm, p, Np), node, g, op, subg, True) #U2
  Bb = virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_subg, virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_subg, Q[1] + Z2, (B, Rm, p, Np), node, g, op, subg, True) + P[2], (B, Rm, p, Np), node, g, op, subg, True) #S2
  pqloweq = virt.cmp_zero_to_virtual(virt.multi_to_virtual([A, P[0]], virt.xor_to_virtual, node, g, op), False, node, g, op)
  pqhighinv = virt.cmp_zero_to_virtual(virt.multi_to_virtual([P[1], virt.addition_to_virtual(pconst, Bb, node, g, op, True, need_carry=False)], virt.xor_to_virtual, node, g, op), False, node, g, op)
  pqhigheq = virt.cmp_zero_to_virtual(virt.multi_to_virtual([Bb, P[1]], virt.xor_to_virtual, node, g, op), False, node, g, op)
  notpzero = virt.not_to_virtual(pzero, node, g, op)
  notqzero = virt.not_to_virtual(qzero, node, g, op)
  pqinv = virt.and_to_virtual([pqloweq, pqhighinv, notpzero, notqzero], node, g, op)
  notpqinv = virt.not_to_virtual(pqinv, node, g, op)
  pqeq = virt.and_to_virtual([pqloweq, pqhigheq, notpzero, notqzero], node, g, op)
  pqnzinv = virt.and_to_virtual([notpzero, notqzero, notpqinv], node, g, op)
  C = virt.bound_to_virtual(virt.addition_to_virtual(A, P[0], node, g, op, True), pconst, node, g, op)
  D = virt.bound_to_virtual(virt.addition_to_virtual(Bb, P[1], node, g, op, True), pconst, node, g, op)
  C2 = virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_sqr, C, (B, Rm, p, Np), node, g, op, subg, True)
  C3 = virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_subg, C2 + C, (B, Rm, p, Np), node, g, op, subg, True)
  P0C2 = virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_subg, P[0] + C2, (B, Rm, p, Np), node, g, op, subg, True)
  X3 = virt.bound_to_virtual(virt.addition_to_virtual(virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_sqr, D, (B, Rm, p, Np), node, g, op, subg, True), virt.bound_to_virtual(virt.addition_to_virtual(C3, virt.bound_to_virtual(virt.get_false() + P0C2, pconst, node, g, op, True), node, g, op), pconst, node, g, op, True), node, g, op, True), pconst, node, g, op)
  Y3, Z3 = virt.bound_to_virtual(virt.addition_to_virtual(virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_subg, D + virt.bound_to_virtual(virt.addition_to_virtual(P0C2, X3, node, g, op, True), pconst, node, g, op), (B, Rm, p, Np), node, g, op, subg, True), virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_subg, P[1] + C3, (B, Rm, p, Np), node, g, op, subg, True), node, g, op, True), pconst, node, g, op), virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_subg, P[2] + C, (B, Rm, p, Np), node, g, op, subg, True)
  #X3d, Y3d, Z3d = point_double_affine_projective_virtual(Q, p, B, Rm, Np, R2, node, g, op, subg)
  dbl = virt.subg_virtual(point_double_affine_projective_virtual_subg, Q[0] + Q[1], (p, B, Rm, Np, R2), node, g, op, subg, True, gated=pqeq)
  X3d, Y3d, Z3d = virt.get_bit_range(dbl, 0, B), virt.get_bit_range(dbl, B, B*2), virt.get_bit_range(dbl, B*2, None)
  X3, Y3, Z3 = virt.selection_to_virtual(pqeq, X3d, X3, node, g, op), virt.selection_to_virtual(pqeq, Y3d, Y3, node, g, op), virt.selection_to_virtual(pqeq, Z3d, Z3, node, g, op)
  return virt.multi_bit_selection_to_virtual([pzero, qzero, pqinv, pqnzinv], [Q[0], P[0], virt.constant_to_virtual(0), X3], node, g, op), virt.multi_bit_selection_to_virtual([pzero, qzero, pqinv, pqnzinv], [Q[1], P[1], virt.constant_to_virtual(0), Y3], node, g, op), virt.multi_bit_selection_to_virtual([pzero, qzero, pqinv, pqnzinv], [virt.constant_to_virtual(virt.montgomeryREDC_eff(R2, B, Rm, p, Np)), P[2], virt.constant_to_virtual(virt.montgomeryREDC_eff(R2, B, Rm, p, Np)), Z3], node, g, op)

def point_scalar_virtual(P, scalar, num_bits, a, p, node, g, op, subg):
  B, Rm, Np, R2 = virt.toMontgomery(p)
  R = (virt.constant_to_virtual(0), virt.constant_to_virtual(0))
  P = (virt.montgomeryREDC_mul_eff(P[0], R2, B, Rm, p, Np), virt.montgomeryREDC_mul_eff(P[1], R2, B, Rm, p, Np))
  P = (virt.constant_to_virtual(P[0]), virt.constant_to_virtual(P[1]))
  a = virt.montgomeryREDC_mul_eff(a, R2, B, Rm, p, Np)
  for i in range(num_bits-1, -1, -1):
    R = point_add_virtual(R, R, a, p, B, Rm, Np, node, g, op, subg)
    RR = point_add_virtual(R, P, a, p, B, Rm, Np, node, g, op, subg)
    R = (virt.selection_to_virtual(scalar[i*2:], RR[0], R[0], node, g, op), virt.selection_to_virtual(virt.get_bit_range(scalar, i, None), RR[1], R[1], node, g, op))
    break
  return virt.montgomeryREDC_to_virtual_mul_eff(R[0], virt.constant_to_virtual(1), B, Rm, p, Np, node, g, op, subg)
def get_naf_to_virtual(d, w, node, g, op):
  dis, stop = [], w
  dlen = virt.get_bit_len(d)
  tot = ((dlen + (w-1)) // w)
  if tot * w == dlen: stop+=1
  d = d + virt.get_false()
  while len(d) > 0:
    if virt.get_bit_len(d) <= stop:
      dis.append(d); break
    di = virt.get_bit_range(d, 0, w)
    d = virt.get_bit_range(virt.addition_to_virtual(d, di + virt.get_bit_range(di, -1, None) * (virt.get_bit_len(d)-virt.get_bit_len(di)), node, g, op, True, need_carry=False), w, None)
    dis.append(di)
  assert len(dis) == tot and all(virt.get_bit_len(d)==w for d in dis[:-1]) and virt.get_bit_len(dis[-1]) == (dlen % w if (dlen % w) != 0 else w)+1
  return dis
def naf_to_const(x, w):
  n, s = 0, 0
  for i in x:
    n += i << s
    s += w
  return n
def test_naf_virtual(num_bits, w=4):
  d = (num_bits + (w-1)) // w
  node, g, op, subg = virt.make_graph()
  inp = virt.make_input(num_bits, node, g, op)
  outp = get_naf_to_virtual(inp, w, node, g, op)
  import random
  for i in range(16):
    scalar = random.randint(0, (1 << 256) -1)
    knaf = get_naf(scalar, w, d)
    accepting = virt.run_virtual(op, g, 1, [inp[i] for i, x in enumerate(virt.zero_extend_num(virt.constant_to_virtual(inpval), num_bits)) if x], inp, [x for y in outp for x in y], subg)
    kn = [virt.virtual_to_constant([x is True or not x is False and x in accepting for x in k], issigned=i != len(outp)-1) for i, k in enumerate(outp)]
    assert scalar == naf_to_const(knaf, w), (scalar, naf_to_const(knaf, w), knaf)
    assert kn == knaf, (scalar, kn, knaf, w)
def projective_to_affine_virtual(Q, p, B, Rm, Np, node, g, op, subg):
  R2 = virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_sqr, Q[2], (B, Rm, p, Np), node, g, op, subg, True)
  return virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_subg, Q[0] + virt.subg_virtual(virt.mul_inv_bin_to_virtual_subg, R2 + virt.zero_extend_num(virt.constant_to_virtual(p), B), (), node, g, op, subg, True), (B, Rm, p, Np), node, g, op, subg, True) #, virt.montgomeryREDC_to_virtual_mul_eff(Q[1], virt.mul_inv_bin_to_virtual(virt.montgomeryREDC_to_virtual_mul_eff(R2, Q[2], B, Rm, p, Np, node, g, op, subg), pconst, node, g, op, subg), B, Rm, p, Np, node, g, op, subg)
def precompute_point_scalar_virtual(P, scalar, num_bits, a, p, node, g, op, subg, w=4):
  d = (num_bits + (w-1)) // w
  #jb = ((1 << (w+1)) - (2 if (w & 1) == 0 else 1)) // 3
  B, Rm, Np, R2 = virt.toMontgomery(p)
  #virt.str_consec_ones(virt.get_consec_ones(p)), virt.str_consec_ones(virt.get_consec_ones(Np))
  P = (virt.montgomeryREDC_mul_eff(P[0], R2, B, Rm, p, Np), virt.montgomeryREDC_mul_eff(P[1], R2, B, Rm, p, Np))
  a = virt.montgomeryREDC_mul_eff(a, R2, B, Rm, p, Np)
  Pt = eff_precompute_points(P, [{j: (1 << (w*i)) * j for j in range(0, (1 << (w-1 if i != d-1 else (num_bits % w if (num_bits % w) != 0 else w)+1))+1)} for i in range(d)], num_bits, a, p, (B, Rm, Np, R2))  
  #A = (virt.constant_to_virtual(0), virt.constant_to_virtual(0), virt.constant_to_virtual(virt.montgomeryREDC_eff(R2, B, Rm, p, Np)))
  knaf = get_naf_to_virtual(scalar, w, node, g, op)
  #print(Pt[1])
  #print(knaf)
  for i in range(d):
    j = knaf[i] #k += j * (1 << (w*i))
    if i != d-1:
      posj = virt.subg_virtual(virt.decoder_shift_to_virtual, virt.get_bit_range(virt.selection_to_virtual(virt.get_bit_range(j, -1, None), virt.multi_not_to_virtual(j, node, g, op), virt.addition_to_virtual(j, virt.constant_to_virtual(1), node, g, op, True, need_carry=False), node, g, op), 0, -1), (), node, g, op, subg)
      isz = virt.cmp_zero_to_virtual(j, False, node, g, op)
      posj = virt.get_bit_range(posj, 0, -1) + virt.and_to_virtual([virt.get_bit_range(posj, -1, None), virt.not_to_virtual(isz, node, g, op)], node, g, op)
      #P0 = virt.multi_bit_selection_to_table_virtual(virt.split_bits(isz+posj), [virt.constant_to_virtual(Pt[i][x][0]) for x in range(0, (1 << (w-1))+1)], node, g, op)
      #P1 = virt.multi_bit_selection_to_table_virtual(virt.split_bits(isz+posj), [virt.constant_to_virtual(Pt[i][x][1]) for x in range(0, (1 << (w-1))+1)], node, g, op)
      P0P1 = virt.multi_bit_selection_to_table_virtual(virt.split_bits(isz+posj), [virt.multi_to_virtual([virt.zero_extend_num(virt.constant_to_virtual(Pt[i][x][0]), B) + virt.zero_extend_num(virt.constant_to_virtual(Pt[i][x][1]), B), virt.get_bit_range(virt.zero_extend_num(virt.constant_to_virtual(x), w) * ((B+w-1) // w), 0, B)], virt.xor_to_virtual, node, g, op) for x in range(0, (1 << (w-1))+1)], node, g, op)
      rposj = virt.multi_to_virtual([virt.addition_to_virtual(j, virt.get_bit_range(j, -1, None) * w, node, g, op, need_carry=False), virt.get_bit_range(j, -1, None) * w], virt.xor_to_virtual, node, g, op)
      P0P1 = virt.multi_to_virtual([P0P1, virt.get_bit_range(rposj * ((B+w-1) // w), 0, B)], virt.xor_to_virtual, node, g, op)
      P0 = virt.get_bit_range(P0P1, 0, B); P1 = virt.get_bit_range(P0P1, B, None)
      P1 = virt.selection_to_virtual(virt.get_bit_range(j, -1, None), virt.addition_to_virtual(virt.constant_to_virtual(p), P1, node, g, op, True, need_carry=False), P1, node, g, op)
    else:
      posj = virt.subg_virtual(virt.decoder_shift_to_virtual, j, (), node, g, op, subg)
      #P0 = virt.multi_bit_selection_to_table_virtual(virt.split_bits(posj), [virt.constant_to_virtual(Pt[i][x][0]) for x in range(0, virt.get_bit_len(posj))], node, g, op)
      #P1 = virt.multi_bit_selection_to_table_virtual(virt.split_bits(posj), [virt.constant_to_virtual(Pt[i][x][1]) for x in range(0, virt.get_bit_len(posj))], node, g, op)
      P0P1 = virt.multi_bit_selection_to_table_virtual(virt.split_bits(posj), [virt.multi_to_virtual([virt.zero_extend_num(virt.constant_to_virtual(Pt[i][x][0]), B) + virt.zero_extend_num(virt.constant_to_virtual(Pt[i][x][1]), B), virt.get_bit_range(virt.zero_extend_num(virt.constant_to_virtual(x), virt.get_bit_len(j)) * ((B+virt.get_bit_len(j)-1) // virt.get_bit_len(j)), 0, B)], virt.xor_to_virtual, node, g, op) for x in range(0, virt.get_bit_len(posj))], node, g, op)
      P0P1 = virt.multi_to_virtual([P0P1, virt.get_bit_range(j * ((B+virt.get_bit_len(j)-1) // virt.get_bit_len(j)), 0, B)], virt.xor_to_virtual, node, g, op)
      P0 = virt.get_bit_range(P0P1, 0, B); P1 = virt.get_bit_range(P0P1, B, None)
    if i == 0:
      P2 = virt.zero_extend_num(virt.constant_to_virtual(virt.montgomeryREDC_eff(R2, B, Rm, p, Np)), B)
      A = (P0, P1, P2)
    else:
      #A = point_add_projective_affine_virtual(A, (P0, P1), p, B, Rm, Np, R2, node, g, op, subg)
      A = virt.subg_virtual(point_add_projective_affine_virtual_subg, A[0] + A[1] + A[2] + P0 + P1, (p, B, Rm, Np, R2), node, g, op, subg, True)
      A = (virt.get_bit_range(A, 0, B), virt.get_bit_range(A, B, B*2), virt.get_bit_range(A, B*2, None))
  R = projective_to_affine_virtual(A, p, B, Rm, Np, node, g, op, subg)
  return virt.montgomeryREDC_to_virtual_mul_eff_const(R, 1, B, Rm, p, Np, node, g, op, subg), A[1:] #, virt.montgomeryREDC_to_virtual_mul_eff_const(A[1], 1, B, Rm, p, Np, node, g, op, subg)
def test_point_add(P, a, p):
  B, Rm, Np, R2 = virt.toMontgomery(p)
  a = virt.montgomeryREDC_mul_eff(a, R2, B, Rm, p, Np)
  """
  node, op, g, subg = virt.make_graph()
  inp = virt.make_input(B*2*2, node, g, op)
  outp = point_add_virtual((virt.get_bit_range(inp, 0, B), virt.get_bit_range(inp, B, B*2)), (virt.get_bit_range(inp, B*2, B*3), virt.get_bit_range(inp, B*3, None)), a, p, B, Rm, Np, node, g, op, subg)
  for Q, R in ((P, P), (P, (P[0], p-P[1])), (point_add(P, P, a, p, (B, Rm, Np, R2)), P), (P, (0, 0)), ((0, 0), P), ((0, 0), (0, 0))):
    Q = (virt.montgomeryREDC_mul_eff(Q[0], R2, B, Rm, p, Np), virt.montgomeryREDC_mul_eff(Q[1], R2, B, Rm, p, Np))
    R = (virt.montgomeryREDC_mul_eff(R[0], R2, B, Rm, p, Np), virt.montgomeryREDC_mul_eff(R[1], R2, B, Rm, p, Np))
    inpval = (R[1] << (256*3)) | (R[0] << (256 * 2)) | (Q[1] << 256) | Q[0]
    accepting = virt.run_virtual(op, g, 1, [inp[i] for i, x in enumerate(virt.zero_extend_num(virt.constant_to_virtual(inpval), B*2*2)) if x], inp, outp[0] + outp[1], subg)
    q0, q1 = virt.virtual_to_constant([x in accepting for x in outp[0]]), virt.virtual_to_constant([x in accepting for x in outp[1]])
    #Q = (montgomeryREDC_mul_eff(q0, B, Rm, p, Np), montgomeryREDC_mul_eff(q1, B, Rm, p, Np))
    assert (q0, q1) == point_add(Q, R, a, p, (B, Rm, Np, R2)), ((q0, q1), point_add(Q, R, a, p, (B, Rm, Np, R2)))
  """
  node, g, op, subg = virt.make_graph()
  inp = virt.make_input(B*2*2+B, node, g, op)
  outp = point_add_projective_affine_virtual((virt.get_bit_range(inp, 0, B), virt.get_bit_range(inp, B, B*2), virt.get_bit_range(inp, B*2, B*3)), (virt.get_bit_range(inp, B*3, B*4), virt.get_bit_range(inp, B*4, None)), p, B, Rm, Np, R2, node, g, op, subg)
  for Q, R in ((P, P), ((0, 0), (0, 0)), ((0, 0), P), (point_add(P, P, a, p, (B, Rm, Np, R2)), P), (P, (P[0], p-P[1])), (P, (0, 0))):
    Q = (virt.montgomeryREDC_mul_eff(Q[0], R2, B, Rm, p, Np), virt.montgomeryREDC_mul_eff(Q[1], R2, B, Rm, p, Np), virt.montgomeryREDC_eff(R2, B, Rm, p, Np))
    R = (virt.montgomeryREDC_mul_eff(R[0], R2, B, Rm, p, Np), virt.montgomeryREDC_mul_eff(R[1], R2, B, Rm, p, Np))
    #Q = point_add_projective_affine(Q, R, p, (B, Rm, Np, R2))
    inpval = (R[1] << (256*4)) | (R[0] << (256 * 3)) | (Q[2] << (256*2)) | (Q[1] << 256) | Q[0]
    accepting = virt.run_virtual(op, g, 1, [inp[i] for i, x in enumerate(virt.zero_extend_num(virt.constant_to_virtual(inpval), B*2*2+B)) if x], inp, outp[0] + outp[1] + outp[2], subg)
    q0, q1, q2 = virt.virtual_to_constant([x in accepting for x in outp[0]]), virt.virtual_to_constant([x in accepting for x in outp[1]]), virt.virtual_to_constant([x in accepting for x in outp[2]])
    assert (q0, q1, q2) == point_add_projective_affine(Q, R, p, (B, Rm, Np, R2)), ((q0, q1, q2), point_add_projective_affine(Q, R, p, (B, Rm, Np, R2)))
def test_point_scalar(P, a, p):
  B, Rm, Np, R2 = virt.toMontgomery(p)
  node, g, op, subg = virt.make_graph()
  inp = virt.make_input(B, node, g, op)
  outp, yz = precompute_point_scalar_virtual(P, inp, B, a, p, node, g, op, subg, w=4)
  for inpval in range(0,32):
    #precompute_point_scalar(P, inpval, B, a, p, 4, True)
    accepting = virt.run_virtual(op, g, 1, [inp[i] for i, x in enumerate(virt.zero_extend_num(virt.constant_to_virtual(inpval), B)) if x], inp, outp, subg)
    q0 = virt.virtual_to_constant([x in accepting for x in outp])
    assert q0 == point_scalar_projective(P, inpval, B, a, p, True)[0], (inpval, q0, point_scalar_projective(P, inpval, B, a, p, True)[0])
def calc_point_xy_diff_virtual(P, p, a, node, g, op, subg):
  B, R, Np, R2 = virt.toMontgomery(p)
  a = virt.montgomeryREDC_mul_eff(a, R2, B, R, p, Np)
  b = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
  b = virt.montgomeryREDC_mul_eff(b, R2, B, R, p, Np)
  pconst = virt.constant_to_virtual(p)
  P0 = virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_const, P[0], (R2, B, R, p, Np), node, g, op, subg, True)
  Z2 = virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_sqr, P[2], (B, R, p, Np), node, g, op, subg, True); Z6 = virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_subg, virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_sqr, Z2, (B, R, p, Np), node, g, op, subg, True) + Z2, (B, R, p, Np), node, g, op, subg, True)
  return virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_sqr, P[1], (B, R, p, Np), node, g, op, subg, True), virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_subg, virt.bound_to_virtual(virt.addition_to_virtual(virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_subg, virt.bound_to_virtual(virt.addition_to_virtual(virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_sqr, P0, (B, R, p, Np), node, g, op, subg, True), virt.constant_to_virtual(a), node, g, op), pconst, node, g, op, True) + P0, (B, R, p, Np), node, g, op, subg, True), virt.constant_to_virtual(b), node, g, op), pconst, node, g, op, True) + Z6, (B, R, p, Np), node, g, op, subg, True)
def do_ecdsa_sign_virtual_subg(inp, G, a, n, p, dm, B, R, Np, R2, aeskey, node, g, op, subg):
  Q, soutp, iserr = do_ecdsa_sign_virtual(virt.get_bit_range(inp, 0, B), virt.get_bit_range(inp, B, None), G, a, n, p, dm, B, R, Np, R2, aeskey, node, g, op, subg)
  return Q + soutp + iserr
def do_ecdsa_sign_virtual(zinp, kinp, G, a, n, p, dm, B, R, Np, R2, aeskey, node, g, op, subg):
  if aeskey:
    import aes
    import random
    kinp = virt.split_bits(kinp)
    for i in range(len(kinp)):
      if random.randint(0, 1) == 1: kinp[i] = virt.not_to_virtual(kinp[i], node, g, op)
    random.shuffle(kinp)
    kinp = [x for y in kinp for x in y]
    aeskey = aes.AES_set_encrypt_key_virtual(kinp, 128, node, g, op)
    k = virt.subg_virtual(aes.aes_virtual_encrypt_subg, zinp[:len(zinp) // 2] + [x for y in aeskey[1] for x in y], (aeskey[0],), node, g, op, subg, True) + virt.subg_virtual(aes.aes_virtual_encrypt_subg, zinp[len(zinp) // 2:] + [x for y in aeskey[1] for x in y], (aeskey[0],), node, g, op, subg, True)
    k = virt.split_bits(k)
    #for i in range(len(k)):
    #  if random.randint(0, 1) == 1: k[i] = virt.not_to_virtual(k[i], node, g, op)
    #random.shuffle(k)
    k = [x for y in k for x in y]
  else: k = addition_to_virtual(zinp, kinp, node, g, op, need_carry=False)
  k, kdidsub = virt.bound_to_virtual(k, virt.constant_to_virtual(n), node, g, op, True, needcmp=True)
  #Q = point_scalar(G, k, 256, a, p, True)
  #Q = virt.constant_to_virtual(Q[0])
  #w value: [(512*(1<<(i-1))*((256+i-1)//i),i,(256+i-1)//i) for i in range(1, 16)]
  Q, yz = precompute_point_scalar_virtual(G, k, B, a, p, node, g, op, subg, w=13)
  #Q = point_scalar_virtual(G, kinp, B, a, p, node, g, op, subg)
  err1 = virt.cmp_zero_to_virtual(k, False, node, g, op)
  Q, Qdidsub = virt.bound_to_virtual(Q, virt.constant_to_virtual(n), node, g, op, True, needcmp=True)
  err2 = virt.cmp_zero_to_virtual(Q, False, node, g, op)
  r = virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_const, Q, (R2, B, R, n, Np), node, g, op, subg, True)
  #err2 = virt.cmp_zero_to_virtual(r, False, node, g, op)
  r = virt.montgomeryREDC_to_virtual_mul_eff_const(r, dm, B, R, n, Np, node, g, op, subg)
  #k_inv = virt.mul_invMontgomery(virt.montgomeryREDC_mul_eff(k, R2, B, R, n, Np), n, B, R, Np, R2)
  k_inv = virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_const, k, (R2, B, R, n, Np), node, g, op, subg, True)
  k_inv = virt.subg_virtual(virt.mul_inv_bin_to_virtual_subg, k_inv + virt.zero_extend_num(virt.constant_to_virtual(n), B), (), node, g, op, subg, True)
  #add aes_decrypt(kinp)-original kinp and y^2-(x^3+ax+b) to k_kinv to corrupt computation if k or r changed
  #k_inv = virt.montgomeryREDC_to_virtual_mul_eff_const(k_inv, R3, B, R, n, Np, node, g, op)
  zm = virt.subg_virtual(virt.montgomeryREDC_to_virtual_mul_eff_const, zinp, (R2, B, R, n, Np), node, g, op, subg, True)
  soutp = virt.bound_to_virtual(virt.addition_to_virtual(zm, r, node, g, op), virt.constant_to_virtual(n), node, g, op, True)
  chkq = virt.montgomeryREDC_to_virtual_mul_eff_const(virt.montgomeryREDC_to_virtual_mul_eff_const(r, virt.mul_inv_almostMontgomery(dm, n, True, True), B, R, n, Np, node, g, op, subg), 1, B, R, n, Np, node, g, op, subg)
  k_inv = virt.get_bit_range(virt.addition_to_virtual(virt.addition_to_virtual(k_inv, chkq, node, g, op, need_carry=True), Q, node, g, op, True, need_carry=False), 0, -1)
  xydiff = calc_point_xy_diff_virtual((virt.bound_to_virtual(Q + Qdidsub, virt.constant_to_virtual(n), node, g, op), yz[0], yz[1]), p, a, node, g, op, subg)
  k_inv = virt.get_bit_range(virt.addition_to_virtual(virt.addition_to_virtual(k_inv, xydiff[0], node, g, op, need_carry=True), xydiff[1], node, g, op, True, need_carry=False), 0, -1)
  kback = virt.bound_to_virtual(k + kdidsub, virt.constant_to_virtual(n), node, g, op)
  if aeskey:
    chkzinp = virt.subg_virtual(aes.aes_virtual_decrypt_subg, kback[:len(kback) // 2] + [x for y in aeskey[1] for x in y], (aeskey[0],), node, g, op, subg, True) + virt.subg_virtual(aes.aes_virtual_decrypt_subg, kback[len(kback) // 2:] + [x for y in aeskey[1] for x in y], (aeskey[0],), node, g, op, subg, True)
    k_inv = virt.get_bit_range(virt.addition_to_virtual(virt.addition_to_virtual(k_inv, zinp, node, g, op, need_carry=True), chkzinp, node, g, op, True, need_carry=False), 0, -1)
  soutp = virt.montgomeryREDC_to_virtual_mul_eff(soutp, k_inv, B, R, n, Np, node, g, op, subg)
  #zm = virt.montgomeryREDC_mul_eff(z, R2, B, R, n, Np)
  #s = virt.montgomeryREDC_mul_eff(virt.montgomeryBound(virt.montgomeryREDC_mul_eff(r, dm, B, R, n, Np) + zm, n), k_inv, B, R, n, Np)
  #s = virt.montgomeryREDC_eff(s, B, R, n, Np)
  #print(s)
  soutp = virt.montgomeryREDC_to_virtual_mul_eff_const(soutp, 1, B, R, n, Np, node, g, op, subg)
  #soutp = k_inv
  err3 = virt.cmp_zero_to_virtual(soutp, False, node, g, op)
  iserr = virt.or_to_virtual([err1, err2, err3], node, g, op)
  return virt.selection_to_virtual(iserr, zinp, Q, node, g, op), virt.selection_to_virtual(iserr, kinp, soutp, node, g, op), iserr
  #zero out r and s in case error occurs
  notiserr = virt.not_to_virtual(iserr, node, g, op)
  Q = virt.multi_to_virtual([Q, notiserr*B], virt.and_to_virtual, node, g, op)
  soutp = virt.multi_to_virtual([soutp, notiserr*B], virt.and_to_virtual, node, g, op)
  return (Q, soutp, iserr*8) #make iserr a byte not a bit for ease in C
def ecdsa_sign_virtual(G_x, G_y, n, p, z, d, aeskey):
  #R3 = montgomeryREDC(R2 * R2, B, R, n, Np)
  G = (G_x, G_y)
  a = p - 3
  B, R, Np, R2 = virt.toMontgomery(n)
  #print(hex(Np), hex(n), hex(R2))
  #print(len(virt.get_consec_ones(n)), len(virt.get_consec_ones(Np)), virt.str_consec_ones(virt.get_consec_ones(n)), virt.str_consec_ones(virt.get_consec_ones(Np)))
  dm = virt.montgomeryREDC_mul_eff(d, R2, B, R, n, Np)
  node, g, op, subg = virt.make_graph()
  zinp = virt.make_input(B, node, g, op)
  Qsoutp = virt.subg_virtual(do_ecdsa_sign_virtual_subg, zinp + virt.get_false()*B, (G, a, n, p, dm, B, R, Np, R2, aeskey), node, g, op, subg, True, repetition=-1, gated=True)
  Q, soutp = virt.get_bit_range(Qsoutp, 0, B), virt.get_bit_range(Qsoutp, B, None)
  virt.virt_to_c("ecdsa" + str(256), "ECDSA_" + str(256), op, g, 10+1, zinp, Qsoutp, subg)  
  accepting = virt.run_virtual(op, g, 1, [zinp[i] for i, x in enumerate(virt.zero_extend_num(virt.constant_to_virtual(z), B)) if x], zinp, Qsoutp, subg)
  r, s = virt.virtual_to_constant([x in accepting for x in Q]), virt.virtual_to_constant([x in accepting for x in soutp])
  print(r, s); return r, s
  k = z
  loop_counter = 0
  kinp = virt.make_input(B, node, g, op)
  inp = zinp + kinp
  Q, soutp, iserr = do_ecdsa_sign_virtual(zinp, kinp, G, a, n, p, dm, B, R, Np, R2, aeskey, node, g, op, subg)
  outp = Q + soutp + iserr
  virt.virt_to_c("ecdsa" + str(256), "ECDSA_" + str(256), op, g, 10+1, inp, outp, subg)  
  while True:
    k += loop_counter
    
    inpval = z | (loop_counter << 256)
    accepting = virt.run_virtual(op, g, 1, [inp[i] for i, x in enumerate(virt.zero_extend_num(virt.constant_to_virtual(inpval), B+B)) if x], inp, outp, subg)
    r, s = virt.virtual_to_constant([x in accepting for x in Q]), virt.virtual_to_constant([x in accepting for x in soutp])
    iserr = virt.virtual_to_constant([x in iserr for x in Q]) != 0
    
    if iserr: print("Error"); loop_counter += 1; continue
    return r, s
def ecdsa_sign_lib(Q, d, z):
  from Crypto.PublicKey import ECC
  from Crypto.Signature import DSS
  from Crypto.Hash import SHA256
  signer = DSS.new(ECC.construct(curve='p256', point_x=Q[0], point_y=Q[1], d=d), 'fips-186-3')
  l = [0]
  def nextl(): #0, 1, 1+2, 1+2+3 n(n-1)/2
    l[0] += 1
    return ((l[0] - 1) * l[0]) // 2
  signer._compute_nonce = lambda msg_hash: z + nextl()
  h = SHA256.new(); h.digest = lambda: z.to_bytes(32, 'big') #h.update(z.to_bytes(32, 'big'))
  res = int.from_bytes(signer.sign(h), 'big')
  sig = res >> 256, res & ((1 << 256) - 1)
  import ecdsa
  assert ecdsa.ecdsa_verify(ecdsa.NIST_P256.Point(
          ecdsa.NIST_P256.Modular(Q[0]),
          ecdsa.NIST_P256.Modular(Q[1])), z, sig)
  return sig
def secure_sign(d, G_x, G_y, n, p):
  import secrets
  import hashlib
  while True:
      # choose a random k
      while True:
        k = secrets.randbelow(n)
        if k != 0: break

      # Q = k x G, r = Q[x]
      Q = point_scalar((G_x, G_y), k, 256, p-3, p, False)
      Q_x = Q[0]

      # h = SHA256(r)
      m = hashlib.sha256()
      m.update(bytes.fromhex(f"{Q_x:064x}"))
      r = int(m.hexdigest(), 16)
      if (r % n) == 0:
          continue

      s = (k - r * d) % n
      if s == 0:
          continue
      return r, s
def gen_ecdsa():
  import secrets
  G_x, G_y, n, p = get_params()
  #for i in range(4, 24): test_naf_virtual(256, i)
  #test_point_scalar((G_x, G_y), p-3, p)
  #test_point_add((G_x, G_y), p-3, p)
  while True:
    d = secrets.randbelow(n)
    if d != 0: break
  #ecdsa.cmd_keygen("CHES2021")
  d = 0x84CCCAA904CB397F41A36FF9E05D4EB6C58B8E203E02373C465B6C3F03280C82
  Q = point_scalar((G_x, G_y), d, 256, p-3, p, False)
  print(f"private key: d = {d:064X}")
  print(f"public key:  Q = (x = {Q[0]:064X}, y = {Q[1]:064X})")
  print(f"encoded public key:  {Q[0]:064X}{Q[1]:064X}")
  z = secrets.randbits(256)
  import ecdsa
  sig = ecdsa_sign(G_x, G_y, n, p, z, d, False)
  assert ecdsa.ecdsa_verify(ecdsa.NIST_P256.Point(
          ecdsa.NIST_P256.Modular(Q[0]),
          ecdsa.NIST_P256.Modular(Q[1])), z, sig)
  assert ecdsa.ecdsa_verify(ecdsa.NIST_P256.Point(
          ecdsa.NIST_P256.Modular(Q[0]),
          ecdsa.NIST_P256.Modular(Q[1])), z, ecdsa_sign_virtual(G_x, G_y, n, p, z, d, True))
  r, s = secure_sign(d, G_x, G_y, n, p)
  print("Signature:", f"{r:064X}{s:064X}")  
  assert ecdsa.ec_schnorr_verify("%064X%064X" % Q, "%064X%064X" % (r, s))
def get_params(): #G_x, G_y, n, p
  return (
    int("6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296", 16),
    int("4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5", 16),
    int("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551", 16),
    int("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff", 16))
def test_ecdsa():
  #p=2^256-2^224+2^192+2^96-2^0
  #N'=2^256-2^224+2^193+2^96+2^0 #n=+2^256-2^224+2^192-2^127+2^126-2^122+2^120-2^117+2^115-2^113+2^112-2^107+2^105+2^103+2^101+2^100-2^98+2^97-2^95+2^93+2^91-2^88+2^84+2^83-2^79+2^77-2^73+2^71+2^66+2^64-2^60+2^58-2^55+2^54-2^51+2^49-2^46+2^43+2^41+2^40-2^38+2^33+2^32-2^26+2^23-2^21+2^18-2^16+2^13+2^10+2^8+2^6+2^4+2^0 (54 terms)
  #N'=+2^255-2^253+2^248-2^246+2^244+2^239-2^237+2^235-2^233+2^230-2^228+2^226-2^223+2^221+2^219+2^217-2^214+2^212+2^211-2^209+2^205+2^203+2^197-2^194+2^190+2^188+2^184-2^177+2^175-2^172+2^171-2^165+2^164-2^162+2^160-2^158+2^154+2^153-2^151+2^147+2^144-2^142+2^139-2^137+2^136-2^132+2^131-2^129+2^126+2^123+2^120-2^118+2^115+2^112+2^110+2^106+2^99+2^95-2^90+2^88+2^87-2^84+2^82+2^80-2^78+2^76+2^73+2^72-2^69+2^66+2^64-2^62+2^60-2^58+2^56-2^54+2^52+2^49-2^46+2^43+2^39+2^37+2^35+2^33+2^32-2^29+2^28-2^25+2^15+2^14-2^10+2^6+2^4-2^0 (94 terms)
    
  #p=((1 << 256) - (1 << 224) + (1 << 192) + (1 << 96) - 1)
  G_x, G_y, n, p = get_params()
  z = int("F7FD41E28DFCCA32C1CEEF637C202CA6E99E57F18AFEF957DF0866B4CDD60F5C", 16)
  import ecdsa
  #d, Q = ecdsa.cmd_keygen(None)
  d = int("9C29EDDAEF2C2B4452052B668B83BE6365004278068884FA1AC3F6D0622875C3", 16)
  Q = point_scalar((G_x, G_y), d, 256, p-3, p, False)
  assert Q == (0x78E0E9DACCC47DE94D674DF3B35624A2F08E600B26B3444077022AD575AF4DB7, 0x3084B4B8657EEA12396FDE260432BA7BDB3E092D61A42F830150D6CC8D798F9F)
  assert Q == point_scalar_projective((G_x, G_y), d, 256, p-3, p, False)
  assert Q == point_scalar_projective((G_x, G_y), d, 256, p-3, p, True)
  assert Q == precompute_point_scalar((G_x, G_y), d, 256, p-3, p, 4, True)
  assert Q == precompute_point_scalar((G_x, G_y), d, 256, p-3, p, 4)
  assert Q == point_scalar((G_x, G_y), d, 256, p-3, p, True)
  assert G_x == 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
  assert G_y == 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
  assert n == 115792089210356248762697446949407573529996955224135760342422259061068512044369
  assert p == 115792089210356248762697446949407573530086143415290314195533631308867097853951
  assert z == 0xf7fd41e28dfcca32c1ceef637c202ca6e99e57f18afef957df0866b4cdd60f5c
  assert d == 0x9C29EDDAEF2C2B4452052B668B83BE6365004278068884FA1AC3F6D0622875C3
  print("Signature: %064X%064X" % ecdsa_sign_lib(Q, d, z))
  sig = ecdsa_sign(G_x, G_y, n, p, z, d, False)
  print("Signature: %064X%064X" % sig)
  assert sig == ecdsa_sign(G_x, G_y, n, p, z, d, True)
  assert sig == (0x8007ABC1CD96650531BD8039893E8CF549A52D26E2A8A0E4700087523A7156A4, 0x2794DE699028D0768259367AD4676BFE2DACCA139263A684D0A7434EA3842BC4)
  assert ecdsa.ecdsa_verify(ecdsa.NIST_P256.Point(
          ecdsa.NIST_P256.Modular(Q[0]),
          ecdsa.NIST_P256.Modular(Q[1])), z, sig)
  sigo = ecdsa_sign_virtual(G_x, G_y, n, p, z, d, None)
  print(hex(sigo[0]), hex(sigo[1]))
  assert ecdsa.ecdsa_verify(ecdsa.NIST_P256.Point(
          ecdsa.NIST_P256.Modular(Q[0]),
          ecdsa.NIST_P256.Modular(Q[1])), z, sigo)
  r, s = ecdsa.cmd_ec_schnorr_sign("%064X" % d)
  assert ecdsa.ec_schnorr_verify("%064X%064X" % Q, "%064X%064X" % (r, s))
  print("Schnorr Signature: %064X%064X" % (r, s))
#test_ecdsa()
gen_ecdsa()