#Windows: "C:\Program Files\SageMath 9.2\runtime\bin\mintty.exe" -t 'SageMath 9.2 Console' /bin/bash --login -c '/opt/sagemath-9.2/sage'
#%run aes.sage
#https://download.hrz.tu-darmstadt.de/media/FB20/Dekanat/Publikationen/CDC/Ahmed_Charfi.bachelor.pdf
#Bosphorus has an anf2cnf solver/converter
#https://arxiv.org/pdf/1812.04580.pdf
#https://github.com/meelgroup/bosphorus
from sage.sat.solvers.dimacs import DIMACS
from sage.sat.converters.polybori import *
n, r, c, e = 10, 4, 4, 8 #n (1-10) is number of encryption rounds, r,c (1,2 or 4) are number of rows/columns in input matrix, e is degree of the underlying field either 4 or 8
"""
sr = mq.SR(n, r, c, e, star=True, gf2=True, polybori=True, allow_zero_inversions=True, correct_only=True)
P = sr.vector([0] * 16 * 8)
K = sr.vector([0] * 16 * 8)
sum([int(x[0]) << (127-i) for i, x in enumerate(sr(P, K).rows())]).to_bytes(length=16, byteorder='big')
F, s = sr.polynomial_system(P=P,K=K) #sr(P, K).str()
B = BooleanPolynomialRing(F.ring().ngens(), F.ring().variable_names())
F = [B(f) for f in F if B(f)]
solver = DIMACS(filename="AES_test.txt") #write the equations in a file called AES_cnf.txt
enc = CNFEncoder(solver, B)
for f in F: enc.clauses(f)
_ = solver.write()
with open("AES_testmap.txt", "w") as f:
	for i, x in enumerate(enc.phi):
		if not x is None: f.write(str(x) + " " + str(i) + "\n")
from sage.sat.solvers.cryptominisat import CryptoMiniSat
solver = CryptoMiniSat() #pip install pycryptosat from Sage Shell run as administrator
#from sage.sat.solvers import Glucose
#solver = Glucose()
solver.clauses("AES_test.txt")
solver()
"""
sr = mq.SR(n, r, c, e, star=True, gf2=True, polybori=True, allow_zero_inversions=True, correct_only=True)
sr.sbox()
sr.key_schedule_polynomials(1)
R = sr.R
print(R.repr_long())
#Now, we can construct the purely symbolic equation system:
vn = sr.varstrs("P",0,16,8) + R.variable_names() + sr.varstrs("C",10,16,8)
R = BooleanPolynomialRing(len(vn),vn)
sr.R = R
P = sr.vars("P",0)
C = sr.vars("C",10)
F,s = sr.polynomial_system(P=P,K=sr.vars("k",0),C=C)
B = BooleanPolynomialRing(F.ring().ngens(), F.ring().variable_names())
solver = DIMACS(filename="AES_cnf.txt") #write the equations in a file called AES_cnf.txt
enc = CNFEncoder(solver, B)
for f in F: enc.clauses(f)
_ = solver.write()
with open("AES_map.txt", "w") as f:
	for i, x in enumerate(enc.phi):
		if not x is None: f.write(str(x) + " " + str(i) + "\n")

#output is default directory of %USERPROFILE% directory on Windows