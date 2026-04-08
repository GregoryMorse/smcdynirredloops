#!/usr/bin/env python3

#import click
import hashlib
import random

#from nist_p256 import NIST_P256
from dataclasses import dataclass


class NIST_P256:
    p = 115792089210356248762697446949407573530086143415290314195533631308867097853951
    n = 115792089210356248762697446949407573529996955224135760342422259061068512044369

    a = p-3
    b = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b

    @dataclass
    class Modular:
        val: int

        def __add__(self, y: "Modular") -> "Modular":
            return NIST_P256.Modular((self.val + y.val) % NIST_P256.p)

        def __sub__(self, y: "Modular") -> "Modular":
            return NIST_P256.Modular((self.val - y.val) % NIST_P256.p)

        def __neg__(self) -> "Modular":
            return NIST_P256.Modular(-self.val)

        def __mul__(self, y: "Modular") -> "Modular":
            return NIST_P256.Modular((self.val * y.val) % NIST_P256.p)

        def __rmul__(self, y: int) -> "Modular":
            return NIST_P256.Modular(y) * self

        def __pow__(self, exp: int) -> "Modular":
            return NIST_P256.Modular(int(pow(self.val, exp, NIST_P256.p)))

        def __truediv__(self, y: "Modular") -> "Modular":
            y_inv = y ** (self.p-2)
            return self * y_inv

        def __eq__(self, y):
            return ((self.val - y.val) % self.p) == 0

        def __repr__(self):
            return f'{self.val:064X}'

    @dataclass
    class Point:
        x: "NIST_P256.Modular"
        y: "NIST_P256.Modular"

        def __add__(self, Q: "Point") -> "Point":
            # either self or Q is the point at infinity
            if self.is_at_infinity:
                return Q
            if Q.is_at_infinity:
                return self

            # self and Q are inverse, including the case where y=0
            if self == -Q:
                return NIST_P256.Point.infinity()

            # normal cases
            if self == Q:  # doubling
                lambda_ = (3 * (self.x ** 2) + self.a) / (2*self.y)
            else:          # add
                lambda_ = (Q.y - self.y) / (Q.x - self.x)

            R_x = (lambda_ ** 2) - self.x - Q.x
            R_y = lambda_ * (self.x - R_x) - self.y
            return NIST_P256.Point(R_x, R_y)

        def __eq__(self, Q):
            return self.x == Q.x and self.y == Q.y

        def __neg__(self) -> "Point":
            return NIST_P256.Point(self.x, -self.y)

        def __sub__(self, Q: "Point") -> "Point":
            return self + (-Q)

        def __rmul__(self, scalar: int) -> "Point":
            R = NIST_P256.Point(0, 0)

            for i, b in enumerate(bin(scalar)[2:]):
                R = R + R
                if int(b):      # adding
                    R = self + R

            return R

        def __repr__(self):
            return f"x = {self.x}, y = {self.y}"

        def __str__(self):
            return f"{self.x}{self.y}"

        @property
        def is_at_infinity(self):
            return self.x == self.y == 0

        @property
        def is_on_curve(self):
            return self.y ** 2 == self.x**3 + self.a*self.x + self.b

        @classmethod
        def infinity(cls):
            return NIST_P256.Point(0, 0)

    G = Point(
        Modular(0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296),
        Modular(0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5)
    )
    Point.a = Modular(a)
    Point.b = Modular(b)
    Modular.p = p

    @classmethod
    def scalar_multiplication(cls, scalar: int, P: Point = None) -> Point:
        if not P:
            P = cls.G
        return scalar * P



#@click.command()
#@click.argument('seed', default="CHES2021")
def cmd_keygen(seed):
    # CHES 2021 will start from September 12, 2021
    random.seed(seed)
    d = random.randint(1, NIST_P256.n-1)
    Q = NIST_P256.scalar_multiplication(d)

    print(f"seed: seed = {seed}")
    print(f"private key: d = {d:064X}")
    print(f"public key:  Q = ({repr(Q)})")
    print(f"encoded public key:  {Q}")

    return d, Q


#@click.command()
#@click.argument('pa_str', metavar="PUBLIC_KEY")
#@click.argument('hash_', metavar="HASH")
#@click.argument('signature', metavar="SIGNATURE")
def cmd_ecdsa_verify(pa_str: str, hash_: str, signature: str):
    if ecdsa_verify_str(pa_str, hash_, signature):
        print("Good signature :)")
    else:
        print("Wrong signature")
    return True


#@click.command()
#@click.argument('d_str', metavar="PRIVATE_KEY")
def cmd_ec_schnorr_sign(d_str: str):
    """Variables names follow BSI EC-Schnorr standardized"""
    d = decode_private(d_str)

    while True:
        # choose a random k
        k = random.randint(1, NIST_P256.n-1)

        # Q = k x G, r = Q[x]
        Q = NIST_P256.scalar_multiplication(k)
        Q_x = Q.x.val

        # h = SHA256(r)
        m = hashlib.sha256()
        m.update(bytes.fromhex(f"{Q_x:064x}"))
        r = int(m.hexdigest(), 16)
        if (r % NIST_P256.n) == 0:
            continue

        s = (k - r * d) % NIST_P256.n
        if s == 0:
            continue

        print("Signature:", f"{r:064X}{s:064X}")

        return r, s


#@click.command()
#@click.argument('pa_str', metavar="PUBLIC_KEY")
#@click.argument('signature', metavar="SIGNATURE")
def cmd_ec_schnorr_verify(pa_str, signature):
    return ec_schnorr_verify(pa_str, signature)


def ec_schnorr_verify(pa_str, signature):
    """Variables names follow BSI EC-Schnorr standardized"""
    P_A = decode_public(pa_str)
    if not check_public_key(P_A):
        return False

    r, s = decode_signature(signature)
    if not check_r_s(r, s):
        return False

    Q = NIST_P256.scalar_multiplication(s) + \
        NIST_P256.scalar_multiplication(r, P_A)
    if Q.is_at_infinity:
        print("Wrong signature")
        return False

    m = hashlib.sha256()
    m.update(bytes.fromhex(f"{Q.x.val:064x}"))
    v = int(m.hexdigest(), 16)

    print("Good signature :)" if r == v else "Wrong signature")
    return r == v


def decode_signature(signature):
    if len(signature) != 128:
        raise click.ClickException(
            "SIGNATURE should be 128 hexadecimal digits long.")
    try:
        r = int(signature[:32*2], 16)
        s = int(signature[32*2:], 16)
    except ValueError:
        raise click.ClickException(
            "PUBLIC_KEY is not in valid hex.")
    return r, s


def decode_private(d_str):
    try:
        d = int(d_str, 16)
    except ValueError:
        raise click.ClickException("PRIVATE_KEY is not in valid hex.")
    return d


def decode_public(pa_str):
    if len(pa_str) != 128:
        raise click.ClickException(
            "PUBLIC_KEY should be 128 hexadecimal digits long.")
    try:
        pa_x = int(pa_str[:64], 16)
        pa_y = int(pa_str[64:], 16)
    except ValueError:
        raise click.ClickException("PUBLIC_KEY is not in valid hex.")
    return NIST_P256.Point(NIST_P256.Modular(pa_x), NIST_P256.Modular(pa_y))


def check_public_key(Q: NIST_P256.Point):
    if Q.is_at_infinity:
        print("Public key should not be infinity")
        return False

    if not Q.is_on_curve:
        print("Public key is not on curve")
        return False

    point_infinity = NIST_P256.scalar_multiplication(NIST_P256.n, Q)
    if not point_infinity.is_at_infinity:
        print("Something wrong with the public key")
        return False

    return True


def validate_private_key(d_str, pa_str):
    try:
        d = decode_private(d_str)
        pa = decode_public(pa_str)
        return pa == NIST_P256.scalar_multiplication(d)
    except:
        return False


def check_r_s(r, s):
    n = NIST_P256.n

    if r < 1 or r > n-1:
        print("r is not between [1, n-1]")
        return False

    if s < 1 or s > n-1:
        print("s is not between [1, n-1]")
        return False

    return True


def ecdsa_verify_str(pa_str: str, hash_: str, signature: str):
    Q = decode_public(pa_str)
    hash_ = int(hash_, 16)
    r, s = decode_signature(signature)
    return ecdsa_verify(Q, hash_, (r, s))


def ecdsa_verify(Q: NIST_P256.Point, hash_: int, signature: (int, int)):
    if not check_public_key(Q):
        return False

    r, s = signature
    if not check_r_s(r, s):
        return False

    n = NIST_P256.n
    z = hash_ % n

    s_inv = int(pow(s, n-2, n))
    assert (s*s_inv) % n == 1
    u1 = (z * s_inv) % n
    u2 = (r * s_inv) % n

    P = NIST_P256.scalar_multiplication(u1) + \
        NIST_P256.scalar_multiplication(u2, Q)
    if P.is_at_infinity:
        print("Invalid signature")
        return False

    return (P.x.val % n) == r
    
if __name__ == "__main__":
    P = NIST_P256.scalar_multiplication(
        12078056106883488161242983286051341125085761470677906721917479268909056)
    print(P)
    
# key pairs
d = 0x9C29EDDAEF2C2B4452052B668B83BE6365004278068884FA1AC3F6D0622875C3
Q_x = 0x78E0E9DACCC47DE94D674DF3B35624A2F08E600B26B3444077022AD575AF4DB7
Q_y = 0x3084B4B8657EEA12396FDE260432BA7BDB3E092D61A42F830150D6CC8D798F9F

# message and random key
# echo -n CHES2021 | sha256sum
hash_ = 0xf7fd41e28dfcca32c1ceef637c202ca6e99e57f18afef957df0866b4cdd60f5c

# cat test_hash | ./dECDSA
r = 0x8007abc1cd96650531bd8039893e8cf549a52d26e2a8a0e4700087523a7156a4
s = 0x2794de699028d0768259367ad4676bfe2dacca139263a684d0a7434ea3842bc4


def test_test_vectors():
    Q = NIST_P256.Point(
        NIST_P256.Modular(Q_x),
        NIST_P256.Modular(Q_y),
    )
    assert ecdsa_verify(Q, hash_, (r, s))