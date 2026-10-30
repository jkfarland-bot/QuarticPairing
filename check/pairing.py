#!/usr/bin/env python3
"""Numerical check of the hypothesis and conclusion of the pairing (QuarticPairing).

For every primary prime c = a + bi of degree one with norm p <= PMAX, compute the normalized quartic
Gauss sum from the definition of David, Dunn, Hamieh and Lin,
    g4(c) = sum_{d mod c} (d/c)_4 e~(d/c),  e~(z) = e(z + conj z),  g~(c) = g4(c)/sqrt(p),
and check (1) g~(c)^2 = -c/|c|, (2) g~(c) * conj(c)/|c| = -conj(g~(c)), and (3) for each class
beta in {1, 1 + lambda^3}, S(X; 1) = -conj S(X; 0) over these primes with weight log p.
"""
import cmath, math, sys
import numpy as np

PMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6000

def primes(n):
    s = bytearray([1]) * (n + 1); s[0:2] = b'\x00\x00'
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]

def two_squares(p):
    for a in range(1, int(math.isqrt(p)) + 1):
        b2 = p - a * a; b = math.isqrt(b2)
        if b * b == b2: return a, b
    raise ValueError

def primary_pair(p):
    a, b = two_squares(p)
    out = []
    for x, y in [(a, b), (b, a)]:
        for sx in (1, -1):
            for sy in (1, -1):
                X, Y = sx * x, sy * y
                if Y % 2 == 0 and (X + Y) % 4 == 1: out.append((X, Y))
    return sorted(set(out))

worst = [0.0, 0.0]; S = {}; count = 0
for p in primes(PMAX):
    if p % 4 != 1: continue
    for a, b in primary_pair(p):
        I = (-a * pow(b, -1, p)) % p          # i mod c, since c | a + b i
        roots = {1: 1, I: 1j, p - 1: -1, (p - I) % p: -1j}
        d = np.arange(1, p)
        pw = np.array([pow(int(x), (p - 1) // 4, p) for x in d])
        chi = np.array([roots[int(v)] for v in pw])
        g = np.sum(chi * np.exp(2j * np.pi * ((2 * a * d) % p) / p)) / math.sqrt(p)
        c = complex(a, b); u = c / abs(c)
        worst[0] = max(worst[0], abs(g * g + u))
        worst[1] = max(worst[1], abs(g * u.conjugate() + g.conjugate()))
        beta = '1' if (a % 4, b % 4) == (1, 0) else '1+l^3'
        assert (a % 4, b % 4) in [(1, 0), (3, 2)]
        s0, s1 = S.get(beta, (0, 0))
        S[beta] = (s0 + g * math.log(p), s1 + g * u.conjugate() * math.log(p))
        count += 1
print(f"primary primes of degree one, norm <= {PMAX}: {count}")
print(f"max |g~(c)^2 + c/|c||            = {worst[0]:.2e}")
print(f"max |g~(c) cbar/|c| + conj g~(c)| = {worst[1]:.2e}")
fail = worst[0] > 1e-8 or worst[1] > 1e-8
for beta, (s0, s1) in sorted(S.items()):
    r = abs(s1 + s0.conjugate())
    print(f"class {beta}: S(X;0) = {s0:.4f}, S(X;1) = {s1:.4f}, |S(X;1) + conj S(X;0)| = {r:.2e}")
    fail |= r > 1e-6
print("failures:", "yes" if fail else "none")
sys.exit(int(fail))
