import math, random
from math import log, sqrt, gcd

def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b'\x00\x00'
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]

NMAX = 200000
PR = primes_upto(NMAX)
PRS = set(PR)
# largest prime factor table
lpf = [0] * (NMAX + 1)
for p in PR:
    for m in range(p, NMAX + 1, p):
        lpf[m] = p
lpf[1] = 1

def smooth_count(w, N):
    return sum(1 for j in range(1, N + 1) if lpf[j] <= w)

def nlog2(n):
    return n.bit_length() - 1 if n >= 1 else 0

bad = 0
# C11, C8
for w in [2, 3, 5, 7, 10, 13, 20]:
    for N in [w ** 4, w ** 4 + 1, 2 * w ** 4, w ** 5, 100000, 200000]:
        if N > NMAX or N < w ** 4:
            continue
        s = smooth_count(w, N)
        rhs = 2048 * N * log(w) ** 2 / log(N) ** 2 + 7 * N ** 0.75
        if s > rhs:
            bad += 1; print('C11 fail', w, N, s, rhs)
for w in [1, 2, 3, 5, 10, 50, 1000]:
    for N in [2, 3, 4, 5, 10, 16, 100, 1000, 50000]:
        s = smooth_count(w, N)
        rhs = sqrt(N) + 2 * N * (log(w) + 10) / log(N)
        if s > rhs:
            bad += 1; print('C8 fail', w, N, s, rhs)
        # C7
        S = [j for j in range(1, N + 1) if lpf[j] <= w]
        lhs = (len(S) - sqrt(N)) * log(N) / 2
        if lhs > sum(log(j) for j in S) + 1e-9:
            bad += 1; print('C7 fail', w, N)
        # C3
        rhs3 = 0.0
        for p in PR:
            if p > w: break
            for i in range(1, nlog2(N) + 1):
                rhs3 += log(p) * smooth_count(w, N // p ** i)
        if sum(log(j) for j in S) > rhs3 + 1e-9:
            bad += 1; print('C3 fail', w, N)
        # C9
        if N >= 16:
            for d in [1, 2, 3, 7, 50, N, N + 5]:
                s9 = smooth_count(w, N // d)
                if s9 > sqrt(N) + 4 * (N / d) * (log(w) + 10) / log(N) + 1e-9:
                    bad += 1; print('C9 fail', w, N, d)
        # C10
        if w >= 2 and w ** 4 <= N:
            if sum(log(j) for j in S) > 2 * N ** 0.75 * log(N) + 4 * N * (log(w) + 10) ** 2 / log(N):
                bad += 1; print('C10 fail', w, N)
# C6, C4, C5
for w in [1, 2, 3, 10, 100, 5000]:
    for I in [0, 1, 2, 5, 40]:
        t = sum(log(p) / p ** i for p in PR if p <= w for i in range(1, I + 1))
        if t > log(w) + 10:
            bad += 1; print('C6 fail', w, I)
    if sum(1 / (n * sqrt(n)) for n in range(2, w + 1)) > 2:
        bad += 1; print('C5 fail', w)
for p in [2, 3, 5, 100]:
    for I in [0, 1, 2, 3, 60]:
        if sum(1 / p ** i for i in range(1, I + 1)) > 1 / p + 2 / p ** 2 + 1e-12:
            bad += 1; print('C4 fail', p, I)
# B: pi table
pi = [0] * (NMAX + 1)
c = 0
for n in range(NMAX + 1):
    if n in PRS: c += 1
    pi[n] = c
for x in [2, 3, 5, 10, 50, 300]:
    for N in [x, x + 1, 2 * x, x * x, 50000, 200000]:
        if N > NMAX or N < x: continue
        Bc = sum(1 for j in range(1, N + 1) if lpf[j] > x)
        s2 = sum(pi[N // m] for m in range(1, N // x + 1))
        if Bc > s2:
            bad += 1; print('B2 fail', x, N)
        rhs = 3 * N * (1 + log(N / x)) / log(x) + 2 * N / sqrt(x)
        if Bc > rhs:
            bad += 1; print('B5 fail', x, N, Bc, rhs)
        for m in range(1, N // x + 1):
            if pi[N // m] > 3 * (N / m) / log(x) + sqrt(N / m):
                bad += 1; print('B3 fail', x, N, m); break
for B in [0, 1, 2, 10, 1000]:
    if sum(1 / sqrt(m) for m in range(1, B + 1)) > 2 * sqrt(B) + 1e-12:
        bad += 1; print('B4 fail', B)
# A lemmas brute force: A4/A5 existence of M
def V(w):
    r = 1.0
    for p in PR:
        if p > w: break
        r *= 1 - 1 / p
    return r
for (x, w, N) in [(7, 3, 30), (11, 5, 60), (13, 2, 100), (13, 13, 50), (10, 0, 40), (11, 3, 200)]:
    P = [p for p in PR if p <= x]
    Q = 1
    for p in P: Q *= p
    K = [j for j in range(1, N + 1) if all(j % p for p in P if p > w)]
    best = min(sum(1 for n in range(M + 1, M + N + 1) if all(n % p for p in P)) for M in range(Q))
    if best > V(w) * len(K) + 1e-9:
        bad += 1; print('A5 fail', x, w, N, best, V(w) * len(K))
    Ks = sum(1 for j in range(1, N + 1) if lpf[j] <= w)
    Kb = sum(1 for j in range(1, N + 1) if lpf[j] > x)
    if len(K) > Ks + Kb:
        bad += 1; print('B1 fail', x, w, N)
# D5 random
random.seed(1)
tested = 0
for _ in range(400000):
    c = 10 ** random.uniform(-3, 2)
    al = (c / 8192) * random.uniform(0.01, 1)
    ep = (c * al / 24) * random.uniform(0.01, 1)
    lx = 10 ** random.uniform(-1, 4)
    lw = al * lx * random.uniform(0.5, 1)
    lN = lx * random.uniform(1, 3)
    N = 10 ** random.uniform(0, 8)
    s4 = 10 ** random.uniform(-1, 6)
    sx = 10 ** random.uniform(-1, 6)
    T = (N / s4) * random.uniform(0, 1)
    LNX = (1 + ep * lx) * random.uniform(-1, 1)
    if not (1 / al * (14 / s4 + 12 / lx + 4 / sx) < c / 4):
        continue
    tested += 1
    lhs = (1 / lw) * (2048 * N * lw ** 2 / lN ** 2 + 7 * T + 3 * N * (1 + LNX) / lx + 2 * N / sx)
    if not lhs < c * N / lx:
        bad += 1; print('D5 fail', c, al, ep, lx, lw, lN, N, s4, sx, T, LNX); break
print('D5 tested', tested)
# D4
for x in [2, 3, 10, 1000]:
    for ep in [0.001, 0.3, 0.99, 2.5]:
        Nn = math.ceil(x ** (1 + ep))
        if not (x <= Nn and log(Nn / x) <= 1 + ep * log(x)):
            bad += 1; print('D4 fail', x, ep)
print('bad', bad)
