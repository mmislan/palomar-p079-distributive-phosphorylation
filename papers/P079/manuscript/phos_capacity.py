"""Exact rational toolkit for the loaded slow system and the stable prefix.

Standard library only; builds on phos_sharp.py (same conventions).
Levels are indexed 0..n, links (sites) 1..n.  All matrices are lists of lists
of fractions.Fraction.
"""
from fractions import Fraction as Q

import phos_sharp as ps


# ---------------------------------------------------------------- linear algebra
def eye(n):
    return [[Q(int(i == j)) for j in range(n)] for i in range(n)]


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))]
            for i in range(len(A))]


def transpose(A):
    return [list(r) for r in zip(*A)]


def inverse(A):
    n = len(A)
    M = [list(row) + [Q(int(i == j)) for j in range(n)] for i, row in enumerate(A)]
    for i in range(n):
        piv = next(j for j in range(i, n) if M[j][i] != 0)
        M[i], M[piv] = M[piv], M[i]
        v = M[i][i]
        M[i] = [x / v for x in M[i]]
        for j in range(n):
            if j != i and M[j][i] != 0:
                w = M[j][i]
                M[j] = [a - w * b for a, b in zip(M[j], M[i])]
    return [row[n:] for row in M]


def ldl_pivots(A):
    """Pivots of the LDL^T factorization; all positive iff A is positive definite."""
    n = len(A)
    L = [[Q(int(i == j)) for j in range(n)] for i in range(n)]
    D = []
    for i in range(n):
        di = A[i][i] - sum(L[i][k] ** 2 * D[k] for k in range(i))
        D.append(di)
        if di == 0:
            return D
        for j in range(i + 1, n):
            L[j][i] = (A[j][i] - sum(L[j][k] * L[i][k] * D[k] for k in range(i))) / di
    return D


def norm_inf(A):
    return max(sum(abs(v) for v in row) for row in A)


def hurwitz(A):
    """Exact Routh test: True iff all eigenvalues lie in the open left half-plane."""
    if len(A) == 0:
        return True
    try:
        rhp, _ = ps.routh_rhp(ps.charpoly(A))
    except AssertionError:
        return False
    return rhp == 0


# ---------------------------------------------------------------- coalesced geometry
def coalesced(n, r):
    """Construction with all 2n-1 auxiliary roots equal to 3."""
    rec = ps.build([Q(3)] * (2 * n - 1), Q(r))
    assert rec['positive']
    return rec


def incidence(n):
    """n x (n+1) matrix with row i (link i+1) equal to e_{i+1} - e_i."""
    R = [[Q(0)] * (n + 1) for _ in range(n)]
    for i in range(n):
        R[i][i] = Q(-1)
        R[i][i + 1] = Q(1)
    return R


def loaded(n, state, ET, FT):
    """Mass matrix M, feedback h and K = (-R + 1 h^T) M^{-1} R^T at a fast-binding state."""
    S = state[:n + 1]
    c = state[n + 3:2 * n + 3] + [Q(0)]
    y = [Q(0)] + state[2 * n + 3:]
    M = [[(S[i] + c[i] + y[i] if i == j else Q(0)) - c[i] * c[j] / ET - y[i] * y[j] / FT
          for j in range(n + 1)] for i in range(n + 1)]
    h = [y[i] / FT - c[i] / ET for i in range(n + 1)]
    R = incidence(n)
    left = [[-R[i][j] + h[j] for j in range(n + 1)] for i in range(n)]
    K = matmul(matmul(left, inverse(M)), transpose(R))
    return M, h, K


def limit_data(n):
    """Large-r limiting objects of the coalesced geometry (exact)."""
    N, J = ps.pair([Q(3)] * (2 * n - 1))
    jm = sum(J)
    assert sum(N) == jm == Q(36) ** (n - 1)
    d = [(N[i] + J[i]) / jm for i in range(n)]
    y = [Q(0)] + [J[i] / jm for i in range(n)]            # y_0..y_n
    v = y[n]
    mu = sum(i * d[i] for i in range(n)) / 2
    R0 = [[Q(0)] * n for _ in range(n - 1)]
    for i in range(n - 1):
        R0[i][i] = Q(-1)
        R0[i][i + 1] = Q(1)
    H = [[sum(R0[a][k] * R0[b][k] / d[k] for k in range(n)) for b in range(n - 1)]
         for a in range(n - 1)]
    g = [(10 * (J[i - 1] if i else 0) + (2 + v) * J[i]) / (2 * (7 - 4 * v) * (N[i] + J[i]))
         for i in range(n)]
    phi = [g[i] - g[i - 1] for i in range(1, n)]
    Bstar = [[-H[a][b] + phi[b] for b in range(n - 1)] for a in range(n - 1)]
    z = [sum(row) for row in inverse(H)] if n > 1 else []
    G = sum(p * q for p, q in zip(phi, z))
    return dict(N=N, J=J, jm=jm, d=d, y=y, v=v, mu=mu, H=H, g=g, phi=phi, Bstar=Bstar,
                z=z, G=G)


def retune(rec, lam, b, beta, eps=Q(1)):
    """Source-preserving kinetics: catalytic scales lam, dissociation b, beta, relaxation eps."""
    A, B, D = rec['A'], rec['B'], rec['D']
    rates = []
    for i in range(len(B)):
        p = B[i] / A[i]
        q = D[i] / A[i + 1]
        g = lam[i]
        c = lam[i] * D[i] / B[i]
        a = (b[i] + c) * p / eps
        bb = (b[i] + c) / eps - c
        al = (beta[i] + g) * q / eps
        be = (beta[i] + g) / eps - g
        rates.append((a, bb, c, al, be, g))
    assert min(min(row) for row in rates) > 0
    return rates
