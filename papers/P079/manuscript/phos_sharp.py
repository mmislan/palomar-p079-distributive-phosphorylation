"""Exact rational toolkit for the 2n-1 sharpness construction.

Standard library only.  Polynomials are ascending coefficient lists of
fractions.Fraction.  Species order of a full state:
(S_0..S_n, E, F, C_1..C_n, Y_1..Y_n).  Rate order per site:
(a, b, c, alpha, beta, gamma).
"""
from fractions import Fraction as Q
from math import lcm


def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def add(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                 for i in range(n)])


def scale(c, a):
    return trim([c * x for x in a])


def mul(a, b):
    p = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            p[i + j] += x * y
    return trim(p)


def val(p, x):
    z = Q(0)
    for c in reversed(p):
        z = z * x + c
    return z


def deriv(p):
    return trim([i * p[i] for i in range(1, len(p))] or [Q(0)])


def ratio(x):
    return (x * x - 1) / 8


def pair(xs):
    """Positive recurrence: (N, J) with (x-1)N(u(x)) - 2J(u(x)) = prod (x-x_j)."""
    N = [Q(1)]
    J = [(xs[0] - 1) / 2]
    for a, b in zip(xs[1::2], xs[2::2]):
        N, J = (add(mul([(a + 1) * (b + 1), Q(8)], N), scale(2 * (a + b), J)),
                add(mul([Q(0), 4 * (a + b)], N), mul([(a - 1) * (b - 1), Q(8)], J)))
    return N, J


def convert(N, J, r):
    """Degree-preserving conversion: returns (Draw, Braw)."""
    m = len(N) - 1
    nr, jr = val(N, r), val(J, r)
    q = [nr * J[0]]
    for i in range(1, m + 1):
        q.append(nr * J[i] + (q[-1] - jr * N[i - 1]) / r)
    # exact division: (u - r) Q = u J_r N - r N_r J
    assert mul([-r, Q(1)], q) == add(mul([Q(0), jr], N), scale(-r * nr, J))
    Draw = scale(4, q)
    Braw = add(scale(r, Draw), add(scale(4 * r * nr - 2 * jr, N), scale(-2 * jr, J)))
    return Draw, Braw


def normalize(Draw, Braw):
    D = scale(1 / Draw[0], Draw)
    B = scale(1 / Draw[0], Braw)
    A = mul([Q(1), Q(1)], D)
    return A, B, D


def rates_from(A, B, D):
    out = []
    for i in range(len(B)):
        c = D[i] / B[i]
        p = B[i] / A[i]
        q = D[i] / A[i + 1]
        out.append((2 * c * p, c, c, 2 * q, Q(1), Q(1)))
    return out


def state_from(A, B, D, u, s, f):
    n = len(B)
    E = u * f
    S = [A[i] * u ** i * s for i in range(n + 1)]
    C = [B[i] * u ** (i + 1) * s * f for i in range(n)]
    Y = [D[i] * u ** (i + 1) * s * f for i in range(n)]
    return S + [E, f] + C + Y


def vector_field(rates, z):
    n = len(rates)
    S, E, F = z[:n + 1], z[n + 1], z[n + 2]
    C, Y = z[n + 3:2 * n + 3], z[2 * n + 3:]
    dz = [Q(0)] * (3 * n + 3)
    for i, (a, b, c, al, be, ga) in enumerate(rates):
        bind = a * S[i] * E - b * C[i]
        cat = c * C[i]
        rbind = al * S[i + 1] * F - be * Y[i]
        rcat = ga * Y[i]
        dz[i] += -bind + rcat
        dz[i + 1] += cat - rbind
        dz[n + 1] += -bind + cat
        dz[n + 2] += -rbind + rcat
        dz[n + 3 + i] += bind - cat
        dz[2 * n + 3 + i] += rbind - rcat
    return dz


def totals(z):
    n = (len(z) - 3) // 3
    S, E, F = z[:n + 1], z[n + 1], z[n + 2]
    C, Y = z[n + 3:2 * n + 3], z[2 * n + 3:]
    return E + sum(C), F + sum(Y), sum(S) + sum(C) + sum(Y)


def jacobian(rates, z):
    """Ambient (3n+3)x(3n+3) Jacobian of the mass-action field."""
    n = len(rates)
    m = 3 * n + 3
    jac = [[Q(0)] * m for _ in range(m)]
    for i, (a, b, c, al, be, ga) in enumerate(rates):
        E, F, C, Y = n + 1, n + 2, n + 3 + i, 2 * n + 3 + i
        reactions = [(a, [i, E], [C]), (b, [C], [i, E]), (c, [C], [i + 1, E]),
                     (al, [i + 1, F], [Y]), (be, [Y], [i + 1, F]), (ga, [Y], [i, F])]
        for rate, reac, prod in reactions:
            st = [0] * m
            for q in prod:
                st[q] += 1
            for q in reac:
                st[q] -= 1
            for q in reac:
                grad = rate
                for w in reac:
                    if w != q:
                        grad *= z[w]
                for j in range(m):
                    if st[j]:
                        jac[j][q] += st[j] * grad
    return jac


def reduced_jacobian(rates, z):
    """Jacobian on ker W in coordinates y=(S_1..S_n, C, Y); S_0, E, F eliminated."""
    n = len(rates)
    m = 3 * n + 3
    idx = list(range(1, n + 1)) + list(range(n + 3, m))
    jac = jacobian(rates, z)
    size = 3 * n
    red = [[Q(0)] * size for _ in range(size)]
    for a, i in enumerate(idx):
        for b, j in enumerate(idx):
            v = jac[i][j] - jac[i][0]          # dS_0/dy_j = -1 for every y_j
            if n <= b < 2 * n:                 # C_j: dE/dC_j = -1
                v -= jac[i][n + 1]
            if b >= 2 * n:                     # Y_j: dF/dY_j = -1
                v -= jac[i][n + 2]
            red[a][b] = v
    return red


def charpoly(mat):
    """Monic characteristic polynomial, descending coefficients (Faddeev-LeVerrier)."""
    size = len(mat)
    den = 1
    for row in mat:
        for v in row:
            den = lcm(den, v.denominator)
    M = [[int(v * den) for v in row] for row in mat]
    aux = [[int(i == j) for j in range(size)] for i in range(size)]
    cint = [1]
    for k in range(1, size + 1):
        aux = [[sum(M[i][l] * aux[l][j] for l in range(size)) for j in range(size)]
               for i in range(size)]
        tr = sum(aux[i][i] for i in range(size))
        assert tr % k == 0
        c = -tr // k
        cint.append(c)
        for i in range(size):
            aux[i][i] += c
    assert all(v == 0 for row in aux for v in row)      # Cayley-Hamilton
    return [Q(c, den ** k) for k, c in enumerate(cint)]


def routh_rhp(coef):
    """Open right-half-plane root count from the Routh array (regular case only)."""
    width = (len(coef) + 1) // 2
    rows = [coef[::2] + [Q(0)] * (width - len(coef[::2])),
            coef[1::2] + [Q(0)] * (width - len(coef[1::2]))]
    while len(rows) < len(coef):
        a, b = rows[-2:]
        assert b[0] != 0
        rows.append([(b[0] * a[j + 1] - a[0] * b[j + 1]) / b[0]
                     for j in range(width - 1)] + [Q(0)])
    first = [r[0] for r in rows]
    assert all(v != 0 for v in first)
    signs = [1 if v > 0 else -1 for v in first]
    return sum(s != t for s, t in zip(signs, signs[1:])), signs


def det(mat):
    size = len(mat)
    M = [row[:] for row in mat]
    d = Q(1)
    for c in range(size):
        piv = next((r for r in range(c, size) if M[r][c] != 0), None)
        if piv is None:
            return Q(0)
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            d = -d
        d *= M[c][c]
        for r in range(c + 1, size):
            if M[r][c] != 0:
                fct = M[r][c] / M[c][c]
                for k in range(c, size):
                    M[r][k] -= fct * M[c][k]
    return d


def chart(A, B, D, r, FT, u):
    """Regular chart: H(u), H'(u), s, f, L(u), M(u), all exact."""
    L = add(B, scale(-r, D))
    M = add(B, scale(-1, mul([Q(0), Q(1)], D)))
    Lv, Mv = val(L, u), val(M, u)
    s = (r - u) / (u * Lv)
    f = FT * Lv / Mv
    Av, Bv, Dv = val(A, u), val(B, u), val(D, u)
    H = s * Av + u * s * f * (Bv + Dv)
    dL, dM = val(deriv(L), u), val(deriv(M), u)
    ds = (-(u * Lv) - (r - u) * (Lv + u * dL)) / (u * Lv) ** 2
    df = FT * (dL * Mv - Lv * dM) / Mv ** 2
    dH = (ds * Av + s * val(deriv(A), u)
          + (s * f + u * ds * f + u * s * df) * (Bv + Dv)
          + u * s * f * (val(deriv(B), u) + val(deriv(D), u)))
    return H, dH, s, f, Lv, Mv


def build(xs, r):
    """Full construction for auxiliary roots xs and enzyme-total ratio r."""
    N, J = pair(xs)
    Draw, Braw = convert(N, J, r)
    ok = min(Draw) > 0 and min(Braw) > 0 and len(Draw) == len(N) == len(Braw)
    rec = dict(xs=xs, r=r, N=N, J=J, Draw=Draw, Braw=Braw, positive=ok)
    if not ok:
        return rec
    A, B, D = normalize(Draw, Braw)
    rates = rates_from(A, B, D)
    states = []
    for x in xs:
        u = ratio(x)
        s = (x - 1) / (2 * u * val(D, u))
        f = 4 / (x + 1)
        states.append(dict(x=x, u=u, s=s, f=f, z=state_from(A, B, D, u, s, f)))
    rec.update(A=A, B=B, D=D, rates=rates, states=states,
               totals=(2 * r, Q(2), 2 * (r + 1)))
    return rec
