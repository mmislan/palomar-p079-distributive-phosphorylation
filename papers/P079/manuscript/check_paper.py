"""Exact replay of every formula and number printed in the paper.

Standard library only.  Usage:  python check_paper.py [--full]
Writes check_paper_report.json next to this file.  The proofs in the paper do
not depend on these computations, except for the statements explicitly marked
as computer-assisted (Section 9).
"""
import json
import random
import sys
import time
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path

import phos_sharp as ps
import phos_capacity as pc

HERE = Path(__file__).resolve().parent
FULL = '--full' in sys.argv
REPORT = {}
COUNT = [0]


def ok(cond, msg=''):
    COUNT[0] += 1
    if not cond:
        raise AssertionError(msg)


# ------------------------------------------------------------------ helpers
def sturm_count_negative(p):
    """Number of distinct real roots of p in (-inf, 0), by Sturm's theorem."""
    def polyrem(a, b):
        a = list(a)
        while len(a) >= len(b) and any(a):
            f = a[-1] / b[-1]
            for i in range(len(b)):
                a[len(a) - len(b) + i] -= f * b[i]
            a.pop()
        return ps.trim(a or [Q(0)])
    seq = [ps.trim(p), ps.deriv(p)]
    while len(seq[-1]) > 1 or seq[-1][0] != 0:
        rem = polyrem(seq[-2], seq[-1])
        if len(rem) == 1 and rem[0] == 0:
            break
        seq.append([-c for c in rem])
    def changes(vals):
        vals = [v for v in vals if v != 0]
        return sum((a > 0) != (b > 0) for a, b in zip(vals, vals[1:]))
    at_minus_inf = [q[-1] * (-1) ** (len(q) - 1) for q in seq]
    at_zero = [q[0] for q in seq]
    return changes(at_minus_inf) - changes(at_zero)


def ratios_ok(N, J):
    m = len(J) - 1
    inc = [J[i - 1] / J[i] if i else Q(0) for i in range(m + 1)]
    ok(all(a < b for a, b in zip(inc, inc[1:])), 'J_{i-1}/J_i strictly increasing')
    rat = [J[i] / N[i] for i in range(m + 1)]
    ok(all(a <= b for a, b in zip(rat, rat[1:])), 'J_i/N_i nondecreasing')


def rate_tuple_list(rows):
    return [tuple(Q(v) for v in row) for row in rows]


# ------------------------------------------------------------------ Section 2: n = 1
def check_base_case():
    rates = [(Q(1),) * 6]
    z = [Q(2), Q(2), Q(1), Q(1), Q(1), Q(1)]
    ok(all(v == 0 for v in ps.vector_field(rates, z)))
    ok(ps.totals(z) == (2, 2, 6))
    JS = ps.reduced_jacobian(rates, z)
    ok(JS == [[-1, 1, 3], [-1, -5, -1], [1, 0, -4]], 'n=1 class matrix')
    cp = ps.charpoly(JS)
    ok(cp == [1, 10, 27, 10])
    rhp, _ = ps.routh_rhp(cp)
    ok(rhp == 0)
    REPORT['base_case_charpoly'] = [str(c) for c in cp]


# ------------------------------------------------------------------ Sections 4: construction
def check_construction():
    rng = random.Random(20260920)
    nmax = 8 if FULL else 6
    for n in range(1, nmax + 1):
        for xs, r in [([Q(j + 2) for j in range(2 * n - 1)], Q((4 * n * n - 1) // 8 + 1)),
                      ([Q(3)] * (2 * n - 1), Q(3 * n, 2) + (1 if n == 1 else 0))]:
            rec = ps.build(xs, r)
            ok(rec['positive'], f'positivity n={n}')
            N, J = rec['N'], rec['J']
            ok(N[-1] == 8 ** (n - 1) and J[-1] == 8 ** (n - 1) * (sum(xs) - 1) / 2)
            if n > 1:
                ok(sturm_count_negative(N) == n - 1 and sturm_count_negative(J) == n - 1,
                   'real negative simple roots')
                ratios_ok(N, J)
            for st in rec['states']:
                ok(all(v == 0 for v in ps.vector_field(rec['rates'], st['z'])))
                ok(ps.totals(st['z']) == rec['totals'])
                ok(min(st['z']) > 0)
                # free inventory identity and free enzymes
                ok(sum(st['z'][:n + 1]) == st['z'][n + 1] + st['z'][n + 2])
                ok(st['z'][n + 1] == (st['x'] - 1) / 2 and st['z'][n + 2] == 4 / (st['x'] + 1))
    # random root configurations, possibly repeated: interlacing consequences and threshold
    trials = 300 if FULL else 80
    for _ in range(trials):
        n = rng.randint(2, 6)
        xs = [Q(rng.randint(11, 60), 10) for _ in range(2 * n - 1)]
        if rng.random() < 0.4:
            xs[1] = xs[0]
        N, J = ps.pair(xs)
        ok(sturm_count_negative(N) == n - 1 and sturm_count_negative(J) == n - 1)
        ratios_ok(N, J)
        # smallest r on a grid satisfying r > max u_j and 4r + sqrt(1+8r) >= sum x_j
        r = max(ps.ratio(x) for x in xs) + Q(1, 100)
        while not (4 * r + Q(isqrt(int((1 + 8 * r) * 10 ** 8)), 10 ** 4) >= sum(xs)):
            r += Q(1, 50)
        Draw, Braw = ps.convert(N, J, r)
        ok(min(Draw) > 0 and min(Braw) > 0, 'threshold positivity')


# ------------------------------------------------------------------ determinant formula
def det_formula_holds(rates, z, r):
    n = len(rates)
    A, B, D = abd_from_rates(rates)
    u = z[n + 1] / z[n + 2]
    FT = ps.totals(z)[1]
    _, dH, _, _, _, Mv = ps.chart(A, B, D, r, FT, u)
    pref = Q(1)
    for (a, b, c, al, be, ga) in rates:
        pref *= (b + c) * al * ga
    lhs = ps.det(ps.reduced_jacobian(rates, z))
    rhs = (-1) ** (n + 1) * pref * z[n + 2] ** n * u * Mv * dH
    return lhs == rhs, lhs


def abd_from_rates(rates):
    t = [Q(1)]
    B, D = [], []
    for (a, b, c, al, be, ga) in rates:
        p, q = a / (b + c), al / (be + ga)
        lam = c * p / (ga * q)
        B.append(p * t[-1])
        t.append(t[-1] * lam)
        D.append(q * t[-1])
    return t, B, D


# ------------------------------------------------------------------ Sections 5-6
def check_coalesced_limits():
    table = []
    nmax = 10 if FULL else 8
    for n in range(2, nmax + 1):
        L = pc.limit_data(n)
        N, J, jm = L['N'], L['J'], L['jm']
        dN, dJ = ps.val(ps.deriv(N), Q(1)), ps.val(ps.deriv(J), Q(1))
        ok(dN / jm == Q(4 * n - 6, 9) and dJ / jm == Q(4 * n, 9), 'moments')
        ok(sum(L['d']) == 2 and sum(L['y']) == 1)
        ok(L['mu'] == Q(4 * n - 3, 9))
        v = L['v']
        ok(v == (3 * n - 2) * Q(2, 9) ** (n - 1) and 0 < v < 1, 'closed form of v')
        ok(all(p > 0 for p in L['phi']), 'feedback entries positive')
        ok(all(zi > 0 for zi in L['z']))
        gap = 1 - L['G']
        ok(gap == v * (50 * n - 45) / (9 * (14 - 8 * v)) and gap > 0, 'gain identity')
        Bz = [sum(a * b for a, b in zip(row, L['z'])) for row in L['Bstar']]
        ok(all(val == -gap for val in Bz))
        ok(all(L['Bstar'][i][j] >= 0 for i in range(n - 1) for j in range(n - 1) if i != j))
        ok(pc.hurwitz(L['Bstar']), 'B* Hurwitz (Routh)')
        # explicit diagonal Lyapunov matrix
        Hinv = pc.inverse(L['H'])
        w = [sum(Hinv[i][j] * L['phi'][j] for j in range(n - 1)) for i in range(n - 1)]
        ok(all(x > 0 for x in w))
        P = [w[i] / L['z'][i] for i in range(n - 1)]
        Qm = [[-(L['Bstar'][j][i] * P[j] + P[i] * L['Bstar'][i][j]) for j in range(n - 1)]
              for i in range(n - 1)]
        ok(all(p > 0 for p in pc.ldl_pivots(Qm)), 'diagonal Lyapunov certificate')
        Qz = [-sum(Qm[i][j] * L['z'][j] for j in range(n - 1)) for i in range(n - 1)]
        ok(all(Qz[i] == -gap * (L['phi'][i] + P[i]) for i in range(n - 1)))
        table.append(dict(n=n, v=str(v), v_float=float(v), gap=str(gap), gap_float=float(gap),
                          asymptotic_ratio=float(gap / (n * n * Q(2, 9) ** (n - 1)))))
    REPORT['feedback_table'] = table


def check_loaded_matrices():
    rows = []
    nmax = 6 if FULL else 5
    for n in range(2, nmax + 1):
        L = pc.limit_data(n)
        errs = []
        for r in (Q(10) ** 3, Q(10) ** 6):
            rec = pc.coalesced(n, r)
            st = rec['states'][0]['z']
            ok(st[n + 1] == 1 and st[n + 2] == 1)
            M, h, K = pc.loaded(n, st, 2 * r, Q(2))
            ok(all(p > 0 for p in pc.ldl_pivots(M)), 'mass matrix positive definite')
            one = [Q(1)] * (n + 1)
            M1 = [sum(row) for row in M]
            S = st[:n + 1]
            c = st[n + 3:2 * n + 3] + [Q(0)]
            y = [Q(0)] + st[2 * n + 3:]
            ok(M1 == [S[i] + c[i] / (2 * r) + y[i] / 2 for i in range(n + 1)])
            ok(sum(M1) == Q(7, 2) - 1 / (2 * r))
            ok(S[n] == y[n] and M[n][n] == 2 * y[n] - y[n] ** 2 / 2)
            ok(ps.det(K) == 0, 'K singular at coalescence')
            Ar = [[r * K[i][j] for j in range(n - 1)] for i in range(n - 1)]
            errs.append(max(abs(Ar[i][j] - L['Bstar'][i][j])
                            for i in range(n - 1) for j in range(n - 1)))
        ok(errs[1] * 100 < errs[0], 'r A_r -> B* at rate O(1/r)')
        # smallest r = 2^k (k >= 1) admissible and with A_r Hurwitz / diagonally certified
        Hinv = pc.inverse(L['H'])
        w = [sum(Hinv[i][j] * L['phi'][j] for j in range(n - 1)) for i in range(n - 1)]
        P = [w[i] / L['z'][i] for i in range(n - 1)]
        first_h = first_p = None
        r = Q(2)
        while first_p is None:
            rec = ps.build([Q(3)] * (2 * n - 1), r)
            if rec['positive']:
                _, _, K = pc.loaded(n, rec['states'][0]['z'], 2 * r, Q(2))
                A = [row[:n - 1] for row in K[:n - 1]]
                if first_h is None and pc.hurwitz(A):
                    first_h = r
                Qm = [[-(A[j][i] * P[j] + P[i] * A[i][j]) for j in range(n - 1)]
                      for i in range(n - 1)]
                if all(p > 0 for p in pc.ldl_pivots(Qm)):
                    first_p = r
            r *= 2
        rows.append(dict(n=n, err_r1e3=float(errs[0]), err_r1e6=float(errs[1]),
                         first_power_of_two_hurwitz=str(first_h),
                         first_power_of_two_diagonal=str(first_p)))
    REPORT['prefix_convergence'] = rows
    # the full matrix K(r) is not Metzler in general (its last row can have a negative entry)
    _, _, K = pc.loaded(4, pc.coalesced(4, 100)['states'][0]['z'], Q(200), Q(2))
    ok(min(K[i][j] for i in range(4) for j in range(4) if i != j) < 0)


def simple_zero_and_stable(mat):
    cp = ps.charpoly(mat)
    if cp[-1] != 0 or cp[-2] == 0:
        return False
    try:
        rhp, _ = ps.routh_rhp(cp[:-1])
    except AssertionError:
        return False
    return rhp == 0


def check_ordered_design():
    """The terminating ordered procedure of Section 7, replayed exactly for small n."""
    out = []
    for n in ([2, 3, 4] if not FULL else [2, 3, 4, 5, 6, 7]):
        r = Q(2)
        while True:
            rec = ps.build([Q(3)] * (2 * n - 1), r)
            if rec['positive']:
                st = rec['states'][0]['z']
                _, _, K = pc.loaded(n, st, 2 * r, Q(2))
                if pc.hurwitz([row[:n - 1] for row in K[:n - 1]]):
                    break
            r *= 2
        t = Q(1)
        while not simple_zero_and_stable([[K[i][j] * (t if j == n - 1 else 1)
                                           for j in range(n)] for i in range(n)]):
            t /= 2
        omega = [Q(1)] * (n - 1) + [t]
        Y = st[2 * n + 3:]
        lam = [omega[i] / Y[i] for i in range(n)]
        eps = Q(1)
        while True:
            rates = pc.retune(rec, lam, [Q(1)] * n, [Q(1)] * n, eps)
            ok(all(v == 0 for v in ps.vector_field(rates, st)))
            if simple_zero_and_stable(ps.reduced_jacobian(rates, st)):
                break
            eps /= 2
        delta = Q(1, 2)
        while True:
            xs = [Q(3) + delta * (j - (n - 1)) for j in range(2 * n - 1)]
            sp = ps.build(xs, r) if min(xs) > 1 else dict(positive=False)
            good = sp['positive']
            if good:
                rates = pc.retune(sp, lam, [Q(1)] * n, [Q(1)] * n, eps)
                counts = []
                for j, s in enumerate(sp['states']):
                    ok(all(v == 0 for v in ps.vector_field(rates, s['z'])))
                    ok(ps.totals(s['z']) == sp['totals'] and min(s['z']) > 0)
                    try:
                        rhp, _ = ps.routh_rhp(ps.charpoly(ps.reduced_jacobian(rates, s['z'])))
                    except AssertionError:
                        rhp = -1
                    counts.append(rhp)
                good = counts == [j % 2 for j in range(2 * n - 1)]
            if good:
                break
            delta /= 2
        for j, s in enumerate(sp['states']):
            holds, d = det_formula_holds(rates, s['z'], r)
            ok(holds, 'determinant formula')
            ok((d > 0) == ((n + j) % 2 == 0), 'sign of det')
        out.append(dict(n=n, r=str(r), last_current=str(t), epsilon=str(eps), delta=str(delta),
                        unstable_counts=counts))
    REPORT['ordered_design'] = out


# ------------------------------------------------------------------ Section 9: benchmark
def I(x):
    return x if isinstance(x, tuple) else (Q(x), Q(x))


def iadd(x, y):
    x, y = I(x), I(y)
    return x[0] + y[0], x[1] + y[1]


def ineg(x):
    x = I(x)
    return -x[1], -x[0]


def imul(x, y):
    x, y = I(x), I(y)
    v = [a * b for a in x for b in y]
    return min(v), max(v)


def isub(x, y):
    return iadd(x, ineg(y))


def mag(x):
    return max(abs(v) for v in I(x))


def structured_bounds(q, tot, rates, scales, P, Rm, rho, eta):
    """Reactionwise interval bounds (same algorithm as the workspace certificate)."""
    ix = [1, 2, 3, 6, 7, 8, 9, 10, 11]
    dim = 9
    T = [[Q(0)] * dim for _ in range(12)]
    T[0] = [-s for s in scales]
    for j, i in enumerate(ix):
        T[i][j] = scales[j]
    for j in range(3, 6):
        T[4][j] = -scales[j]
    for j in range(6, 9):
        T[5][j] = -scales[j]
    z0 = [tot[2] - sum(q)] + q[:3] + [tot[0] - sum(q[3:6]), tot[1] - sum(q[6:])] + q[3:]
    zc = [I(v) for v in z0]
    zc[0] = (z0[0] - eta * tot[2], z0[0] + eta * tot[2])
    zc[4] = (z0[4] - eta * tot[0], z0[4] + eta * tot[0])
    zc[5] = (z0[5] - eta * tot[1], z0[5] + eta * tot[1])
    zb = [iadd(zc[i], (-rho * sum(abs(v) for v in T[i]), rho * sum(abs(v) for v in T[i])))
          for i in range(12)]
    RJ = [[I(0)] * dim for _ in range(dim)]
    DQ = [[I(0)] * dim for _ in range(dim)]
    RF = [I(0)] * dim
    for link in range(3):
        E, Ph, C, Y = 4, 5, 6 + link, 9 + link
        recipe = [([link, E], [C]), ([C], [link, E]), ([C], [link + 1, E]),
                  ([link + 1, Ph], [Y]), ([Y], [link + 1, Ph]), ([Y], [link, Ph])]
        for k, (react, prod) in zip(rates[link], recipe):
            st = [0] * 12
            for j in prod:
                st[j] += 1
            for j in react:
                st[j] -= 1
            st = [Q(st[i]) / scales[j] for j, i in enumerate(ix)]
            rs = [sum(Rm[i][j] * st[j] for j in range(dim)) for i in range(dim)]
            pv = [sum(P[i][j] * st[j] for j in range(dim)) for i in range(dim)]
            ki = (k * (1 - eta), k * (1 + eta))
            fc, fn = I(ki), k
            for j in react:
                fc = imul(fc, zc[j])
                fn *= z0[j]
            diff = isub(fc, fn)
            for i in range(dim):
                RF[i] = iadd(RF[i], imul(rs[i], diff))
            gd = []
            for j in range(dim):
                if len(react) == 1:
                    g = imul(isub(ki, k), T[react[0]][j])
                else:
                    a, b = react
                    g = iadd(imul(isub(imul(ki, zb[a]), k * z0[a]), T[b][j]),
                             imul(isub(imul(ki, zb[b]), k * z0[b]), T[a][j]))
                gd.append(g)
            for i in range(dim):
                for j in range(dim):
                    RJ[i][j] = iadd(RJ[i][j], imul(rs[i], gd[j]))
                    DQ[i][j] = iadd(DQ[i][j], ineg(iadd(imul(pv[i], gd[j]), imul(pv[j], gd[i]))))
    con = max(sum(mag(v) for v in row) for row in RJ)
    shift = max(mag(v) for v in RF)
    return dict(contraction=con, equilibrium_shift_bound=shift / (1 - con),
                lyapunov_loss_bound=max(sum(mag(v) for v in row) for row in DQ),
                positive_species_lower=min(a for a, b in zb))


def check_benchmark():
    ex = json.loads((HERE / 'data' / 'worked_example.json').read_text())
    cert = json.loads((HERE / 'data' / 'operational_certificate.json').read_text())
    rates = rate_tuple_list(ex['record']['rates'])
    ok(rate_tuple_list(cert['rates']) == rates)
    xs = [Q(v) for v in ex['selection']['xs']]
    r = Q(ex['selection']['r'])
    ok(xs == [Q(2), Q(7, 2), Q(5), Q(13, 2), Q(8)] and r == 9)
    geo = ps.build(xs, r)
    ok(geo['positive'])
    tA, tB, tD = abd_from_rates(rates)
    ok((tA, tB, tD) == (geo['A'], geo['B'], geo['D']), 'rates realize the constructed geometry')
    tot = (Q(18), Q(2), Q(20))
    states, counts, readouts, slopes = [], [], [], []
    for j, prof in enumerate(ex['record']['profiles']):
        z = [Q(v) for v in prof['state']]
        ok(z == geo['states'][j]['z'])
        ok(all(v == 0 for v in ps.vector_field(rates, z)) and ps.totals(z) == tot and min(z) > 0)
        rhp, _ = ps.routh_rhp(ps.charpoly(ps.reduced_jacobian(rates, z)))
        counts.append(rhp)
        holds, _ = det_formula_holds(rates, z, r)
        ok(holds, 'determinant formula on the benchmark')
        x, u = xs[j], ps.ratio(xs[j])
        R = z[3] + z[11]
        ok(R == tD[2] / 2 * u ** 2 / ps.val(tD, u) * (x - 1) * (x + 5) / (x + 1), 'readout formula')
        readouts.append(R)
        slopes.append(ps.chart(geo['A'], geo['B'], geo['D'], r, Q(2), u)[1])
        states.append(z)
    ok(counts == [0, 1, 0, 1, 0], 'Routh counts')
    ok(all(a < b for a, b in zip(readouts, readouts[1:])))
    ok([s < 0 for s in slopes] == [True, False, True, False, True])
    flat = [v for row in rates for v in row]
    uni = [v for row in rates for v in (row[1], row[2], row[4], row[5])]
    assoc = [v for row in rates for v in (row[0], row[3])]
    ok(max(assoc) <= 2 and max(uni) <= 2)
    C0, T0 = Q(1, 10), Q(10)
    REPORT['benchmark'] = dict(
        unstable_counts=counts,
        E=[str(z[4]) for z in states], F=[str(z[5]) for z in states],
        u=[str(ps.ratio(x)) for x in xs],
        readout_micromolar=[float(R * C0) for R in readouts],
        S3_micromolar=[float(z[3] * C0) for z in states],
        slopes=[float(s) for s in slopes],
        unimolecular_spread=float(max(uni) / min(uni)),
        rates_physical=[[float(row[0] / (C0 * T0)), float(row[1] / T0), float(row[2] / T0),
                         float(row[3] / (C0 * T0)), float(row[4] / T0), float(row[5] / T0)]
                        for row in rates],
        D=[str(c) for c in geo['D']], B=[str(c) for c in geo['B']],
        N=[str(c) for c in geo['N']], J=[str(c) for c in geo['J']])
    # operational certificate: replay and sharpening
    eta = Q(cert['common_independent_relative_rate_total_radius'])
    ok(eta == Q(1, 671088640000))
    sharp = []
    for sink in cert['sinks']:
        z = states[sink['index']]
        q = z[1:4] + z[6:]
        scales = [Q(v) for v in sink['coordinate_scales']]
        ok(scales == q)
        JS = ps.reduced_jacobian(rates, z)
        J0 = [[JS[i][j] * scales[j] / scales[i] for j in range(9)] for i in range(9)]
        P = [[Q(v) for v in row] for row in sink['P']]
        Qm = [[Q(v) for v in row] for row in sink['Q']]
        ok(P == pc.transpose(P))
        JtP = pc.matmul(pc.transpose(J0), P)
        ok(Qm == [[-(JtP[i][j] + JtP[j][i]) for j in range(9)] for i in range(9)], 'Q = -(J^T P + P J)')
        ok(all(p > 0 for p in pc.ldl_pivots(P)) and all(p > 0 for p in pc.ldl_pivots(Qm)))
        rho = Q(sink['rho'])
        b = structured_bounds(q, list(tot), rates, scales, P, pc.inverse(J0), rho, eta)
        stored = sink['interval_bounds']
        ok(b['contraction'] <= Q(1, 2) and b['equilibrium_shift_bound'] <= rho / 4
           and b['positive_species_lower'] > 0)
        ok(b['lyapunov_loss_bound'] <= Q(stored['lyapunov_loss_bound']), 'loss within stored bound')
        M = pc.norm_inf(P)
        qlow = 1 / pc.norm_inf(pc.inverse(Qm))
        loss = Q(stored['lyapunov_loss_bound'])
        c = qlow - loss
        ok(c > 0)
        ok(M <= Q(sink['P_upper']) and Q(sink['P_lower']) <= 1 / pc.norm_inf(pc.inverse(P)))
        t10 = 6 * T0 * M / c
        sharp.append(dict(index=sink['index'], M=float(M), c=float(c),
                          tenfold_seconds=float(t10), margin_per_second=float(c / (2 * T0 * M)),
                          old_tenfold_seconds=float(Q(sink['tenfold_envelope_time']) * T0),
                          initial_radius=sink['initial_scaled_euclidean_radius'],
                          M_exact=str(M), c_exact=str(c)))
    ok(sharp[0]['tenfold_seconds'] < 357000 and sharp[1]['tenfold_seconds'] < 32918000
       and sharp[2]['tenfold_seconds'] < 23433000)
    iv = [[Q(a) * C0, Q(b) * C0] for a, b in cert['readout_intervals_including_measurement']]
    ok(all(iv[i][1] < iv[i + 1][0] for i in range(2)))
    REPORT['sharpened_certificate'] = sharp
    REPORT['readout_intervals_micromolar'] = [[float(a), float(b)] for a, b in iv]
    ref = json.loads((HERE / 'data' / 'refinement.json').read_text())
    REPORT['refinement_gaps'] = [dict(xs=t['xs'], r=t['r'], gap=t['worst_gap_diagnostic'])
                                 for t in ref['trials']]


def check_example_two_sites():
    """Example 9.2: every printed number."""
    n, r = 2, Q(2)
    st = pc.coalesced(n, r)['states'][0]['z']
    lam = [1 / y for y in st[2 * n + 3:]]
    sp = ps.build([Q(5, 2), Q(3), Q(7, 2)], r)
    ok(sp['N'] == [Q(111, 4), Q(8)] and sp['J'] == [Q(15, 4), Q(32)])
    ok(sp['D'] == [Q(1), Q(8672, 2625)] and sp['B'] == [Q(1287, 125), Q(2288, 875)])
    rates = pc.retune(sp, lam, [Q(1)] * n, [Q(1)] * n, Q(1))
    ok(rates == [(Q(19782, 1375), Q(1), Q(625, 1573), Q(147000, 124267), Q(1), Q(45, 11)),
                 (Q(311808, 192049), Q(1), Q(4065, 2431), Q(79, 34), Q(1), Q(45, 34))])
    printed = [[Q(250, 693), Q(1027, 1008), Q(271, 528), Q(3, 4), Q(8, 7), Q(39, 14), Q(13, 28),
                Q(125, 462), Q(271, 462)],
               [Q(2625, 11297), Q(1), Q(8672, 11297), Q(1), Q(1), Q(189, 79), Q(48, 79),
                Q(2625, 11297), Q(8672, 11297)],
               [Q(350, 2223), Q(869, 912), Q(4065, 3952), Q(5, 4), Q(8, 9), Q(77, 38), Q(55, 76),
                Q(875, 4446), Q(1355, 1482)]]
    counts = []
    for s, z in zip(sp['states'], printed):
        ok(s['z'] == z and ps.totals(z) == (4, 2, 6))
        ok(all(v == 0 for v in ps.vector_field(rates, z)))
        counts.append(ps.routh_rhp(ps.charpoly(ps.reduced_jacobian(rates, z)))[0])
    ok(counts == [0, 1, 0])


if __name__ == '__main__':
    t0 = time.time()
    for fn in (check_base_case, check_construction, check_coalesced_limits,
               check_loaded_matrices, check_ordered_design, check_example_two_sites,
               check_benchmark):
        t1 = time.time()
        fn()
        print(f'{fn.__name__}: ok ({time.time() - t1:.1f}s, {COUNT[0]} checks so far)', flush=True)
    REPORT['checks'] = COUNT[0]
    REPORT['seconds'] = round(time.time() - t0, 1)
    REPORT['mode'] = 'full' if FULL else 'default'
    (HERE / 'check_paper_report.json').write_text(json.dumps(REPORT, indent=1))
    print('ALL CHECKS PASSED:', COUNT[0])
