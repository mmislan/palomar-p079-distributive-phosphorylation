"""Figures for the paper, drawn from exact rational data (rendering only in floating point)."""
import json
from fractions import Fraction as Q
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

import phos_sharp as ps
import phos_capacity as pc

HERE = Path(__file__).resolve().parent
plt.rcParams.update({'font.size': 9, 'font.family': 'serif', 'mathtext.fontset': 'cm',
                     'axes.linewidth': 0.6, 'pdf.fonttype': 42})


def benchmark_figure():
    ex = json.loads((HERE / 'data' / 'worked_example.json').read_text())
    cert = json.loads((HERE / 'data' / 'operational_certificate.json').read_text())
    xs = [Q(v) for v in ex['selection']['xs']]
    r = Q(ex['selection']['r'])
    geo = ps.build(xs, r)
    A, B, D = geo['A'], geo['B'], geo['D']
    grid = [Q(k, 400) for k in range(20, int(8.4 * 400))]
    res = [float(ps.chart(A, B, D, r, Q(2), u)[0] - 2 * (r + 1)) for u in grid]
    scale = 0.004
    fig, ax = plt.subplots(1, 2, figsize=(6.9, 2.7))
    a = ax[0]
    a.plot([float(u) for u in grid], np.arcsinh(np.array(res) / scale), color='#1f4e79', lw=1.1)
    a.axhline(0, color='0.55', lw=0.5)
    for j, x in enumerate(xs):
        u = float(ps.ratio(x))
        a.plot([u], [0], 'o', ms=5, mfc=('#1f4e79' if j % 2 == 0 else 'white'), mec='#1f4e79',
               mew=1.0, zorder=5)
    ticks = [-1, -0.1, -0.01, 0, 0.01, 0.1, 1]
    a.set_yticks(np.arcsinh(np.array(ticks) / scale))
    a.set_yticklabels([str(t) for t in ticks])
    a.set_xlabel(r'free-enzyme ratio $u=E/F$')
    a.set_ylabel(r'$\Phi(u)-S_{\mathrm{T}}$')
    a.set_title('(a) scalar residual', fontsize=9)
    b = ax[1]
    C0 = Q(1, 10)
    iv = {s['index']: iv for s, iv in zip(cert['sinks'], cert['readout_intervals_including_measurement'])}
    for j, st in enumerate(geo['states']):
        z = st['z']
        R = float((z[3] + z[11]) * C0)
        if j in iv:
            lo, hi = (float(Q(v) * C0) for v in iv[j])
            b.fill_between([float(xs[j]) - 0.35, float(xs[j]) + 0.35], lo, hi, color='#1f4e79',
                           alpha=0.25, lw=0)
        b.plot([float(xs[j])], [R], 'o', ms=5, mfc=('#1f4e79' if j % 2 == 0 else 'white'),
               mec='#1f4e79', mew=1.0, zorder=5)
    b.set_xlabel(r'auxiliary coordinate $x=\sqrt{1+8u}$')
    b.set_ylabel(r'readout $S_3+Y_3$ ($\mu$M)')
    b.set_title('(b) readout at the five equilibria', fontsize=9)
    b.set_xlim(1, 9)
    fig.tight_layout()
    fig.savefig(HERE / 'figures' / 'benchmark.pdf')
    plt.close(fig)


def deficit_figure():
    ns = list(range(2, 21))
    gap, v = [], []
    for n in ns:
        vn = (3 * n - 2) * Q(2, 9) ** (n - 1)
        v.append(float(vn))
        gap.append(float(vn * (50 * n - 45) / (9 * (14 - 8 * vn))))
    fig, ax = plt.subplots(1, 2, figsize=(6.9, 2.6))
    a = ax[0]
    a.semilogy(ns, gap, 'o-', ms=3.5, lw=0.9, color='#1f4e79', label=r'$1-G_n$')
    a.semilogy(ns, [25 / 21 * n * n * (2 / 9) ** (n - 1) for n in ns], '--', lw=0.8, color='0.4',
               label=r'$\frac{25}{21}n^2(2/9)^{n-1}$')
    a.semilogy(ns, v, 's-', ms=3, lw=0.8, color='#b5651d', label=r'$v_n$')
    a.set_xlabel(r'number of sites $n$')
    a.set_xticks([2, 5, 10, 15, 20])
    a.legend(frameon=False, fontsize=8)
    a.set_title('(a) feedback deficit of the limiting prefix', fontsize=9)
    b = ax[1]
    for n, col in [(2, '#1f4e79'), (3, '#b5651d'), (4, '#2e7d32'), (5, '#7b1fa2')]:
        L = pc.limit_data(n)
        rs = [Q(10) ** k for k in range(2, 8)]
        errs = []
        for r in rs:
            st = pc.coalesced(n, r)['states'][0]['z']
            _, _, K = pc.loaded(n, st, 2 * r, Q(2))
            errs.append(float(max(abs(r * K[i][j] - L['Bstar'][i][j])
                                  for i in range(n - 1) for j in range(n - 1))))
        b.loglog([float(r) for r in rs], errs, 'o-', ms=3, lw=0.9, color=col, label=f'$n={n}$')
    b.set_xlabel(r'enzyme-total ratio $r$')
    b.set_ylabel(r'$\max_{ij}|(r\mathbf{A}_r-\mathbf{B}_*)_{ij}|$')
    b.legend(frameon=False, fontsize=8)
    b.set_title(r'(b) convergence of the scaled prefix', fontsize=9)
    fig.tight_layout()
    fig.savefig(HERE / 'figures' / 'deficit.pdf')
    plt.close(fig)


if __name__ == '__main__':
    benchmark_figure()
    deficit_figure()
    print('figures written')
