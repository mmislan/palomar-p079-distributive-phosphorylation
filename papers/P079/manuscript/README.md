# Sharp equilibrium and stable-state capacities of multisite phosphorylation

Sources of `../paper.pdf`. The author is Michael Mislan. Section 10 describes
the selected main-theorem formalization and its quantitative boundary.

Main result: for the sequential distributive n-site phosphorylation cycle, for every n >= 1,
the maximal number of positive equilibria in one compatibility class is 2n-1 and the maximal
number of locally asymptotically stable equilibria is n (ceiling includes nonhyperbolic
attractors; attainment by rational data, on an open parameter set).

## Files

| File | Purpose |
|---|---|
| `main.tex`, `part1.tex`, `part2.tex`, `part3.tex`, `refs.bib` | LaTeX sources (Sections 1; 2-4; 5-7; 8-11) |
| `figures/benchmark.pdf`, `figures/deficit.pdf` | Figures, produced by `make_figures.py` |
| `phos_sharp.py` | Exact rational toolkit for the equilibrium construction (shared with the earlier 2n-1 sharpness paper) |
| `phos_capacity.py` | Exact toolkit for the loaded slow matrix, limiting prefix, retuning |
| `check_paper.py` | Replays every formula and number in the paper in exact arithmetic; `--full` extends Proposition 9.1 to n <= 7 (about 45 s) |
| `check_paper_report.json` | Output of the last `--full` run |
| `data/worked_example.json`, `data/operational_certificate.json`, `data/refinement.json` | Exact benchmark data copied from the workspace `publication/data` |
| `../../../proofs/`, `../../../DifferentialGeometry/` | Current proof and pinned degree source; see the P079 release provenance and verification review |

## Build

```bash
python check_paper.py --full
python make_figures.py
pdflatex main && bibtex main && pdflatex main && pdflatex main
```

MiKTeX binaries: `%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64`. For arXiv, upload
`main.tex part*.tex main.bbl figures/*.pdf` (the `.bbl` is kept next to the sources).
Python: the repository `.venv` (3.11); `check_paper.py` needs only the standard library,
`make_figures.py` needs matplotlib and numpy.

## Formalization scope

The independent Challenge selects nineteen literal-model statements. Together they cover both universal ceilings, rational simultaneous attainment, open persistence, the common-witness quantitative splitting law and rational member, compact-current and closed-interval refinements, all printed finite spectra, the nominal three-site benchmark, the two-site dominant tail, and the same-witness operational recovery and measured-readout guarantee. The four additional global statements expose arbitrary-source conversion positivity, the literal admissibility range for B, global scalar readout order, and complete simple negative interlacing with positive partial fractions and coefficient ratios. Repeated prescribed roots and degree zero are retained where specified.

The sink conclusions include nonlinear local asymptotic stability. Each saddle has one simple positive real restricted-Jacobian eigenvalue and all other eigenvalues strictly in the left half-plane. Supporting Lean proofs construct an embedded, immersed analytic local unstable curve at every odd-index saddle of the same rational attaining family. The curve is tangent to its positive real eigenvector and satisfies the actual field-invariance identity. Its backward trajectories stay on the curve and converge to that equilibrium; the curve and trajectories remain positive and in the same compatibility class. The common rates, totals, complete equilibrium list, sink and saddle assertions, and exact count are retained. These supporting results are additional to the nineteen selected statements.

The supporting prescribed-root construction retains every strictly ordered real root list above one, every admissible r and every positive choice of b,beta,gamma. It proves positive rates from the actual normalized family and retains the prescribed common-total equilibrium list, exhaustion, exact count and rationality for rational inputs. All equilibria are nondegenerate, the odd-index restricted Jacobians have an odd number of positive real eigenvalues counted with algebraic multiplicity, and the complete nondegenerate configuration persists on a nonempty open neighborhood in the full positive rate-and-total parameter space. This universally quantified construction is additional to the existential stable-capacity witnesses. The checked supporting construction also includes the original rational four-loop first-success procedure with the original Routh tests and physical eligibility guards. Its earliest returned a,b,c,d retain the same rates, totals, complete equilibrium list, current identities and sink/saddle conclusions. No iteration bound is claimed. The printed finite witnesses are certified independently and are not asserted to be outputs of this search. The analytical readout and reciprocal-time corollaries retain the same construction witnesses.

The selected proof sources and required supporting modules have passed strict source compilation with warnings treated as errors. Reproduction uses exact-snapshot Comparator, con-ron, nanoda and Lean default verification; the source manifest and accompanying external verification record identify the checked package. Earlier receipts continue to cover only their own snapshots. Publication and submission remain separate actions.

## Relation to earlier manuscripts

* Supersedes the 14-page workspace manuscript
  `problem_workspaces/RAF_exact_stable-state_capacity_n-site_phosphorylation_system/Phosphorylation_Stable_State_Capacity.pdf`
  and merges the follow-up material (`publication/FOLLOWUP_PROOFS.md`, `FOLLOWUP_REPORT.md`)
  and the supplemental-information plan of 2026-09-20.
* Reuses, with proofs, the equilibrium construction, interlacing/positivity theorem and
  determinant formula of `../Sharp_Steady_State_Bound_Phosphorylation_arxiv`. It proves the
  first sentence of Conjecture 8.3 of that paper (n stable states for every n), with different
  kinetics; the second sentence (standard kinetics, x_j = j+2) remains open.

## Changes relative to the 14-page manuscript

* Introduction with the exact historical gap; explicit definitions of the three capacities.
* Ceiling: index lemma for degenerate attractors written out; transversality via linearity in
  the rate constants.
* Construction: interlacing lemma stated for repeated roots; explicit admissible range of r
  (r >= 3n/2 at coalescence) replaces "r sufficiently large".
* Determinant formula added; it replaces the qualitative elimination argument, gives
  det J = 0 at coalescence for all kinetics, identifies the even-indexed equilibria as the
  sinks without a degree count, and yields the splitting law with an explicit constant.
* Loaded reduction: full derivation of the mass matrix, of the fast block (detailed balance),
  of the slow Jacobian, and a direct proof that K is singular at coalescence.
* Large-r limit: scaled-inverse lemma with a convergence proof (block elimination) and the two
  exact row identities written out; level potential defined.
* New: Table of the feedback deficit; diagonal Lyapunov matrix and compact-current corollary;
  readout monotonicity and separation-recovery corollary; label corollary.
* New exact witnesses: the ordered design terminates immediately for n <= 7 (t = eps = 1),
  Proposition 9.1 and Example 9.2.
* Benchmark: tables, declared units, and the sharpened recovery certificate
  (worst bound 1.2e9 s -> < 32,918,000 s) with an independent replay of the interval bounds.
* Notation: substrate-total function Phi (not H), path matrix H, mass matrix M in bold,
  inventories Lambda_i, eta = r-u, v reserved for J_m/J(1).
