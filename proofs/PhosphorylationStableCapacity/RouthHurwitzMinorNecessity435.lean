module
public import proofs.PhosphorylationStableCapacity.RouthDeterminantRecursion435
public import proofs.PhosphorylationStableCapacity.RouthHurwitzFirstPivot435
public import proofs.PhosphorylationStableCapacity.RouthReductionHurwitzPreservation435
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial Matrix Filter
open scoped Topology

noncomputable section

/-- The first coefficient of the explicit reduced polynomial is literally
the first Routh pivot, including the constant reduction of a linear input. -/
theorem routhReducedPolynomial_top_coeff {R : Type*} [Field R]
    (d : ℕ) (hd : 0 < d) (p : R[X]) :
    (routhReducedPolynomial d p).coeff (d-1) = routhDescendingCoeff d p 1 := by
  have hn : d-1 < d := by omega
  have harg : (d : ℤ)-1-((d-1 : ℕ) : ℤ) = 0 := by omega
  rw [routhReducedPolynomial_coeff, ite_eq_left hn, harg]
  simp [routhReducedCoefficients]

/-- The finite producer has exactly degree one less whenever its first
Routh pivot is nonzero. No stability or determinant test is assumed. -/
theorem routhReducedPolynomial_natDegree {R : Type*} [Field R]
    (d : ℕ) (hd : 0 < d) (p : R[X])
    (hpivot : routhDescendingCoeff d p 1 ≠ 0) :
    (routhReducedPolynomial d p).natDegree = d-1 := by
  have hupper : (routhReducedPolynomial d p).natDegree ≤ d-1 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [routhReducedPolynomial_coeff, ite_eq_right (by omega)]
  have hnonzero : (routhReducedPolynomial d p).coeff (d-1) ≠ 0 := by
    rw [routhReducedPolynomial_top_coeff d hd p]
    exact hpivot
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hupper hnonzero

/-- The new leading coefficient is the first pivot, with no normalization
or replacement of the reduced polynomial. -/
theorem routhReducedPolynomial_leadingCoeff {R : Type*} [Field R]
    (d : ℕ) (hd : 0 < d) (p : R[X])
    (hpivot : routhDescendingCoeff d p 1 ≠ 0) :
    (routhReducedPolynomial d p).leadingCoeff = routhDescendingCoeff d p 1 := by
  unfold Polynomial.leadingCoeff
  rw [routhReducedPolynomial_natDegree d hd p hpivot]
  exact routhReducedPolynomial_top_coeff d hd p

/-- Every Hurwitz minor of a positive-leading real Hurwitz polynomial is
strictly positive. Degree induction uses actual spectral preservation of
the explicit Routh reduction and the proved determinant recursion. Thus
positive minors or a pre-existing full Routh criterion are not hypotheses. -/
theorem hurwitzPolynomial_all_routh_minors_positive
    (p : ℝ[X]) (hleading : 0 < p.leadingCoeff)
    (hstable : ∀ z : ℂ,
      (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0) :
    ∀ k : ℕ, k ≤ p.natDegree → 0 < routhHurwitzMinor p.natDegree k p := by
  suffices h : ∀ d : ℕ, ∀ q : ℝ[X], q.natDegree = d →
      0 < q.leadingCoeff →
      (∀ z : ℂ, (q.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0) →
      ∀ k : ℕ, k ≤ d → 0 < routhHurwitzMinor d k q from
    h p.natDegree p rfl hleading hstable
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
      intro q hdegree hlead hhurwitz k hk
      cases k with
      | zero => simp [routhHurwitzMinor]
      | succ k =>
          have hd : 0 < d := by omega
          have hqdegree : 0 < q.natDegree := by omega
          have hpivot : 0 < routhDescendingCoeff d q 1 := by
            simpa only [hdegree] using
              routhHurwitz_first_pivot_pos q hqdegree hlead hhurwitz
          let reduced := routhReducedPolynomial d q
          have hreduced_degree : reduced.natDegree = d-1 :=
            routhReducedPolynomial_natDegree d hd q hpivot.ne'
          have hreduced_leading : 0 < reduced.leadingCoeff := by
            change 0 < (routhReducedPolynomial d q).leadingCoeff
            rw [routhReducedPolynomial_leadingCoeff d hd q hpivot.ne']
            exact hpivot
          have hreduced_stable : ∀ z : ℂ,
              (reduced.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0 := by
            simpa only [reduced, hdegree] using
              routhReducedPolynomial_hurwitz q hqdegree hlead hhurwitz
          have hreduced_minor : 0 < routhHurwitzMinor (d-1) k reduced :=
            ih (d-1) (by omega) reduced hreduced_degree hreduced_leading
              hreduced_stable k (by omega)
          rw [routhHurwitzMinor_reduction d hd q hpivot.ne' k]
          exact mul_pos hpivot hreduced_minor

/-- The constant coefficient is also strictly positive, including degree
zero. For positive degree this follows from the literal final determinant
identity and positivity of its preceding minor. -/
theorem hurwitzPolynomial_constantCoeff_pos
    (p : ℝ[X]) (hleading : 0 < p.leadingCoeff)
    (hstable : ∀ z : ℂ,
      (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0) :
    0 < p.coeff 0 := by
  cases hdegree : p.natDegree with
  | zero => simpa only [Polynomial.leadingCoeff, hdegree] using hleading
  | succ d =>
      have hprevious : 0 < routhHurwitzMinor (d+1) d p := by
        simpa only [hdegree] using
          hurwitzPolynomial_all_routh_minors_positive p hleading hstable d (by omega)
      have hlast : 0 < routhHurwitzMinor (d+1) (d+1) p := by
        simpa only [hdegree] using
          hurwitzPolynomial_all_routh_minors_positive p hleading hstable (d+1) (by omega)
      rw [routhHurwitzMinor_last] at hlast
      exact (mul_pos_iff_of_pos_right hprevious).mp hlast

/-- The original local determinant definitions gain proper-minor
positivity directly from the Hurwitz property of the coalesced deflation.
The conclusion is the exact existing local matrix/minor predicate. -/
theorem properRouthMinors_eventually_positive_of_hurwitz
    {ι : Type*} [Fintype ι]
    (d : ℕ) (P : ι → ℝ → ℝ[X]) (q : ℝ[X])
    (hdegree : q.natDegree = d) (hleading : 0 < q.leadingCoeff)
    (hstable : ∀ z : ℂ,
      (q.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0)
    (hzero : ∀ j, P j 0 = Polynomial.X*q)
    (hcoeff : ∀ j n, ContinuousAt (fun δ => (P j δ).coeff n) 0) :
    ∀ᶠ δ : ℝ in 𝓝 0, ∀ j : ι, ∀ k : Fin d,
      0 < routhHurwitzMinor (d+1) (k.val+1) (P j δ) := by
  apply properRouthMinors_eventually_positive d P q hzero hcoeff
  intro k
  have hk : k.val+1 ≤ q.natDegree := by omega
  simpa only [hdegree] using
    hurwitzPolynomial_all_routh_minors_positive q hleading hstable (k.val+1) hk

/-- Halving eventually accepts the manuscript's literal alternating
minor/sign test, with its former minor-positivity assumption discharged by
Hurwitz necessity rather than replaced by an unrelated search. -/
theorem localRouthPattern_has_halving_index_of_hurwitz
    {ι : Type*} [Fintype ι]
    (d : ℕ) (P : ι → ℝ → ℝ[X]) (q : ℝ[X]) (odd : ι → Bool)
    (hdegree : q.natDegree = d) (hleading : 0 < q.leadingCoeff)
    (hstable : ∀ z : ℂ,
      (q.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0)
    (hzero : ∀ j, P j 0 = Polynomial.X*q)
    (hcoeff : ∀ j n, ContinuousAt (fun δ => (P j δ).coeff n) 0)
    (hsign : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j, if odd j then (P j δ).coeff 0 < 0 else 0 < (P j δ).coeff 0) :
    ∃ b : ℕ, ∀ j : ι,
      (∀ k : Fin d,
        0 < routhHurwitzMinor (d+1) (k.val+1) (P j ((1/2 : ℝ)^b))) ∧
      (if odd j then (P j ((1/2 : ℝ)^b)).coeff 0 < 0
        else 0 < (P j ((1/2 : ℝ)^b)).coeff 0) := by
  apply localRouthPattern_has_halving_index d P q odd hzero hcoeff _ hsign
  intro k
  have hk : k.val+1 ≤ q.natDegree := by omega
  simpa only [hdegree] using
    hurwitzPolynomial_all_routh_minors_positive q hleading hstable (k.val+1) hk

/-- The exact rational checker accepts at one common finite halving
index. The original cast identity and constant-sign hypotheses are kept;
the generic Hurwitz-minor necessity supplies the previously missing input. -/
theorem rationalLocalRouthFamily_has_halving_index_of_hurwitz
    {ι : Type*} [Fintype ι]
    (d : ℕ) (P : ι → ℝ → ℝ[X]) (Q : ι → ℚ → ℚ[X])
    (q : ℝ[X]) (odd : ι → Bool)
    (hdegree : q.natDegree = d) (hleading : 0 < q.leadingCoeff)
    (hstable : ∀ z : ℂ,
      (q.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0)
    (hcast : ∀ j b,
      (Q j ((1/2 : ℚ)^b)).map (algebraMap ℚ ℝ) = P j ((1/2 : ℝ)^b))
    (hzero : ∀ j, P j 0 = Polynomial.X*q)
    (hcoeff : ∀ j n, ContinuousAt (fun δ => (P j δ).coeff n) 0)
    (hsign : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j, if odd j then (P j δ).coeff 0 < 0 else 0 < (P j δ).coeff 0) :
    ∃ b : ℕ, ∀ j : ι,
      rationalLocalRouthAccepts (d+1) (Q j ((1/2 : ℚ)^b)) (odd j) = true := by
  apply rationalLocalRouthFamily_has_halving_index
    d P Q q odd hcast hzero hcoeff _ hsign
  intro k
  have hk : k.val+1 ≤ q.natDegree := by omega
  simpa only [hdegree] using
    hurwitzPolynomial_all_routh_minors_positive q hleading hstable (k.val+1) hk

end
end PhosphorylationStableCapacity
