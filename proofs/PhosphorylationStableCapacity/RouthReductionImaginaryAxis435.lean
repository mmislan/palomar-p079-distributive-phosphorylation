module
public import proofs.PhosphorylationStableCapacity.RouthDeterminantRecursion435
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.RCLike.Lemmas

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

open Polynomial Filter
open scoped ComplexConjugate Topology

noncomputable section

/-- The component with parity opposite to the declared leading degree.
This is an exact polynomial projection, including the constant term. -/
def routhOppositeParity (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  Polynomial.C (1 / 2 : ℝ) *
    (p - Polynomial.C ((-1 : ℝ)^d) * p.comp (-Polynomial.X))

/-- The full real Routh homotopy. At the leading-coefficient ratio it
loses its highest term; the imaginary-axis theorem below does not assume
that its degree stays constant. -/
def routhPolynomialHomotopy (d : ℕ) (p : ℝ[X]) (t : ℝ) : ℝ[X] :=
  p - Polynomial.C t * Polynomial.X * routhOppositeParity d p

theorem routhOppositeParity_coeff (d n : ℕ) (p : ℝ[X]) :
    (routhOppositeParity d p).coeff n =
      if d % 2 = n % 2 then 0 else p.coeff n := by
  have hreflect : (p.comp (-Polynomial.X)).coeff n =
      p.coeff n * (-1 : ℝ)^n := by
    simpa only [Polynomial.C_neg, Polynomial.C_1, neg_mul, one_mul] using
      (Polynomial.comp_C_mul_X_coeff (p := p) (r := (-1 : ℝ)) (n := n))
  simp only [routhOppositeParity, Polynomial.coeff_C_mul,
    Polynomial.coeff_sub, hreflect]
  rw [neg_one_pow_eq_pow_mod_two d, neg_one_pow_eq_pow_mod_two n]
  have hd : d % 2 = 0 ∨ d % 2 = 1 := by omega
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hd with hd | hd <;> rcases hn with hn | hn <;>
    simp [hd, hn] <;> ring

private theorem routhDescendingCoeff_at_nonnegative
    (d : ℕ) (p : ℝ[X]) (s : ℤ) (hs : 0 ≤ s ∧ s ≤ (d : ℤ)) :
    routhDescendingCoeff d p s = p.coeff (d-s.toNat) := by
  simp only [routhDescendingCoeff, ite_eq_left hs]

theorem routhPolynomialHomotopy_coeff_succ
    (d n : ℕ) (p : ℝ[X]) (t : ℝ) :
    (routhPolynomialHomotopy d p t).coeff (n+1) =
      p.coeff (n+1) - t *
        (if d % 2 = n % 2 then 0 else p.coeff n) := by
  simp [routhPolynomialHomotopy, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_mul, mul_assoc, routhOppositeParity_coeff]

theorem routhPolynomialHomotopy_coeff_zero
    (d : ℕ) (p : ℝ[X]) (t : ℝ) :
    (routhPolynomialHomotopy d p t).coeff 0 = p.coeff 0 := by
  simp [routhPolynomialHomotopy, mul_assoc]

theorem routhPolynomialHomotopy_eval
    (d : ℕ) (p : ℝ[X]) (t : ℝ) (z : ℂ) :
    ((routhPolynomialHomotopy d p t).map (algebraMap ℝ ℂ)).eval z =
      (p.map (algebraMap ℝ ℂ)).eval z -
        (t : ℂ)*z*((routhOppositeParity d p).map (algebraMap ℝ ℂ)).eval z := by
  simp [routhPolynomialHomotopy, Polynomial.eval_map]

theorem routhPolynomialHomotopy_eval_continuous
    (d : ℕ) (p : ℝ[X]) (z : ℂ) :
    Continuous (fun t : ℝ => ((routhPolynomialHomotopy d p t).map
      (algebraMap ℝ ℂ)).eval z) := by
  simp only [routhPolynomialHomotopy_eval]
  exact continuous_const.sub
    ((Complex.continuous_ofReal.mul continuous_const).mul continuous_const)

theorem routhPolynomialHomotopy_coeff_continuous
    (d i : ℕ) (p : ℝ[X]) :
    Continuous (fun t : ℝ => (routhPolynomialHomotopy d p t).coeff i) := by
  cases i with
  | zero =>
      simp only [routhPolynomialHomotopy_coeff_zero]
      exact continuous_const
  | succ i =>
      simp only [routhPolynomialHomotopy_coeff_succ]
      exact continuous_const.sub (continuous_id.mul continuous_const)

theorem routhPolynomialHomotopy_natDegree_le
    (d : ℕ) (p : ℝ[X]) (hdegree : p.natDegree ≤ d) (t : ℝ) :
    (routhPolynomialHomotopy d p t).natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro N hN
  cases N with
  | zero => omega
  | succ n =>
      rw [routhPolynomialHomotopy_coeff_succ]
      have hc : p.coeff (n+1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hc]
      by_cases hn : n = d
      · subst n
        simp
      · have hcn : p.coeff n = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        simp [hcn]

theorem routhPolynomialHomotopy_top_coefficient
    (d : ℕ) (hd : 0 < d) (p : ℝ[X]) (t : ℝ) :
    (routhPolynomialHomotopy d p t).coeff d =
      p.coeff d - t * p.coeff (d-1) := by
  have hpar : ¬ (d % 2 = (d-1) % 2) := by omega
  have heq : d-1+1 = d := by omega
  have h := routhPolynomialHomotopy_coeff_succ d (d-1) p t
  simpa only [heq, ite_eq_right hpar] using h

/-- Before the leading-coefficient ratio the degree genuinely stays
constant and the leading coefficient stays positive. This supplies the
normalization needed by a subsequent topological no-crossing proof. -/
theorem routhPolynomialHomotopy_interior_degree_and_leading
    (d : ℕ) (hd : 0 < d) (p : ℝ[X]) (hdegree : p.natDegree ≤ d)
    (hpivot : 0 < p.coeff (d-1)) (t : ℝ)
    (ht : t < p.coeff d / p.coeff (d-1)) :
    (routhPolynomialHomotopy d p t).natDegree = d ∧
      (routhPolynomialHomotopy d p t).leadingCoeff =
        p.coeff d - t * p.coeff (d-1) ∧
      0 < (routhPolynomialHomotopy d p t).leadingCoeff := by
  have htop := routhPolynomialHomotopy_top_coefficient d hd p t
  have hpos : 0 < p.coeff d - t*p.coeff (d-1) := by
    have hmul := (lt_div_iff₀ hpivot).mp ht
    linarith
  have hdeg : (routhPolynomialHomotopy d p t).natDegree = d :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (routhPolynomialHomotopy_natDegree_le d p hdegree t)
      (by rw [htop]; exact ne_of_gt hpos)
  have hlead : (routhPolynomialHomotopy d p t).leadingCoeff =
      p.coeff d - t*p.coeff (d-1) := by
    rw [← Polynomial.coeff_natDegree, hdeg, htop]
  exact ⟨hdeg, hlead, by rw [hlead]; exact hpos⟩

/-- The coefficient producer used by the determinant recursion is
exactly the endpoint of the polynomial homotopy. The leading term is
cancelled explicitly, rather than silently dropping it from the sum. -/
theorem routhReducedPolynomial_eq_homotopy
    (d : ℕ) (hd : 0 < d) (p : ℝ[X]) (hdegree : p.natDegree ≤ d)
    (hpivot : routhDescendingCoeff d p 1 ≠ 0) :
    routhReducedPolynomial d p = routhPolynomialHomotopy d p
      (routhDescendingCoeff d p 0 / routhDescendingCoeff d p 1) := by
  let a := routhDescendingCoeff d p
  let c := a 0 / a 1
  have hcancel : a 0 = c*a 1 := (div_mul_cancel₀ (a 0) hpivot).symm
  have hzero : a 0 = p.coeff d := by simp [a, routhDescendingCoeff]
  have hone : a 1 = p.coeff (d-1) := by
    simp [a, routhDescendingCoeff, show (1 : ℤ) ≤ (d : ℤ) by omega]
  ext n
  change (routhReducedPolynomial d p).coeff n =
    (routhPolynomialHomotopy d p c).coeff n
  rw [routhReducedPolynomial_coeff]
  cases n with
  | zero =>
      rw [ite_eq_left hd]
      have had : a ((d : ℤ)-1+1) = p.coeff 0 := by
        rw [show (d : ℤ)-1+1 = (d : ℤ) by omega]
        simp [a, routhDescendingCoeff]
      have hadnext : a ((d : ℤ)-1+2) = 0 := by
        simp [a, routhDescendingCoeff,
          show ¬ (0 ≤ (d : ℤ)-1+2 ∧ (d : ℤ)-1+2 ≤ (d : ℤ)) by omega]
      change routhReducedCoefficients a c ((d : ℤ)-1-0) = _
      simp only [sub_zero, routhReducedCoefficients, had, hadnext, mul_zero,
        ite_self]
      simp [routhPolynomialHomotopy, mul_assoc]
  | succ n =>
      have hh : (routhPolynomialHomotopy d p c).coeff (n+1) =
          p.coeff (n+1) - c * (routhOppositeParity d p).coeff n := by
        simp [routhPolynomialHomotopy, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_mul, mul_assoc]
      rw [hh, routhOppositeParity_coeff]
      by_cases hsmall : n+1 < d
      · rw [ite_eq_left hsmall]
        have ha1 : a ((d : ℤ)-1-((n+1 : ℕ) : ℤ)+1) =
            p.coeff (n+1) := by
          dsimp only [a]
          rw [routhDescendingCoeff_at_nonnegative d p _ (by omega)]
          congr 1
          omega
        have ha2 : a ((d : ℤ)-1-((n+1 : ℕ) : ℤ)+2) =
            p.coeff n := by
          dsimp only [a]
          rw [routhDescendingCoeff_at_nonnegative d p _ (by omega)]
          congr 1
          omega
        have hpar : ((d : ℤ)-1-((n+1 : ℕ) : ℤ)) % 2 = 0 ↔
            d % 2 = n % 2 := by omega
        change routhReducedCoefficients a c ((d : ℤ)-1-((n+1 : ℕ) : ℤ)) = _
        simp only [routhReducedCoefficients, ha1, ha2]
        by_cases heven : d % 2 = n % 2
        · simp only [ite_eq_left heven, ite_eq_left (hpar.mpr heven), mul_zero,
            sub_zero]
        · have hodd : ¬ (((d : ℤ)-1-((n+1 : ℕ) : ℤ)) % 2 = 0) :=
            fun h => heven (hpar.mp h)
          simp only [ite_eq_right heven, ite_eq_right hodd]
      · rw [ite_eq_right hsmall]
        by_cases heq : n+1 = d
        · have hpar : ¬ (d % 2 = n % 2) := by omega
          rw [ite_eq_right hpar]
          rw [hzero, hone] at hcancel
          simpa only [← heq, Nat.add_sub_cancel] using
            (sub_eq_zero.mpr hcancel).symm
        · have hlarge : d < n+1 := by omega
          have hcoeff : p.coeff (n+1) = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegree hlarge)
          rw [hcoeff]
          by_cases hn : n = d
          · subst n
            simp
          · have hcn : p.coeff n = 0 :=
              Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
            simp [hcn]

/-- Pointwise evaluation convergence at the degree-dropping endpoint.
This is independent of any root-continuity or stability assumption. -/
theorem routhPolynomialHomotopy_eval_tendsto_reduced
    (d : ℕ) (hd : 0 < d) (p : ℝ[X]) (hdegree : p.natDegree ≤ d)
    (hpivot : routhDescendingCoeff d p 1 ≠ 0) (z : ℂ) :
    Tendsto (fun t : ℝ => ((routhPolynomialHomotopy d p t).map
      (algebraMap ℝ ℂ)).eval z)
      (𝓝 (routhDescendingCoeff d p 0 / routhDescendingCoeff d p 1))
      (𝓝 (((routhReducedPolynomial d p).map (algebraMap ℝ ℂ)).eval z)) := by
  rw [routhReducedPolynomial_eq_homotopy d hd p hdegree hpivot]
  exact (routhPolynomialHomotopy_eval_continuous d p z).tendsto _

private theorem real_polynomial_eval_neg_of_re_zero
    (p : ℝ[X]) (z : ℂ) (hz : z.re = 0) :
    (p.map (algebraMap ℝ ℂ)).eval (-z) =
      conj ((p.map (algebraMap ℝ ℂ)).eval z) := by
  have hconj : conj z = -z := by
    apply Complex.ext <;> simp [hz]
  have h := Polynomial.aeval_conj p z
  simpa only [hconj, Polynomial.aeval_def, Polynomial.eval_map] using h

theorem routhOppositeParity_eval_imaginary_axis
    (d : ℕ) (p : ℝ[X]) (z : ℂ) (hz : z.re = 0) :
    ((routhOppositeParity d p).map (algebraMap ℝ ℂ)).eval z =
      (1 / 2 : ℂ) * ((p.map (algebraMap ℝ ℂ)).eval z -
        ((-1 : ℂ)^d) * conj ((p.map (algebraMap ℝ ℂ)).eval z)) := by
  have hconst : ((Polynomial.C ((-1 : ℝ)^d)).map
      (algebraMap ℝ ℂ)).eval z = (-1 : ℂ)^d := by
    rw [Polynomial.map_C, Polynomial.eval_C]
    simp only [map_pow, map_neg, map_one]
  have hcomp : ((p.comp (-Polynomial.X)).map
      (algebraMap ℝ ℂ)).eval z = (p.map (algebraMap ℝ ℂ)).eval (-z) := by
    rw [Polynomial.map_comp, Polynomial.eval_comp, Polynomial.map_neg,
      Polynomial.map_X, Polynomial.eval_neg, Polynomial.eval_X]
  rw [routhOppositeParity, Polynomial.map_mul, Polynomial.eval_mul,
    Polynomial.map_C, Polynomial.eval_C, Polynomial.map_sub,
    Polynomial.eval_sub, Polynomial.map_mul, Polynomial.eval_mul,
    hconst, hcomp, real_polynomial_eval_neg_of_re_zero p z hz]
  simp only [map_div₀, map_one, map_ofNat]

/-- No member of the Routh homotopy creates an imaginary-axis root.
The parity component is orthogonal to its imaginary-axis correction.
No Hurwitz criterion, determinant sign, or root-count assertion is an
input to this algebraic implication. -/
theorem routhPolynomialHomotopy_imaginary_root_implies
    (d : ℕ) (p : ℝ[X]) (t : ℝ) (z : ℂ) (hz : z.re = 0)
    (hroot : ((routhPolynomialHomotopy d p t).map
      (algebraMap ℝ ℂ)).eval z = 0) :
    (p.map (algebraMap ℝ ℂ)).eval z = 0 := by
  let v := (p.map (algebraMap ℝ ℂ)).eval z
  have heq : v - (t : ℂ) * z *
      ((1 / 2 : ℂ) * (v - (-1 : ℂ)^d * conj v)) = 0 := by
    simpa only [routhPolynomialHomotopy_eval,
      routhOppositeParity_eval_imaginary_axis d p z hz, v] using hroot
  rw [neg_one_pow_eq_pow_mod_two d] at heq
  have hd : d % 2 = 0 ∨ d % 2 = 1 := by omega
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  change v = 0
  apply Complex.ext
  · change v.re = 0
    rcases hd with hd | hd
    · simp [hd, Complex.mul_re, Complex.mul_im, hz] at hre him
      simpa only [him, add_zero, mul_zero] using hre
    · simpa [hd, Complex.mul_re, Complex.mul_im, hz] using hre
  · change v.im = 0
    rcases hd with hd | hd
    · simpa [hd, Complex.mul_re, Complex.mul_im, hz] using him
    · simp [hd, Complex.mul_re, Complex.mul_im, hz] at hre him
      simpa only [hre, add_zero, mul_zero, sub_zero] using him

theorem routhPolynomialHomotopy_no_imaginary_axis_roots
    (d : ℕ) (p : ℝ[X])
    (hstable : ∀ z : ℂ,
      (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0)
    (t : ℝ) (z : ℂ) (hz : z.re = 0) :
    ((routhPolynomialHomotopy d p t).map
      (algebraMap ℝ ℂ)).eval z ≠ 0 := by
  intro hroot
  have h := hstable z
    (routhPolynomialHomotopy_imaginary_root_implies d p t z hz hroot)
  linarith

/-- The actual finite reduced polynomial has no new imaginary-axis
roots. The proof includes its coefficient-producer correspondence. -/
theorem routhReducedPolynomial_imaginary_root_implies
    (d : ℕ) (hd : 0 < d) (p : ℝ[X]) (hdegree : p.natDegree ≤ d)
    (hpivot : routhDescendingCoeff d p 1 ≠ 0)
    (z : ℂ) (hz : z.re = 0)
    (hroot : ((routhReducedPolynomial d p).map
      (algebraMap ℝ ℂ)).eval z = 0) :
    (p.map (algebraMap ℝ ℂ)).eval z = 0 := by
  rw [routhReducedPolynomial_eq_homotopy d hd p hdegree hpivot] at hroot
  exact routhPolynomialHomotopy_imaginary_root_implies d p _ z hz hroot

theorem routhReducedPolynomial_no_imaginary_axis_roots
    (d : ℕ) (hd : 0 < d) (p : ℝ[X]) (hdegree : p.natDegree ≤ d)
    (hpivot : routhDescendingCoeff d p 1 ≠ 0)
    (hstable : ∀ z : ℂ,
      (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0)
    (z : ℂ) (hz : z.re = 0) :
    ((routhReducedPolynomial d p).map
      (algebraMap ℝ ℂ)).eval z ≠ 0 := by
  intro hroot
  have h := hstable z
    (routhReducedPolynomial_imaginary_root_implies d hd p hdegree hpivot z hz hroot)
  linarith

end
end PhosphorylationStableCapacity
