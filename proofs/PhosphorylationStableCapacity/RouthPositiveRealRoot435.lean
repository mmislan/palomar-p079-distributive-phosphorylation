module
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega
public import Lean.Meta.Tactic.NormCast

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial Filter
open scoped Topology BigOperators

/-- Ascending polynomial coefficients change once from nonpositive to
nonnegative. The strictly negative constant and positive cut are kept
separate so strict derivative statements do not rely on zero coefficients. -/
def SignedCoefficientTransition (p : ℝ[X]) (cut : ℕ) : Prop :=
  0 < cut ∧ p.coeff 0 < 0 ∧
    (∀ i, i < cut → p.coeff i ≤ 0) ∧
    (∀ i, cut ≤ i → 0 ≤ p.coeff i)

/-- The exact weighted derivative is a finite sum whose summands all
have nonnegative sign under one coefficient transition. Its constant
summand is strictly positive. -/
theorem signedCoefficientTransition_weighted_derivative_pos
    (p : ℝ[X]) (cut : ℕ) (h : SignedCoefficientTransition p cut)
    (x : ℝ) (hx : 0 < x) :
    0 < x*p.derivative.eval x-(cut : ℝ)*p.eval x := by
  classical
  obtain ⟨hcut, hconstant, hbelow, habove⟩ := h
  have hderiv : p.derivative.eval x =
      ∑ i ∈ Finset.range (p.natDegree+1), p.coeff i*(i : ℝ)*x^(i-1) := by
    rw [Polynomial.derivative_eval]
    exact p.sum_over_range (by intro i; simp)
  have heval : p.eval x =
      ∑ i ∈ Finset.range (p.natDegree+1), p.coeff i*x^i :=
    Polynomial.eval_eq_sum_range x
  have hidentity : x*p.derivative.eval x-(cut : ℝ)*p.eval x =
      ∑ i ∈ Finset.range (p.natDegree+1),
        p.coeff i*((i : ℝ)-(cut : ℝ))*x^i := by
    rw [hderiv, heval, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    cases i with
    | zero =>
        simp only [Nat.cast_zero, mul_zero, zero_sub,
          Nat.zero_sub, pow_zero, mul_one]
        ring
    | succ i =>
        simp only [Nat.add_sub_cancel, pow_succ]
        ring
  rw [hidentity]
  have hnonneg : ∀ i ∈ Finset.range (p.natDegree+1),
      0 ≤ p.coeff i*((i : ℝ)-(cut : ℝ))*x^i := by
    intro i _hi
    by_cases hi : i < cut
    · have hcast : (i : ℝ) ≤ (cut : ℝ) := by exact_mod_cast hi.le
      exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos
        (hbelow i hi) (sub_nonpos.mpr hcast)) (pow_nonneg hx.le _)
    · have hi' : cut ≤ i := Nat.le_of_not_gt hi
      have hcast : (cut : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi'
      exact mul_nonneg (mul_nonneg (habove i hi') (sub_nonneg.mpr hcast))
        (pow_nonneg hx.le _)
  apply (Finset.sum_pos_iff_of_nonneg hnonneg).mpr
  refine ⟨0, by simp, ?_⟩
  have hcast : 0 < (cut : ℝ) := by exact_mod_cast hcut
  have hterm : 0 < p.coeff 0*(-(cut : ℝ)) :=
    mul_pos_of_neg_of_neg hconstant (neg_lt_zero.mpr hcast)
  simpa only [Nat.cast_zero, zero_sub, pow_zero, mul_one] using hterm

/-- Every positive real root is simple under the coefficient transition.
This proves the real-root simplicity obligation only, not a complex
right-half-plane count. -/
theorem signedCoefficientTransition_derivative_at_positive_root
    (p : ℝ[X]) (cut : ℕ) (h : SignedCoefficientTransition p cut)
    (x : ℝ) (hx : 0 < x) (hroot : p.eval x = 0) :
    0 < p.derivative.eval x := by
  have hweighted := signedCoefficientTransition_weighted_derivative_pos p cut h x hx
  rw [hroot, mul_zero, sub_zero] at hweighted
  exact (mul_pos_iff_of_pos_left hx).mp hweighted

private theorem signedCoefficientTransition_normalized_positive_derivative
    (p : ℝ[X]) (cut : ℕ) (h : SignedCoefficientTransition p cut)
    (x : ℝ) (hx : 0 < x) :
    ∃ v : ℝ, 0 < v ∧ HasDerivAt (fun y : ℝ => p.eval y/y^cut) v x := by
  have hcut : 0 < cut := h.1
  have hpower : HasDerivAt (fun y : ℝ => y^cut)
      ((cut : ℝ)*x^(cut-1)) x := by
    have hfun : (id : ℝ → ℝ)^cut = (fun y : ℝ => y^cut) := by
      funext y
      exact Pi.pow_apply (id : ℝ → ℝ) cut y
    simpa only [hfun, id_eq, mul_one] using (hasDerivAt_id x).pow cut
  let v : ℝ := (p.derivative.eval x*x^cut-
    p.eval x*((cut : ℝ)*x^(cut-1)))/(x^cut)^2
  have hidentity : p.derivative.eval x*x^cut-
      p.eval x*((cut : ℝ)*x^(cut-1)) =
      x^(cut-1)*(x*p.derivative.eval x-(cut : ℝ)*p.eval x) := by
    have hp : x^cut = x^(cut-1)*x := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hp]
    ring
  have hv : 0 < v := by
    dsimp only [v]
    rw [hidentity]
    exact div_pos (mul_pos (pow_pos hx _)
      (signedCoefficientTransition_weighted_derivative_pos p cut h x hx))
      (sq_pos_of_pos (pow_pos hx cut))
  refine ⟨v, hv, ?_⟩
  exact (p.hasDerivAt x).div hpower (pow_ne_zero _ hx.ne')

/-- Normalized evaluation is strictly increasing on the whole positive
axis, proving uniqueness without a Descartes/root-count theorem. -/
theorem signedCoefficientTransition_normalized_strictMonoOn
    (p : ℝ[X]) (cut : ℕ) (h : SignedCoefficientTransition p cut) :
    StrictMonoOn (fun x : ℝ => p.eval x/x^cut) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ))
  · intro x hx
    obtain ⟨v, _hv, hderiv⟩ :=
      signedCoefficientTransition_normalized_positive_derivative p cut h x hx
    exact hderiv.continuousAt.continuousWithinAt
  · intro x hx
    have hxpos : 0 < x := by simpa only [interior_Ioi, Set.mem_Ioi] using hx
    obtain ⟨v, hv, hderiv⟩ :=
      signedCoefficientTransition_normalized_positive_derivative p cut h x hxpos
    rw [hderiv.deriv]
    exact hv

/-- Two positive real roots under this transition must coincide. This
is the real-root uniqueness obligation, without any complex conclusion. -/
theorem signedCoefficientTransition_positive_root_unique
    (p : ℝ[X]) (cut : ℕ) (h : SignedCoefficientTransition p cut)
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (huroot : p.eval u = 0) (hvroot : p.eval v = 0) : u = v := by
  apply (signedCoefficientTransition_normalized_strictMonoOn p cut h).injOn hu hv
  simp only [huroot, hvroot, zero_div]

/-- Every strict positive bracket around the unique positive root has
the signs needed by the continuous-root IVT construction. -/
theorem signedCoefficientTransition_root_bracket_signs
    (p : ℝ[X]) (cut : ℕ) (h : SignedCoefficientTransition p cut)
    (u l r : ℝ) (hu : 0 < u) (hroot : p.eval u = 0)
    (hl : 0 < l) (hlu : l < u) (hur : u < r) :
    p.eval l < 0 ∧ 0 < p.eval r := by
  have hr : 0 < r := lt_trans hu hur
  have hmono := signedCoefficientTransition_normalized_strictMonoOn p cut h
  have hleft := hmono hl hu hlu
  have hright := hmono hu hr hur
  dsimp only at hleft hright
  rw [hroot, zero_div] at hleft hright
  refine ⟨?_, ?_⟩
  · simpa only [zero_mul] using (div_lt_iff₀ (pow_pos hl cut)).mp hleft
  · simpa only [zero_mul] using (lt_div_iff₀ (pow_pos hr cut)).mp hright

/-- Negative constant and positive leading coefficient guarantee a
positive root by the intermediate value theorem. -/
theorem polynomial_positive_root_of_negative_constant
    (p : ℝ[X]) (hconstant : p.coeff 0 < 0) (hleading : 0 < p.leadingCoeff) :
    ∃ u : ℝ, 0 < u ∧ p.eval u = 0 := by
  have hdegree : 0 < p.natDegree := by
    by_contra hdegree
    have hd : p.natDegree = 0 := Nat.eq_zero_of_not_pos hdegree
    have hlead : p.leadingCoeff = p.coeff 0 := by
      simp only [Polynomial.leadingCoeff, hd]
    exact (not_lt_of_ge hleading.le) (by simpa only [← hlead] using hconstant)
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < p.eval x :=
    (p.tendsto_atTop_of_leadingCoeff_nonneg
      (Polynomial.natDegree_pos_iff_degree_pos.mp hdegree) hleading.le).eventually_gt_atTop 0
  obtain ⟨b, hb, hpb⟩ := ((eventually_gt_atTop (0 : ℝ)).and hpos).exists
  have hpzero : p.eval 0 < 0 := by simpa only [← Polynomial.coeff_zero_eq_eval_zero] using hconstant
  obtain ⟨u, hu, hroot⟩ := intermediate_value_Icc hb.le p.continuous.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (p.eval 0) (p.eval b) from ⟨hpzero.le, hpb.le⟩)
  have hune : u ≠ 0 := by
    intro hzero
    have hpzeroeq : p.eval 0 = 0 := by simpa only [hzero] using hroot
    exact (ne_of_lt hpzero) hpzeroeq
  exact ⟨u, lt_of_le_of_ne hu.1 hune.symm, hroot⟩

/-- Complete existence, uniqueness and simplicity of the positive real
root from one coefficient transition. Complex spectral counting still
requires the separate signed-family topology argument. -/
theorem signedCoefficientTransition_unique_simple_positive_root
    (p : ℝ[X]) (cut : ℕ) (h : SignedCoefficientTransition p cut)
    (hleading : 0 < p.leadingCoeff) :
    ∃ u : ℝ, 0 < u ∧ p.eval u = 0 ∧ 0 < p.derivative.eval u ∧
      ∀ v : ℝ, 0 < v → p.eval v = 0 → v = u := by
  obtain ⟨u, hu, hroot⟩ := polynomial_positive_root_of_negative_constant p h.2.1 hleading
  refine ⟨u, hu, hroot,
    signedCoefficientTransition_derivative_at_positive_root p cut h u hu hroot, ?_⟩
  intro v hv hvroot
  exact signedCoefficientTransition_positive_root_unique p cut h v u hv hu hvroot hroot

private theorem positiveRootReal_eval_map (p : ℝ[X]) (u : ℝ) :
    (p.map (algebraMap ℝ ℂ)).eval (u : ℂ) = ((p.eval u : ℝ) : ℂ) := by
  simpa only [Complex.coe_algebraMap] using
    (Polynomial.eval_map_apply (p := p) (f := algebraMap ℝ ℂ) u)

/-- The same unique simple positive root is preserved by the exact real
to complex coefficient embedding, ready for the signed topology endpoint. -/
theorem signedCoefficientTransition_unique_simple_positive_complex_root
    (p : ℝ[X]) (cut : ℕ) (h : SignedCoefficientTransition p cut)
    (hleading : 0 < p.leadingCoeff) :
    ∃ u : ℝ, 0 < u ∧ (p.map (algebraMap ℝ ℂ)).eval (u : ℂ) = 0 ∧
      (p.map (algebraMap ℝ ℂ)).derivative.eval (u : ℂ) ≠ 0 ∧
      ∀ v : ℝ, 0 < v → (p.map (algebraMap ℝ ℂ)).eval (v : ℂ) = 0 → v = u := by
  obtain ⟨u, hu, hroot, hderiv, hunique⟩ :=
    signedCoefficientTransition_unique_simple_positive_root p cut h hleading
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · simpa only [positiveRootReal_eval_map, Complex.ofReal_eq_zero] using hroot
  · have hnonzero : ((p.derivative.eval u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hderiv.ne'
    simpa only [Polynomial.derivative_map, positiveRootReal_eval_map] using hnonzero
  · intro v hv hvroot
    apply hunique v hv
    have hcast : ((p.eval v : ℝ) : ℂ) = 0 := by
      simpa only [positiveRootReal_eval_map] using hvroot
    exact_mod_cast hcast

end
end PhosphorylationStableCapacity
