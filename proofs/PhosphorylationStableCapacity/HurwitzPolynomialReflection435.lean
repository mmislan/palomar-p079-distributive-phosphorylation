module
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Basic.Complex.Basic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial

/-- Reflection at a fixed bound has exactly that degree whenever the
original constant coefficient is nonzero, even if the original degree drops. -/
theorem fixed_reflection_degree_and_leadingCoeff
    {R : Type*} [Semiring R] (p : R[X]) (d : ℕ)
    (hd : p.natDegree ≤ d) (hzero : p.coeff 0 ≠ 0) :
    (p.reflect d).natDegree = d ∧ (p.reflect d).leadingCoeff = p.coeff 0 := by
  have hcoeff : (p.reflect d).coeff d = p.coeff 0 := by
    rw [coeff_reflect, revAt_le le_rfl, Nat.sub_self]
  have hlow : d ≤ (p.reflect d).natDegree :=
    le_natDegree_of_ne_zero (by simpa only [hcoeff] using hzero)
  have hhigh : (p.reflect d).natDegree ≤ d := by
    simpa only [max_eq_left hd] using
      (Polynomial.natDegree_reflect_le (N := d) (p := p))
  have heq := le_antisymm hhigh hlow
  exact ⟨heq, by simpa only [Polynomial.leadingCoeff, heq] using hcoeff⟩

/-- Coefficient maps commute with fixed-length reflection. -/
theorem fixed_reflection_map
    {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (p : R[X]) (d : ℕ) :
    (p.reflect d).map f = (p.map f).reflect d :=
  (Polynomial.reflect_map f p d).symm

/-- Nonzero reflected roots are reciprocals of original roots. Fixed
reflection length permits the original degree to be strictly smaller. -/
theorem fixed_reflection_eval_zero_iff
    (p : ℂ[X]) (d : ℕ) (hd : p.natDegree ≤ d)
    (z : ℂ) (hz : z ≠ 0) :
    (p.reflect d).eval z = 0 ↔ p.eval z⁻¹ = 0 := by
  let : Invertible (z⁻¹) := invertibleOfNonzero (inv_ne_zero hz)
  simpa only [invOf_eq_inv, inv_inv, Polynomial.eval₂_id] using
    Polynomial.eval₂_reflect_eq_zero_iff (RingHom.id ℂ) (z⁻¹) d p hd

/-- Complex inversion preserves the strict sign of the real part. -/
theorem complex_inv_re_neg_iff (z : ℂ) : (z⁻¹).re < 0 ↔ z.re < 0 := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [Complex.inv_re]
    simpa only [zero_mul] using (show z.re / Complex.normSq z < (0 : ℝ) ↔ z.re < 0 * Complex.normSq z from div_lt_iff₀ (Complex.normSq_pos.mpr hz))

/-- Complex inversion preserves the closed left half-plane, including zero. -/
theorem complex_inv_re_nonpos_iff (z : ℂ) : (z⁻¹).re ≤ 0 ↔ z.re ≤ 0 := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [Complex.inv_re]
    simpa only [zero_mul] using (show z.re / Complex.normSq z ≤ (0 : ℝ) ↔ z.re ≤ 0 * Complex.normSq z from div_le_iff₀ (Complex.normSq_pos.mpr hz))

/-- Inversion also preserves membership in the imaginary axis. -/
theorem complex_inv_re_eq_zero_iff (z : ℂ) : (z⁻¹).re = 0 ↔ z.re = 0 := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [Complex.inv_re]
    simp only [div_eq_zero_iff, (Complex.normSq_pos.mpr hz).ne', or_false]

/-- A strict Hurwitz polynomial remains strict Hurwitz under reflection at
its actual degree. This excludes the reflected zero root using the original
nonzero leading coefficient; a larger reflection length would not do so. -/
theorem fixed_reflection_hurwitz_of_exact_degree
    (p : ℂ[X]) (d : ℕ) (hd : p.natDegree = d)
    (hroots : ∀ z : ℂ, p.eval z = 0 → z.re < 0) :
    ∀ z : ℂ, (p.reflect d).eval z = 0 → z.re < 0 := by
  have hp : p ≠ 0 := by
    intro hpzero
    have hbad := hroots 0 (by simp [hpzero])
    simp only [Complex.zero_re, lt_self_iff_false] at hbad
  have hconstant : (p.reflect d).coeff 0 = p.leadingCoeff := by
    rw [coeff_reflect, revAt_le (Nat.zero_le d), Nat.sub_zero, ← hd]
    rfl
  intro z hz
  have hznonzero : z ≠ 0 := by
    intro hz0
    have hleading : p.leadingCoeff = 0 := by
      simpa only [hz0, ← coeff_zero_eq_eval_zero, hconstant] using hz
    exact (Polynomial.leadingCoeff_ne_zero.mpr hp) hleading
  have hroot : p.eval z⁻¹ = 0 :=
    (fixed_reflection_eval_zero_iff p d hd.le z hznonzero).mp hz
  exact (complex_inv_re_neg_iff z).mp (hroots z⁻¹ hroot)

/-- Scaling a fixed-length reflection by the reciprocal constant
coefficient produces a monic polynomial of constant degree. -/
theorem normalized_fixed_reflection_monic_and_degree
    (p : ℂ[X]) (d : ℕ) (hd : p.natDegree ≤ d) (hzero : p.coeff 0 ≠ 0) :
    (C ((p.coeff 0)⁻¹)*p.reflect d).Monic ∧
      (C ((p.coeff 0)⁻¹)*p.reflect d).natDegree = d := by
  obtain ⟨hdegree, hleading⟩ := fixed_reflection_degree_and_leadingCoeff p d hd hzero
  have hunit : IsUnit ((p.coeff 0)⁻¹) := isUnit_iff_ne_zero.mpr (inv_ne_zero hzero)
  refine ⟨?_, ?_⟩
  · change (C ((p.coeff 0)⁻¹)*p.reflect d).leadingCoeff = 1
    rw [leadingCoeff_C_mul_of_isUnit hunit, hleading, inv_mul_cancel₀ hzero]
  · rw [natDegree_C_mul_of_isUnit hunit, hdegree]

end

end PhosphorylationStableCapacity
