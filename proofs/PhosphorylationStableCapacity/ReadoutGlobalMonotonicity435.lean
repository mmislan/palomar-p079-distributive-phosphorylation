module
public import proofs.PhosphorylationStableCapacity.ReadoutDerivative435
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Polynomial

/-- A polynomial with nonnegative coefficients and degree at most `m`
has nondecreasing `u^m / D(u)` on positive arguments. Dense positivity
provides the actual positive denominator used by the paper. -/
theorem densePositive_power_div_eval_monotoneOn
    (m : ℕ) (D : ℝ[X]) (hD : DensePositive D m) :
    MonotoneOn (fun u : ℝ => u^m / D.eval u) (Set.Ioi 0) := by
  intro u hu v hv huv
  have hu0 : 0 < u := hu
  have hv0 : 0 < v := hv
  have hDu : 0 < D.eval u := hD.eval_pos hu0
  have hDv : 0 < D.eval v := hD.eval_pos hv0
  apply (div_le_div_iff₀ hDu hDv).mpr
  rw [D.eval_eq_sum_range' (n := m+1) (by rw [hD.degree_eq]; omega) v,
    D.eval_eq_sum_range' (n := m+1) (by rw [hD.degree_eq]; omega) u,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have him : i ≤ m := by have := Finset.mem_range.mp hi; omega
  have hpow : u^(m-i) ≤ v^(m-i) := pow_le_pow_left₀ hu0.le huv _
  have hscaled : u^(m-i) * (u^i*v^i) ≤ v^(m-i) * (u^i*v^i) :=
    mul_le_mul_of_nonneg_right hpow (mul_nonneg (pow_nonneg hu0.le _) (pow_nonneg hv0.le _))
  have hexp : m-i+i = m := Nat.sub_add_cancel him
  have hupow : u^(m-i)*u^i = u^m := by rw [← pow_add, hexp]
  have hvpow : v^(m-i)*v^i = v^m := by rw [← pow_add, hexp]
  have hcross : u^m*v^i ≤ v^m*u^i := by
    calc
      u^m*v^i = u^(m-i)*(u^i*v^i) := by rw [← hupow]; ring
      _ ≤ v^(m-i)*(u^i*v^i) := hscaled
      _ = v^m*u^i := by rw [← hvpow]; ring
  have hcoeff : 0 ≤ D.coeff i := hD.nonneg i
  convert mul_le_mul_of_nonneg_left hcross hcoeff using 1 <;> ring

private theorem readout_factor_pos {x : ℝ} (hx : 1 < x) :
    0 < (x-1)*(x+5)/(x+1) := by
  apply div_pos
  · exact mul_pos (by linarith) (by linarith)
  · linarith

private theorem readout_factor_eq {x : ℝ} (hx : 1 < x) :
    (x-1)*(x+5)/(x+1) = x+3-8/(x+1) := by
  have hden : x+1 ≠ 0 := by linarith
  field_simp [hden]
  ring

private theorem readout_factor_strictMonoOn :
    StrictMonoOn (fun x : ℝ => (x-1)*(x+5)/(x+1)) (Set.Ioi 1) := by
  intro a ha b hb hab
  have ha0 : 0 < a+1 := by have : 1 < a := ha; linarith
  have hb0 : 0 < b+1 := by have : 1 < b := hb; linarith
  have hdiv : (8 : ℝ)/(b+1) ≤ 8/(a+1) :=
    (div_le_div_iff₀ hb0 ha0).mpr (by linarith)
  change (a-1)*(a+5)/(a+1) < (b-1)*(b+5)/(b+1)
  rw [readout_factor_eq ha, readout_factor_eq hb]
  linarith

/-- The manuscript's scalar physical readout is strictly increasing
throughout the full domain `x > 1`, for every dense positive conversion
polynomial. This is a global statement, including degree zero; it does
not infer global monotonicity from its derivative at coalescence. -/
theorem splitReadoutScalar_strictMonoOn_Ioi_one
    (m : ℕ) (D : ℝ[X]) (hD : DensePositive D m) :
    StrictMonoOn (splitReadoutScalar m D) (Set.Ioi 1) := by
  intro a ha b hb hab
  have hua : 0 < ratio a := ratio_pos ha
  have hub : 0 < ratio b := ratio_pos hb
  have huv : ratio a ≤ ratio b := by
    unfold ratio
    have ha0 : 0 < a := by have : 1 < a := ha; linarith
    have hsquares : a^2 ≤ b^2 := pow_le_pow_left₀ ha0.le hab.le 2
    apply (div_le_div_iff₀ (by norm_num : 0 < (8 : ℝ))
      (by norm_num : 0 < (8 : ℝ))).mpr
    nlinarith [hsquares]
  have hf := densePositive_power_div_eval_monotoneOn m D hD hua hub huv
  have hfa : 0 < (ratio a)^m / D.eval (ratio a) :=
    div_pos (pow_pos hua _) (hD.eval_pos hua)
  have hscale : 0 < D.coeff m / 2 := div_pos (hD.1 m le_rfl) (by norm_num)
  have hg := readout_factor_strictMonoOn ha hb hab
  have hgb : 0 < (b-1)*(b+5)/(b+1) := readout_factor_pos hb
  unfold splitReadoutScalar
  exact lt_of_lt_of_le
    (mul_lt_mul_of_pos_left hg (mul_pos hscale hfa))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf hscale.le) hgb.le)

/-- Explicit comparison form of the global readout-order theorem. -/
theorem splitReadoutScalar_lt_of_one_lt
    (m : ℕ) (D : ℝ[X]) (hD : DensePositive D m)
    {a b : ℝ} (ha : 1 < a) (hab : a < b) :
    splitReadoutScalar m D a < splitReadoutScalar m D b :=
  splitReadoutScalar_strictMonoOn_Ioi_one m D hD ha (lt_trans ha hab) hab

end
end PhosphorylationStableCapacity
