module
public import proofs.PhosphorylationStableCapacity.P079AnalyticalCorollaries435
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter
open scoped Topology

/-- The normalized leading coefficient tends to zero despite its linear
prefactor. -/
theorem coalescedV_tendsto_zero :
    Tendsto (fun m : ℕ => coalescedV m) atTop (𝓝 0) := by
  let q : ℝ := 2 / 9
  have hpow : Tendsto (fun m : ℕ => q^m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num [q]) (by norm_num [q])
  have hlinear : Tendsto (fun m : ℕ => (m : ℝ) * q^m) atTop (𝓝 0) := by
    simpa [q] using
      (tendsto_self_mul_const_pow_of_abs_lt_one
        (by norm_num : |(2 / 9 : ℝ)| < 1))
  have hscaled : Tendsto
      (fun m : ℕ => (3 * (m : ℝ) + 4) * q^m) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun m : ℕ => 3 * ((m : ℝ) * q^m))
        atTop (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_const_nhds (x := (3 : ℝ))).mul hlinear
    have h₂ : Tendsto (fun m : ℕ => 4 * q^m)
        atTop (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_const_nhds (x := (4 : ℝ))).mul hpow
    have h := h₁.add h₂
    have heq : (fun m : ℕ => (3 * (m : ℝ) + 4) * q^m) =
        (fun m : ℕ => 3 * ((m : ℝ) * q^m) + 4 * q^m) := by
      funext m
      ring_nf
    rw [heq]
    simpa using h
  have h := (tendsto_const_nhds (x := q)).mul hscaled
  convert h using 1
  · funext m
    rw [coalescedV_closed_form]
    dsimp [q]
    rw [pow_succ]
    ring_nf
  · ring_nf

/-- The manuscript's exact geometric asymptotic of the feedback deficit:
for `n=m+2`, `(1-G_n)/(n²(2/9)^(n-1)) → 25/21`. -/
theorem coalescedFeedbackDeficit_asymptotic :
    Tendsto
      (fun m : ℕ =>
        (1 - coalescedFeedbackGain m) /
          (((m : ℝ) + 2)^2 * (2 / 9 : ℝ)^(m+1)))
      atTop (𝓝 (25 / 21 : ℝ)) := by
  let q : ℝ := 2 / 9
  have hinv : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 2))
      atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    convert h using 1
    funext m
    simp [Nat.cast_add]
    ring_nf
  have hv := coalescedV_tendsto_zero
  have hnum : Tendsto
      (fun m : ℕ =>
        (3 - 2 / ((m : ℝ) + 2)) *
          (50 - 45 / ((m : ℝ) + 2)))
      atTop (𝓝 (3 * 50 : ℝ)) := by
    have h₃ : Tendsto (fun m : ℕ => 3 - 2 / ((m : ℝ) + 2))
        atTop (𝓝 (3 : ℝ)) := by
      have h := (tendsto_const_nhds (x := (3 : ℝ))).sub
        ((tendsto_const_nhds (x := (2 : ℝ))).mul hinv)
      simpa [div_eq_mul_inv] using h
    have h₅₀ : Tendsto (fun m : ℕ => 50 - 45 / ((m : ℝ) + 2))
        atTop (𝓝 (50 : ℝ)) := by
      have h := (tendsto_const_nhds (x := (50 : ℝ))).sub
        ((tendsto_const_nhds (x := (45 : ℝ))).mul hinv)
      simpa [div_eq_mul_inv] using h
    exact h₃.mul h₅₀
  have hden : Tendsto (fun m : ℕ =>
      9 * (14 - 8 * coalescedV m)) atTop (𝓝 (9 * 14 : ℝ)) := by
    convert (tendsto_const_nhds (x := (9 : ℝ))).mul
      (tendsto_const_nhds.sub
        ((tendsto_const_nhds (x := (8 : ℝ))).mul hv)) using 1;
      norm_num
  have hratio := hnum.div hden (by norm_num : (9 * 14 : ℝ) ≠ 0)
  have hlimit : Tendsto
      (fun m : ℕ =>
        ((3 - 2 / ((m : ℝ) + 2)) *
          (50 - 45 / ((m : ℝ) + 2))) /
          (9 * (14 - 8 * coalescedV m)))
      atTop (𝓝 (25 / 21 : ℝ)) := by
    convert hratio using 1; norm_num
  apply hlimit.congr'
  filter_upwards [] with m
  have hq : q^(m+1) ≠ 0 := pow_ne_zero _ (by norm_num [q])
  have hm : ((m : ℝ) + 2) ≠ 0 := by positivity
  have hden' : 14 - 8 * coalescedV m ≠ 0 := by
    have hb := coalescedV_bounds m
    linarith
  rw [coalescedFeedbackDeficit_closed_form,
    coalescedV_closed_form]
  rw [coalescedV_closed_form] at hden'
  dsimp [q] at hq
  field_simp [hq, hm, hden']
  ring_nf

end

end PhosphorylationStableCapacity
