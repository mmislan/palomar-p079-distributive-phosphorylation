module
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter
open scoped Topology BigOperators

/-- A finite affine current family needs first-order checks only at the
all-one vector and one positive two-at-a-site probe per edge. The
resulting bound is uniform on any set with bounded current coordinates.
No derivative in the current parameter is assumed. -/
theorem affine_positive_probe_uniform_first_order
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set (ι → ℝ)) (F : (ι → ℝ) → ℝ → E)
    (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hbound : ∀ w ∈ K, ∀ i, |w i - 1| ≤ M)
    (haffine : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), ∀ w ∈ K,
      F w δ = F (fun _ => 1) δ +
        ∑ i : ι, (w i - 1) •
          (F (fun j => if j = i then 2 else 1) δ -
            F (fun _ => 1) δ))
    (haffine0 : ∀ w ∈ K,
      F w 0 = F (fun _ => 1) 0 +
        ∑ i : ι, (w i - 1) •
          (F (fun j => if j = i then 2 else 1) 0 -
            F (fun _ => 1) 0))
    (hprobe : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ),
      ‖F (fun _ => 1) δ - F (fun _ => 1) 0‖ ≤ C * |δ| ∧
      ∀ i : ι,
        ‖F (fun j => if j = i then 2 else 1) δ -
          F (fun j => if j = i then 2 else 1) 0‖ ≤ C * |δ|) :
    ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), ∀ w ∈ K,
      ‖F w δ - F w 0‖ ≤
        (C + (Fintype.card ι : ℝ) * M * (2 * C)) * |δ| := by
  filter_upwards [hprobe, haffine] with δ hδ haffineδ w hw
  let Δ₀ := F (fun _ : ι => 1) δ - F (fun _ : ι => 1) 0
  let Δ : ι → E := fun i =>
    F (fun j => if j = i then 2 else 1) δ -
      F (fun j => if j = i then 2 else 1) 0
  have hdecomp : F w δ - F w 0 =
      Δ₀ + ∑ i : ι, (w i - 1) • (Δ i - Δ₀) := by
    rw [haffineδ w hw, haffine0 w hw]
    dsimp [Δ₀, Δ]
    simp only [Finset.sum_sub_distrib, smul_sub]
    abel
  have hΔ₀ : ‖Δ₀‖ ≤ C * |δ| := hδ.1
  have hΔ (i : ι) : ‖Δ i‖ ≤ C * |δ| := hδ.2 i
  have hdiff (i : ι) : ‖Δ i - Δ₀‖ ≤ 2 * C * |δ| := by
    calc
      ‖Δ i - Δ₀‖ ≤ ‖Δ i‖ + ‖Δ₀‖ := norm_sub_le _ _
      _ ≤ C * |δ| + C * |δ| := add_le_add (hΔ i) hΔ₀
      _ = 2 * C * |δ| := by ring
  rw [hdecomp]
  calc
    ‖Δ₀ + ∑ i : ι, (w i - 1) • (Δ i - Δ₀)‖ ≤
        ‖Δ₀‖ + ‖∑ i : ι, (w i - 1) • (Δ i - Δ₀)‖ :=
      norm_add_le _ _
    _ ≤ C * |δ| + ∑ i : ι, ‖(w i - 1) • (Δ i - Δ₀)‖ :=
      add_le_add hΔ₀ (norm_sum_le _ _)
    _ ≤ C * |δ| + ∑ _i : ι, M * (2 * C * |δ|) := by
      apply add_le_add (le_refl (C * |δ|))
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      have hwabs : |w i - 1| ≤ |M| :=
        (hbound w hw i).trans (le_abs_self M)
      have hmajorant : 0 ≤ 2 * C * |δ| :=
        mul_nonneg (mul_nonneg zero_le_two hC) (abs_nonneg δ)
      simpa only [abs_of_nonneg hM, mul_comm] using
        mul_le_mul (hdiff i) hwabs (abs_nonneg _) hmajorant
    _ = (C + (Fintype.card ι : ℝ) * M * (2 * C)) * |δ| := by
      simp [mul_assoc, mul_left_comm, mul_comm]
      ring

end

end PhosphorylationStableCapacity
