module
public import proofs.PhosphorylationStableCapacity.SplitFirstOrderBound

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter
open scoped Topology

/-- Multiplying a shared scalar split factor by a compactly bounded
parameter family preserves a single first-order constant on one
signed split-parameter tube. -/
theorem uniform_fixed_factor_product_first_order
    {α : Type*} (K : Set α) (G : ℝ → ℝ) (H : α → ℝ → ℝ)
    (Cg Ch B : ℝ) (hCg : 0 ≤ Cg) (hCh : 0 ≤ Ch)
    (hB : 0 ≤ B)
    (hG : ∀ᶠ δ : ℝ in 𝓝 0,
      |G δ-G 0| ≤ Cg*|δ|)
    (hH : ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ a ∈ K, |H a δ-H a 0| ≤ Ch*|δ|)
    (hH0 : ∀ a ∈ K, |H a 0| ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ δ : ℝ in 𝓝 0,
        ∀ a ∈ K,
          |G δ*H a δ-G 0*H a 0| ≤ C*|δ| := by
  let C := Cg*(B+Ch)+|G 0| *Ch+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hsmall : ∀ᶠ δ : ℝ in 𝓝 0, |δ| ≤ 1 := by
    have hball : ∀ᶠ δ : ℝ in 𝓝 0,
        δ ∈ Metric.ball (0 : ℝ) 1 :=
      Metric.ball_mem_nhds 0 (by norm_num)
    filter_upwards [hball] with δ hd
    exact le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hd)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hG, hH, hsmall] with δ hGδ hHδ hsmallδ a ha
  have hHδbound : |H a δ| ≤ B+Ch := by
    calc
      |H a δ| = |(H a δ-H a 0)+H a 0| := by congr 1; ring
      _ ≤ |H a δ-H a 0|+|H a 0| := abs_add_le _ _
      _ ≤ Ch*|δ|+B := add_le_add (hHδ a ha) (hH0 a ha)
      _ ≤ B+Ch := by nlinarith [hsmallδ]
  have hraw :
      |G δ*H a δ-G 0*H a 0| ≤
        |G δ-G 0| *|H a δ|+|G 0| *|H a δ-H a 0| := by
    have heq : G δ*H a δ-G 0*H a 0 =
        (G δ-G 0)*H a δ+G 0*(H a δ-H a 0) := by ring
    rw [heq]
    simpa only [abs_mul] using
      abs_add_le ((G δ-G 0)*H a δ) (G 0*(H a δ-H a 0))
  calc
    _ ≤ |G δ-G 0| *|H a δ|+|G 0| *|H a δ-H a 0| := hraw
    _ ≤ (Cg*|δ|)*(B+Ch)+|G 0| *(Ch*|δ|) := by
      apply add_le_add
      · exact mul_le_mul hGδ hHδbound (abs_nonneg _)
          (mul_nonneg hCg (abs_nonneg δ))
      · exact mul_le_mul_of_nonneg_left (hHδ a ha) (abs_nonneg _)
    _ ≤ C*|δ| := by
      dsimp [C]
      nlinarith [abs_nonneg δ]

end

end PhosphorylationStableCapacity
