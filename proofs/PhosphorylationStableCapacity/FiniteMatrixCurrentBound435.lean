module
public import proofs.PhosphorylationStableCapacity.FiniteMatrixFirstOrder435
public import Mathlib.Topology.Algebra.Order.Group

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter Matrix
open scoped Topology

/-- Continuous finite matrix entries have one absolute upper bound on
every compact parameter set. -/
theorem compact_matrix_entry_abs_upper
    {α ι : Type*} [TopologicalSpace α]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (K : Set α) (hK : IsCompact K)
    (W : α → Matrix ι ι ℝ) (hW : ContinuousOn W K) :
    ∃ M : ℝ, 0 < M ∧ ∀ a ∈ K, ∀ i j, |W a i j| ≤ M := by
  by_cases hnon : K.Nonempty
  · have hper (i j : ι) : ∃ M : ℝ, 0 < M ∧
        ∀ a ∈ K, |W a i j| ≤ M := by
      have hcont : ContinuousOn (fun a => |W a i j|) K := by
        intro a ha
        have heval : ContinuousAt
            (fun A : Matrix ι ι ℝ => |A i j|) (W a) := by
          exact ((continuous_apply j).comp
            (continuous_apply i : Continuous (fun A : Matrix ι ι ℝ => A i))).continuousAt.abs
        exact heval.comp_continuousWithinAt (hW a ha)
      obtain ⟨a₀, ha₀, hmax⟩ := hK.exists_isMaxOn hnon hcont
      let M := max 1 |W a₀ i j|
      refine ⟨M, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
      intro a ha
      exact (hmax ha).trans (le_max_right _ _)
    choose M hM hbound using hper
    let Mall := ∑ i : ι, ∑ j : ι, M i j
    have hinner (i : ι) : 0 < ∑ j : ι, M i j :=
      Finset.sum_pos (fun j _ => hM i j) Finset.univ_nonempty
    have hMall : 0 < Mall :=
      Finset.sum_pos (fun i _ => hinner i) Finset.univ_nonempty
    have hMbound (i j : ι) : M i j ≤ Mall := by
      have h₁ : M i j ≤ ∑ q : ι, M i q :=
        Finset.single_le_sum (fun q hq => (hM i q).le)
          (Finset.mem_univ j)
      have h₂ : (∑ q : ι, M i q) ≤ Mall :=
        Finset.single_le_sum (fun q hq => (hinner q).le)
          (Finset.mem_univ i)
      exact h₁.trans h₂
    exact ⟨Mall, hMall,
      fun a ha i j => (hbound i j a ha).trans (hMbound i j)⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro a ha
    exact (hnon ⟨a, ha⟩).elim

/-- A bounded compact current matrix multiplies a fixed finite matrix
family with one first-order constant, uniformly over the current set.
The current factor is independent of the split parameter. -/
theorem finite_matrix_left_factor_first_order_bound
    {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Set α) (W : α → Matrix ι ι ℝ)
    (B : ℝ → Matrix ι ι ℝ)
    (M C : ℝ) (hM : 0 ≤ M) (_hC : 0 ≤ C)
    (hW : ∀ a ∈ K, ∀ i j, |W a i j| ≤ M)
    (hB : ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ i j, |B δ i j - B 0 i j| ≤ C*|δ|) :
    ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ a ∈ K, ∀ i j,
        |(W a * B δ) i j - (W a * B 0) i j| ≤
          (Fintype.card ι : ℝ)*M*C*|δ| := by
  filter_upwards [hB] with δ hBδ a ha i j
  have hsum :
      (W a * B δ) i j - (W a * B 0) i j =
        ∑ k : ι, W a i k * (B δ k j - B 0 k j) := by
    simp [Matrix.mul_apply, Finset.sum_sub_distrib, mul_sub]
  rw [hsum]
  calc
    |∑ k : ι, W a i k * (B δ k j - B 0 k j)| ≤
        ∑ k : ι, |W a i k * (B δ k j - B 0 k j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : ι, M*(C*|δ|) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      exact mul_le_mul (hW a ha i k) (hBδ k j)
        (abs_nonneg _) hM
    _ = (Fintype.card ι : ℝ)*M*C*|δ| := by
      simp [mul_assoc, mul_comm, mul_left_comm]

end

end PhosphorylationStableCapacity
