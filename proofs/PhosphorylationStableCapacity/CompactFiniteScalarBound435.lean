module
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open scoped BigOperators

/-- A continuous finite family of real scalar observables is bounded
uniformly on a compact parameter set, including the empty set. -/
theorem compact_finite_scalar_abs_upper
    {α β : Type*} [TopologicalSpace α] [Fintype β]
    (K : Set α) (hK : IsCompact K)
    (f : β → α → ℝ)
    (hf : ∀ b, ContinuousOn (f b) K) :
    ∃ M : ℝ, 0 < M ∧
      ∀ a ∈ K, ∀ b : β, |f b a| ≤ M := by
  classical
  by_cases hnon : K.Nonempty
  · have hper (b : β) : ∃ M : ℝ, 0 < M ∧
        ∀ a ∈ K, |f b a| ≤ M := by
      obtain ⟨a₀, ha₀, hmax⟩ :=
        hK.exists_isMaxOn hnon
          (continuous_abs.comp_continuousOn (hf b))
      let M := max 1 |f b a₀|
      refine ⟨M, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
      intro a ha
      exact (hmax ha).trans (le_max_right _ _)
    choose M hM hbound using hper
    let Mall := (∑ b : β, M b)+1
    have hMall : 0 < Mall := by
      dsimp [Mall]
      have hsum : 0 ≤ ∑ b : β, M b :=
        Finset.sum_nonneg (fun b _ => (hM b).le)
      linarith
    refine ⟨Mall, hMall, ?_⟩
    intro a ha b
    have hle : M b ≤ ∑ i : β, M i :=
      Finset.single_le_sum
        (fun i _ => (hM i).le) (Finset.mem_univ b)
    exact (hbound b a ha).trans (by dsimp [Mall]; linarith)
  · refine ⟨1, by norm_num, ?_⟩
    intro a ha
    exact (hnon ⟨a, ha⟩).elim

end

end PhosphorylationStableCapacity
