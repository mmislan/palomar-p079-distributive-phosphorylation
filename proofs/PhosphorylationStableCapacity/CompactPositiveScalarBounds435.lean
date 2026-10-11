module
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- A positive continuous scalar over a compact parameter set has one
positive lower bound, including the empty-set case. -/
theorem compact_continuous_positive_lower
    {α : Type*} [TopologicalSpace α]
    (K : Set α) (hK : IsCompact K)
    (f : α → ℝ) (hf : ContinuousOn f K)
    (hpos : ∀ a ∈ K, 0 < f a) :
    ∃ c : ℝ, 0 < c ∧ ∀ a ∈ K, c ≤ f a := by
  by_cases hnon : K.Nonempty
  · obtain ⟨a₀, ha₀, hmin⟩ := hK.exists_isMinOn hnon hf
    exact ⟨f a₀, hpos a₀ ha₀, fun a ha => hmin ha⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro a ha
    exact (hnon ⟨a, ha⟩).elim

end

end PhosphorylationStableCapacity
