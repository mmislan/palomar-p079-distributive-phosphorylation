module
public import proofs.PhosphorylationStableCapacity.CompactLocalPersistence435

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter
open scoped Topology

/-- Local spectral margins on a compact zero slice can be replaced by
one positive margin and one common perturbation interval. The predicate
is monotone toward smaller margins, as is `z.re ≤ -margin`. -/
theorem compact_uniform_margin_of_local
    {α : Type*} [TopologicalSpace α]
    (K : Set α) (hK : IsCompact K)
    (P : ℝ → α × ℝ → Prop)
    (hmono : ∀ {c d : ℝ}, 0 < d → d ≤ c →
      ∀ p, P c p → P d p)
    (hloc : ∀ a ∈ K, ∃ c : ℝ, 0 < c ∧
      {p : α × ℝ | P c p} ∈ 𝓝 (a, 0)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ δ : ℝ in 𝓝 0, ∀ a ∈ K, P c (a, δ) := by
  classical
  by_cases hnon : K.Nonempty
  · let c : K → ℝ := fun a => Classical.choose (hloc a.val a.property)
    have hc (a : K) : 0 < c a ∧
        {p : α × ℝ | P (c a) p} ∈ 𝓝 (a.val, 0) :=
      Classical.choose_spec (hloc a.val a.property)
    let U : K → Set α := fun a =>
      {b | (b, (0 : ℝ)) ∈ interior {p : α × ℝ | P (c a) p}}
    have hUopen : ∀ a, IsOpen (U a) := by
      intro a
      exact isOpen_interior.preimage
        (continuous_id.prodMk continuous_const)
    have hcover : K ⊆ ⋃ a, U a := by
      intro b hb
      apply Set.mem_iUnion.mpr
      refine ⟨⟨b, hb⟩, ?_⟩
      exact mem_interior_iff_mem_nhds.mpr (hc ⟨b, hb⟩).2
    obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hUopen hcover
    have hsnon : (s : Set K).Nonempty := by
      obtain ⟨b, hb⟩ := hnon
      obtain ⟨a, ha, _⟩ := Set.mem_iUnion₂.mp (hs hb)
      exact ⟨a, ha⟩
    obtain ⟨a₀, ha₀, hmin⟩ :=
      Set.exists_min_image (s : Set K) c s.finite_toSet hsnon
    have hc₀ : 0 < c a₀ := (hc a₀).1
    refine ⟨c a₀, hc₀, ?_⟩
    apply compact_eventually_of_local_neighborhoods K hK 0
      {p : α × ℝ | P (c a₀) p}
    intro b hb
    obtain ⟨a, ha, hU⟩ := Set.mem_iUnion₂.mp (hs hb)
    have hmem : {p : α × ℝ | P (c a) p} ∈ 𝓝 (b, 0) :=
      mem_interior_iff_mem_nhds.mp hU
    apply Filter.mem_of_superset hmem
    intro p hp
    exact hmono hc₀ (hmin a ha) p hp
  · refine ⟨1, by norm_num, ?_⟩
    filter_upwards [] with δ a ha
    exact (hnon ⟨a, ha⟩).elim

end PhosphorylationStableCapacity
