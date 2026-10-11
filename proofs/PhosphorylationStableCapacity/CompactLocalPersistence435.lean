module
public import proofs.PhosphorylationStableCapacity.CompactParameterUniformity

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter
open scoped Topology

/-- Pointwise neighborhood persistence along a compact zero slice has
one common parameter neighborhood. Only continuity at the slice is
needed; the predicate need not be globally open. -/
theorem compact_eventually_of_local_neighborhoods
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (K : Set α) (hK : IsCompact K) (b : β)
    (S : Set (α × β))
    (hlocal : ∀ a ∈ K, S ∈ 𝓝 (a, b)) :
    ∀ᶠ y : β in 𝓝 b, ∀ a ∈ K, (a, y) ∈ S := by
  have hprod : K ×ˢ ({b} : Set β) ⊆ interior S := by
    rintro ⟨a, y⟩ ⟨ha, hy⟩
    have hyb : y = b := Set.mem_singleton_iff.mp hy
    subst y
    exact mem_interior_iff_mem_nhds.mpr (hlocal a ha)
  obtain ⟨U, V, _, hVopen, hKU, hbV, hUV⟩ :=
    generalized_tube_lemma hK isCompact_singleton isOpen_interior hprod
  filter_upwards [hVopen.mem_nhds (hbV (by simp))] with y hy a ha
  exact interior_subset (hUV ⟨hKU ha, hy⟩)

end PhosphorylationStableCapacity
