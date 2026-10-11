module
public import proofs.PhosphorylationStableCapacity.ClassPhysicalTimeSemigroup

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter Set
open scoped Topology

noncomputable section

/-- Pointwise attraction plus Lyapunov stability is uniform on each
compact subset of the basin for a continuous forward semigroup. -/
theorem compact_attraction_uniformity
    {X : Type*} [MetricSpace X]
    (F : ℝ → X → X) (x : X) (K : Set X)
    (hK : IsCompact K)
    (hcont : ∀ T : ℝ, 0 ≤ T → Continuous (F T))
    (hsemigroup : ∀ S T : ℝ, 0 ≤ S → 0 ≤ T →
      ∀ u : X, F (S + T) u = F S (F T u))
    (hstable : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ z : X, dist z x < δ →
        ∀ t : ℝ, 0 ≤ t → dist (F t z) x < ε)
    (hattract : ∀ z ∈ K, Tendsto (fun t : ℝ => F t z) atTop (𝓝 x)) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 ≤ T ∧
      ∀ z ∈ K, ∀ t : ℝ, T ≤ t → dist (F t z) x < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hstableδ⟩ := hstable ε hε
  let U : Set.Ici (0 : ℝ) → Set X :=
    fun T => {z | dist (F T.1 z) x < δ}
  have hUopen : ∀ T, IsOpen (U T) := by
    intro T
    change IsOpen ((F T.1) ⁻¹' Metric.ball x δ)
    exact Metric.isOpen_ball.preimage (hcont T.1 T.2)
  have hcover : K ⊆ ⋃ T, U T := by
    intro z hz
    have hev := (hattract z hz).eventually
      (Metric.ball_mem_nhds x hδ)
    obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 hev
    let T : Set.Ici (0 : ℝ) :=
      ⟨max 0 B, show 0 ≤ max 0 B from le_max_left _ _⟩
    apply Set.mem_iUnion.mpr
    refine ⟨T, ?_⟩
    exact hB T.1 (le_max_right _ _)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hUopen hcover
  by_cases hempty : K = ∅
  · refine ⟨0, le_refl _, ?_⟩
    intro z hz
    simp [hempty] at hz
  obtain ⟨z₀, hz₀⟩ : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨i₀, hi₀, _⟩ := Set.mem_iUnion₂.mp (hs hz₀)
  have hsne : s.Nonempty := ⟨i₀, hi₀⟩
  let T : ℝ := s.sup' hsne (fun i => i.1)
  have hT : 0 ≤ T :=
    i₀.2.trans (Finset.le_sup' (fun i => i.1) hi₀)
  refine ⟨T, hT, ?_⟩
  intro z hz t ht
  obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (hs hz)
  have hiT : i.1 ≤ T := Finset.le_sup' (fun j => j.1) hi
  have hrest : 0 ≤ t - i.1 := by linarith
  have htime : t - i.1 + i.1 = t := by ring
  rw [← htime, hsemigroup (t - i.1) i.1 hrest i.2 z]
  exact hstableδ (F i.1 z) hzi (t - i.1) hrest

end
end PhosphorylationStableCapacity
