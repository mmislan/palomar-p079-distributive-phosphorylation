module
public import proofs.PhosphorylationStableCapacity.CompactAttractionUniformity

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter
open scoped Topology

noncomputable section

open PhosphorylationSharpness

/-- The physical flow of a literal local attractor converges uniformly
on every compact subset of its attraction neighborhood. -/
theorem local_attractor_uniform_on_compact {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n)
    (hx : IsLocallyAsymptoticallyStableClass ET FT ST k x)
    (hxmem : x ∈ classPolytope n ET FT ST) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ K : Set (classPolytope n ET FT ST), IsCompact K →
        (∀ z ∈ K, dist (z : CoordinateSpace n) x < δ) →
        ∀ ε : ℝ, 0 < ε →
          ∃ T : ℝ, 0 ≤ T ∧
            ∀ z ∈ K, ∀ t : ℝ, T ≤ t →
              dist (physicalForwardCurve ET FT ST hET k hk z t) x < ε := by
  obtain ⟨δ, hδ, hattract⟩ := hx.2.2.1
  refine ⟨δ, hδ, ?_⟩
  intro K hK hnear ε hε
  let F : ℝ → classPolytope n ET FT ST → classPolytope n ET FT ST :=
    fun t => if ht : 0 ≤ t then physicalTimeMap ET FT ST hET k hk t ht else id
  have hFcont : ∀ t : ℝ, 0 ≤ t → Continuous (F t) := by
    intro t ht
    simpa [F, ht] using physicalTimeMap_continuous ET FT ST hET k hk t ht
  have hFsemigroup : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      ∀ z, F (s + t) z = F s (F t z) := by
    intro s t hs ht z
    simpa [F, hs, ht, add_nonneg hs ht] using
      (physicalTimeMap_semigroup ET FT ST hET k hk s t hs ht z).symm
  have hFstable : ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ z : classPolytope n ET FT ST, dist z ⟨x, hxmem⟩ < ρ →
        ∀ t : ℝ, 0 ≤ t → dist (F t z) ⟨x, hxmem⟩ < ε := by
    intro e he
    obtain ⟨ρ, hρ, hstab⟩ := hx.2.1 e he
    refine ⟨ρ, hρ, ?_⟩
    intro z hz t ht
    have hz' : dist (z : CoordinateSpace n) x < ρ := by
      simpa only [Subtype.dist_eq] using hz
    have hcurve := (physicalForwardCurve_spec ET FT ST hET k hk z).1
    have hbound := hstab z.1 hz'
      (physicalForwardCurve ET FT ST hET k hk z) hcurve t ht
    simpa [F, ht, physicalTimeMap, Subtype.dist_eq] using hbound
  have hFattract : ∀ z ∈ K,
      Tendsto (fun t : ℝ => F t z) atTop (𝓝 (⟨x, hxmem⟩ :
        classPolytope n ET FT ST)) := by
    intro z hz
    have hz' := hattract z.1 (hnear z hz)
      (physicalForwardCurve ET FT ST hET k hk z)
      (physicalForwardCurve_spec ET FT ST hET k hk z).1
    apply tendsto_subtype_rng.mpr
    have hev : (fun t : ℝ => (F t z : CoordinateSpace n)) =ᶠ[atTop]
        fun t => physicalForwardCurve ET FT ST hET k hk z t := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      simp [F, ht, physicalTimeMap]
    exact hz'.congr' hev.symm
  obtain ⟨T, hT, hbound⟩ :=
    compact_attraction_uniformity F ⟨x, hxmem⟩ K hK
      hFcont hFsemigroup hFstable hFattract ε hε
  refine ⟨T, hT, ?_⟩
  intro z hz t ht
  have ht0 : 0 ≤ t := hT.trans ht
  simpa [F, ht0, physicalTimeMap, Subtype.dist_eq] using hbound z hz t ht

/-- A whole closed class ball around a possibly nonhyperbolic local
attractor enters every prescribed neighborhood by one common time. -/
theorem local_attractor_uniform_on_closedBall {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n)
    (hx : IsLocallyAsymptoticallyStableClass ET FT ST k x)
    (hxmem : x ∈ classPolytope n ET FT ST) :
    ∃ r : ℝ, 0 < r ∧
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 ≤ T ∧
        ∀ z ∈ Metric.closedBall (⟨x, hxmem⟩ :
            classPolytope n ET FT ST) r,
          ∀ t : ℝ, T ≤ t →
            dist (physicalForwardCurve ET FT ST hET k hk z t) x < ε := by
  obtain ⟨δ, hδ, huniform⟩ :=
    local_attractor_uniform_on_compact ET FT ST hET k hk x hx hxmem
  let r := δ / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hsub : ∀ z ∈ Metric.closedBall
      (⟨x, hxmem⟩ : classPolytope n ET FT ST) r,
      dist (z : CoordinateSpace n) x < δ := by
    intro z hz
    have hzle : dist (z : CoordinateSpace n) x ≤ r := by
      simpa only [Metric.mem_closedBall, Subtype.dist_eq] using hz
    dsimp [r] at hzle
    linarith
  have hCompact : CompactSpace (classPolytope n ET FT ST) :=
    isCompact_iff_compactSpace.mp (classPolytope_isCompact n ET FT ST)
  have hK : IsCompact (Metric.closedBall
      (⟨x, hxmem⟩ : classPolytope n ET FT ST) r) :=
    @IsClosed.isCompact (classPolytope n ET FT ST) _ _ hCompact
      Metric.isClosed_closedBall
  exact ⟨r, hr, huniform _ hK hsub⟩

/-- At one common physical time, the whole closed ball of a local
attractor flows strictly inside itself. No hyperbolicity is used. -/
theorem local_attractor_inward_time_map {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n)
    (hx : IsLocallyAsymptoticallyStableClass ET FT ST k x)
    (hxmem : x ∈ classPolytope n ET FT ST) :
    ∃ r : ℝ, 0 < r ∧ ∃ T : ℝ, 0 ≤ T ∧
      ∀ z ∈ Metric.closedBall (⟨x, hxmem⟩ :
          classPolytope n ET FT ST) r,
        dist (physicalForwardCurve ET FT ST hET k hk z T) x < r := by
  obtain ⟨r, hr, huniform⟩ :=
    local_attractor_uniform_on_closedBall ET FT ST hET k hk x hx hxmem
  obtain ⟨T, hT, hbound⟩ := huniform r hr
  exact ⟨r, hr, T, hT, fun z hz => hbound z hz T (le_refl T)⟩

end
end PhosphorylationStableCapacity
