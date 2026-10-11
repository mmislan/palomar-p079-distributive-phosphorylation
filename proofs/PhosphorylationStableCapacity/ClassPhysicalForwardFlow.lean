module
public import proofs.PhosphorylationStableCapacity.FullPhysicalForwardFlow
public import proofs.PhosphorylationStableCapacity.LocalAsymptoticStability

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- Projection and reconstruction are inverse on a fixed literal class. -/
theorem classEmbedding_projection_of_inClass {n : ℕ}
    (ET FT ST : ℝ) (x : FullSpace n)
    (hx : InClass ET FT ST (ofFullSpace x)) :
    classEmbedding ET FT ST (classProjection x) = x := by
  simp only [classEmbedding, classProjection, of_toCoordinateSpace]
  rw [unChart_chart_of_inClass ET FT ST (ofFullSpace x) hx]
  exact to_ofFullSpace x

/-- The free-coordinate projection carries a full derivative to its
corresponding class-coordinate derivative. -/
theorem hasDerivAt_classProjection_comp {n : ℕ}
    (γ : ℝ → FullSpace n) (v : FullSpace n) (t : ℝ)
    (hγ : HasDerivAt γ v t) :
    HasDerivAt (fun s => classProjection (γ s)) (classProjection v) t := by
  have hS : ∀ i : Fin (n + 1),
      HasDerivAt (fun s => (γ s).1 i) (v.1 i) t := by
    intro i
    simpa using (hasDerivAt_pi.mp (hγ.hasFDerivAt.fst.hasDerivAt)) i
  have hC : ∀ i : Fin n,
      HasDerivAt (fun s => (γ s).2.2.1 i) (v.2.2.1 i) t := by
    intro i
    simpa using (hasDerivAt_pi.mp (hγ.hasFDerivAt.snd.snd.fst.hasDerivAt)) i
  have hD : ∀ i : Fin n,
      HasDerivAt (fun s => (γ s).2.2.2 i) (v.2.2.2 i) t := by
    intro i
    simpa using (hasDerivAt_pi.mp (hγ.hasFDerivAt.snd.snd.snd.hasDerivAt)) i
  change HasDerivAt
    (fun s => ((fun i : Fin n => (γ s).1 i.succ),
      (γ s).2.2.1, (γ s).2.2.2))
    ((fun i : Fin n => v.1 i.succ), v.2.2.1, v.2.2.2) t
  apply HasDerivAt.prodMk
  · exact hasDerivAt_pi.mpr (fun i => hS i.succ)
  · apply HasDerivAt.prodMk
    · exact hasDerivAt_pi.mpr hC
    · exact hasDerivAt_pi.mpr hD

/-- Every nonnegative point of the exact class polytope admits a global
forward curve for the literal restricted mass-action ODE. The curve
remains in the same nonnegative class at every forward time. -/
theorem exists_physical_forward_class_curve {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (u : CoordinateSpace n) (hu : u ∈ classPolytope n ET FT ST) :
    ∃ β : ℝ → CoordinateSpace n,
      IsForwardClassCurve (restrictedFieldEuclid ET FT ST k) u β ∧
      ∀ t : ℝ, 0 ≤ t → β t ∈ classPolytope n ET FT ST := by
  let x₀ := unChart ET FT ST (ofCoordinateSpace u)
  have hx₀ : NonnegativeState x₀ :=
    (mem_classPolytope_iff_nonnegative ET FT ST u).mp hu
  have hclass₀ : InClass ET FT ST x₀ :=
    unChart_inClass ET FT ST (ofCoordinateSpace u)
  obtain ⟨γ, hγ0, hγ⟩ :=
    exists_full_physical_forward_curve ET FT ST hET k hk x₀ hx₀ hclass₀
  let β : ℝ → CoordinateSpace n := fun t => classProjection (γ t)
  refine ⟨β, ?_, ?_⟩
  · constructor
    · simp [β, hγ0, x₀, classProjection, of_toFullSpace,
        chart_unChart, to_ofCoordinateSpace]
    · intro t ht
      obtain ⟨hderiv, _, hclass⟩ := hγ t ht
      have hembed : classEmbedding ET FT ST (β t) = γ t :=
        classEmbedding_projection_of_inClass ET FT ST (γ t) hclass
      have hproject := hasDerivAt_classProjection_comp γ
        (fullFieldEuclid k (γ t)) t hderiv
      have hfield : classProjection (fullFieldEuclid k (γ t)) =
          restrictedFieldEuclid ET FT ST k (β t) := by
        rw [← hembed]
        exact (restricted_eq_project_full_embed ET FT ST k (β t)).symm
      rw [hfield] at hproject
      exact hproject.hasDerivWithinAt
  · intro t ht
    obtain ⟨_, hnonneg, hclass⟩ := hγ t ht
    apply (mem_classPolytope_iff_nonnegative ET FT ST (β t)).mpr
    change NonnegativeState
      (unChart ET FT ST (ofCoordinateSpace (classProjection (γ t))))
    simpa [classProjection, of_toCoordinateSpace] using
      (show NonnegativeState
        (unChart ET FT ST (chart (ofFullSpace (γ t)))) from
        (unChart_chart_of_inClass ET FT ST (ofFullSpace (γ t)) hclass).symm ▸ hnonneg)

end
end PhosphorylationStableCapacity
