module
public import proofs.PhosphorylationStableCapacity.ClassForwardUniqueness

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness
open scoped NNReal

/-- On a compact forward time interval a forward class curve is
continuous, including at the time-zero endpoint. -/
theorem forward_class_curve_continuousOn_interval {n : ℕ}
    {f : CoordinateSpace n → CoordinateSpace n}
    {u : CoordinateSpace n} {γ : ℝ → CoordinateSpace n}
    (hγ : IsForwardClassCurve f u γ) (T : ℝ) :
    ContinuousOn γ (Set.Icc (0 : ℝ) T) := by
  intro t ht
  exact (hγ.2 t ht.1).continuousWithinAt.mono
    Set.Icc_subset_Ici_self

/-- Grönwall control of two literal class trajectories that remain
in the nonnegative compatibility class. In particular, the time map
depends continuously on its initial state. -/
theorem exists_forward_class_curve_exponential_bound {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) :
    ∃ K : ℝ≥0,
      ∀ (u v : CoordinateSpace n)
        (γ η : ℝ → CoordinateSpace n),
        IsForwardClassCurve (restrictedFieldEuclid ET FT ST k) u γ →
        IsForwardClassCurve (restrictedFieldEuclid ET FT ST k) v η →
        (∀ t : ℝ, 0 ≤ t → γ t ∈ classPolytope n ET FT ST) →
        (∀ t : ℝ, 0 ≤ t → η t ∈ classPolytope n ET FT ST) →
        ∀ T : ℝ, 0 ≤ T →
          dist (γ T) (η T) ≤
            dist u v * Real.exp ((K : ℝ) * T) := by
  obtain ⟨K, hLip⟩ :=
    restrictedFieldEuclid_lipschitzOn_classPolytope ET FT ST k
  refine ⟨K, ?_⟩
  intro u v γ η hγ hη hγmem hηmem T hT
  have hbound := dist_le_of_trajectories_ODE_of_mem
    (K := K)
    (v := fun _ => restrictedFieldEuclid ET FT ST k)
    (s := fun _ => classPolytope n ET FT ST)
    (a := (0 : ℝ)) (b := T)
    (f := γ) (g := η) (δ := dist u v)
    (fun _ _ => hLip)
    (forward_class_curve_continuousOn_interval hγ T)
    (by
      intro t ht
      exact (hγ.2 t ht.1).mono (Set.Ici_subset_Ici.mpr ht.1))
    (fun t ht => hγmem t ht.1)
    (forward_class_curve_continuousOn_interval hη T)
    (by
      intro t ht
      exact (hη.2 t ht.1).mono (Set.Ici_subset_Ici.mpr ht.1))
    (fun t ht => hηmem t ht.1)
    (by rw [hγ.1, hη.1]) T ⟨hT, le_refl T⟩
  simpa using hbound

end
end PhosphorylationStableCapacity
