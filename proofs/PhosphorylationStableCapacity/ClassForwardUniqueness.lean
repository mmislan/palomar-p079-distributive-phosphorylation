module
public import proofs.PhosphorylationStableCapacity.PositiveForwardExistence
public import proofs.PhosphorylationStableCapacity.ClassFieldCompactBounds
public import Mathlib.Analysis.ODE.Gronwall

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- A forward class curve is continuous on every compact forward
time interval. -/
private theorem forwardCurve_continuousOn_Icc {n : ℕ}
    {f : CoordinateSpace n → CoordinateSpace n}
    {u : CoordinateSpace n} {γ : ℝ → CoordinateSpace n}
    (hγ : IsForwardClassCurve f u γ) (T : ℝ) :
    ContinuousOn γ (Set.Icc (0 : ℝ) T) := by
  intro t ht
  have ht0 : t ∈ Set.Ici (0 : ℝ) := ht.1
  exact (hγ.2 t ht0).continuousWithinAt.mono
    (Set.Icc_subset_Ici_self)

/-- All forward solutions that remain in the exact nonnegative class
agree on every forward time interval when they have the same initial
state. This uses the uniform Lipschitz bound on that class. -/
theorem forward_class_curves_unique_in_polytope {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n)
    (γ η : ℝ → CoordinateSpace n)
    (hγ : IsForwardClassCurve
      (restrictedFieldEuclid ET FT ST k) u γ)
    (hη : IsForwardClassCurve
      (restrictedFieldEuclid ET FT ST k) u η)
    (hγmem : ∀ t : ℝ, 0 ≤ t →
      γ t ∈ classPolytope n ET FT ST)
    (hηmem : ∀ t : ℝ, 0 ≤ t →
      η t ∈ classPolytope n ET FT ST) :
    ∀ t : ℝ, 0 ≤ t → γ t = η t := by
  obtain ⟨K, hLip⟩ :=
    restrictedFieldEuclid_lipschitzOn_classPolytope ET FT ST k
  intro T hT
  have huniq := ODE_solution_unique_of_mem_Icc_right
    (K := K)
    (v := fun _ => restrictedFieldEuclid ET FT ST k)
    (s := fun _ => classPolytope n ET FT ST)
    (a := (0 : ℝ)) (b := T)
    (f := γ) (g := η)
    (fun _ _ => hLip)
    (forwardCurve_continuousOn_Icc hγ T)
    (by
      intro t ht
      exact (hγ.2 t ht.1).mono (Set.Ici_subset_Ici.mpr ht.1))
    (fun t ht => hγmem t ht.1)
    (forwardCurve_continuousOn_Icc hη T)
    (by
      intro t ht
      exact (hη.2 t ht.1).mono (Set.Ici_subset_Ici.mpr ht.1))
    (fun t ht => hηmem t ht.1)
    (hγ.1.trans hη.1.symm)
  exact huniq ⟨hT, le_refl T⟩

/-- Any two forward curves of the exact class field with the same
initial state agree, whether or not class membership was assumed.
On each compact time interval their images fit inside one closed ball,
where the polynomial class field is uniformly Lipschitz. -/
theorem forward_class_curves_unique {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n)
    (γ η : ℝ → CoordinateSpace n)
    (hγ : IsForwardClassCurve
      (restrictedFieldEuclid ET FT ST k) u γ)
    (hη : IsForwardClassCurve
      (restrictedFieldEuclid ET FT ST k) u η) :
    ∀ t : ℝ, 0 ≤ t → γ t = η t := by
  intro T hT
  have hγcont := forwardCurve_continuousOn_Icc hγ T
  have hηcont := forwardCurve_continuousOn_Icc hη T
  obtain ⟨Cγ, hCγ⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hγcont
  obtain ⟨Cη, hCη⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hηcont
  let R : ℝ := max 0 (max Cγ Cη)
  have hR : 0 ≤ R := le_max_left _ _
  have hγball : ∀ t ∈ Set.Icc (0 : ℝ) T,
      γ t ∈ Metric.closedBall (0 : CoordinateSpace n) R := by
    intro t ht
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hCγ t ht).trans (le_trans (le_max_left _ _) (le_max_right _ _))
  have hηball : ∀ t ∈ Set.Icc (0 : ℝ) T,
      η t ∈ Metric.closedBall (0 : CoordinateSpace n) R := by
    intro t ht
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hCη t ht).trans (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨K, hLip⟩ :=
    (contDiff_restrictedFieldEuclid_fixed_rates ET FT ST k).contDiffOn
      |>.exists_lipschitzOnWith (by norm_num)
        (convex_closedBall _ _) (isCompact_closedBall _ _)
  have huniq := ODE_solution_unique_of_mem_Icc_right
    (K := K)
    (v := fun _ => restrictedFieldEuclid ET FT ST k)
    (s := fun _ => Metric.closedBall (0 : CoordinateSpace n) R)
    (a := (0 : ℝ)) (b := T)
    (f := γ) (g := η)
    (fun _ _ => hLip)
    hγcont
    (by
      intro t ht
      exact (hγ.2 t ht.1).mono (Set.Ici_subset_Ici.mpr ht.1))
    (fun t ht => hγball t ⟨ht.1, ht.2.le⟩)
    hηcont
    (by
      intro t ht
      exact (hη.2 t ht.1).mono (Set.Ici_subset_Ici.mpr ht.1))
    (fun t ht => hηball t ⟨ht.1, ht.2.le⟩)
    (hγ.1.trans hη.1.symm)
  exact huniq ⟨hT, le_refl T⟩

/-- Every forward solution starting in the nonnegative compatibility
class remains in that class. The global physical solution supplies
the comparison curve, and unconditional uniqueness identifies any
other forward solution with it. -/
theorem every_forward_class_curve_in_polytope {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (u : CoordinateSpace n) (hu : u ∈ classPolytope n ET FT ST)
    (γ : ℝ → CoordinateSpace n)
    (hγ : IsForwardClassCurve
      (restrictedFieldEuclid ET FT ST k) u γ) :
    ∀ t : ℝ, 0 ≤ t → γ t ∈ classPolytope n ET FT ST := by
  obtain ⟨β, hβ, hβmem⟩ :=
    exists_physical_forward_class_curve ET FT ST hET k hk u hu
  intro t ht
  rw [forward_class_curves_unique ET FT ST k u γ β hγ hβ t ht]
  exact hβmem t ht

end
end PhosphorylationStableCapacity
