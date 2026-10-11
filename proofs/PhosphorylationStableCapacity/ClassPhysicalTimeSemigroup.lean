module
public import proofs.PhosphorylationStableCapacity.ClassPhysicalTimeMap
public import Mathlib.Analysis.Calculus.Deriv.Shift

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness
open scoped Topology

/-- A nonnegative time shift of a forward class curve is again a
forward class curve. -/
theorem forward_class_curve_shift {n : ℕ}
    {f : CoordinateSpace n → CoordinateSpace n}
    {u : CoordinateSpace n} {γ : ℝ → CoordinateSpace n}
    (hγ : IsForwardClassCurve f u γ)
    (T : ℝ) (hT : 0 ≤ T) :
    IsForwardClassCurve f (γ T) (fun t => γ (t + T)) := by
  constructor
  · simp
  · intro t ht
    by_cases hzero : T = 0
    · subst T
      simpa using hγ.2 t ht
    · have hpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hzero)
      have ht0 : 0 ≤ t := ht
      have htime : 0 < t + T := by linarith
      have hmem : Set.Ici (0 : ℝ) ∈ 𝓝 (t + T) := by
        filter_upwards [Ioi_mem_nhds htime] with s hs
        exact (show 0 < s from hs).le
      have hd : HasDerivAt γ (f (γ (t + T))) (t + T) :=
        (hγ.2 (t + T) htime.le).hasDerivAt hmem
      exact (hd.comp_add_const t T).hasDerivWithinAt

/-- The chosen physical flow satisfies the semigroup law on the
nonnegative compatibility class. -/
theorem physicalTimeMap_semigroup {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (S T : ℝ) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (u : classPolytope n ET FT ST) :
    physicalTimeMap ET FT ST hET k hk S hS
      (physicalTimeMap ET FT ST hET k hk T hT u) =
    physicalTimeMap ET FT ST hET k hk (S + T) (add_nonneg hS hT) u := by
  apply Subtype.ext
  let γ := physicalForwardCurve ET FT ST hET k hk u
  let v := physicalTimeMap ET FT ST hET k hk T hT u
  let η := physicalForwardCurve ET FT ST hET k hk v
  have hγ := (physicalForwardCurve_spec ET FT ST hET k hk u).1
  have hη := (physicalForwardCurve_spec ET FT ST hET k hk v).1
  have hshift : IsForwardClassCurve
      (restrictedFieldEuclid ET FT ST k) (γ T)
      (fun t => γ (t + T)) := forward_class_curve_shift hγ T hT
  have hv : (v : CoordinateSpace n) = γ T := rfl
  rw [← hv] at hshift
  have heq := forward_class_curves_unique ET FT ST k
    v.1 (fun t => γ (t + T)) η hshift hη S hS
  simpa [physicalTimeMap, γ, η, v] using heq.symm

end
end PhosphorylationStableCapacity
