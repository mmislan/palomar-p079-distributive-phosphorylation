module
public import proofs.PhosphorylationStableCapacity.LinearizationRemainder
public import proofs.PhosphorylationStableCapacity.LocalAsymptoticStability
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- The quadratic energy associated with a continuous bilinear form
has its expected derivative along every literal class forward curve. -/
theorem bilinear_energy_hasDerivWithinAt_forward {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n)
    (x u : CoordinateSpace n)
    (B : CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ)
    (γ : ℝ → CoordinateSpace n)
    (hγ : IsForwardClassCurve
      (restrictedFieldEuclid ET FT ST k) u γ)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt
      (fun r => B (γ r - x) (γ r - x))
      (B (γ t - x) (restrictedFieldEuclid ET FT ST k (γ t)) +
        B (restrictedFieldEuclid ET FT ST k (γ t)) (γ t - x))
      (Set.Ici (0 : ℝ)) t := by
  have hdisp := (hγ.2 t ht).sub_const x
  exact B.hasDerivWithinAt_of_bilinear hdisp hdisp

end
end PhosphorylationStableCapacity
