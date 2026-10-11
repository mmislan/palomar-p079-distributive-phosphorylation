module
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import proofs.PhosphorylationStableCapacity.LoadedProjectionFastField

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- If a literal path is tangent to the fixed phosphatase total and has
zero phosphatase-complex velocity, the projected loaded fast row has zero
derivative. -/
theorem loadedProjectionFastField_D_hasDerivAt_zero {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (x : ℝ → State n)
    (i : Fin n) (dS : ℝ)
    (hbase : totalF (x 0) = FT)
    (hTF : HasDerivAt (fun t => totalF (x t)) 0 0)
    (hS : HasDerivAt (fun t => (x t).S i.succ) dS 0)
    (hfast : ∀ t : ℝ, (field k (x t)).D i = 0) :
    HasDerivAt (fun t =>
      (loadedRestrictedField ET FT ST k
        (loadedCoordOfState (x t))).2.2 i) 0 0 := by
  have hδ : HasDerivAt (fun t : ℝ => FT - totalF (x t)) 0 0 := by
    simpa only [Pi.sub_def, sub_self] using
      (hasDerivAt_const (0 : ℝ) FT).sub hTF
  have hδ0 : FT - totalF (x 0) = 0 := by rw [hbase]; ring
  have hprod := (hS.mul hδ).const_mul (k.alpha i)
  have hproduct : HasDerivAt (fun t : ℝ =>
      k.alpha i * ((x t).S i.succ * (FT - totalF (x t)))) 0 0 := by
    simpa [hδ0, Pi.mul_def] using hprod
  have hfun : (fun t : ℝ =>
      (loadedRestrictedField ET FT ST k
        (loadedCoordOfState (x t))).2.2 i) =
      (fun t : ℝ =>
        k.alpha i * ((x t).S i.succ * (FT - totalF (x t)))) := by
    funext t
    rw [loadedProjectionFastField_D, hfast t]
    ring
  rw [hfun]
  exact hproduct

end
end PhosphorylationStableCapacity
