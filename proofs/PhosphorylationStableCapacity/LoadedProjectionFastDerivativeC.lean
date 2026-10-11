module
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import proofs.PhosphorylationStableCapacity.LoadedProjectionFastField

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- A fixed-class projection of a path tangent to the kinase total has
zero first-order kinase-complex velocity whenever the original path has
zero fast velocity and the projected substrate derivative agrees with the
original substrate derivative. -/
theorem loadedProjectionFastField_C_hasDerivAt_zero {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (x : ℝ → State n)
    (i : Fin n) (dS dE : ℝ)
    (hbase : InClass ET FT ST (x 0))
    (hTE : HasDerivAt (fun t => totalE (x t)) 0 0)
    (hS : HasDerivAt (fun t => (x t).S i.castSucc) dS 0)
    (hprojS : HasDerivAt (fun t =>
      (stateFromLoaded ET FT ST (loadedCoordOfState (x t))).S
        i.castSucc) dS 0)
    (hE : HasDerivAt (fun t => (x t).E) dE 0)
    (hfast : ∀ t : ℝ, (field k (x t)).C i = 0) :
    HasDerivAt (fun t =>
      (loadedRestrictedField ET FT ST k
        (loadedCoordOfState (x t))).2.1 i) 0 0 := by
  have hδE : HasDerivAt
      (fun t : ℝ => ET - totalE (x t)) 0 0 := by
    simpa only [Pi.sub_def, sub_self] using
      (hasDerivAt_const (0 : ℝ) ET).sub hTE
  have hδE0 : ET - totalE (x 0) = 0 := by
    rw [hbase.1]
    ring
  have hδS : HasDerivAt (fun t : ℝ =>
      (stateFromLoaded ET FT ST (loadedCoordOfState (x t))).S
        i.castSucc - (x t).S i.castSucc) 0 0 := by
    simpa only [Pi.sub_def, sub_self] using hprojS.sub hS
  have hδS0 :
      (stateFromLoaded ET FT ST (loadedCoordOfState (x 0))).S
        i.castSucc - (x 0).S i.castSucc = 0 := by
    rw [stateFromLoaded_loadedCoordOfState ET FT ST (x 0) hbase]
    ring
  have h1 : HasDerivAt (fun t : ℝ =>
      (stateFromLoaded ET FT ST (loadedCoordOfState (x t))).S
        i.castSucc * (ET - totalE (x t))) 0 0 := by
    simpa [hδE0, Pi.mul_def] using
      hprojS.mul hδE
  have h2 : HasDerivAt (fun t : ℝ =>
      ((stateFromLoaded ET FT ST (loadedCoordOfState (x t))).S
        i.castSucc - (x t).S i.castSucc) * (x t).E) 0 0 := by
    simpa [hδS0, Pi.mul_def] using
      hδS.mul hE
  have hproduct := (h1.add h2).const_mul (k.a i)
  have hfun : (fun t : ℝ =>
      (loadedRestrictedField ET FT ST k
        (loadedCoordOfState (x t))).2.1 i) =
      (fun t : ℝ => k.a i * (
        (stateFromLoaded ET FT ST (loadedCoordOfState (x t))).S
          i.castSucc * (ET - totalE (x t)) +
        ((stateFromLoaded ET FT ST (loadedCoordOfState (x t))).S
          i.castSucc - (x t).S i.castSucc) * (x t).E)) := by
    funext t
    rw [loadedProjectionFastField_C, hfast t]
    ring
  rw [hfun]
  simpa using hproduct

end
end PhosphorylationStableCapacity
