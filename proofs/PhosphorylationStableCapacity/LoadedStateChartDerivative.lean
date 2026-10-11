module
public import Mathlib.Analysis.Calculus.Deriv.Add
public import proofs.PhosphorylationStableCapacity.LoadedStateChartDefect

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- If a literal state path has zero first-order kinase-total error, its
fixed-class projection has the same free-kinase derivative. -/
theorem stateFromLoaded_projection_E_hasDerivAt {n : ℕ}
    (ET FT ST : ℝ) (x : ℝ → State n) (d : ℝ)
    (hE : HasDerivAt (fun t => (x t).E) d 0)
    (hTE : HasDerivAt (fun t => totalE (x t)) 0 0) :
    HasDerivAt (fun t =>
      (stateFromLoaded ET FT ST (loadedCoordOfState (x t))).E) d 0 := by
  have h := hE.add ((hasDerivAt_const (0 : ℝ) ET).sub hTE)
  simpa only [stateFromLoaded_loadedCoordOfState_E,
    Pi.add_def, Pi.sub_def,
    sub_zero, add_zero] using h

theorem stateFromLoaded_projection_F_hasDerivAt {n : ℕ}
    (ET FT ST : ℝ) (x : ℝ → State n) (d : ℝ)
    (hF : HasDerivAt (fun t => (x t).F) d 0)
    (hTF : HasDerivAt (fun t => totalF (x t)) 0 0) :
    HasDerivAt (fun t =>
      (stateFromLoaded ET FT ST (loadedCoordOfState (x t))).F) d 0 := by
  have h := hF.add ((hasDerivAt_const (0 : ℝ) FT).sub hTF)
  simpa only [stateFromLoaded_loadedCoordOfState_F,
    Pi.add_def, Pi.sub_def,
    sub_zero, add_zero] using h

theorem stateFromLoaded_projection_S_zero_hasDerivAt {n : ℕ}
    (ET FT ST : ℝ) (x : ℝ → State n) (d : ℝ)
    (hS : HasDerivAt (fun t => (x t).S 0) d 0)
    (hTS : HasDerivAt (fun t => totalS (x t)) 0 0) :
    HasDerivAt (fun t =>
      (stateFromLoaded ET FT ST (loadedCoordOfState (x t))).S 0) d 0 := by
  have h := hS.add ((hasDerivAt_const (0 : ℝ) ST).sub hTS)
  simpa only [stateFromLoaded_loadedCoordOfState_S_zero,
    Pi.add_def, Pi.sub_def,
    sub_zero, add_zero] using h

end
end PhosphorylationStableCapacity
