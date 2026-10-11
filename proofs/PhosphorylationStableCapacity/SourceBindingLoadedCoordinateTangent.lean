module
public import proofs.PhosphorylationStableCapacity.SourceBindingFastTangent
public import proofs.PhosphorylationStableCapacity.LoadedStateChartBridge

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The actual tangent of the fixed-enzyme-total binding path in loaded
class coordinates: loaded inventory followed by the two complex lists. -/
def sourceBindingLoadedCoordinateTangent {n : ℕ}
    (k : Rates n) (x : State n) (σ : Fin (n+1) → ℝ) :
    CoordinateSpace n :=
  ((fun i =>
      (loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
        (totalE x) (totalF x)).mulVec σ i.succ),
    (fun i =>
      bindingComplex (totalE x) (sourceBindingP k) x.S i.castSucc *
        (σ i.castSucc -
          (∑ j, bindingComplex (totalE x) (sourceBindingP k) x.S j *
            σ j) / totalE x)),
    (fun i =>
      bindingComplex (totalF x) (sourceBindingQ k) x.S i.succ *
        (σ i.succ -
          (∑ j, bindingComplex (totalF x) (sourceBindingQ k) x.S j *
            σ j) / totalF x)))

theorem equilibrium_sourceBindingLoadedCoordinate_hasDerivAt {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) (σ : Fin (n+1) → ℝ) :
    HasDerivAt (fun t : ℝ =>
      loadedCoordOfState (bindingState (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k)
        (bindingLinearPath x.S σ t)))
      (sourceBindingLoadedCoordinateTangent k x σ) 0 := by
  obtain ⟨hdenP, hdenQ⟩ :=
    equilibrium_sourceBindingDenominators_ne_zero k x hk hx heq
  have hET : 0 < totalE x := by
    simp [totalE]
    exact add_pos_of_pos_of_nonneg hx.2.1
      (Finset.sum_nonneg fun i _ => (hx.2.2.2.1 i).le)
  have hFT : 0 < totalF x := by
    simp [totalF]
    exact add_pos_of_pos_of_nonneg hx.2.2.1
      (Finset.sum_nonneg fun i _ => (hx.2.2.2.2 i).le)
  have hs : HasDerivAt (fun t : ℝ =>
      (loadedCoordOfState (bindingState (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k)
        (bindingLinearPath x.S σ t))).1)
      (sourceBindingLoadedCoordinateTangent k x σ).1 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simp only [loadedCoordOfState_slow,
      sourceBindingLoadedCoordinateTangent]
    change HasDerivAt (fun t : ℝ =>
      loadedLevel (bindingState (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k)
        (bindingLinearPath x.S σ t)) i.succ)
      ((loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
        (totalE x) (totalF x)).mulVec σ i.succ) 0
    have hfun : (fun t : ℝ =>
        loadedLevel (bindingState (totalE x) (totalF x)
          (sourceBindingP k) (sourceBindingQ k)
          (bindingLinearPath x.S σ t)) i.succ) =
      (fun t : ℝ =>
        bindingLoadedLevel (totalE x) (totalF x)
          (sourceBindingP k) (sourceBindingQ k)
          (bindingLinearPath x.S σ t) i.succ) := by
      funext t
      apply loadedLevel_bindingState_eq_bindingLoadedLevel
      · simp [bindingComplex, sourceBindingP]
      · simp [bindingComplex, sourceBindingQ]
    rw [hfun]
    exact equilibrium_source_loadedBindingMass_hasDerivAt_kinetic
      k x hk hx heq σ i.succ
  have hc : HasDerivAt (fun t : ℝ =>
      (loadedCoordOfState (bindingState (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k)
        (bindingLinearPath x.S σ t))).2.1)
      (sourceBindingLoadedCoordinateTangent k x σ).2.1 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    have h := bindingComplex_hasDerivAt_linearPath
      (totalE x) (sourceBindingP k) x.S σ i.castSucc
      (ne_of_gt hET) hdenP
    simpa only [loadedCoordOfState_C, bindingState,
      sourceBindingLoadedCoordinateTangent] using h
  have hd : HasDerivAt (fun t : ℝ =>
      (loadedCoordOfState (bindingState (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k)
        (bindingLinearPath x.S σ t))).2.2)
      (sourceBindingLoadedCoordinateTangent k x σ).2.2 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    have h := bindingComplex_hasDerivAt_linearPath
      (totalF x) (sourceBindingQ k) x.S σ i.succ
      (ne_of_gt hFT) hdenQ
    simpa only [loadedCoordOfState_D, bindingState,
      sourceBindingLoadedCoordinateTangent] using h
  exact hs.prodMk (hc.prodMk hd)

end
end PhosphorylationStableCapacity
