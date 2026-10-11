module
public import proofs.PhosphorylationStableCapacity.SourceBindingLoadedCoordinateTangent
public import proofs.PhosphorylationStableCapacity.LoadedProjectionFastDerivativeC
public import proofs.PhosphorylationStableCapacity.LoadedProjectionFastDerivativeD
public import proofs.PhosphorylationStableCapacity.LoadedStateChartDerivative
public import proofs.PhosphorylationStableCapacity.BindingStatePathDerivatives

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- At every positive literal equilibrium, the fixed-class loaded
kinase-complex field has zero derivative along a compensated binding path. -/
theorem equilibrium_sourceProjectedFastC_hasDerivAt_zero {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) (j i : Fin n) :
    let A := (totalAndLevelOutputMatrix n) *
      loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
        (totalE x) (totalF x)
    let σ := firstPivotFixedTangent A j
    HasDerivAt (fun t : ℝ =>
      (loadedRestrictedField (totalE x) (totalF x) (totalS x) k
        (loadedCoordOfState (bindingState (totalE x) (totalF x)
          (sourceBindingP k) (sourceBindingQ k)
          (bindingLinearPath x.S σ t)))).2.1 i) 0 0 := by
  dsimp only
  let A := (totalAndLevelOutputMatrix n) *
    loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
      (totalE x) (totalF x)
  let σ := firstPivotFixedTangent A j
  let X : ℝ → State n := fun t =>
    bindingState (totalE x) (totalF x)
      (sourceBindingP k) (sourceBindingQ k)
      (bindingLinearPath x.S σ t)
  have hpath0 : bindingLinearPath x.S σ 0 = x.S := by
    funext l
    simp [bindingLinearPath]
  have hbase : InClass (totalE x) (totalF x) (totalS x) (X 0) := by
    change InClass (totalE x) (totalF x) (totalS x)
      (bindingState (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k)
        (bindingLinearPath x.S σ 0))
    rw [hpath0, equilibrium_bindingState_eq_source k x hk hx heq]
    exact ⟨rfl, rfl, rfl⟩
  let dS := x.S i.castSucc * σ i.castSucc
  have hS : HasDerivAt (fun t : ℝ => (X t).S i.castSucc) dS 0 := by
    exact bindingLinearPath_hasDerivAt x.S σ i.castSucc
  have hTS : HasDerivAt (fun t : ℝ => totalS (X t)) 0 0 :=
    equilibrium_bindingState_fixedTangent_totalS_hasDerivAt_zero
      k x hk hx heq j
  have hprojS : HasDerivAt (fun t : ℝ =>
      (stateFromLoaded (totalE x) (totalF x) (totalS x)
        (loadedCoordOfState (X t))).S i.castSucc) dS 0 := by
    by_cases hz : i.castSucc = 0
    · have hS0 : HasDerivAt (fun t : ℝ => (X t).S 0) dS 0 := by
        simpa only [hz] using hS
      have hp := stateFromLoaded_projection_S_zero_hasDerivAt
        (totalE x) (totalF x) (totalS x) X dS hS0 hTS
      simpa only [hz] using hp
    · obtain ⟨l, hl⟩ := Fin.exists_succ_eq_of_ne_zero hz
      rw [← hl] at hS ⊢
      simpa only [stateFromLoaded_loadedCoordOfState_S_succ] using hS
  obtain ⟨hdenP, _⟩ :=
    equilibrium_sourceBindingDenominators_ne_zero k x hk hx heq
  have hE : HasDerivAt (fun t : ℝ => (X t).E)
      (-(totalE x * bindingWeightedTangent (sourceBindingP k)
          x.S σ) / (bindingDenominator (sourceBindingP k) x.S) ^ 2) 0 := by
    exact bindingFree_hasDerivAt_linearPath
      (totalE x) (sourceBindingP k) x.S σ hdenP
  have hfast : ∀ t : ℝ, (field k (X t)).C i = 0 := by
    intro t
    exact (bindingState_fast_balance
      (totalE x) (totalF x) (sourceBindingP k) (sourceBindingQ k)
      k (sourceBindingRatios_rate_identities k hk).1
        (sourceBindingRatios_rate_identities k hk).2
      (bindingLinearPath x.S σ t) i).1
  exact loadedProjectionFastField_C_hasDerivAt_zero
    (totalE x) (totalF x) (totalS x) k X i dS _ hbase
    (equilibrium_sourceBindingPath_enzymeTotals_hasDerivAt_zero
      k x hk hx heq σ).1 hS hprojS hE hfast

theorem equilibrium_sourceProjectedFastD_hasDerivAt_zero {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) (j i : Fin n) :
    let A := (totalAndLevelOutputMatrix n) *
      loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
        (totalE x) (totalF x)
    let σ := firstPivotFixedTangent A j
    HasDerivAt (fun t : ℝ =>
      (loadedRestrictedField (totalE x) (totalF x) (totalS x) k
        (loadedCoordOfState (bindingState (totalE x) (totalF x)
          (sourceBindingP k) (sourceBindingQ k)
          (bindingLinearPath x.S σ t)))).2.2 i) 0 0 := by
  dsimp only
  let A := (totalAndLevelOutputMatrix n) *
    loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
      (totalE x) (totalF x)
  let σ := firstPivotFixedTangent A j
  let X : ℝ → State n := fun t =>
    bindingState (totalE x) (totalF x)
      (sourceBindingP k) (sourceBindingQ k)
      (bindingLinearPath x.S σ t)
  have hpath0 : bindingLinearPath x.S σ 0 = x.S := by
    funext l
    simp [bindingLinearPath]
  have hbase : totalF (X 0) = totalF x := by
    change totalF (bindingState (totalE x) (totalF x)
      (sourceBindingP k) (sourceBindingQ k)
      (bindingLinearPath x.S σ 0)) = totalF x
    rw [hpath0, equilibrium_bindingState_eq_source k x hk hx heq]
  have hS : HasDerivAt (fun t : ℝ => (X t).S i.succ)
      (x.S i.succ * σ i.succ) 0 :=
    bindingLinearPath_hasDerivAt x.S σ i.succ
  have hfast : ∀ t : ℝ, (field k (X t)).D i = 0 := by
    intro t
    exact (bindingState_fast_balance
      (totalE x) (totalF x) (sourceBindingP k) (sourceBindingQ k)
      k (sourceBindingRatios_rate_identities k hk).1
        (sourceBindingRatios_rate_identities k hk).2
      (bindingLinearPath x.S σ t) i).2
  exact loadedProjectionFastField_D_hasDerivAt_zero
    (totalE x) (totalF x) (totalS x) k X i _ hbase
    (equilibrium_sourceBindingPath_enzymeTotals_hasDerivAt_zero
      k x hk hx heq σ).2 hS hfast

/-- The full fast block of the literal loaded class field has zero
derivative along every positive-equilibrium compensated binding tangent. -/
theorem equilibrium_sourceProjectedFast_hasDerivAt_zero {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) (j : Fin n) :
    let A := (totalAndLevelOutputMatrix n) *
      loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
        (totalE x) (totalF x)
    let σ := firstPivotFixedTangent A j
    HasDerivAt (fun t : ℝ =>
      (loadedRestrictedField (totalE x) (totalF x) (totalS x) k
        (loadedCoordOfState (bindingState (totalE x) (totalF x)
          (sourceBindingP k) (sourceBindingQ k)
          (bindingLinearPath x.S σ t)))).2)
      (0 : FastSpace n) 0 := by
  dsimp only
  have hc : HasDerivAt (fun t : ℝ =>
      (loadedRestrictedField (totalE x) (totalF x) (totalS x) k
        (loadedCoordOfState (bindingState (totalE x) (totalF x)
          (sourceBindingP k) (sourceBindingQ k)
          (bindingLinearPath x.S
            (firstPivotFixedTangent
              ((totalAndLevelOutputMatrix n) *
                loadedBindingMass x.S (sourceLevelC x)
                  (sourceLevelD x) (totalE x) (totalF x)) j) t)))).2.1)
      (0 : Fin n → ℝ) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    exact equilibrium_sourceProjectedFastC_hasDerivAt_zero
      k x hk hx heq j i
  have hd : HasDerivAt (fun t : ℝ =>
      (loadedRestrictedField (totalE x) (totalF x) (totalS x) k
        (loadedCoordOfState (bindingState (totalE x) (totalF x)
          (sourceBindingP k) (sourceBindingQ k)
          (bindingLinearPath x.S
            (firstPivotFixedTangent
              ((totalAndLevelOutputMatrix n) *
                loadedBindingMass x.S (sourceLevelC x)
                  (sourceLevelD x) (totalE x) (totalF x)) j) t)))).2.2)
      (0 : Fin n → ℝ) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    exact equilibrium_sourceProjectedFastD_hasDerivAt_zero
      k x hk hx heq j i
  convert hc.prodMk hd using 1

end
end PhosphorylationStableCapacity
