module
public import proofs.PhosphorylationStableCapacity.SourceAugmentedCurrentOrientation
public import proofs.PhosphorylationStableCapacity.BindingManifoldFastBalance
public import proofs.PhosphorylationStableCapacity.LoadedTotalIdentity
public import proofs.PhosphorylationStableCapacity.BindingStateEnzymeTangent

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

theorem equilibrium_sourceBindingDenominators_ne_zero {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) :
    bindingDenominator (sourceBindingP k) x.S ≠ 0 ∧
      bindingDenominator (sourceBindingQ k) x.S ≠ 0 := by
  have hstate := equilibrium_bindingState_eq_source k x hk hx heq
  have hE := congrArg (fun y : State n => y.E) hstate
  have hF := congrArg (fun y : State n => y.F) hstate
  constructor
  · intro hden
    simp [bindingState, hden] at hE
    linarith [hx.2.1]
  · intro hden
    simp [bindingState, hden] at hF
    linarith [hx.2.2.1]

theorem equilibrium_sourceBindingPath_enzymeTotals_hasDerivAt_zero
    {n : ℕ} (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) (σ : Fin (n+1) → ℝ) :
    HasDerivAt (fun t : ℝ =>
      totalE (bindingState (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k)
        (bindingLinearPath x.S σ t))) 0 0 ∧
    HasDerivAt (fun t : ℝ =>
      totalF (bindingState (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k)
        (bindingLinearPath x.S σ t))) 0 0 := by
  obtain ⟨hp, hq⟩ :=
    equilibrium_sourceBindingDenominators_ne_zero k x hk hx heq
  constructor
  · apply bindingState_totalE_path_hasDerivAt_zero
    · intro T
      simp [bindingComplex, sourceBindingP]
    · exact hp
  · apply bindingState_totalF_path_hasDerivAt_zero
    · intro T
      simp [bindingComplex, sourceBindingQ]
    · exact hq

/-- The fixed-enzyme-total binding state's literal total substrate is
the sum of its binding loaded-level inventories. -/
theorem source_bindingState_totalS_eq_bindingLoadedLevel_sum {n : ℕ}
    (k : Rates n) (ET FT : ℝ) (S : Fin (n+1) → ℝ) :
    totalS (bindingState ET FT (sourceBindingP k) (sourceBindingQ k) S) =
      ∑ j, bindingLoadedLevel ET FT
        (sourceBindingP k) (sourceBindingQ k) S j := by
  rw [← sum_loadedLevel_eq_totalS]
  apply Finset.sum_congr rfl
  intro j _
  apply loadedLevel_bindingState_eq_bindingLoadedLevel
  · simp [bindingComplex, sourceBindingP]
  · simp [bindingComplex, sourceBindingQ]

/-- Along each compensated substrate tangent, the actual literal
total-substrate inventory is stationary to first order. -/
theorem equilibrium_bindingState_fixedTangent_totalS_hasDerivAt_zero {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) (j : Fin n) :
    let A := (totalAndLevelOutputMatrix n) *
      loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
        (totalE x) (totalF x)
    let σ := firstPivotFixedTangent A j
    HasDerivAt (fun t : ℝ =>
      totalS (bindingState (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k)
        (bindingLinearPath x.S σ t))) 0 0 := by
  simpa only [source_bindingState_totalS_eq_bindingLoadedLevel_sum]
    using equilibrium_firstPivotFixedTangent_total_hasDerivAt_zero
      k x hk hx heq j

/-- The literal complex velocities vanish along the entire binding
path, so their directional derivatives vanish at the equilibrium. -/
theorem source_bindingState_fast_hasDerivAt_zero {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (σ : Fin (n+1) → ℝ) (i : Fin n) :
    HasDerivAt (fun t : ℝ =>
      (field k (bindingState (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k)
        (bindingLinearPath x.S σ t))).C i) 0 0 ∧
    HasDerivAt (fun t : ℝ =>
      (field k (bindingState (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k)
        (bindingLinearPath x.S σ t))).D i) 0 0 := by
  have hbalanced (t : ℝ) := bindingState_fast_balance
    (totalE x) (totalF x) (sourceBindingP k) (sourceBindingQ k)
    k (sourceBindingRatios_rate_identities k hk).1
      (sourceBindingRatios_rate_identities k hk).2
    (bindingLinearPath x.S σ t) i
  constructor
  · have hfun : (fun t : ℝ =>
        (field k (bindingState (totalE x) (totalF x)
          (sourceBindingP k) (sourceBindingQ k)
          (bindingLinearPath x.S σ t))).C i) =
        fun _ => (0 : ℝ) := by
      funext t
      exact (hbalanced t).1
    rw [hfun]
    exact hasDerivAt_const _ _
  · have hfun : (fun t : ℝ =>
        (field k (bindingState (totalE x) (totalF x)
          (sourceBindingP k) (sourceBindingQ k)
          (bindingLinearPath x.S σ t))).D i) =
        fun _ => (0 : ℝ) := by
      funext t
      exact (hbalanced t).2
    rw [hfun]
    exact hasDerivAt_const _ _

end
end PhosphorylationStableCapacity
