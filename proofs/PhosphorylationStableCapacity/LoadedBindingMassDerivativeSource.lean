module
public import proofs.PhosphorylationStableCapacity.LoadedBindingMassOrientation
public import proofs.PhosphorylationStableCapacity.LoadedBindingDerivative
public import proofs.PhosphorylationStableCapacity.SourceBindingCurrentBridge
public import proofs.PhosphorylationStableCapacity.LoadedBindingLevelBridge

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Binding ratios recovered from arbitrary positive free enzyme,
free-substrate, and level-attached complex concentrations. -/
def physicalBindingRatio {ι : Type*} (S C : ι → ℝ) (E : ℝ) : ι → ℝ :=
  fun i => C i / (E * S i)

theorem physicalBindingRatio_denominator {ι : Type*} [Fintype ι]
    (S C : ι → ℝ) (E ET : ℝ)
    (hS : ∀ i, S i ≠ 0) (hE : E ≠ 0)
    (hET : ET = E + ∑ i, C i) :
    bindingDenominator (physicalBindingRatio S C E) S = ET / E := by
  have hterm (i : ι) : physicalBindingRatio S C E i * S i = C i / E := by
    unfold physicalBindingRatio
    field_simp [hS i, hE]
  unfold bindingDenominator
  simp_rw [hterm]
  rw [← Finset.sum_div]
  rw [hET]
  field_simp [hE]

theorem physicalBindingRatio_complex {ι : Type*} [Fintype ι]
    (S C : ι → ℝ) (E ET : ℝ)
    (hS : ∀ i, S i ≠ 0) (hE : E ≠ 0) (hET0 : ET ≠ 0)
    (hET : ET = E + ∑ i, C i) (i : ι) :
    bindingComplex ET (physicalBindingRatio S C E) S i = C i := by
  unfold bindingComplex
  rw [physicalBindingRatio_denominator S C E ET hS hE hET]
  unfold physicalBindingRatio
  field_simp [hS i, hE, hET0]

/-- The positive-state mass matrix is the actual derivative of the
binding loaded inventories at arbitrary free enzyme concentrations. -/
theorem loadedBindingMass_hasDerivAt_physical
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S C Y σ : ι → ℝ) (E F ET FT : ℝ) (i : ι)
    (hS : ∀ j, S j ≠ 0)
    (hE : E ≠ 0) (hF : F ≠ 0)
    (hET0 : ET ≠ 0) (hFT0 : FT ≠ 0)
    (hET : ET = E + ∑ j, C j)
    (hFT : FT = F + ∑ j, Y j) :
    HasDerivAt (fun t : ℝ =>
      bindingLoadedLevel ET FT
        (physicalBindingRatio S C E)
        (physicalBindingRatio S Y F)
        (bindingLinearPath S σ t) i)
      ((loadedBindingMass S C Y ET FT).mulVec σ i) 0 := by
  have hp : bindingDenominator (physicalBindingRatio S C E) S ≠ 0 := by
    rw [physicalBindingRatio_denominator S C E ET hS hE hET]
    exact div_ne_zero hET0 hE
  have hq : bindingDenominator (physicalBindingRatio S Y F) S ≠ 0 := by
    rw [physicalBindingRatio_denominator S Y F FT hS hF hFT]
    exact div_ne_zero hFT0 hF
  have h := bindingLoadedLevel_hasDerivAt_linearPath ET FT
    (physicalBindingRatio S C E) (physicalBindingRatio S Y F)
    S σ i hET0 hFT0 hp hq
  have hC : bindingComplex ET (physicalBindingRatio S C E) S = C := by
    funext j
    exact physicalBindingRatio_complex S C E ET hS hE hET0 hET j
  have hY : bindingComplex FT (physicalBindingRatio S Y F) S = Y := by
    funext j
    exact physicalBindingRatio_complex S Y F FT hS hF hFT0 hFT j
  simpa only [hC, hY] using h

theorem source_loadedBindingMass_hasDerivAt {n : ℕ}
    (x : State n) (hx : x.Positive)
    (σ : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    HasDerivAt (fun t : ℝ =>
      bindingLoadedLevel (totalE x) (totalF x)
        (physicalBindingRatio x.S (sourceLevelC x) x.E)
        (physicalBindingRatio x.S (sourceLevelD x) x.F)
        (bindingLinearPath x.S σ t) i)
      ((loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
        (totalE x) (totalF x)).mulVec σ i) 0 := by
  apply loadedBindingMass_hasDerivAt_physical
    x.S (sourceLevelC x) (sourceLevelD x) σ
    x.E x.F (totalE x) (totalF x) i
  · intro j
    exact ne_of_gt (hx.1 j)
  · exact ne_of_gt hx.2.1
  · exact ne_of_gt hx.2.2.1
  · have h : 0 < totalE x := by
      simp [totalE]
      exact add_pos_of_pos_of_nonneg hx.2.1
        (Finset.sum_nonneg fun j _ => (hx.2.2.2.1 j).le)
    exact ne_of_gt h
  · have h : 0 < totalF x := by
      simp [totalF]
      exact add_pos_of_pos_of_nonneg hx.2.2.1
        (Finset.sum_nonneg fun j _ => (hx.2.2.2.2 j).le)
    exact ne_of_gt h
  · simp [totalE, sourceLevelC_sum]
  · simp [totalF, sourceLevelD_sum]

theorem sourceLevelC_castSucc {n : ℕ} (x : State n) (i : Fin n) :
    sourceLevelC x i.castSucc = x.C i := by
  simp [sourceLevelC]

theorem sourceLevelC_last {n : ℕ} (x : State n) :
    sourceLevelC x (Fin.last n) = 0 := by
  simp [sourceLevelC]

theorem sourceLevelD_zero {n : ℕ} (x : State n) :
    sourceLevelD x 0 = 0 := by
  simp [sourceLevelD]

theorem sourceLevelD_succ {n : ℕ} (x : State n) (i : Fin n) :
    sourceLevelD x i.succ = x.D i := by
  simp [sourceLevelD]

/-- At a positive literal equilibrium, the concentration-derived binding
ratios coincide with the fixed rate ratios on every substrate level. -/
theorem equilibrium_physicalBindingRatio_eq_rateRatios {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) :
    physicalBindingRatio x.S (sourceLevelC x) x.E = sourceBindingP k ∧
    physicalBindingRatio x.S (sourceLevelD x) x.F = sourceBindingQ k := by
  obtain ⟨hC, hD⟩ := equilibrium_binding_complex_formulas
    k (sourceBindingP k) (sourceBindingQ k) x hk heq
    (sourceBindingRatios_rate_identities k hk).1
    (sourceBindingRatios_rate_identities k hk).2
  constructor
  · funext j
    cases j using Fin.lastCases with
    | last => simp [physicalBindingRatio, sourceLevelC_last, sourceBindingP]
    | cast i =>
        rw [physicalBindingRatio,
          sourceLevelC_castSucc, hC i]
        field_simp [ne_of_gt (hx.1 i.castSucc), ne_of_gt hx.2.1]
  · funext j
    cases j using Fin.cases with
    | zero => simp [physicalBindingRatio, sourceLevelD_zero, sourceBindingQ]
    | succ i =>
        rw [physicalBindingRatio,
          sourceLevelD_succ, hD i]
        field_simp [ne_of_gt (hx.1 i.succ), ne_of_gt hx.2.2.1]

/-- At a positive literal equilibrium, the loaded binding mass matrix is
the derivative of the kinetic-ratio binding inventory along any substrate
direction. -/
theorem equilibrium_source_loadedBindingMass_hasDerivAt_kinetic {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x)
    (σ : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    HasDerivAt (fun t : ℝ =>
      bindingLoadedLevel (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k)
        (bindingLinearPath x.S σ t) i)
      ((loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
        (totalE x) (totalF x)).mulVec σ i) 0 := by
  obtain ⟨hp, hq⟩ :=
    equilibrium_physicalBindingRatio_eq_rateRatios k x hk hx heq
  rw [← hp, ← hq]
  exact source_loadedBindingMass_hasDerivAt x hx σ i

/-- The fixed-total binding chart built from the literal rate ratios
reconstructs every positive literal equilibrium exactly. -/
theorem equilibrium_bindingState_eq_source {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) :
    bindingState (totalE x) (totalF x)
      (sourceBindingP k) (sourceBindingQ k) x.S = x := by
  obtain ⟨hp, hq⟩ :=
    equilibrium_physicalBindingRatio_eq_rateRatios k x hk hx heq
  have hET : 0 < totalE x := by
    simp [totalE]
    exact add_pos_of_pos_of_nonneg hx.2.1
      (Finset.sum_nonneg fun j _ => (hx.2.2.2.1 j).le)
  have hFT : 0 < totalF x := by
    simp [totalF]
    exact add_pos_of_pos_of_nonneg hx.2.2.1
      (Finset.sum_nonneg fun j _ => (hx.2.2.2.2 j).le)
  have hdenP : bindingDenominator (sourceBindingP k) x.S =
      totalE x / x.E := by
    rw [← hp]
    exact physicalBindingRatio_denominator x.S (sourceLevelC x)
      x.E (totalE x) (fun j => ne_of_gt (hx.1 j))
      (ne_of_gt hx.2.1) (by simp [totalE, sourceLevelC_sum])
  have hdenQ : bindingDenominator (sourceBindingQ k) x.S =
      totalF x / x.F := by
    rw [← hq]
    exact physicalBindingRatio_denominator x.S (sourceLevelD x)
      x.F (totalF x) (fun j => ne_of_gt (hx.1 j))
      (ne_of_gt hx.2.2.1) (by simp [totalF, sourceLevelD_sum])
  have hC (i : Fin n) :
      bindingComplex (totalE x) (sourceBindingP k) x.S i.castSucc =
        x.C i := by
    rw [← hp]
    rw [physicalBindingRatio_complex x.S (sourceLevelC x) x.E
      (totalE x) (fun j => ne_of_gt (hx.1 j)) (ne_of_gt hx.2.1)
      (ne_of_gt hET) (by simp [totalE, sourceLevelC_sum])]
    exact sourceLevelC_castSucc x i
  have hD (i : Fin n) :
      bindingComplex (totalF x) (sourceBindingQ k) x.S i.succ =
        x.D i := by
    rw [← hq]
    rw [physicalBindingRatio_complex x.S (sourceLevelD x) x.F
      (totalF x) (fun j => ne_of_gt (hx.1 j)) (ne_of_gt hx.2.2.1)
      (ne_of_gt hFT) (by simp [totalF, sourceLevelD_sum])]
    exact sourceLevelD_succ x i
  cases x with
  | mk S E F C D =>
      simp only [bindingState, State.mk.injEq]
      constructor
      · trivial
      constructor
      · rw [hdenP]
        field_simp [ne_of_gt hET, ne_of_gt hx.2.1]
      constructor
      · rw [hdenQ]
        field_simp [ne_of_gt hFT, ne_of_gt hx.2.2.1]
      constructor
      · funext i
        exact hC i
      · funext i
        exact hD i

/-- The binding inventory whose derivative is the loaded mass matrix is
the literal loaded-level coordinate at every positive equilibrium. -/
theorem equilibrium_loadedLevel_eq_bindingLoadedLevel {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) (j : Fin (n+1)) :
    loadedLevel x j = bindingLoadedLevel (totalE x) (totalF x)
      (sourceBindingP k) (sourceBindingQ k) x.S j := by
  have hp : bindingComplex (totalE x) (sourceBindingP k) x.S
      (Fin.last n) = 0 := by
    simp [bindingComplex, sourceBindingP]
  have hq : bindingComplex (totalF x) (sourceBindingQ k) x.S
      0 = 0 := by
    simp [bindingComplex, sourceBindingQ]
  calc
    loadedLevel x j = loadedLevel
        (bindingState (totalE x) (totalF x)
          (sourceBindingP k) (sourceBindingQ k) x.S) j := by
      rw [equilibrium_bindingState_eq_source k x hk hx heq]
    _ = bindingLoadedLevel (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k) x.S j :=
      loadedLevel_bindingState_eq_bindingLoadedLevel
        (totalE x) (totalF x) (sourceBindingP k) (sourceBindingQ k)
        x.S hp hq j

end
end PhosphorylationStableCapacity
