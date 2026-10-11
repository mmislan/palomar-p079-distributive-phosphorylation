module
public import proofs.PhosphorylationStableCapacity.PaperCoalescedPhysicalData435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter PhosphorylationSharpness Matrix Polynomial

open scoped Topology

theorem paperPointwise_bindingState (m : ℕ) (r : ℝ)
    (hdata : PaperCoalescedPhysicalData m r) :
    bindingState (2*r) 2 (coalescedBindingP m r) (coalescedBindingQ m r)
      (coalescedFiniteState (m+1) r).S = coalescedFiniteState (m+1) r :=
  coalescedBindingState_eq_finiteState m r hdata.statePositive
    hdata.sumC_eq hdata.sumD_eq hdata.sourceNeZero


/-- Pointwise derivative identity from explicit physical source data. -/
theorem paperPointwise_inventory (m : ℕ) (r : ℝ)
    (hdata : PaperCoalescedPhysicalData m r) :
    ∀ (q : Fin (m + 3) → ℝ) (k : Fin (m + 3)),
        HasDerivAt (fun t : ℝ =>
          bindingLoadedLevel (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) k)
          (r * q k) 0 := by
  have hmass := fun σ i => coalescedFullMass_hasDerivAt_bindingLevel
    m r σ i hdata.statePositive hdata.sumC_eq hdata.sumD_eq hdata.sourceNeZero
  have hdet := hdata.massDetNeZero
  intro q k
  have h := hmass (coalescedInverseResponse m r q) k
  have heq :
      (coalescedFullMass m r).mulVec
        (coalescedInverseResponse m r q) k = r * q k := by
    have hs := congrArg (fun f : Fin (m + 3) → ℝ => f k)
      (coalescedInverseResponse_mass_equation m r q hdet)
    simpa only [Pi.smul_apply, smul_eq_mul] using hs
  rw [heq] at h
  exact h


/-- Pointwise derivative identity from explicit physical source data. -/
theorem paperPointwise_literalInventory (m : ℕ) (r : ℝ)
    (hdata : PaperCoalescedPhysicalData m r) :
    ∀ (q : Fin (m + 3) → ℝ) (k : Fin (m + 3)),
        HasDerivAt (fun t : ℝ =>
          loadedLevel (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t)) k)
          (r * q k) 0 := by
  have hmass := paperPointwise_inventory m r hdata
  intro q k
  have h := hmass q k
  have hfun : (fun t : ℝ =>
      loadedLevel (bindingState (2 * r) 2
        (coalescedBindingP m r) (coalescedBindingQ m r)
        (bindingLinearPath (coalescedFiniteState (m + 1) r).S
          (coalescedInverseResponse m r q) t)) k) =
      (fun t : ℝ =>
        bindingLoadedLevel (2 * r) 2
          (coalescedBindingP m r) (coalescedBindingQ m r)
          (bindingLinearPath (coalescedFiniteState (m + 1) r).S
            (coalescedInverseResponse m r q) t) k) := by
    funext t
    exact coalescedBindingLevel_eq_loadedLevel m r _ k
  rw [hfun]
  exact h


/-- Pointwise derivative identity from explicit physical source data. -/
theorem paperPointwise_totalS (m : ℕ) (r : ℝ)
    (hdata : PaperCoalescedPhysicalData m r) :
    ∀ (q : Fin (m + 3) → ℝ),
        (∑ k, q k) = 0 →
        HasDerivAt (fun t : ℝ =>
          totalS (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t))) 0 0 := by
  have hlevels := paperPointwise_literalInventory m r hdata
  intro q hq
  have hs : HasDerivAt (fun t : ℝ =>
      ∑ k : Fin (m + 3),
        loadedLevel (bindingState (2 * r) 2
          (coalescedBindingP m r) (coalescedBindingQ m r)
          (bindingLinearPath (coalescedFiniteState (m + 1) r).S
            (coalescedInverseResponse m r q) t)) k)
      (∑ k : Fin (m + 3), r * q k) 0 := by
    apply HasDerivAt.fun_sum
    intro k _
    exact hlevels q k
  have hfun : (fun t : ℝ =>
      ∑ k : Fin (m + 3),
        loadedLevel (bindingState (2 * r) 2
          (coalescedBindingP m r) (coalescedBindingQ m r)
          (bindingLinearPath (coalescedFiniteState (m + 1) r).S
            (coalescedInverseResponse m r q) t)) k) =
      (fun t : ℝ =>
        totalS (bindingState (2 * r) 2
          (coalescedBindingP m r) (coalescedBindingQ m r)
          (bindingLinearPath (coalescedFiniteState (m + 1) r).S
            (coalescedInverseResponse m r q) t))) := by
    funext t
    exact sum_loadedLevel_eq_totalS _
  have hzero : (∑ k : Fin (m + 3), r * q k) = 0 := by
    rw [← Finset.mul_sum, hq, mul_zero]
  rw [hfun, hzero] at hs
  exact hs


/-- Pointwise derivative identity from explicit physical source data. -/
theorem paperPointwise_bindingDenominators (m : ℕ) (r : ℝ)
    (hdata : PaperCoalescedPhysicalData m r) :
    bindingDenominator (coalescedBindingP m r)
          (coalescedFiniteState (m + 1) r).S ≠ 0 ∧
        bindingDenominator (coalescedBindingQ m r)
          (coalescedFiniteState (m + 1) r).S ≠ 0 := by
  have hstate := paperPointwise_bindingState m r hdata
  have hE := congrArg (fun x : State (m + 2) => x.E) hstate
  have hF := congrArg (fun x : State (m + 2) => x.F) hstate
  have hEF := coalescedFiniteState_EF (m + 1) r
  constructor
  · intro hz
    change (2 * r) /
      bindingDenominator (coalescedBindingP m r)
        (coalescedFiniteState (m + 1) r).S =
          (coalescedFiniteState (m + 1) r).E at hE
    rw [hEF.1, hz, div_zero] at hE
    norm_num at hE
  · intro hz
    change (2 : ℝ) /
      bindingDenominator (coalescedBindingQ m r)
        (coalescedFiniteState (m + 1) r).S =
          (coalescedFiniteState (m + 1) r).F at hF
    rw [hEF.2, hz, div_zero] at hF
    norm_num at hF


/-- Pointwise derivative identity from explicit physical source data. -/
theorem paperPointwise_enzymeTotals (m : ℕ) (r : ℝ)
    (hdata : PaperCoalescedPhysicalData m r) :
    ∀ q : Fin (m + 3) → ℝ,
        HasDerivAt (fun t : ℝ =>
          totalE (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t))) 0 0 ∧
        HasDerivAt (fun t : ℝ =>
          totalF (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t))) 0 0 := by
  have hden := paperPointwise_bindingDenominators m r hdata
  intro q
  have hp : ∀ T : Fin (m + 3) → ℝ,
      bindingComplex (2 * r) (coalescedBindingP m r) T
        (Fin.last (m + 2)) = 0 :=
    fun T => (coalescedBinding_endpoint_complexes_zero m r T).1
  have hq : ∀ T : Fin (m + 3) → ℝ,
      bindingComplex 2 (coalescedBindingQ m r) T 0 = 0 :=
    fun T => (coalescedBinding_endpoint_complexes_zero m r T).2
  exact ⟨bindingState_totalE_path_hasDerivAt_zero
      (2 * r) 2 (coalescedBindingP m r) (coalescedBindingQ m r)
      (coalescedFiniteState (m + 1) r).S
      (coalescedInverseResponse m r q) hp hden.1,
    bindingState_totalF_path_hasDerivAt_zero
      (2 * r) 2 (coalescedBindingP m r) (coalescedBindingQ m r)
      (coalescedFiniteState (m + 1) r).S
      (coalescedInverseResponse m r q) hq hden.2⟩


/-- Pointwise derivative identity from explicit physical source data. -/
theorem paperPointwise_allTotals (m : ℕ) (r : ℝ)
    (hdata : PaperCoalescedPhysicalData m r) :
    ∀ q : Fin (m + 3) → ℝ,
        (∑ k, q k) = 0 →
        HasDerivAt (fun t : ℝ =>
          totalE (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t))) 0 0 ∧
        HasDerivAt (fun t : ℝ =>
          totalF (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t))) 0 0 ∧
        HasDerivAt (fun t : ℝ =>
          totalS (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t))) 0 0 := by
  have henz := paperPointwise_enzymeTotals m r hdata
  have hsub := paperPointwise_totalS m r hdata
  intro q hq
  exact ⟨(henz q).1, (henz q).2, hsub q hq⟩


/-- Pointwise derivative identity from explicit physical source data. -/
theorem paperPointwise_loadedCoordPath (m : ℕ) (r : ℝ)
    (hdata : PaperCoalescedPhysicalData m r) :
    ∀ q : Fin (m + 3) → ℝ,
        HasDerivAt (fun t : ℝ =>
          loadedCoordOfState (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t)))
          (coalescedBindingCoordTangent m r q) 0 := by
  have hlevels := paperPointwise_literalInventory m r hdata
  have hden := paperPointwise_bindingDenominators m r hdata
  intro q
  have hs : HasDerivAt (fun t : ℝ =>
      (loadedCoordOfState (bindingState (2 * r) 2
        (coalescedBindingP m r) (coalescedBindingQ m r)
        (bindingLinearPath (coalescedFiniteState (m + 1) r).S
          (coalescedInverseResponse m r q) t))).1)
      (coalescedBindingCoordTangent m r q).1 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa only [loadedCoordOfState_slow,
      coalescedBindingCoordTangent] using hlevels q i.succ
  have hc : HasDerivAt (fun t : ℝ =>
      (loadedCoordOfState (bindingState (2 * r) 2
        (coalescedBindingP m r) (coalescedBindingQ m r)
        (bindingLinearPath (coalescedFiniteState (m + 1) r).S
          (coalescedInverseResponse m r q) t))).2.1)
      (coalescedBindingCoordTangent m r q).2.1 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    have h := bindingComplex_hasDerivAt_linearPath_raw
      (2 * r) (coalescedBindingP m r)
      (coalescedFiniteState (m + 1) r).S
      (coalescedInverseResponse m r q) i.castSucc hden.1
    simpa only [loadedCoordOfState_C, bindingState,
      coalescedBindingCoordTangent, bindingComplexRawTangent] using h
  have hd : HasDerivAt (fun t : ℝ =>
      (loadedCoordOfState (bindingState (2 * r) 2
        (coalescedBindingP m r) (coalescedBindingQ m r)
        (bindingLinearPath (coalescedFiniteState (m + 1) r).S
          (coalescedInverseResponse m r q) t))).2.2)
      (coalescedBindingCoordTangent m r q).2.2 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    have h := bindingComplex_hasDerivAt_linearPath_raw
      2 (coalescedBindingQ m r)
      (coalescedFiniteState (m + 1) r).S
      (coalescedInverseResponse m r q) i.succ hden.2
    simpa only [loadedCoordOfState_D, bindingState,
      coalescedBindingCoordTangent, bindingComplexRawTangent] using h
  exact hs.prodMk (hc.prodMk hd)


/-- Pointwise derivative identity from explicit physical source data. -/
theorem paperPointwise_projectedFastC (m : ℕ) (r : ℝ)
    (hdata : PaperCoalescedPhysicalData m r) :
    ∀ (q : Fin (m + 3) → ℝ),
        (∑ k, q k) = 0 →
        ∀ i : Fin (m + 2),
          HasDerivAt (fun t : ℝ =>
            (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
              (coalescedFiniteRates (m + 1) r)
              (loadedCoordOfState
                (bindingState (2 * r) 2
                  (coalescedBindingP m r) (coalescedBindingQ m r)
                  (bindingLinearPath (coalescedFiniteState (m + 1) r).S
                    (coalescedInverseResponse m r q) t)))).2.1 i) 0 0 := by
  have hclass := paperPointwise_allTotals m r hdata
  have hden := paperPointwise_bindingDenominators m r hdata
  have hstate := paperPointwise_bindingState m r hdata
  have hsource : (coalescedFiniteRates (m+1) r).Positive ∧
      (coalescedFiniteState (m+1) r).Positive ∧
      Equilibrium (coalescedFiniteRates (m+1) r) (coalescedFiniteState (m+1) r) ∧
      totalE (coalescedFiniteState (m+1) r) = 2*r ∧
      totalF (coalescedFiniteState (m+1) r) = 2 ∧
      totalS (coalescedFiniteState (m+1) r) = 2*(r+1) :=
    ⟨hdata.ratesPositive, hdata.statePositive, hdata.stateEquilibrium,
      hdata.totalE_eq, hdata.totalF_eq, hdata.totalS_eq⟩
  obtain ⟨_, hpos, heq, htotalE, htotalF, htotalS⟩ := hsource
  intro q hq i
  let x : ℝ → State (m + 2) := fun t =>
    bindingState (2 * r) 2
      (coalescedBindingP m r) (coalescedBindingQ m r)
      (bindingLinearPath (coalescedFiniteState (m + 1) r).S
        (coalescedInverseResponse m r q) t)
  have hpath0 : bindingLinearPath (coalescedFiniteState (m + 1) r).S
      (coalescedInverseResponse m r q) 0 =
        (coalescedFiniteState (m + 1) r).S := by
    funext j
    simp [bindingLinearPath]
  have hbase : InClass (2 * r) 2 (2 * (r + 1)) (x 0) := by
    change InClass (2 * r) 2 (2 * (r + 1))
      (bindingState (2 * r) 2
        (coalescedBindingP m r) (coalescedBindingQ m r)
        (bindingLinearPath (coalescedFiniteState (m + 1) r).S
          (coalescedInverseResponse m r q) 0))
    rw [hpath0, hstate]
    exact ⟨htotalE, htotalF, htotalS⟩
  let dS : ℝ := (coalescedFiniteState (m + 1) r).S i.castSucc *
    (coalescedInverseResponse m r q) i.castSucc
  have hS : HasDerivAt (fun t : ℝ => (x t).S i.castSucc) dS 0 := by
    change HasDerivAt (fun t : ℝ =>
      bindingLinearPath (coalescedFiniteState (m + 1) r).S
        (coalescedInverseResponse m r q) t i.castSucc) dS 0
    exact bindingLinearPath_hasDerivAt _ _ i.castSucc
  have hTS : HasDerivAt (fun t : ℝ => totalS (x t)) 0 0 :=
    (hclass q hq).2.2
  have hprojS : HasDerivAt (fun t : ℝ =>
      (stateFromLoaded (2 * r) 2 (2 * (r + 1))
        (loadedCoordOfState (x t))).S i.castSucc) dS 0 := by
    by_cases hz : i.castSucc = 0
    · have hS0 : HasDerivAt (fun t : ℝ => (x t).S 0) dS 0 := by
        simpa only [hz] using hS
      have hp := stateFromLoaded_projection_S_zero_hasDerivAt
        (2 * r) 2 (2 * (r + 1)) x dS hS0 hTS
      simpa only [hz] using hp
    · obtain ⟨j, hj⟩ := Fin.exists_succ_eq_of_ne_zero hz
      rw [← hj] at hS ⊢
      simpa only [stateFromLoaded_loadedCoordOfState_S_succ] using hS
  have hE : HasDerivAt (fun t : ℝ => (x t).E)
      (-(2 * r * bindingWeightedTangent (coalescedBindingP m r)
          (coalescedFiniteState (m + 1) r).S
          (coalescedInverseResponse m r q)) /
        (bindingDenominator (coalescedBindingP m r)
          (coalescedFiniteState (m + 1) r).S) ^ 2) 0 := by
    change HasDerivAt (fun t : ℝ =>
      (2 * r) / bindingDenominator (coalescedBindingP m r)
        (bindingLinearPath (coalescedFiniteState (m + 1) r).S
          (coalescedInverseResponse m r q) t)) _ 0
    exact bindingFree_hasDerivAt_linearPath _ _ _ _ hden.1
  have hfast : ∀ t : ℝ,
      (field (coalescedFiniteRates (m + 1) r) (x t)).C i = 0 := by
    intro t
    exact (coalescedBindingState_fast_zero m r hpos heq _ i).1
  exact loadedProjectionFastField_C_hasDerivAt_zero
    (2 * r) 2 (2 * (r + 1)) (coalescedFiniteRates (m + 1) r)
    x i dS _ hbase (hclass q hq).1 hS hprojS hE hfast


/-- Pointwise derivative identity from explicit physical source data. -/
theorem paperPointwise_projectedFastD (m : ℕ) (r : ℝ)
    (hdata : PaperCoalescedPhysicalData m r) :
    ∀ (q : Fin (m + 3) → ℝ) (i : Fin (m + 2)),
        HasDerivAt (fun t : ℝ =>
          (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
            (coalescedFiniteRates (m + 1) r)
            (loadedCoordOfState
              (bindingState (2 * r) 2
                (coalescedBindingP m r) (coalescedBindingQ m r)
                (bindingLinearPath (coalescedFiniteState (m + 1) r).S
                  (coalescedInverseResponse m r q) t)))).2.2 i) 0 0 := by
  have henz := paperPointwise_enzymeTotals m r hdata
  have hstate := paperPointwise_bindingState m r hdata
  have hsource : (coalescedFiniteRates (m+1) r).Positive ∧
      (coalescedFiniteState (m+1) r).Positive ∧
      Equilibrium (coalescedFiniteRates (m+1) r) (coalescedFiniteState (m+1) r) ∧
      totalE (coalescedFiniteState (m+1) r) = 2*r ∧
      totalF (coalescedFiniteState (m+1) r) = 2 ∧
      totalS (coalescedFiniteState (m+1) r) = 2*(r+1) :=
    ⟨hdata.ratesPositive, hdata.statePositive, hdata.stateEquilibrium,
      hdata.totalE_eq, hdata.totalF_eq, hdata.totalS_eq⟩
  obtain ⟨_, hpos, heq, _, hF, _⟩ := hsource
  intro q i
  let x : ℝ → State (m + 2) := fun t =>
    bindingState (2 * r) 2
      (coalescedBindingP m r) (coalescedBindingQ m r)
      (bindingLinearPath (coalescedFiniteState (m + 1) r).S
        (coalescedInverseResponse m r q) t)
  have hpath0 : bindingLinearPath (coalescedFiniteState (m + 1) r).S
      (coalescedInverseResponse m r q) 0 =
        (coalescedFiniteState (m + 1) r).S := by
    funext j
    simp [bindingLinearPath]
  have hbase : totalF (x 0) = 2 := by
    change totalF (bindingState (2 * r) 2
      (coalescedBindingP m r) (coalescedBindingQ m r)
      (bindingLinearPath (coalescedFiniteState (m + 1) r).S
        (coalescedInverseResponse m r q) 0)) = 2
    rw [hpath0, hstate]
    exact hF
  have hS : HasDerivAt (fun t : ℝ => (x t).S i.succ)
      ((coalescedFiniteState (m + 1) r).S i.succ *
        (coalescedInverseResponse m r q) i.succ) 0 := by
    change HasDerivAt (fun t : ℝ =>
      bindingLinearPath (coalescedFiniteState (m + 1) r).S
        (coalescedInverseResponse m r q) t i.succ) _ 0
    exact bindingLinearPath_hasDerivAt _ _ i.succ
  have hfast : ∀ t : ℝ,
      (field (coalescedFiniteRates (m + 1) r) (x t)).D i = 0 := by
    intro t
    exact (coalescedBindingState_fast_zero m r hpos heq _ i).2
  exact loadedProjectionFastField_D_hasDerivAt_zero
    (2 * r) 2 (2 * (r + 1)) (coalescedFiniteRates (m + 1) r)
    x i _ hbase (henz q).2 hS hfast


/-- Pointwise derivative identity from explicit physical source data. -/
theorem paperPointwise_inverseCurrent (m : ℕ) (r : ℝ)
    (hdata : PaperCoalescedPhysicalData m r) :
    ∀ (q : Fin (m + 3) → ℝ) (i : Fin (m + 2)),
        HasDerivAt (fun t : ℝ =>
          bindingCatalyticCurrent (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            Fin.castSucc Fin.succ
            (coalescedFiniteRates (m + 1) r).c
            (coalescedFiniteRates (m + 1) r).gamma
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) i)
          ((coalescedCurrentJacobianMatrix m r).mulVec
            (coalescedInverseResponse m r q) i) 0 := by
  intro q i
  exact coalescedCatalyticCurrent_hasDerivAt_matrix m r
    (coalescedInverseResponse m r q) i hdata.statePositive
    hdata.sumC_eq hdata.sumD_eq hdata.sourceNeZero


/-- Pointwise derivative identity from explicit physical source data. -/
theorem paperPointwise_allEdgeCurrent (m : ℕ) (r : ℝ)
    (hdata : PaperCoalescedPhysicalData m r) :
    ∀ (w : Fin (m+2) → ℝ) (q : Fin (m+3) → ℝ)
        (i : Fin (m+2)),
        HasDerivAt (fun t : ℝ =>
          bindingCatalyticCurrent (2*r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            Fin.castSucc Fin.succ
            (coalescedAllScaledRates m r w).c
            (coalescedAllScaledRates m r w).gamma
            (bindingLinearPath (coalescedFiniteState (m+1) r).S
              (coalescedInverseResponse m r q) t) i)
          (w i * (coalescedCurrentJacobianMatrix m r).mulVec
            (coalescedInverseResponse m r q) i) 0 := by
  have hcurrent := paperPointwise_inverseCurrent m r hdata
  intro w q i
  have h := (hcurrent q i).const_mul (w i)
  simpa only [coalescedAllScaledRates, edgeScaledRates,
    edgeScaled_bindingCatalyticCurrent] using h


/-- Pointwise derivative identity from explicit physical source data. -/
theorem paperPointwise_allReducedSlow (m : ℕ) (r : ℝ)
    (hdata : PaperCoalescedPhysicalData m r) :
    ∀ (w : Fin (m + 2) → ℝ) (q : Fin (m + 3) → ℝ) (j : Fin (m + 3)),
        HasDerivAt (fun t : ℝ =>
          bindingReducedSlowField (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (coalescedAllScaledRates m r w)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) j)
          (∑ i : Fin (m + 2),
            ((if i.succ = j then
              w i *
                (coalescedCurrentJacobianMatrix m r).mulVec
                  (coalescedInverseResponse m r q) i else 0) -
             (if i.castSucc = j then
              w i *
                (coalescedCurrentJacobianMatrix m r).mulVec
                  (coalescedInverseResponse m r q) i else 0))) 0 := by
  have hcurrent := paperPointwise_allEdgeCurrent m r hdata
  intro w q j
  have hsum : HasDerivAt (fun t : ℝ =>
      ∑ i : Fin (m + 2),
        ((if i.succ = j then
          bindingCatalyticCurrent (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            Fin.castSucc Fin.succ
            (coalescedAllScaledRates m r w).c
            (coalescedAllScaledRates m r w).gamma
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) i else 0) -
         (if i.castSucc = j then
          bindingCatalyticCurrent (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            Fin.castSucc Fin.succ
            (coalescedAllScaledRates m r w).c
            (coalescedAllScaledRates m r w).gamma
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) i else 0)))
      (∑ i : Fin (m + 2),
        ((if i.succ = j then
          w i *
            (coalescedCurrentJacobianMatrix m r).mulVec
              (coalescedInverseResponse m r q) i else 0) -
         (if i.castSucc = j then
          w i *
            (coalescedCurrentJacobianMatrix m r).mulVec
              (coalescedInverseResponse m r q) i else 0))) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    have hcur := hcurrent w q i
    have hright : HasDerivAt (fun t : ℝ =>
        if i.succ = j then
          bindingCatalyticCurrent (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            Fin.castSucc Fin.succ
            (coalescedAllScaledRates m r w).c
            (coalescedAllScaledRates m r w).gamma
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) i else 0)
        (if i.succ = j then
          w i *
            (coalescedCurrentJacobianMatrix m r).mulVec
              (coalescedInverseResponse m r q) i else 0) 0 := by
      by_cases hj : i.succ = j
      · simpa [hj] using hcur
      · simpa [hj] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    have hleft : HasDerivAt (fun t : ℝ =>
        if i.castSucc = j then
          bindingCatalyticCurrent (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            Fin.castSucc Fin.succ
            (coalescedAllScaledRates m r w).c
            (coalescedAllScaledRates m r w).gamma
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) i else 0)
        (if i.castSucc = j then
          w i *
            (coalescedCurrentJacobianMatrix m r).mulVec
              (coalescedInverseResponse m r q) i else 0) 0 := by
      by_cases hj : i.castSucc = j
      · simpa [hj] using hcur
      · simpa [hj] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    exact hright.sub hleft
  simpa only [bindingReducedSlowField_eq_current_sum] using hsum


/-- Pointwise derivative identity from explicit physical source data. -/
theorem paperPointwise_allProjectedFast (m : ℕ) (r : ℝ)
    (hdata : PaperCoalescedPhysicalData m r) :
    ∀ (w : Fin (m + 2) → ℝ) (q : Fin (m + 3) → ℝ),
        (∑ k, q k) = 0 →
        HasDerivAt (fun t : ℝ =>
          (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
            (coalescedAllScaledRates m r w)
            (loadedCoordOfState
              (bindingState (2 * r) 2
                (coalescedBindingP m r) (coalescedBindingQ m r)
                (bindingLinearPath (coalescedFiniteState (m + 1) r).S
                  (coalescedInverseResponse m r q) t)))).2)
          (0 : (Fin (m + 2) → ℝ) × (Fin (m + 2) → ℝ)) 0 := by
  have hC := paperPointwise_projectedFastC m r hdata
  have hD := paperPointwise_projectedFastD m r hdata
  intro w q hq
  have hc : HasDerivAt (fun t : ℝ =>
      (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
        (coalescedAllScaledRates m r w)
        (loadedCoordOfState
          (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t)))).2.1)
      (0 : Fin (m + 2) → ℝ) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    have h := (hC q hq i).const_mul (w i)
    convert h using 1 <;>
      simp only [coalescedAllScaledRates,
        edgeScaledRates_loadedRestrictedField_C, mul_zero, Pi.zero_apply]
  have hd : HasDerivAt (fun t : ℝ =>
      (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
        (coalescedAllScaledRates m r w)
        (loadedCoordOfState
          (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t)))).2.2)
      (0 : Fin (m + 2) → ℝ) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    have h := (hD q i).const_mul (w i)
    convert h using 1 <;>
      simp only [coalescedAllScaledRates,
        edgeScaledRates_loadedRestrictedField_D, mul_zero, Pi.zero_apply]
  convert hc.prodMk hd using 1


/-- Pointwise derivative identity from explicit physical source data. -/
theorem paperPointwise_allLoadedFderiv (m : ℕ) (r : ℝ)
    (hdata : PaperCoalescedPhysicalData m r) :
    ∀ (w : Fin (m + 2) → ℝ) (q : Fin (m + 3) → ℝ),
        (∑ k, q k) = 0 →
        fderiv ℝ
          (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
            (coalescedAllScaledRates m r w))
          (loadedCoordOfState (coalescedFiniteState (m + 1) r))
          (coalescedBindingCoordTangent m r q) =
            (coalescedAllInverseSlowAction m r w q,
              (0 : (Fin (m + 2) → ℝ) × (Fin (m + 2) → ℝ))) := by
  have hcoord := paperPointwise_loadedCoordPath m r hdata
  have hfast := paperPointwise_allProjectedFast m r hdata
  have hslow := paperPointwise_allReducedSlow m r hdata
  have hstate := paperPointwise_bindingState m r hdata
  intro w q hq
  let u : ℝ → CoordinateSpace (m + 2) := fun t =>
    loadedCoordOfState (bindingState (2 * r) 2
      (coalescedBindingP m r) (coalescedBindingQ m r)
      (bindingLinearPath (coalescedFiniteState (m + 1) r).S
        (coalescedInverseResponse m r q) t))
  have hpath0 : bindingLinearPath (coalescedFiniteState (m + 1) r).S
      (coalescedInverseResponse m r q) 0 =
        (coalescedFiniteState (m + 1) r).S := by
    funext j
    simp [bindingLinearPath]
  have hbase : u 0 =
      loadedCoordOfState (coalescedFiniteState (m + 1) r) := by
    change loadedCoordOfState (bindingState (2 * r) 2
      (coalescedBindingP m r) (coalescedBindingQ m r)
      (bindingLinearPath (coalescedFiniteState (m + 1) r).S
        (coalescedInverseResponse m r q) 0)) = _
    rw [hpath0, hstate]
  have hpath : HasDerivAt u (coalescedBindingCoordTangent m r q) 0 :=
    hcoord q
  have hfield : HasDerivAt (fun t : ℝ =>
      loadedRestrictedField (2 * r) 2 (2 * (r + 1))
        (coalescedAllScaledRates m r w) (u t))
      (fderiv ℝ
        (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
          (coalescedAllScaledRates m r w))
        (u 0) (coalescedBindingCoordTangent m r q)) 0 := by
    simpa only [Function.comp_def] using
      (((differentiable_loadedRestrictedField (2 * r) 2 (2 * (r + 1))
        (coalescedAllScaledRates m r w)).differentiableAt
        (x := u 0)).hasFDerivAt.comp_hasDerivAt 0 hpath)
  have hs : HasDerivAt (fun t : ℝ =>
      (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
        (coalescedAllScaledRates m r w) (u t)).1)
      (coalescedAllInverseSlowAction m r w q) 0 := by
    apply hasDerivAt_pi.mpr
    intro j
    simpa only [u, coalescedAllInverseSlowAction,
      loadedRestrictedField_bindingState_slow] using
        hslow w q j.succ
  have hf : HasDerivAt (fun t : ℝ =>
      (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
        (coalescedAllScaledRates m r w) (u t)).2)
      (0 : (Fin (m + 2) → ℝ) × (Fin (m + 2) → ℝ)) 0 := by
    simpa only [u] using hfast w q hq
  have hboth : HasDerivAt (fun t : ℝ =>
      loadedRestrictedField (2 * r) 2 (2 * (r + 1))
        (coalescedAllScaledRates m r w) (u t))
      (coalescedAllInverseSlowAction m r w q,
        (0 : (Fin (m + 2) → ℝ) × (Fin (m + 2) → ℝ))) 0 := by
    simpa using hs.prodMk hf
  have heq := hfield.unique hboth
  rw [hbase] at heq
  exact heq


/-- Pointwise derivative identity from explicit physical source data. -/
theorem paperPointwise_fixedBindingSchur_action (m : ℕ) (r : ℝ)
    (hdata : PaperCoalescedPhysicalData m r) :
    ∀ w : Fin (m+2) → ℝ, (∀ i, 0 < w i) →
        let u := loadedCoordOfState (coalescedFiniteState (m+1) r)
        let k := paperFixedBindingRates (coalescedAllScaledRates m r w)
        let x := stateFromLoaded (2*r) 2 (2*(r+1)) u
        ∀ (hpos : x.Positive) (_heq : Equilibrium k x)
          (hρ : ∀ j : Fin (m+2), 0 < k.a j*x.S j.castSucc*x.E)
          (hσ : ∀ j : Fin (m+2), 0 < k.alpha j*x.S j.succ*x.F)
          (q : Fin (m+3) → ℝ), (∑ j, q j)=0 →
          schurLinear
            (loadedBlockA (2*r) 2 (2*(r+1)) k u).toLinearMap
            (loadedBlockB (2*r) 2 (2*(r+1)) k u).toLinearMap
            (loadedBlockC (2*r) 2 (2*(r+1)) k u).toLinearMap
            (fastBindingEquiv x hpos
              (fun j => k.a j*x.S j.castSucc*x.E)
              (fun j => k.alpha j*x.S j.succ*x.F) hρ hσ)
            (coalescedBindingCoordTangent m r q).1 =
              coalescedAllInverseSlowAction m r w q := by
  have haction := paperPointwise_allLoadedFderiv m r hdata
  have hsource (w : Fin (m+2) → ℝ) (hw : ∀ i, 0 < w i) :
      (coalescedAllScaledRates m r w).Positive :=
    edgeScaledRates_positive w (coalescedFiniteRates (m+1) r) hw hdata.ratesPositive
  intro w hw u k x hpos heq hρ hσ q hq
  have hbasepos := hsource w hw
  let v := coalescedBindingCoordTangent m r q
  have hbase := haction w q hq
  have hpaper := paperFixedBindingRates_loadedFderiv_fastZero
    (2*r) 2 (2*(r+1)) (coalescedAllScaledRates m r w)
    hbasepos u v (coalescedAllInverseSlowAction m r w q) hbase
  have hblock := loadedFderiv_block_action
    (2*r) 2 (2*(r+1)) k u v.1 v.2
  have hv : (v.1, v.2) = v := by cases v; rfl
  rw [hv] at hblock
  change fderiv ℝ (loadedRestrictedField (2*r) 2 (2*(r+1)) k)
      u v = (coalescedAllInverseSlowAction m r w q,
        (0 : (Fin (m+2) → ℝ) × (Fin (m+2) → ℝ))) at hpaper
  rw [hblock] at hpaper
  have hslow := congrArg Prod.fst hpaper
  have hfast := congrArg Prod.snd hpaper
  have hSchur := loadedSchur_action_of_fast_zero
    (2*r) 2 (2*(r+1)) k u hpos heq hρ hσ v.1 v.2 hfast
  dsimp only [Prod.fst] at hslow
  rw [hslow] at hSchur
  exact hSchur


/-- Pointwise derivative identity from explicit physical source data. -/
theorem paperPointwise_fixedBindingSchur_intertwining (m : ℕ) (r : ℝ)
    (hdata : PaperCoalescedPhysicalData m r) :
    ∀ w : Fin (m+2) → ℝ, (∀ i, 0 < w i) →
        let u := loadedCoordOfState (coalescedFiniteState (m+1) r)
        let k := paperFixedBindingRates (coalescedAllScaledRates m r w)
        let x := stateFromLoaded (2*r) 2 (2*(r+1)) u
        ∀ (hpos : x.Positive) (_heq : Equilibrium k x)
          (hρ : ∀ j : Fin (m+2), 0 < k.a j*x.S j.castSucc*x.E)
          (hσ : ∀ j : Fin (m+2), 0 < k.alpha j*x.S j.succ*x.F)
          (z : Fin (m+2) → ℝ),
          schurLinear
            (loadedBlockA (2*r) 2 (2*(r+1)) k u).toLinearMap
            (loadedBlockB (2*r) 2 (2*(r+1)) k u).toLinearMap
            (loadedBlockC (2*r) 2 (2*(r+1)) k u).toLinearMap
            (fastBindingEquiv x hpos
              (fun j => k.a j*x.S j.castSucc*x.E)
              (fun j => k.alpha j*x.S j.succ*x.F) hρ hσ)
            ((projectedPathIncidence (m+2)).mulVec z) =
              (projectedPathIncidence (m+2)).mulVec
                ((Matrix.diagonal w * coalescedFullLoadedMatrix m r).mulVec z) := by
  have haction := paperPointwise_fixedBindingSchur_action m r hdata
  intro w hw u k x hpos heq hρ hσ z
  have h := haction w hw hpos heq hρ hσ
    ((coalescedFullEdgeForcingMatrix m).mulVec z)
    (coalescedFullEdgeForcing_sum_zero m z)
  rw [coalescedBindingCoordTangent_fullEdge_slow,
    coalescedAllInverseSlowAction_fullEdge] at h
  rw [map_smul] at h
  exact (smul_right_injective (Fin (m+2) → ℝ) hdata.sourceNeZero) h


/-- Pointwise derivative identity from explicit physical source data. -/
theorem paperPointwise_fixedBindingSchur_charpoly (m : ℕ) (r : ℝ)
    (hdata : PaperCoalescedPhysicalData m r) :
    ∀ w : Fin (m+2) → ℝ, (∀ i, 0 < w i) →
        let u := loadedCoordOfState (coalescedFiniteState (m+1) r)
        let k := paperFixedBindingRates (coalescedAllScaledRates m r w)
        let x := stateFromLoaded (2*r) 2 (2*(r+1)) u
        ∀ (hpos : x.Positive) (_heq : Equilibrium k x)
          (hρ : ∀ j : Fin (m+2), 0 < k.a j*x.S j.castSucc*x.E)
          (hσ : ∀ j : Fin (m+2), 0 < k.alpha j*x.S j.succ*x.F),
          (schurLinear
            (loadedBlockA (2*r) 2 (2*(r+1)) k u).toLinearMap
            (loadedBlockB (2*r) 2 (2*(r+1)) k u).toLinearMap
            (loadedBlockC (2*r) 2 (2*(r+1)) k u).toLinearMap
            (fastBindingEquiv x hpos
              (fun j => k.a j*x.S j.castSucc*x.E)
              (fun j => k.alpha j*x.S j.succ*x.F) hρ hσ)).charpoly =
            (coalescedFullLoadedMatrix m r * Matrix.diagonal w).charpoly := by
  have hinter := paperPointwise_fixedBindingSchur_intertwining m r hdata
  intro w hw u k x hpos heq hρ hσ
  have hchar := charpoly_of_matrix_intertwining
    (schurLinear
      (loadedBlockA (2*r) 2 (2*(r+1)) k u).toLinearMap
      (loadedBlockB (2*r) 2 (2*(r+1)) k u).toLinearMap
      (loadedBlockC (2*r) 2 (2*(r+1)) k u).toLinearMap
      (fastBindingEquiv x hpos
        (fun j => k.a j*x.S j.castSucc*x.E)
        (fun j => k.alpha j*x.S j.succ*x.F) hρ hσ))
    (projectedPathIncidence (m+2))
    (Matrix.diagonal w * coalescedFullLoadedMatrix m r)
    (projectedPathIncidence_isUnit (m+2))
    (hinter w hw hpos heq hρ hσ)
  calc
    _ = (Matrix.diagonal w * coalescedFullLoadedMatrix m r).charpoly := hchar
    _ = (coalescedFullLoadedMatrix m r * Matrix.diagonal w).charpoly :=
      Matrix.charpoly_mul_comm (Matrix.diagonal w) (coalescedFullLoadedMatrix m r)


end

end PhosphorylationStableCapacity

