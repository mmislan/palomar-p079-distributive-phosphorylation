module
public import proofs.PhosphorylationStableCapacity.SourceProjectedFastDerivative
public import proofs.PhosphorylationStableCapacity.LoadedProjectionSlowField

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The projected path incidence is the literal incoming-minus-outgoing
edge-current assembly on each nonzero loaded level. -/
theorem projectedPathIncidence_mulVec_eq_current_sum {n : ℕ}
    (z : Fin n → ℝ) (i : Fin n) :
    (projectedPathIncidence n).mulVec z i =
      ∑ e : Fin n,
        ((if e.succ = i.succ then z e else 0) -
          (if e.castSucc = i.succ then z e else 0)) := by
  simp [projectedPathIncidence, pathIncidence, Matrix.mulVec,
    dotProduct, Finset.sum_sub_distrib, sub_mul]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : i.succ = e.castSucc
  · simp only [h, reduceIte]
  · have h' : e.castSucc ≠ i.succ := fun h' => h h'.symm
    simp only [h, h', reduceIte]

theorem equilibrium_sourceProjectedSlow_hasDerivAt {n : ℕ}
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
          (bindingLinearPath x.S σ t)))).1 i)
      ((projectedPathIncidence n).mulVec
        (fun e => sourceConstrainedCurrentDerivative k x e j) i) 0 := by
  dsimp only
  let A := (totalAndLevelOutputMatrix n) *
    loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
      (totalE x) (totalF x)
  let σ := firstPivotFixedTangent A j
  let current (t : ℝ) (e : Fin n) :=
    bindingCatalyticCurrent (totalE x) (totalF x)
      (sourceBindingP k) (sourceBindingQ k)
      Fin.castSucc Fin.succ k.c k.gamma
      (bindingLinearPath x.S σ t) e
  have hsum : HasDerivAt (fun t : ℝ =>
      ∑ e : Fin n,
        ((if e.succ = i.succ then current t e else 0) -
          (if e.castSucc = i.succ then current t e else 0)))
      (∑ e : Fin n,
        ((if e.succ = i.succ then
            sourceConstrainedCurrentDerivative k x e j else 0) -
          (if e.castSucc = i.succ then
            sourceConstrainedCurrentDerivative k x e j else 0))) 0 := by
    apply HasDerivAt.fun_sum
    intro e _
    have hcur := equilibrium_sourceConstrainedCurrentDerivative_hasDerivAt
      k x hk hx heq e j
    have hright : HasDerivAt (fun t : ℝ =>
        if e.succ = i.succ then current t e else 0)
        (if e.succ = i.succ then
          sourceConstrainedCurrentDerivative k x e j else 0) 0 := by
      by_cases h : e.succ = i.succ
      · simpa [h, current] using hcur
      · simpa [h] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    have hleft : HasDerivAt (fun t : ℝ =>
        if e.castSucc = i.succ then current t e else 0)
        (if e.castSucc = i.succ then
          sourceConstrainedCurrentDerivative k x e j else 0) 0 := by
      by_cases h : e.castSucc = i.succ
      · simpa [h, current] using hcur
      · simpa [h] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    exact hright.sub hleft
  simpa only [loadedRestrictedField_bindingState_slow,
    bindingReducedSlowField_eq_current_sum,
    projectedPathIncidence_mulVec_eq_current_sum] using hsum

end
end PhosphorylationStableCapacity
