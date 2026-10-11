module
public import proofs.PhosphorylationStableCapacity.PositiveTotalSchur
public import proofs.PhosphorylationStableCapacity.BoundaryEquilibrium

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The literal positive equilibrium supplies the balanced-edge current
derivative on its fixed-enzyme-total binding manifold. -/
theorem equilibrium_bindingCatalyticCurrent_hasDerivAt_kinetic {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x)
    (σ : Fin (n+1) → ℝ) (i : Fin n) :
    HasDerivAt (fun t : ℝ =>
      bindingCatalyticCurrent (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k)
        Fin.castSucc Fin.succ k.c k.gamma
        (bindingLinearPath x.S σ t) i)
      (k.c i * x.C i *
        (σ i.castSucc - σ i.succ +
          (∑ j, sourceLevelD x j * σ j) / totalF x -
          (∑ j, sourceLevelC x j * σ j) / totalE x)) 0 := by
  have hstate := equilibrium_bindingState_eq_source k x hk hx heq
  have hC (j : Fin n) :
      bindingComplex (totalE x) (sourceBindingP k) x.S j.castSucc =
        x.C j := by
    have h := congrArg (fun y : State n => y.C j) hstate
    exact h
  have hD (j : Fin n) :
      bindingComplex (totalF x) (sourceBindingQ k) x.S j.succ =
        x.D j := by
    have h := congrArg (fun y : State n => y.D j) hstate
    exact h
  have hCall : bindingComplex (totalE x) (sourceBindingP k) x.S =
      sourceLevelC x := by
    funext j
    cases j using Fin.lastCases with
    | last => simp [bindingComplex, sourceBindingP, sourceLevelC_last]
    | cast i => simpa [sourceLevelC_castSucc] using hC i
  have hDall : bindingComplex (totalF x) (sourceBindingQ k) x.S =
      sourceLevelD x := by
    funext j
    cases j using Fin.cases with
    | zero => simp [bindingComplex, sourceBindingQ, sourceLevelD_zero]
    | succ i => simpa [sourceLevelD_succ] using hD i
  have hE := congrArg (fun y : State n => y.E) hstate
  have hF := congrArg (fun y : State n => y.F) hstate
  have hdenP : bindingDenominator (sourceBindingP k) x.S ≠ 0 := by
    intro hden
    simp [bindingState, hden] at hE
    linarith [hx.2.1]
  have hdenQ : bindingDenominator (sourceBindingQ k) x.S ≠ 0 := by
    intro hden
    simp [bindingState, hden] at hF
    linarith [hx.2.2.1]
  have hET : 0 < totalE x := by
    simp [totalE]
    exact add_pos_of_pos_of_nonneg hx.2.1
      (Finset.sum_nonneg fun j _ => (hx.2.2.2.1 j).le)
  have hFT : 0 < totalF x := by
    simp [totalF]
    exact add_pos_of_pos_of_nonneg hx.2.2.1
      (Finset.sum_nonneg fun j _ => (hx.2.2.2.2 j).le)
  have h := bindingCatalyticCurrent_hasDerivAt_linearPath
    (totalE x) (totalF x) (sourceBindingP k) (sourceBindingQ k)
    x.S σ Fin.castSucc Fin.succ k.c k.gamma
    (fun j => k.c j * x.C j) i
    (ne_of_gt hET) (ne_of_gt hFT) hdenP hdenQ
    (by rw [hC i])
    (by rw [hD i]; exact (equilibrium_catalytic_balance k x heq i).symm)
  simpa only [hCall, hDall] using h

end
end PhosphorylationStableCapacity
