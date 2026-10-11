module
public import proofs.PhosphorylationStableCapacity.SourceBindingCurrentDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Literal catalytic-current derivative on the first-order fixed-total
binding chart, with columns indexed by the nonzero free-substrate levels. -/
def sourceConstrainedCurrentDerivative {n : ℕ}
    (k : Rates n) (x : State n) : Matrix (Fin n) (Fin n) ℝ :=
  let A := (totalAndLevelOutputMatrix n) *
    loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
      (totalE x) (totalF x)
  fun i j =>
    let σ := firstPivotFixedTangent A j
    k.c i * x.C i *
      (σ i.castSucc - σ i.succ +
        (∑ l, sourceLevelD x l * σ l) / totalF x -
        (∑ l, sourceLevelC x l * σ l) / totalE x)

/-- Each entry is the actual catalytic-current derivative along its
compensated substrate direction at a positive literal equilibrium. -/
theorem equilibrium_sourceConstrainedCurrentDerivative_hasDerivAt {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) (i j : Fin n) :
    let A := (totalAndLevelOutputMatrix n) *
      loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
        (totalE x) (totalF x)
    let σ := firstPivotFixedTangent A j
    HasDerivAt (fun t : ℝ =>
      bindingCatalyticCurrent (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k)
        Fin.castSucc Fin.succ k.c k.gamma
        (bindingLinearPath x.S σ t) i)
      (sourceConstrainedCurrentDerivative k x i j) 0 := by
  exact equilibrium_bindingCatalyticCurrent_hasDerivAt_kinetic
    k x hk hx heq _ i

theorem sourceCatalyticEdgeWeight_pos {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive) (i : Fin n) :
    0 < k.c i * x.C i :=
  mul_pos (hk i).2.2.1 (hx.2.2.2.1 i)

end
end PhosphorylationStableCapacity
