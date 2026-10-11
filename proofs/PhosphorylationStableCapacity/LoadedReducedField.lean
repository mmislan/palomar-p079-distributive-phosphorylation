module
public import proofs.PhosphorylationStableCapacity.LoadedFieldCurrent
public import proofs.PhosphorylationStableCapacity.LoadedCurrentDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- The reversible binding equilibrium at fixed free-substrate levels and
fixed enzyme totals, with complexes attached to their literal edge species. -/
def bindingState {n : ℕ} (ET FT : ℝ) (p q : Fin (n + 1) → ℝ)
    (S : Fin (n + 1) → ℝ) : State n where
  S := S
  E := ET / bindingDenominator p S
  F := FT / bindingDenominator q S
  C i := bindingComplex ET p S i.castSucc
  D i := bindingComplex FT q S i.succ

/-- The loaded-level velocity obtained by evaluating the literal full field
on the fixed-total binding manifold. -/
def bindingReducedSlowField {n : ℕ} (ET FT : ℝ)
    (p q : Fin (n + 1) → ℝ) (k : Rates n)
    (S : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  loadedLevel (field k (bindingState ET FT p q S)) j

/-- This reduced field is exactly the incidence assembly of the catalytic
currents on the binding manifold, at every substrate state. -/
theorem bindingReducedSlowField_eq_current_sum {n : ℕ}
    (ET FT : ℝ) (p q : Fin (n + 1) → ℝ) (k : Rates n)
    (S : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    bindingReducedSlowField ET FT p q k S j =
      ∑ i : Fin n, (
        (if i.succ = j then
          bindingCatalyticCurrent ET FT p q Fin.castSucc Fin.succ
            k.c k.gamma S i else 0) -
        (if i.castSucc = j then
          bindingCatalyticCurrent ET FT p q Fin.castSucc Fin.succ
            k.c k.gamma S i else 0)) := by
  rw [bindingReducedSlowField, loadedLevel_field_eq_catalytic_flux]
  apply Finset.sum_congr rfl
  intro i _
  simp [bindingState, bindingCatalyticCurrent]

/-- The directional derivative of the literal full field restricted to the
fixed-total binding manifold is the incidence assembly of the balanced edge
derivatives. -/
theorem bindingReducedSlowField_hasDerivAt_linearPath {n : ℕ}
    (ET FT : ℝ) (p q S σ : Fin (n + 1) → ℝ)
    (k : Rates n) (w : Fin n → ℝ) (j : Fin (n + 1))
    (hET : ET ≠ 0) (hFT : FT ≠ 0)
    (hp : bindingDenominator p S ≠ 0)
    (hq : bindingDenominator q S ≠ 0)
    (hbalance : ∀ i : Fin n,
      k.c i * bindingComplex ET p S i.castSucc = w i ∧
        k.gamma i * bindingComplex FT q S i.succ = w i) :
    HasDerivAt (fun t : ℝ =>
      bindingReducedSlowField ET FT p q k (bindingLinearPath S σ t) j)
      (∑ i : Fin n, (
        (if i.succ = j then
          w i * (σ i.castSucc - σ i.succ +
            (∑ l, bindingComplex FT q S l * σ l) / FT -
            (∑ l, bindingComplex ET p S l * σ l) / ET) else 0) -
        (if i.castSucc = j then
          w i * (σ i.castSucc - σ i.succ +
            (∑ l, bindingComplex FT q S l * σ l) / FT -
            (∑ l, bindingComplex ET p S l * σ l) / ET) else 0))) 0 := by
  have hsum : HasDerivAt (fun t : ℝ =>
      ∑ i : Fin n, (
        (if i.succ = j then
          bindingCatalyticCurrent ET FT p q Fin.castSucc Fin.succ
            k.c k.gamma (bindingLinearPath S σ t) i else 0) -
        (if i.castSucc = j then
          bindingCatalyticCurrent ET FT p q Fin.castSucc Fin.succ
            k.c k.gamma (bindingLinearPath S σ t) i else 0)))
      (∑ i : Fin n, (
        (if i.succ = j then
          w i * (σ i.castSucc - σ i.succ +
            (∑ l, bindingComplex FT q S l * σ l) / FT -
            (∑ l, bindingComplex ET p S l * σ l) / ET) else 0) -
        (if i.castSucc = j then
          w i * (σ i.castSucc - σ i.succ +
            (∑ l, bindingComplex FT q S l * σ l) / FT -
            (∑ l, bindingComplex ET p S l * σ l) / ET) else 0))) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    have hcur := bindingCatalyticCurrent_hasDerivAt_linearPath
      ET FT p q S σ Fin.castSucc Fin.succ k.c k.gamma w i
      hET hFT hp hq (hbalance i).1 (hbalance i).2
    have hright : HasDerivAt (fun t : ℝ =>
        if i.succ = j then
          bindingCatalyticCurrent ET FT p q Fin.castSucc Fin.succ
            k.c k.gamma (bindingLinearPath S σ t) i else 0)
        (if i.succ = j then
          w i * (σ i.castSucc - σ i.succ +
            (∑ l, bindingComplex FT q S l * σ l) / FT -
            (∑ l, bindingComplex ET p S l * σ l) / ET) else 0) 0 := by
      by_cases hj : i.succ = j
      · simpa [hj] using hcur
      · simpa [hj] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    have hleft : HasDerivAt (fun t : ℝ =>
        if i.castSucc = j then
          bindingCatalyticCurrent ET FT p q Fin.castSucc Fin.succ
            k.c k.gamma (bindingLinearPath S σ t) i else 0)
        (if i.castSucc = j then
          w i * (σ i.castSucc - σ i.succ +
            (∑ l, bindingComplex FT q S l * σ l) / FT -
            (∑ l, bindingComplex ET p S l * σ l) / ET) else 0) 0 := by
      by_cases hj : i.castSucc = j
      · simpa [hj] using hcur
      · simpa [hj] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    exact hright.sub hleft
  simpa only [bindingReducedSlowField_eq_current_sum] using hsum

end
end PhosphorylationStableCapacity
