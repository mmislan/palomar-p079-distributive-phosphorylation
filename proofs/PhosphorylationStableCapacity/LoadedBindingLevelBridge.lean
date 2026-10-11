module
public import proofs.PhosphorylationStableCapacity.LoadedReducedField

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- With the two absent endpoint complexes zero, the binding-equilibrium
inventory is exactly the loaded-level coordinate of the literal state. -/
theorem loadedLevel_bindingState_eq_bindingLoadedLevel {n : ℕ}
    (ET FT : ℝ) (p q S : Fin (n + 1) → ℝ)
    (hp : bindingComplex ET p S (Fin.last n) = 0)
    (hq : bindingComplex FT q S 0 = 0)
    (j : Fin (n + 1)) :
    loadedLevel (bindingState ET FT p q S) j =
      bindingLoadedLevel ET FT p q S j := by
  have hC :
      (∑ i : Fin n, if i.castSucc = j then
        bindingComplex ET p S i.castSucc else 0) =
          bindingComplex ET p S j := by
    have h : (∑ k : Fin (n + 1), if k = j then
        bindingComplex ET p S k else 0) =
          bindingComplex ET p S j := by simp
    rw [Fin.sum_univ_castSucc] at h
    have hlast :
        (if Fin.last n = j then
          bindingComplex ET p S (Fin.last n) else 0) = 0 := by
      by_cases hj : Fin.last n = j
      · simp only [hj, ↓reduceIte]
        simpa only [hj] using hp
      · simp only [hj, ↓reduceIte]
    simpa only [hlast, add_zero] using h
  have hD :
      (∑ i : Fin n, if i.succ = j then
        bindingComplex FT q S i.succ else 0) =
          bindingComplex FT q S j := by
    have h : (∑ k : Fin (n + 1), if k = j then
        bindingComplex FT q S k else 0) =
          bindingComplex FT q S j := by simp
    rw [Fin.sum_univ_succ] at h
    have hzero :
        (if (0 : Fin (n + 1)) = j then
          bindingComplex FT q S 0 else 0) = 0 := by
      by_cases hj : (0 : Fin (n + 1)) = j
      · simp only [hj, ↓reduceIte]
        simpa only [hj] using hq
      · simp only [hj, ↓reduceIte]
    simpa only [hzero, zero_add] using h
  change S j +
      (∑ i : Fin n, if i.castSucc = j then
        bindingComplex ET p S i.castSucc else 0) +
      (∑ i : Fin n, if i.succ = j then
        bindingComplex FT q S i.succ else 0) =
        S j + bindingComplex ET p S j + bindingComplex FT q S j
  rw [hC, hD]

end
end PhosphorylationStableCapacity
