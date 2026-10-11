module
public import proofs.PhosphorylationStableCapacity.CoalescedCurrentDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- The literal catalytic-current derivative matrix in logarithmic
free-substrate coordinates, on all edges of the coalesced source. -/
def coalescedCurrentJacobianMatrix (m : ℕ) (r : ℝ) :
    Matrix (Fin (m + 2)) (Fin (m + 3)) ℝ :=
  fun i k => (coalescedFiniteState (m + 1) r).D i *
    ((if k = i.castSucc then 1 else 0) -
      (if k = i.succ then 1 else 0) +
      (coalescedFiniteYLevel m r k / 2 -
        coalescedFiniteCLevel m r k / (2 * r)))

/-- Matrix multiplication reproduces the exact loaded-feedback current
action on every free-substrate logarithmic tangent. -/
theorem coalescedCurrentJacobianMatrix_mulVec (m : ℕ) (r : ℝ)
    (σ : Fin (m + 3) → ℝ) (i : Fin (m + 2)) :
    (coalescedCurrentJacobianMatrix m r).mulVec σ i =
      (coalescedFiniteState (m + 1) r).D i *
        (σ i.castSucc - σ i.succ +
          ∑ k : Fin (m + 3),
            (coalescedFiniteYLevel m r k / 2 -
              coalescedFiniteCLevel m r k / (2 * r)) * σ k) := by
  classical
  have hdelta (a : Fin (m + 3)) :
      (∑ k : Fin (m + 3),
        (if k = a then (1 : ℝ) else 0) * σ k) = σ a := by
    simp
  unfold coalescedCurrentJacobianMatrix Matrix.mulVec dotProduct
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [add_mul, sub_mul]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    hdelta i.castSucc, hdelta i.succ]

/-- The weighted feedback sum is the common term of the exact catalytic
current derivative. -/
theorem coalescedCurrentJacobianFeedback_sum (m : ℕ) (r : ℝ)
    (σ : Fin (m + 3) → ℝ) :
    (∑ k : Fin (m + 3),
      (coalescedFiniteYLevel m r k / 2 -
        coalescedFiniteCLevel m r k / (2 * r)) * σ k) =
      (∑ k : Fin (m + 3),
        coalescedFiniteYLevel m r k * σ k) / 2 -
      (∑ k : Fin (m + 3),
        coalescedFiniteCLevel m r k * σ k) / (2 * r) := by
  simp_rw [sub_mul, div_mul_eq_mul_div]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]

/-- At a positive balanced source equilibrium the literal catalytic
current derivative is the matrix action above. -/
theorem coalescedCatalyticCurrent_hasDerivAt_matrix
    (m : ℕ) (r : ℝ) (σ : Fin (m + 3) → ℝ) (i : Fin (m + 2))
    (hpos : (coalescedFiniteState (m + 1) r).Positive)
    (hC : (∑ j : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).C j) = 2 * r - 1)
    (hD : (∑ j : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).D j) = 1)
    (hr : r ≠ 0) :
    HasDerivAt (fun t : ℝ =>
      bindingCatalyticCurrent (2 * r) 2
        (coalescedBindingP m r) (coalescedBindingQ m r)
        Fin.castSucc Fin.succ
        (coalescedFiniteRates (m + 1) r).c
        (coalescedFiniteRates (m + 1) r).gamma
        (bindingLinearPath (coalescedFiniteState (m + 1) r).S σ t) i)
      ((coalescedCurrentJacobianMatrix m r).mulVec σ i) 0 := by
  have h := coalescedCatalyticCurrent_hasDerivAt_D_weight
    m r σ i hpos hC hD hr
  rw [coalescedCurrentJacobianMatrix_mulVec,
    coalescedCurrentJacobianFeedback_sum]
  convert h using 1
  ring

end
end PhosphorylationStableCapacity
