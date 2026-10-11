module
public import proofs.PhosphorylationStableCapacity.SourceAffineCurrentKernel

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The balanced-current derivative on an affine log-substrate tangent
has one common scalar bracket on every catalytic edge. -/
theorem sourceCurrentLogMatrix_affine_action {n : ℕ}
    (k : Rates n) (x : State n) (a b : ℝ) (i : Fin n) :
    (sourceCurrentLogMatrix k x).mulVec
      (sourceAffineLogTangent a b) i =
      k.c i * x.C i *
        (a * (∑ j : Fin (n+1), sourceOccupancyDifference x j) +
          b * (sourceOccupancyFirstMoment x - 1)) := by
  let σ : Fin (n+1) → ℝ := sourceAffineLogTangent a b
  have hD :
      (∑ j, sourceLevelD x j * σ j) / totalF x =
      ∑ j, sourceLevelD x j / totalF x * σ j := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hC :
      (∑ j, sourceLevelC x j * σ j) / totalE x =
      ∑ j, sourceLevelC x j / totalE x * σ j := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsum :
      (∑ j, sourceLevelD x j * σ j) / totalF x -
        (∑ j, sourceLevelC x j * σ j) / totalE x =
      ∑ j, sourceOccupancyDifference x j * σ j := by
    rw [hD, hC]
    simp only [sourceOccupancyDifference, sub_mul,
      Finset.sum_sub_distrib]
  have hdiff : σ i.castSucc - σ i.succ = -b := by
    simp [σ, sourceAffineLogTangent]
    ring
  rw [sourceCurrentLogMatrix_mulVec]
  change k.c i * x.C i *
    (σ i.castSucc - σ i.succ +
      (∑ j, sourceLevelD x j * σ j) / totalF x -
      (∑ j, sourceLevelC x j * σ j) / totalE x) = _
  rw [hdiff]
  calc
    k.c i * x.C i *
        (-b + (∑ j, sourceLevelD x j * σ j) / totalF x -
          (∑ j, sourceLevelC x j * σ j) / totalE x) =
      k.c i * x.C i *
        (-b + ((∑ j, sourceLevelD x j * σ j) / totalF x -
          (∑ j, sourceLevelC x j * σ j) / totalE x)) := by ring
    _ = k.c i * x.C i *
        (-b + ∑ j, sourceOccupancyDifference x j * σ j) := by
          rw [hsum]
    _ = _ := by
      rw [sourceOccupancyDifference_affine_sum x a b]
      ring

/-- The common scalar bracket is the exact condition for an affine
log-substrate direction to lie in every current equation's kernel. -/
theorem sourceCurrentLogMatrix_affine_kernel {n : ℕ}
    (k : Rates n) (x : State n) (a b : ℝ)
    (h : a * (∑ j : Fin (n+1), sourceOccupancyDifference x j) +
      b * (sourceOccupancyFirstMoment x - 1) = 0) :
    (sourceCurrentLogMatrix k x).mulVec
      (sourceAffineLogTangent a b) = 0 := by
  funext i
  rw [sourceCurrentLogMatrix_affine_action, h]
  simp

end
end PhosphorylationStableCapacity
