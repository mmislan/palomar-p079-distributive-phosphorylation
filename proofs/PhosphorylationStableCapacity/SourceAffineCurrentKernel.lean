module
public import proofs.PhosphorylationStableCapacity.SourceAugmentedCurrentOrientation
public import proofs.PhosphorylationStableCapacity.SourceAugmentedSlopeFactor

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Infinitesimal logarithmic substrate variation along a monomial
equilibrium source chart: a common scale change plus a ratio change. -/
def sourceAffineLogTangent {n : ℕ} (a b : ℝ) :
    Fin (n+1) → ℝ := fun j => a + (j.val : ℝ) * b

def sourceOccupancyFirstMoment {n : ℕ} (x : State n) : ℝ :=
  ∑ j : Fin (n+1), (j.val : ℝ) * sourceOccupancyDifference x j

theorem sourceOccupancyDifference_affine_sum {n : ℕ}
    (x : State n) (a b : ℝ) :
    (∑ j : Fin (n+1), sourceOccupancyDifference x j *
      sourceAffineLogTangent a b j) =
      a * (∑ j : Fin (n+1), sourceOccupancyDifference x j) +
      b * sourceOccupancyFirstMoment x := by
  simp only [sourceAffineLogTangent, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  unfold sourceOccupancyFirstMoment
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

end
end PhosphorylationStableCapacity
