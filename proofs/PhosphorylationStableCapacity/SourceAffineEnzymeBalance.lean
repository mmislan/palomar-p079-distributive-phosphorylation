module
public import proofs.PhosphorylationStableCapacity.SourceAugmentedAffineOrientation

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Matrix

theorem sourceLevelC_weighted_sum {n : ℕ}
    (x : State n) (σ : Fin (n+1) → ℝ) :
    (∑ j, sourceLevelC x j * σ j) =
      ∑ i : Fin n, x.C i * σ i.castSucc := by
  simp [sourceLevelC, Finset.sum_comm, Finset.sum_mul]

theorem sourceLevelD_weighted_sum {n : ℕ}
    (x : State n) (σ : Fin (n+1) → ℝ) :
    (∑ j, sourceLevelD x j * σ j) =
      ∑ i : Fin n, x.D i * σ i.succ := by
  simp [sourceLevelD, Finset.sum_comm, Finset.sum_mul]

/-- Fixed kinase and phosphatase totals along an affine monomial
source tangent force the same scalar kernel relation as the literal
balanced-edge current derivative. -/
theorem source_affine_current_kernel_of_enzyme_balances {n : ℕ}
    (x : State n) (hx : x.Positive) (a b z : ℝ)
    (hE : totalE x * (b + z) +
      ∑ i : Fin n, x.C i * sourceAffineLogTangent a b i.castSucc = 0)
    (hF : totalF x * z +
      ∑ i : Fin n, x.D i * sourceAffineLogTangent a b i.succ = 0) :
    a * (∑ j : Fin (n+1), sourceOccupancyDifference x j) +
      b * (sourceOccupancyFirstMoment x - 1) = 0 := by
  let σ : Fin (n+1) → ℝ := sourceAffineLogTangent a b
  have hET : totalE x ≠ 0 := by
    apply ne_of_gt
    simp [totalE]
    exact add_pos_of_pos_of_nonneg hx.2.1
      (Finset.sum_nonneg fun i _ => (hx.2.2.2.1 i).le)
  have hFT : totalF x ≠ 0 := by
    apply ne_of_gt
    simp [totalF]
    exact add_pos_of_pos_of_nonneg hx.2.2.1
      (Finset.sum_nonneg fun i _ => (hx.2.2.2.2 i).le)
  have hC : (∑ i : Fin n, x.C i * σ i.castSucc) / totalE x =
      -(b + z) := by
    apply (div_eq_iff hET).2
    dsimp [σ] at hE ⊢
    linear_combination hE
  have hD : (∑ i : Fin n, x.D i * σ i.succ) / totalF x =
      -z := by
    apply (div_eq_iff hFT).2
    dsimp [σ] at hF ⊢
    linear_combination hF
  have hdot :
      (∑ j : Fin (n+1), sourceOccupancyDifference x j * σ j) = b := by
    simp only [sourceOccupancyDifference, sub_mul,
      Finset.sum_sub_distrib]
    have hds :
        (∑ j : Fin (n+1), sourceLevelD x j / totalF x * σ j) =
          (∑ j, sourceLevelD x j * σ j) / totalF x := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hcs :
        (∑ j : Fin (n+1), sourceLevelC x j / totalE x * σ j) =
          (∑ j, sourceLevelC x j * σ j) / totalE x := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hds, hcs, sourceLevelD_weighted_sum,
      sourceLevelC_weighted_sum, hD, hC]
    ring
  rw [sourceOccupancyDifference_affine_sum] at hdot
  linarith

end
end PhosphorylationStableCapacity
