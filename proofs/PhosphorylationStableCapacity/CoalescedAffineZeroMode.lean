module
public import proofs.PhosphorylationStableCapacity.CoalescedLiteralMassMoments
public import proofs.PhosphorylationStableCapacity.CoalescedCurrentJacobianMatrix

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter

noncomputable section

def coalescedAffineZeroTangent (m : ℕ) (r : ℝ) :
    Fin (m + 3) → ℝ :=
  fun k => (1 - coalescedSourceH1 m r) +
    coalescedSourceH0 r * (k.val : ℝ)

theorem affine_weighted_sum {N : ℕ} (w : Fin N → ℝ)
    (a b : ℝ) :
    (∑ k : Fin N, w k * (a + b * (k.val : ℝ))) =
      a * (∑ k : Fin N, w k) +
        b * (∑ k : Fin N, w k * (k.val : ℝ)) := by
  calc
    _ = ∑ k : Fin N,
        (w k * a + b * (w k * (k.val : ℝ))) := by
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      ring

/-- The explicit affine source tangent kills every row of the literal
all-edge catalytic-current derivative, at sufficiently large finite r. -/
theorem coalescedAffineZeroTangent_eventually_current_zero (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ i : Fin (m + 2),
        (coalescedCurrentJacobianMatrix m r).mulVec
          (coalescedAffineZeroTangent m r) i = 0 := by
  filter_upwards [coalescedLiteralFeedbackMoments_eventually m]
    with r hmoment
  let σ := coalescedAffineZeroTangent m r
  have hfeedback :
      (∑ k : Fin (m + 3),
        coalescedLiteralFeedbackWeight m r k * σ k) =
          coalescedSourceH0 r := by
    rw [show σ = fun k : Fin (m + 3) =>
      (1 - coalescedSourceH1 m r) +
        coalescedSourceH0 r * (k.val : ℝ) from rfl]
    rw [affine_weighted_sum, hmoment.1, hmoment.2]
    ring
  intro i
  rw [coalescedCurrentJacobianMatrix_mulVec]
  change (coalescedFiniteState (m + 1) r).D i *
    (σ i.castSucc - σ i.succ +
      ∑ k : Fin (m + 3),
        coalescedLiteralFeedbackWeight m r k * σ k) = 0
  rw [hfeedback]
  simp only [σ, coalescedAffineZeroTangent,
    Fin.val_castSucc, Fin.val_succ]
  push_cast
  ring

/-- For every source parameter greater than one, the affine zero-current
tangent is nonzero because its adjacent-level slope is nonzero. -/
theorem coalescedAffineZeroTangent_ne_zero (m : ℕ) (r : ℝ)
    (hr : 1 < r) : coalescedAffineZeroTangent m r ≠ 0 := by
  intro hz
  have h0 := congrArg
    (fun f : Fin (m + 3) → ℝ => f ⟨0, by omega⟩) hz
  have h1 := congrArg
    (fun f : Fin (m + 3) → ℝ => f ⟨1, by omega⟩) hz
  simp only [coalescedAffineZeroTangent,
    Nat.cast_zero, mul_zero, add_zero, Pi.zero_apply] at h0
  simp only [coalescedAffineZeroTangent,
    Nat.cast_one, mul_one, Pi.zero_apply] at h1
  have hH0 : coalescedSourceH0 r = 0 := by linarith
  have hnum : 1 - r ≠ 0 := sub_ne_zero.mpr (ne_of_lt hr)
  have hden : 2 * r ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt (lt_trans (by norm_num) hr))
  exact (div_ne_zero hnum hden) (by simpa [coalescedSourceH0] using hH0)

end
end PhosphorylationStableCapacity
