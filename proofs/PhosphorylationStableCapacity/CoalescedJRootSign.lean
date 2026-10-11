module
public import proofs.PhosphorylationStableCapacity.CoalescedJAtNRoots

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The adjacent numerator evaluated at an explicit zero has a signed
trigonometric expression, and hence so does the companion polynomial. -/
theorem coalescedJ_at_N_root_trig (m j : ℕ) (hj : j < m) :
    (12 * (coalescedPair m).2.eval (coalescedRoot m j)) *
        Real.sin (coalescedTheta m j / 2) =
      coalescedLam (coalescedRoot m j) ^ (m + 1) *
        ((-1 : ℝ) ^ (j + 1) * Real.sin (coalescedTheta m j)) := by
  let θ := coalescedTheta m j
  let u := coalescedRoot m j
  have hrneg := coalescedRoot_neg m j hj
  have hune : u ≠ 1 := by dsimp [u]; linarith
  have hkpos : 0 < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hphase : ((2 * m + 1 : ℕ) : ℝ) * θ / 2 =
      ((j + 1 : ℕ) : ℝ) * Real.pi := by
    dsimp [θ, coalescedTheta]
    field_simp [ne_of_gt hkpos]
  have hphaseSucc : ((2 * (m + 1) + 1 : ℕ) : ℝ) * θ / 2 =
      ((j + 1 : ℕ) : ℝ) * Real.pi + θ := by
    rw [← hphase]
    push_cast
    ring
  calc
    (12 * (coalescedPair m).2.eval u) * Real.sin (θ / 2) =
        (coalescedPair (m + 1)).1.eval u * Real.sin (θ / 2) := by
      rw [coalescedJ_at_N_root m j hj]
    _ = coalescedLam u ^ (m + 1) *
          (coalescedChebF (m + 1) (Real.cos θ) * Real.sin (θ / 2)) := by
      rw [coalescedN_cheb_scale (m + 1) u hune,
        coalescedT_root m j hj]
      ring
    _ = coalescedLam u ^ (m + 1) *
          Real.sin (((2 * (m + 1) + 1 : ℕ) : ℝ) * θ / 2) := by
      rw [coalescedChebF_cos]
    _ = coalescedLam u ^ (m + 1) *
          ((-1 : ℝ) ^ (j + 1) * Real.sin θ) := by
      rw [hphaseSucc, Real.sin_add, Real.sin_nat_mul_pi,
        Real.cos_nat_mul_pi]
      ring

end
end PhosphorylationStableCapacity
