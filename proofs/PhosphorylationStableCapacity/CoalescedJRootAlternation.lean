module
public import proofs.PhosphorylationStableCapacity.CoalescedJRootSign

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The companion source polynomial alternates sign at consecutive
numerator roots. This is the endpoint-sign input for interlacing. -/
theorem coalescedJ_at_N_root_alternating (m j : ℕ) (hj : j < m) :
    0 < (-1 : ℝ) ^ (j + 1) *
      (coalescedPair m).2.eval (coalescedRoot m j) := by
  let u := coalescedRoot m j
  let θ := coalescedTheta m j
  have hθ := coalescedTheta_mem_Ioo m j hj
  have hhalf : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by dsimp [θ]; linarith [hθ.1])
      (by dsimp [θ]; linarith [hθ.2, Real.pi_pos])
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hroot := coalescedRoot_neg m j hj
  have hlam : 0 < coalescedLam u := by
    unfold coalescedLam
    dsimp [u]
    linarith
  have hpow : 0 < coalescedLam u ^ (m + 1) := pow_pos hlam _
  have hval := coalescedJ_at_N_root_trig m j hj
  by_cases he : Even (j + 1)
  · have hs : (-1 : ℝ) ^ (j + 1) = 1 := Even.neg_one_pow he
    rw [hs, one_mul] at hval ⊢
    have hprod : 0 < (12 * (coalescedPair m).2.eval u) *
        Real.sin (θ / 2) := by
      rw [hval]
      exact mul_pos hpow hsin
    have := pos_of_mul_pos_left hprod hhalf.le
    linarith
  · have ho : Odd (j + 1) := Nat.not_even_iff_odd.mp he
    have hs : (-1 : ℝ) ^ (j + 1) = -1 := Odd.neg_one_pow ho
    rw [hs] at hval ⊢
    have hprod : (12 * (coalescedPair m).2.eval u) *
        Real.sin (θ / 2) < 0 := by
      rw [hval]
      exact mul_neg_of_pos_of_neg hpow (by linarith)
    have hprod' : 0 < (-(12 * (coalescedPair m).2.eval u)) *
        Real.sin (θ / 2) := by nlinarith [hprod]
    have := pos_of_mul_pos_left hprod' hhalf.le
    nlinarith

end
end PhosphorylationStableCapacity
