module
public import proofs.PhosphorylationStableCapacity.CoalescedInverseParticular

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Vanishing of the independent prefix rows of the literal limiting
replacement matrix forces a common occupied-level value. -/
theorem coalescedReplacementLimit_prefix_kernel_constant (m : ℕ)
    (x : Fin (m + 3) → ℝ)
    (hx : ∀ k : Fin (m + 1),
      (coalescedReplacementLimit m).mulVec x k.castSucc.castSucc = 0)
    (i : Fin (m + 2)) :
    x i.castSucc =
      (∑ j : Fin (m + 2), coalescedLevelWeight m j.val * x j.castSucc) / 2 := by
  have hsum :
      (∑ j : Fin (m + 3), coalescedFullLevelWeight m j * x j) =
      ∑ j : Fin (m + 2), coalescedLevelWeight m j.val * x j.castSucc := by
    rw [Fin.sum_univ_castSucc]
    have hterms :
        (∑ j : Fin (m + 2),
          coalescedFullLevelWeight m j.castSucc * x j.castSucc) =
        ∑ j : Fin (m + 2),
          coalescedLevelWeight m j.val * x j.castSucc := by
      apply Finset.sum_congr rfl
      intro j _
      simp [coalescedFullLevelWeight, j.isLt]
    rw [hterms]
    simp [coalescedFullLevelWeight, Fin.val_last]
  have hprefix : ∀ k : Fin (m + 1),
      (rankOneMass (fun j : Fin (m + 2) =>
        coalescedLevelWeight m j.val)).mulVec
        (fun j => x j.castSucc) k.castSucc = 0 := by
    intro k
    have hrow := hx k
    have hleading :
        (rankOneMass (coalescedFullLevelWeight m)).mulVec x
          k.castSucc.castSucc = 0 := by
      simpa [coalescedReplacementLimit, Matrix.mulVec, dotProduct,
        k.isLt] using hrow
    rw [rankOneMass_action] at hleading ⊢
    rw [hsum] at hleading
    have hk : k.val < m + 2 := by omega
    simpa [coalescedFullLevelWeight, hk] using hleading
  exact coalescedLeadingMass_prefix_kernel_constant m
    (fun j => x j.castSucc) hprefix i

/-- Equation (5): every limiting replacement-system solution is the
explicit particular vector plus one common occupied-level constant. -/
theorem coalescedReplacementSolution_occupied_formula (m : ℕ)
    (q x : Fin (m + 3) → ℝ)
    (hqsum : (∑ j : Fin (m + 3), q j) = 0)
    (hqlast : q (Fin.last (m + 2)) = 0)
    (hsol : (coalescedReplacementLimit m).mulVec x =
      coalescedReplacementTarget m q)
    (i : Fin (m + 2)) :
    x i.castSucc = q i.castSucc / coalescedLevelWeight m i.val +
      (∑ j : Fin (m + 2), coalescedLevelWeight m j.val *
        (x j.castSucc - coalescedInverseParticular m q j.castSucc)) / 2 := by
  let ξ := x - coalescedInverseParticular m q
  have hprefix : ∀ k : Fin (m + 1),
      (coalescedReplacementLimit m).mulVec ξ k.castSucc.castSucc = 0 := by
    intro k
    have hrow := congrFun hsol k.castSucc.castSucc
    have hpart :
        (coalescedReplacementLimit m).mulVec
          (coalescedInverseParticular m q) k.castSucc.castSucc =
        q k.castSucc.castSucc := by
      simpa [coalescedReplacementLimit, Matrix.mulVec, dotProduct,
        k.isLt] using
        coalescedInverseParticular_leading_action m q hqsum hqlast
          k.castSucc
    have htarget : coalescedReplacementTarget m q k.castSucc.castSucc =
        q k.castSucc.castSucc := by
      simp [coalescedReplacementTarget, k.isLt]
    change (coalescedReplacementLimit m).mulVec
      (x - coalescedInverseParticular m q) k.castSucc.castSucc = 0
    rw [Matrix.mulVec_sub, Pi.sub_apply, hrow, htarget, hpart, sub_self]
  have hi := coalescedReplacementLimit_prefix_kernel_constant m ξ hprefix i
  simp only [ξ, Pi.sub_apply] at hi
  rw [coalescedInverseParticular_occupied] at hi
  linarith

end
end PhosphorylationStableCapacity
