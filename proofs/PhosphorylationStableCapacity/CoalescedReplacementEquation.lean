module
public import proofs.PhosphorylationStableCapacity.CoalescedReplacementRows
public import proofs.PhosphorylationStableCapacity.CoalescedInverseModeRows

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- The right-hand side after replacing the dependent occupied row by the
total inventory row and retaining the final mass row. -/
def coalescedReplacementTarget (m : ℕ)
    (q : Fin (m + 3) → ℝ) : Fin (m + 3) → ℝ :=
  fun i => if i.val < m + 1 then q i else 0

theorem coalescedReplacementMass_prefix_action
    (m : ℕ) (r : ℝ) (σ : Fin (m + 3) → ℝ)
    (i : Fin (m + 1)) :
    (coalescedReplacementMass m r).mulVec σ i.castSucc.castSucc =
      (coalescedFullMass m r).mulVec σ i.castSucc.castSucc / r := by
  simp only [Matrix.mulVec, dotProduct,
    coalescedReplacementMass_prefix_row]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem coalescedReplacementMass_mode_action
    (m : ℕ) (r : ℝ) (σ : Fin (m + 3) → ℝ) :
    (coalescedReplacementMass m r).mulVec σ (coalescedModeRow m) =
      ∑ i : Fin (m + 3), (coalescedFullMass m r).mulVec σ i := by
  simp only [Matrix.mulVec, dotProduct,
    coalescedReplacementMass_mode_row]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

theorem coalescedReplacementMass_final_action
    (m : ℕ) (r : ℝ) (σ : Fin (m + 3) → ℝ) :
    (coalescedReplacementMass m r).mulVec σ (Fin.last (m + 2)) =
      (coalescedFullMass m r).mulVec σ (Fin.last (m + 2)) := by
  simp only [Matrix.mulVec, dotProduct,
    coalescedReplacementMass_final_row]

/-- The actual finite scaled inverse response solves the replacement
system exactly whenever its direction has zero total and zero final entry. -/
theorem coalescedInverseResponse_replacement_equation
    (m : ℕ) (r : ℝ) (q : Fin (m + 3) → ℝ)
    (hqsum : (∑ i : Fin (m + 3), q i) = 0)
    (hqlast : q (Fin.last (m + 2)) = 0)
    (hr : r ≠ 0)
    (hdet : (coalescedFullMass m r).det ≠ 0) :
    (coalescedReplacementMass m r).mulVec
        (coalescedInverseResponse m r q) =
      coalescedReplacementTarget m q := by
  let σ := coalescedInverseResponse m r q
  have hmx := coalescedInverseResponse_mass_equation m r q hdet
  funext i
  by_cases hi : i.val < m + 1
  · let i' : Fin (m + 1) := ⟨i.val, hi⟩
    have heq : i = i'.castSucc.castSucc := by
      apply Fin.ext
      simp [i']
    rw [heq, coalescedReplacementMass_prefix_action]
    have hcoord := congrFun hmx i'.castSucc.castSucc
    rw [hcoord]
    have htarget : coalescedReplacementTarget m q i'.castSucc.castSucc =
        q i'.castSucc.castSucc := by
      simp [coalescedReplacementTarget, i'.isLt]
    rw [htarget]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [hr]
  · by_cases hm : i.val = m + 1
    · have heq : i = coalescedModeRow m := by
        ext
        exact hm
      rw [heq, coalescedReplacementMass_mode_action]
      have hsum : (∑ k : Fin (m + 3),
          (coalescedFullMass m r).mulVec σ k) = 0 := by
        calc
          _ = ∑ k : Fin (m + 3), (r • q) k := by rw [hmx]
          _ = r * (∑ k : Fin (m + 3), q k) := by
            simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          _ = 0 := by rw [hqsum, mul_zero]
      simpa [coalescedReplacementTarget, coalescedModeRow] using hsum
    · have heq : i = Fin.last (m + 2) := by
        ext
        simp [Fin.val_last]
        omega
      rw [heq, coalescedReplacementMass_final_action]
      have hcoord := congrFun hmx (Fin.last (m + 2))
      rw [hcoord]
      simp [coalescedReplacementTarget, Fin.val_last,
        Pi.smul_apply, hqlast]

/-- The exact replacement equation is eventually available on every
literal coalesced source. -/
theorem coalescedInverseResponse_eventually_replacement_equation
    (m : ℕ) (q : Fin (m + 3) → ℝ)
    (hqsum : (∑ i : Fin (m + 3), q i) = 0)
    (hqlast : q (Fin.last (m + 2)) = 0) :
    ∀ᶠ r : ℝ in atTop,
      (coalescedReplacementMass m r).mulVec
        (coalescedInverseResponse m r q) =
          coalescedReplacementTarget m q := by
  filter_upwards [coalescedFullMass_eventually_det_ne_zero m,
    eventually_gt_atTop (0 : ℝ)] with r hdet hr
  exact coalescedInverseResponse_replacement_equation
    m r q hqsum hqlast (ne_of_gt hr) hdet

end
end PhosphorylationStableCapacity
