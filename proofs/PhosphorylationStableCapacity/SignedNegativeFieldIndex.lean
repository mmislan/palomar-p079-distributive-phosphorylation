module
public import proofs.PhosphorylationStableCapacity.SplitDeterminantSlowSign

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness

/-- The regular zero's signed index for the *negative* restricted
class field, using the actual ordered class Jacobian. The exponent is
the cardinality of its coordinate basis, namely `3n`. -/
def signedNegativeFieldIndex {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (z : State n) : ℤ :=
  if 0 < (-1 : ℝ) ^
      Fintype.card (Fin n ⊕ (Fin n ⊕ Fin n)) *
      (restrictedJacobianMatrix ET FT ST k
        (toCoordinateSpace (chart z))).det
  then 1 else -1

theorem signedNegativeFieldIndex_eq_neg_matrix_det {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (z : State n) :
    signedNegativeFieldIndex ET FT ST k z =
      (if 0 < (-(restrictedJacobianMatrix ET FT ST k
        (toCoordinateSpace (chart z)))).det then 1 else -1) := by
  simp only [signedNegativeFieldIndex, Matrix.det_neg]

theorem signedNegativeFieldIndex_eq_one_or_neg_one {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (z : State n) :
    signedNegativeFieldIndex ET FT ST k z = 1 ∨
      signedNegativeFieldIndex ET FT ST k z = -1 := by
  unfold signedNegativeFieldIndex
  split_ifs <;> simp

/-- Fixes the orientation convention against the already verified
Hurwitz determinant-sign theorem. -/
theorem signedNegativeFieldIndex_of_hurwitz {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (z : State n)
    (hHurwitz : IsHurwitz (restrictedJacobianMatrix ET FT ST k
      (toCoordinateSpace (chart z)))) :
    signedNegativeFieldIndex ET FT ST k z = 1 := by
  unfold signedNegativeFieldIndex
  have hpos := isHurwitz_parity_det_pos _ hHurwitz
  split_ifs
  all_goals simp_all

end
end PhosphorylationStableCapacity
