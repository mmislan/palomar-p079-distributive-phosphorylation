module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitRootGapParity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Once the relative splitting error is smaller than one, the selected
    real eigenvalue has the opposite sign to the root-gap product. -/
theorem slow_root_sign_of_relative_error
    (N : ℕ) (a K δ gap lam : ℝ)
    (ha : 0 < a) (hδ : 0 < δ) (hsmall : K*|δ| < 1)
    (hbound : |lam / (-a*δ^N*gap)-1| ≤ K*|δ|) :
    (0 < gap → lam < 0) ∧
      (gap < 0 → 0 < lam) := by
  have hquot : 0 < lam / (-a*δ^N*gap) := by
    have hleft := (abs_le.mp hbound).1
    linarith
  have hpow : 0 < δ^N := pow_pos hδ N
  have hpre : -a*δ^N < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hpow
  constructor
  · intro hgap
    have hbase : -a*δ^N*gap < 0 := mul_neg_of_neg_of_pos hpre hgap
    have hident : lam = (lam / (-a*δ^N*gap)) * (-a*δ^N*gap) := by
      exact (div_mul_cancel₀ lam (ne_of_lt hbase)).symm
    rw [hident]
    exact mul_neg_of_pos_of_neg hquot hbase
  · intro hgap
    have hbase : 0 < -a*δ^N*gap := mul_pos_of_neg_of_neg hpre hgap
    have hident : lam = (lam / (-a*δ^N*gap)) * (-a*δ^N*gap) := by
      exact (div_mul_cancel₀ lam (ne_of_gt hbase)).symm
    rw [hident]
    exact mul_pos hquot hbase

end
end PhosphorylationStableCapacity
