module
public import proofs.PhosphorylationStableCapacity.SplitSlowSignFromRelativeError

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- A relative error at most one half remains first order after taking
    the reciprocal. -/
theorem reciprocal_relative_error_bound
    (x e : ℝ) (he : 0 ≤ e) (hhalf : e ≤ 1/2)
    (hx : |x-1| ≤ e) :
    0 < x ∧ |1/x-1| ≤ 2*e := by
  have hxlo : 1-e ≤ x := by
    have h := (abs_le.mp hx).1
    linarith
  have hxhalf : 1/2 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  refine ⟨hxpos, ?_⟩
  have hident : 1/x-1 = -(x-1)/x := by
    field_simp [ne_of_gt hxpos]
    ring
  rw [hident, abs_div, abs_neg, abs_of_pos hxpos]
  apply (div_le_iff₀ hxpos).mpr
  have hbound : e ≤ 2*e*x := by
    nlinarith [mul_nonneg he (sub_nonneg.mpr hxhalf)]
  exact hx.trans hbound

/-- The slow-root splitting law implies the manuscript's reciprocal
    relaxation-time formula with an explicit multiplicative O(δ) error. -/
theorem slow_mode_reciprocal_first_order_law
    (N : ℕ) (a K δ gap lam : ℝ)
    (ha : 0 < a) (hδ : 0 < δ) (hgap : gap ≠ 0)
    (hK : 0 ≤ K) (hsmall : K*|δ| ≤ 1/2)
    (hrelative : |lam / (-a*δ^N*gap)-1| ≤ K*|δ|) :
    ∃ err : ℝ,
      |err| ≤ 2*K*|δ| ∧
      1/|lam| = (1+err)/(a*|gap| *δ^N) := by
  let L := -a*δ^N*gap
  have hL : L ≠ 0 := by
    dsimp [L]
    exact mul_ne_zero
      (mul_ne_zero (neg_ne_zero.mpr (ne_of_gt ha))
        (pow_ne_zero N (ne_of_gt hδ))) hgap
  have hnonneg : 0 ≤ K*|δ| := mul_nonneg hK (abs_nonneg δ)
  obtain ⟨hxpos, hrecip⟩ := reciprocal_relative_error_bound
    (lam/L) (K*|δ|) hnonneg hsmall hrelative
  have hlam : lam ≠ 0 := by
    intro hzero
    simp [hzero, L] at hxpos
  have hratio : |L|/|lam| = 1/(lam/L) := by
    have hq : lam/L = |lam|/|L| := by
      rw [← abs_div, abs_of_pos hxpos]
    rw [hq]
    field_simp [abs_ne_zero.mpr hL, abs_ne_zero.mpr hlam]
  let err := |L|/|lam|-1
  have herr : |err| ≤ 2*K*|δ| := by
    dsimp [err]
    rw [hratio]
    simpa only [mul_assoc] using hrecip
  have habsL : |L| = a*|gap| *δ^N := by
    dsimp [L]
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos ha, abs_pow,
      abs_of_pos hδ]
    ring
  have hden : a*|gap| *δ^N ≠ 0 := by
    rw [← habsL]
    exact abs_ne_zero.mpr hL
  refine ⟨err, herr, ?_⟩
  dsimp [err]
  rw [← habsL]
  field_simp [hden, hlam, abs_ne_zero.mpr hL]; ring

end
end PhosphorylationStableCapacity
