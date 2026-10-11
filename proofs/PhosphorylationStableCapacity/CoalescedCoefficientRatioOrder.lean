module
public import proofs.PhosphorylationStableCapacity.CoalescedIndexedFactors

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial PhosphorylationSharpness

noncomputable section

theorem coeffRatioMono_C_mul {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hm : CoeffRatioMono p q m)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    CoeffRatioMono (C c * p) (C d * q) m := by
  intro i hi
  have h := hm i hi
  have hpi := hp.1 i (by omega)
  have hpn := hp.1 (i + 1) (by omega)
  simp only [coeff_C_mul]
  calc
    (d * q.coeff i) / (c * p.coeff i) =
        (d / c) * (q.coeff i / p.coeff i) := by
      field_simp [ne_of_gt hc, ne_of_gt hpi]
    _ ≤ (d / c) * (q.coeff (i + 1) / p.coeff (i + 1)) :=
      mul_le_mul_of_nonneg_left h (div_nonneg hd.le hc.le)
    _ = (d * q.coeff (i + 1)) / (c * p.coeff (i + 1)) := by
      field_simp [ne_of_gt hc, ne_of_gt hpn]

/-- The literal coalesced source coefficient ratio `J_i/N_i` is
nondecreasing for every source length. -/
theorem coalescedJN_coeff_ratio_mono (m : ℕ) :
    CoeffRatioMono (coalescedPair m).1 (coalescedPair m).2 m := by
  have hmonic := positiveFactorProduct_ratio_mono
    (coalescedNFactors m) (coalescedJFactors m)
    (coalescedFactors_pairwise m)
    (coalescedNFactors_pos m) (coalescedJFactors_pos m)
  have hlen : (coalescedNFactors m).length = m := by
    simp [coalescedNFactors, coalescedFactorIndices_length]
  rw [hlen] at hmonic
  have hN := (coalescedPair_dense m).1
  have hJ := (coalescedPair_dense m).2
  have hleadN : 0 < (coalescedPair m).1.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hN.degree_eq]
    exact hN.1 m le_rfl
  have hleadJ : 0 < (coalescedPair m).2.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hJ.degree_eq]
    exact hJ.1 m le_rfl
  have hpositive := positiveFactorProduct_dense (coalescedNFactors m)
    (coalescedNFactors_pos m)
  rw [hlen] at hpositive
  have hscaled := coeffRatioMono_C_mul hpositive hmonic hleadN hleadJ
  rw [coalescedN_indexed_factorization,
    coalescedJ_indexed_factorization] at hscaled
  exact hscaled

end
end PhosphorylationStableCapacity
