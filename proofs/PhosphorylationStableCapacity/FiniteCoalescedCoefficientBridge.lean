module
public import proofs.PhosphorylationStableCapacity.CoalescedFiniteSource
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitConversion

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Polynomial

/-- The reference complex coordinates use the same raw coefficient
normalization as the printed construction. -/
theorem coalescedFiniteState_D_eq_coeff_div_eval
    (m : ℕ) (r : ℝ) (i : Fin (m+1)) :
    (coalescedFiniteState m r).D i =
      (coalescedRawD m r).coeff i / (coalescedRawD m r).eval 1 := by
  change (coalescedRawD m r).coeff i * (ratio 3)^(i.val+1) *
    rootS 3 ((coalescedRawD m r).eval (ratio 3)) * rootF 3 = _
  have hu : ratio 3 = 1 := by norm_num [ratio]
  have hf : rootF 3 = 1 := by norm_num [rootF]
  rw [hu, hf, rootS_three]
  simp only [one_pow, mul_one, div_eq_mul_inv, one_mul]

/-- Positive finite coalesced coefficients give positive reference complexes;
the generic support theorem supplies all higher zero coefficients. -/
theorem coalescedFiniteState_D_positive_of_coeff_positive
    (m : ℕ) (r : ℝ)
    (hcoeff : ∀ i : Fin (m+1), 0 < (coalescedRawD m r).coeff i) :
    ∀ i : Fin (m+1), 0 < (coalescedFiniteState m r).D i := by
  obtain ⟨hp, hq⟩ := coalescedPair_dense m
  have hD : DensePositive (coalescedRawD m r) m := by
    constructor
    · intro i hi
      exact hcoeff ⟨i, by omega⟩
    · intro i hi
      exact (raw_support hp hq r i hi).1
  have heval : 0 < (coalescedRawD m r).eval 1 :=
    hD.eval_pos (by norm_num)
  intro i
  change 0 < (coalescedRawD m r).coeff i * (ratio 3)^(i.val+1) *
    rootS 3 ((coalescedRawD m r).eval (ratio 3)) * rootF 3
  have hu : ratio 3 = 1 := by norm_num [ratio]
  have hf : rootF 3 = 1 := by norm_num [rootF]
  rw [hu, hf, rootS_three]
  simpa only [one_pow, mul_one] using
    mul_pos (hcoeff i) (one_div_pos.mpr heval)

end
end PhosphorylationStableCapacity
