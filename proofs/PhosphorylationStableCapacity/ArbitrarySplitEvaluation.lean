module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitContinuity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial
open scoped Topology

/-- Conversion preserves the prescribed degree bound for arbitrary offsets. -/
theorem arbitrarySplitRaw_coeff_zero_above (m : ℕ) (ξ : ℕ → ℝ)
    (r δ : ℝ) (i : ℕ) (hi : m < i) :
    (arbitrarySplitRawD m ξ r δ).coeff i = 0 ∧
      (arbitrarySplitRawB m ξ r δ).coeff i = 0 := by
  let p := (arbitrarySplitPair m ξ δ).1
  let q := (arbitrarySplitPair m ξ δ).2
  have hsupport := arbitrarySplitPair_coeff_zero_above m ξ δ
  have hnum : (conversionNumerator p q r).natDegree ≤ m+1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    cases j with
    | zero => omega
    | succ j =>
        simp only [conversionNumerator, coeff_sub, coeff_C_mul, coeff_X_mul]
        rw [hsupport.1 j (by omega), hsupport.2 (j+1) (by omega)]
        ring
  have hquot : (quotient p q r).natDegree ≤ m := by
    rw [quotient, natDegree_divByMonic _ (monic_X_sub_C r),
      natDegree_X_sub_C]
    omega
  have hh : (quotient p q r).coeff i = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hquot hi)
  dsimp [p, q] at hh
  simp only [arbitrarySplitRawD, arbitrarySplitRawB, rawD, rawB,
    coeff_sub, coeff_add, coeff_C_mul, hh,
    hsupport.1 i hi, hsupport.2 i hi]
  constructor <;> ring

/-- Evaluation at a moving argument remains continuous. -/
theorem arbitrarySplitRawD_eval_continuous (m : ℕ) (ξ : ℕ → ℝ)
    (r : ℝ) (hr : r ≠ 0) (u : ℝ → ℝ) (hu : Continuous u) :
    Continuous (fun δ => (arbitrarySplitRawD m ξ r δ).eval (u δ)) := by
  have hsum : Continuous (fun δ : ℝ =>
      ∑ i ∈ Finset.range (m+1),
        (arbitrarySplitRawD m ξ r δ).coeff i * (u δ)^i) := by
    apply continuous_finsetSum
    intro i hi
    exact (arbitrarySplitRawD_coeff_continuous m ξ r hr i).mul (hu.pow i)
  convert hsum using 1
  funext δ
  exact eval_eq_sum_range'
    (show (arbitrarySplitRawD m ξ r δ).natDegree < m+1 by
      have hle := natDegree_le_iff_coeff_eq_zero.mpr
        (fun i hi => (arbitrarySplitRaw_coeff_zero_above m ξ r δ i hi).1)
      omega) (u δ)

theorem arbitrarySplitRawB_eval_continuous (m : ℕ) (ξ : ℕ → ℝ)
    (r : ℝ) (hr : r ≠ 0) (u : ℝ → ℝ) (hu : Continuous u) :
    Continuous (fun δ => (arbitrarySplitRawB m ξ r δ).eval (u δ)) := by
  have hsum : Continuous (fun δ : ℝ =>
      ∑ i ∈ Finset.range (m+1),
        (arbitrarySplitRawB m ξ r δ).coeff i * (u δ)^i) := by
    apply continuous_finsetSum
    intro i hi
    exact (arbitrarySplitRawB_coeff_continuous m ξ r hr i).mul (hu.pow i)
  convert hsum using 1
  funext δ
  exact eval_eq_sum_range'
    (show (arbitrarySplitRawB m ξ r δ).natDegree < m+1 by
      have hle := natDegree_le_iff_coeff_eq_zero.mpr
        (fun i hi => (arbitrarySplitRaw_coeff_zero_above m ξ r δ i hi).2)
      omega) (u δ)

theorem arbitrarySplitInventory_coeff_continuous (m : ℕ) (ξ : ℕ → ℝ)
    (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    Continuous (fun δ =>
      (((1 + Polynomial.X) * arbitrarySplitRawD m ξ r δ : ℝ[X]).coeff i)) := by
  -- The finite-coefficient continuity algebra avoids a topology on ℝ[X].
  have hconst : RealCoeffContinuous (fun _ : ℝ => (1 + Polynomial.X : ℝ[X])) := by
    intro j
    exact continuous_const
  have hD : RealCoeffContinuous (fun δ => arbitrarySplitRawD m ξ r δ) :=
    fun j => arbitrarySplitRawD_coeff_continuous m ξ r hr j
  -- Coefficient multiplication is a finite convolution.
  have h : Continuous (fun δ : ℝ =>
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal i,
        ((1 + Polynomial.X : ℝ[X]).coeff ij.1) *
          (arbitrarySplitRawD m ξ r δ).coeff ij.2) := by
    apply continuous_finsetSum
    intro ij hij
    exact (hconst ij.1).mul (hD ij.2)
  simpa only [Polynomial.coeff_mul] using h

end
end PhosphorylationStableCapacity
