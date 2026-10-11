module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingAffineRates435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness

/-- The finitely many positive probe currents used to recover the
manuscript's affine current dependence without evaluating a singular
zero-current rate realization. -/
def paperPositiveCurrentProbe {n : ℕ} (i : Fin n) : Fin n → ℝ :=
  fun j => if j = i then 2 else 1

theorem paperPositiveCurrentProbe_pos {n : ℕ} (i : Fin n) :
    ∀ j, 0 < paperPositiveCurrentProbe i j := by
  intro j
  by_cases h : j = i <;> simp [paperPositiveCurrentProbe, h]

/-- Every coordinate of the literal frozen-binding rate vector is
reconstructed from the all-one family and the positive probe at that
edge. This identity is valid only for positive actual current factors. -/
theorem paperFixedBinding_rateVector_single_positive_probe
    {n : ℕ} (k : Rates n) (ε : ℝ)
    (hk : k.Positive) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (j : Fin 6) (i : Fin n) :
    rateVector (relaxRates
      (paperFixedBindingRates (edgeScaledRates w k)) ε) j i =
      rateVector (relaxRates
        (paperFixedBindingRates (edgeScaledRates (fun _ => 1) k)) ε) j i +
      (w i - 1) *
        (rateVector (relaxRates
          (paperFixedBindingRates
            (edgeScaledRates (paperPositiveCurrentProbe i) k)) ε) j i -
         rateVector (relaxRates
           (paperFixedBindingRates (edgeScaledRates (fun _ => 1) k)) ε) j i) := by
  have hreal := paperFixedBinding_relaxed_rateVector_affine
    k w ε hk hw j i
  have hone := paperFixedBinding_relaxed_rateVector_affine
    k (fun _ => 1) ε hk (by intro q; norm_num) j i
  have hprobe := paperFixedBinding_relaxed_rateVector_affine
    k (paperPositiveCurrentProbe i) ε hk
      (paperPositiveCurrentProbe_pos i) j i
  have hprobeEval : paperPositiveCurrentProbe i i = 2 := by
    simp [paperPositiveCurrentProbe]
  rw [hprobeEval] at hprobe
  rw [hreal, hone, hprobe]
  ring

/-- The full literal rate array is an affine combination of finitely
many positive probe arrays. The identity is pointwise in the split
parameter and therefore remains valid on the entire denominator-safe
positive-rate tube used for the compact spectral law. -/
theorem paperFixedBinding_rateVector_all_positive_probes
    {n : ℕ} (k : Rates n) (ε : ℝ)
    (hk : k.Positive) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) :
    rateVector (relaxRates
      (paperFixedBindingRates (edgeScaledRates w k)) ε) =
      rateVector (relaxRates
        (paperFixedBindingRates (edgeScaledRates (fun _ => 1) k)) ε) +
      ∑ p : Fin n, (w p - 1) •
        (rateVector (relaxRates
          (paperFixedBindingRates
            (edgeScaledRates (paperPositiveCurrentProbe p) k)) ε) -
         rateVector (relaxRates
           (paperFixedBindingRates (edgeScaledRates (fun _ => 1) k)) ε)) := by
  funext j i
  let a := paperFixedBindingRateIntercept k ε j i
  let b := paperFixedBindingRateSlope k ε j i
  have hreal := paperFixedBinding_relaxed_rateVector_affine
    k w ε hk hw j i
  have hone := paperFixedBinding_relaxed_rateVector_affine
    k (fun _ => 1) ε hk (by intro q; norm_num) j i
  have hterm (p : Fin n) :
      rateVector (relaxRates
        (paperFixedBindingRates
          (edgeScaledRates (paperPositiveCurrentProbe p) k)) ε) j i -
        rateVector (relaxRates
          (paperFixedBindingRates (edgeScaledRates (fun _ => 1) k)) ε) j i =
        (if i = p then 1 else 0) * b := by
    rw [paperFixedBinding_relaxed_rateVector_affine k
      (paperPositiveCurrentProbe p) ε hk
      (paperPositiveCurrentProbe_pos p) j i, hone]
    by_cases h : i = p
    · subst p
      simp [paperPositiveCurrentProbe, b]
      ring
    · simp [paperPositiveCurrentProbe, h, b]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul]
  simp_rw [hterm]
  rw [hreal, hone]
  simp [Finset.sum_ite_eq]
  ring

end

end PhosphorylationStableCapacity
