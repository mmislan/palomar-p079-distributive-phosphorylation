module
public import proofs.PhosphorylationStableCapacity.CoefficientRatioComposition

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial PhosphorylationSharpness

noncomputable section

/-- Replacing one positive linear factor by a smaller positive factor makes
the coefficient ratio increase with degree. -/
theorem factorReplacement_coeffRatioMono {p : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hlc : CoeffLogConcave p m)
    {a b : ℝ} (ha : 0 < a) (hba : b ≤ a) :
    CoeffRatioMono (positiveLinearStep a p)
      (positiveLinearStep b p) (m + 1) := by
  intro i hi
  have hda := positiveLinearStep_dense hp ha
  have hden0 := hda.1 i (by omega)
  have hden1 := hda.1 (i + 1) (by omega)
  cases i with
  | zero =>
      have hlog : 0 * p.coeff 1 ≤ p.coeff 0 ^ 2 := by nlinarith
      have h := factor_replacement_ratio_mono a b 0
        (p.coeff 0) (p.coeff 1) hba hlog
        (by simpa [positiveLinearStep_coeff_zero] using hden0)
        (by simpa [positiveLinearStep_coeff_succ] using hden1)
      simpa [positiveLinearStep_coeff_zero,
        positiveLinearStep_coeff_succ] using h
  | succ j =>
      have hlog : p.coeff j * p.coeff (j + 2) ≤
          p.coeff (j + 1) ^ 2 := by
        by_cases hinner : j + 1 < m
        · simpa [Nat.add_assoc] using
            hlc (j + 1) (by omega) hinner
        · rw [hp.2 (j + 2) (by omega)]
          nlinarith
      have h := factor_replacement_ratio_mono a b
        (p.coeff j) (p.coeff (j + 1)) (p.coeff (j + 2))
        hba hlog
        (by simpa [positiveLinearStep_coeff_succ] using hden0)
        (by simpa [positiveLinearStep_coeff_succ] using hden1)
      simpa [positiveLinearStep_coeff_succ, Nat.add_assoc] using h

end
end PhosphorylationStableCapacity
