module
public import proofs.PhosphorylationStableCapacity.ScaledIntegerMatrixCertificates
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

theorem scaledComplex_entry {ι κ : Type*}
    (A : ScaledIntegerMatrix ι κ) (i : ι) (j : κ) :
    (A.realMatrix.map (algebraMap ℝ ℂ)) i j =
      (((A.entries i j : ℝ) / (A.denominator : ℝ)) : ℂ) := by
  simp [ScaledIntegerMatrix.realMatrix, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem scaledComplex_entry_re {ι κ : Type*}
    (A : ScaledIntegerMatrix ι κ) (i : ι) (j : κ) :
    ((A.realMatrix.map (algebraMap ℝ ℂ)) i j).re =
      (A.entries i j : ℝ) / (A.denominator : ℝ) := by
  rw [scaledComplex_entry]
  rw [← Complex.ofReal_div, Complex.ofReal_re]

theorem scaledComplex_entry_norm {ι κ : Type*}
    (A : ScaledIntegerMatrix ι κ) (hden : 0 < A.denominator)
    (i : ι) (j : κ) :
    ‖(A.realMatrix.map (algebraMap ℝ ℂ)) i j‖ =
      (|A.entries i j| : ℝ) / (A.denominator : ℝ) := by
  rw [scaledComplex_entry, ← Complex.ofReal_div, Complex.norm_real,
    Real.norm_eq_abs, abs_div]
  have hdenReal : 0 < (A.denominator : ℝ) := Nat.cast_pos.mpr hden
  rw [abs_of_pos hdenReal]

end
end PhosphorylationStableCapacity
