module
public import proofs.PhosphorylationStableCapacity.HurwitzSpectralGap
public import Mathlib.Analysis.Complex.Norm

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- A small positive explicit Euler step maps a left-half-plane
eigenvalue of bounded squared modulus strictly into the unit disk. -/
theorem euler_root_inside_disk
    (α R h : ℝ) (z : ℂ)
    (hh : 0 < h)
    (hreal : z.re ≤ -α)
    (hnorm : Complex.normSq z ≤ R)
    (hstep : h * R < 2 * α) :
    ‖(1 : ℂ) + (h : ℂ) * z‖ < 1 := by
  have hformula :
      Complex.normSq ((1 : ℂ) + (h : ℂ) * z) =
        1 + 2*h*z.re + h^2*Complex.normSq z := by
    simp [Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im]
    ring
  have hreal' : 2*h*z.re ≤ -2*h*α := by
    nlinarith [mul_nonneg (show 0 ≤ 2*h by positivity)
      (sub_nonneg.mpr (show z.re ≤ -α from hreal))]
  have hnorm' : h^2*Complex.normSq z ≤ h^2*R :=
    mul_le_mul_of_nonneg_left hnorm (sq_nonneg h)
  have hneg : 2*h*z.re + h^2*Complex.normSq z < 0 := by
    nlinarith [mul_pos hh (sub_pos.mpr hstep)]
  have hsq : Complex.normSq ((1 : ℂ) + (h : ℂ) * z) < 1 := by
    rw [hformula]
    linarith
  have hnormsq : ‖(1 : ℂ) + (h : ℂ) * z‖^2 < 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hsq
  exact (sq_lt_sq₀ (norm_nonneg _) (by norm_num)).mp
    (by simpa using hnormsq)

end
end PhosphorylationStableCapacity
