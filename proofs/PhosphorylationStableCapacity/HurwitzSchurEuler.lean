module
public import proofs.PhosphorylationStableCapacity.EulerMatrixSpectrum

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Every finite real Hurwitz matrix has a positive Euler step whose
actual stepped matrix has all complex characteristic roots strictly
inside the unit disk. -/
theorem isHurwitz_exists_schur_euler_step
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : IsHurwitz A) :
    ∃ h : ℝ, 0 < h ∧
      ∀ w : ℂ,
        (((((1 : Matrix ι ι ℝ) + h • A).map
          (algebraMap ℝ ℂ)).charpoly).eval w = 0) →
          ‖w‖ < 1 := by
  obtain ⟨h, hh, hroots⟩ := isHurwitz_exists_euler_root_step A hA
  refine ⟨h, hh, ?_⟩
  intro w hw
  have hne : h ≠ 0 := ne_of_gt hh
  have hnec : (h:ℂ) ≠ 0 := by exact_mod_cast hne
  have hz := euler_matrix_root_pullback A h hne w hw
  have hdisk := hroots ((w-1)/(h:ℂ)) hz
  have hwform : (1 : ℂ) + (h:ℂ) * ((w-1)/(h:ℂ)) = w := by
    field_simp [hnec]
    ring
  simpa [hwform] using hdisk

end
end PhosphorylationStableCapacity
