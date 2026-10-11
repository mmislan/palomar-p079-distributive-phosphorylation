module
public import proofs.PhosphorylationStableCapacity.HurwitzEulerRootDisk

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- A characteristic root of an Euler-stepped real matrix pulls back
to a characteristic root of the original matrix. -/
theorem euler_matrix_root_pullback
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (h : ℝ) (hh : h ≠ 0)
    (w : ℂ)
    (hw : ((((1 : Matrix ι ι ℝ) + h • A).map
      (algebraMap ℝ ℂ)).charpoly).eval w = 0) :
    (((A.map (algebraMap ℝ ℂ)).charpoly).eval
      ((w-1)/(h:ℂ))) = 0 := by
  let z : ℂ := (w-1)/(h:ℂ)
  have hhc : (h:ℂ) ≠ 0 := by exact_mod_cast hh
  have hmat :
      Matrix.scalar ι w -
        ((1 : Matrix ι ι ℝ) + h • A).map (algebraMap ℝ ℂ) =
      (h:ℂ) • (Matrix.scalar ι z - A.map (algebraMap ℝ ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [z, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
        Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
      field_simp
      ring
    · simp [z, hij, Matrix.scalar_apply, Matrix.diagonal_apply_ne,
        Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply]
  have hdet :
      (Matrix.scalar ι w -
        ((1 : Matrix ι ι ℝ) + h • A).map
          (algebraMap ℝ ℂ)).det = 0 := by
    simpa [Matrix.eval_charpoly] using hw
  rw [hmat, Matrix.det_smul] at hdet
  have hpow : (h:ℂ)^Fintype.card ι ≠ 0 := pow_ne_zero _ hhc
  have hzdet :
      (Matrix.scalar ι z - A.map (algebraMap ℝ ℂ)).det = 0 :=
    (mul_eq_zero.mp hdet).resolve_left hpow
  simpa [z, Matrix.eval_charpoly] using hzdet

end
end PhosphorylationStableCapacity
