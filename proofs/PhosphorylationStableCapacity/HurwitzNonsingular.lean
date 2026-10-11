module
public import proofs.PhosphorylationStableCapacity.MetzlerWeighted

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- A matrix whose complex characteristic roots all have negative real part
is nonsingular. -/
theorem isHurwitz_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : IsHurwitz A) : A.det ≠ 0 := by
  intro hdet
  have hmap : (A.map (algebraMap ℝ ℂ)).det = 0 := by
    change Matrix.det ((algebraMap ℝ ℂ).mapMatrix A) = 0
    rw [← RingHom.map_det, hdet, map_zero]
  have hmap' : (A.map Complex.ofReal).det = 0 := by
    simpa using hmap
  have hroot : ((A.map (algebraMap ℝ ℂ)).charpoly).eval 0 = 0 := by
    rw [Matrix.eval_charpoly]
    simp [Matrix.det_neg, hmap']
  have hneg := hA 0 hroot
  norm_num at hneg

end
end PhosphorylationStableCapacity
