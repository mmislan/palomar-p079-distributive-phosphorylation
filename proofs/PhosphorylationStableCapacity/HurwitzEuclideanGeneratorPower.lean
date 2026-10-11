module
public import proofs.PhosphorylationStableCapacity.HurwitzRealEuclideanPowerContract

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Move the real Euler-power bound through the matrix-to-Euclidean
algebra equivalence. -/
theorem isHurwitz_exists_euclidean_generator_contracting_power
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : IsHurwitz A) :
    ∃ h : ℝ, 0 < h ∧ ∃ m : ℕ, 0 < m ∧
      ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ v : EuclideanSpace ℝ ι,
        ‖(((1 : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) +
          h • Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A)^m) v‖ ≤
          r * ‖v‖ := by
  obtain ⟨h, hh, m, hm, r, hr0, hr1, hcontract⟩ :=
    isHurwitz_exists_real_euclidean_contracting_power A hA
  refine ⟨h, hh, m, hm, r, hr0, hr1, ?_⟩
  intro v
  have hstep : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
      ((1 : Matrix ι ι ℝ) + h • A) =
      (1 : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) +
        h • Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A := by
    simp
  have hpower : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
      (((1 : Matrix ι ι ℝ) + h • A)^m) =
      ((1 : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) +
        h • Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A)^m := by
    rw [map_pow, hstep]
  rw [← hpower]
  exact hcontract v

end
end PhosphorylationStableCapacity
