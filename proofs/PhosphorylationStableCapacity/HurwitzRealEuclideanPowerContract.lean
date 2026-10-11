module
public import proofs.PhosphorylationStableCapacity.SchurFrobeniusPowerContract
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.RowCol

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open scoped Matrix.Norms.Frobenius
open Matrix WithLp

/-- The Frobenius norm bounds the Euclidean action of a real matrix. -/
theorem frobenius_norm_mulVec_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (v : ι → ℝ) :
    ‖(toLp 2 (B *ᵥ v))‖ ≤ ‖B‖ * ‖(toLp 2 v)‖ := by
  calc
    ‖(toLp 2 (B *ᵥ v))‖ = ‖Matrix.replicateCol Unit (B *ᵥ v)‖ := by simp
    _ = ‖B * Matrix.replicateCol Unit v‖ := by
      rw [Matrix.replicateCol_mulVec]
    _ ≤ ‖B‖ * ‖Matrix.replicateCol Unit v‖ :=
      Matrix.frobenius_norm_mul B _
    _ = ‖B‖ * ‖(toLp 2 v)‖ := by simp

/-- A real Hurwitz matrix has a positive Euler step with a power
contracting on real Euclidean space. -/
theorem isHurwitz_exists_real_euclidean_contracting_power
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : IsHurwitz A) :
    ∃ h : ℝ, 0 < h ∧ ∃ m : ℕ, 0 < m ∧
      ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ v : EuclideanSpace ℝ ι,
        ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
          (((1 : Matrix ι ι ℝ) + h • A)^m) v‖ ≤ r * ‖v‖ := by
  obtain ⟨h, hh, m, hm, hcontract⟩ :=
    isHurwitz_exists_real_frobenius_contracting_power A hA
  refine ⟨h, hh, m, hm, _, norm_nonneg _, hcontract, ?_⟩
  intro v
  let B : Matrix ι ι ℝ := ((1 : Matrix ι ι ℝ) + h • A)^m
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) B v‖ ≤ ‖B‖ * ‖v‖
  calc
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) B v‖ =
        ‖toLp 2 (B *ᵥ ofLp v)‖ := by
          rw [← Matrix.toEuclideanCLM_toLp B (ofLp v), toLp_ofLp]
    _ ≤ ‖B‖ * ‖v‖ := by
      simpa only [toLp_ofLp] using
        frobenius_norm_mulVec_bound B (ofLp v)

end
end PhosphorylationStableCapacity
