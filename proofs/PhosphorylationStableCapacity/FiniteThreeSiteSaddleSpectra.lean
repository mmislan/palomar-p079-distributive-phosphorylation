module
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import proofs.PhosphorylationStableCapacity.BenchmarkSaddleSpectrumOne
public import proofs.PhosphorylationStableCapacity.BenchmarkSaddleSpectrumThree
public import proofs.PhosphorylationStableCapacity.BenchmarkSaddleLiteralOne
public import proofs.PhosphorylationStableCapacity.BenchmarkSaddleLiteralThree

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

private theorem one_unstable_of_charpoly_eq
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hchar : A.charpoly = B.charpoly)
    (hB : ∃ x : ℝ, 0 < x ∧ B.charpoly.IsRoot x ∧
      ((B.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ, z ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)) →
        z.re < 0 ∨ z = (x : ℂ)) :
    ∃ x : ℝ, 0 < x ∧ A.charpoly.IsRoot x ∧
      ((A.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ, z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) →
        z.re < 0 ∨ z = (x : ℂ) := by
  obtain ⟨x, hx, hr, hd, hrest⟩ := hB
  refine ⟨x, hx, ?_, ?_, ?_⟩
  · simpa only [hchar] using hr
  · simpa only [Matrix.charpoly_map, hchar] using hd
  · intro z hz
    have hz' : z ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)) := by
      apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
      have hzr := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
      simpa only [Matrix.charpoly_map, hchar] using hzr
    exact hrest z hz'

private theorem benchmarkThreeSite_charpoly_one :
    (restrictedJacobianMatrix 18 2 20 benchmarkThreeSiteRates
      (benchmarkThreeSiteCoord 1)).charpoly =
        benchmarkSaddleOneA.realMatrix.charpoly := by
  calc
    _ = (benchmarkThreeSiteMatrixFin 1).charpoly :=
      (Matrix.charpoly_reindex _ _).symm
    _ = benchmarkSaddleOneA.realMatrix.charpoly := by
      rw [benchmarkSaddleOneA_eq_literal]

private theorem benchmarkThreeSite_charpoly_three :
    (restrictedJacobianMatrix 18 2 20 benchmarkThreeSiteRates
      (benchmarkThreeSiteCoord 3)).charpoly =
        benchmarkSaddleThreeA.realMatrix.charpoly := by
  calc
    _ = (benchmarkThreeSiteMatrixFin 3).charpoly :=
      (Matrix.charpoly_reindex _ _).symm
    _ = benchmarkSaddleThreeA.realMatrix.charpoly := by
      rw [benchmarkSaddleThreeA_eq_literal]

/-- The first printed three-site saddle is classified on the literal
restricted mass-action Jacobian. -/
theorem benchmarkThreeSite_one_is_one_unstable_saddle :
    let A := restrictedJacobianMatrix 18 2 20 benchmarkThreeSiteRates
      (benchmarkThreeSiteCoord 1)
    ∃ x : ℝ, 0 < x ∧ A.charpoly.IsRoot x ∧
      ((A.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ, z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) →
        z.re < 0 ∨ z = (x : ℂ) := by
  exact one_unstable_of_charpoly_eq _ _ benchmarkThreeSite_charpoly_one
    benchmarkSaddleOneA_one_unstable

/-- The second printed three-site saddle is classified on the literal
restricted mass-action Jacobian. -/
theorem benchmarkThreeSite_three_is_one_unstable_saddle :
    let A := restrictedJacobianMatrix 18 2 20 benchmarkThreeSiteRates
      (benchmarkThreeSiteCoord 3)
    ∃ x : ℝ, 0 < x ∧ A.charpoly.IsRoot x ∧
      ((A.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ, z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) →
        z.re < 0 ∨ z = (x : ℂ) := by
  exact one_unstable_of_charpoly_eq _ _ benchmarkThreeSite_charpoly_three
    benchmarkSaddleThreeA_one_unstable

end
end PhosphorylationStableCapacity
