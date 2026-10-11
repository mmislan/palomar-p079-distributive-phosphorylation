module
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import proofs.PhosphorylationStableCapacity.BenchmarkSaddlePositiveRootOne
public import proofs.PhosphorylationStableCapacity.BenchmarkSaddleSimpleOne

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The first printed three-site saddle certificate has one simple positive
eigenvalue and all its other complex spectral points strictly left. -/
theorem benchmarkSaddleOneA_one_unstable :
    ∃ x : ℝ, 0 < x ∧ benchmarkSaddleOneA.realMatrix.charpoly.IsRoot x ∧
      ((benchmarkSaddleOneA.realMatrix.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
        (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ,
        z ∈ spectrum ℂ (benchmarkSaddleOneA.realMatrix.map (algebraMap ℝ ℂ)) →
          z.re < 0 ∨ z = (x : ℂ) := by
  obtain ⟨x, hx, hroot⟩ := benchmarkSaddleOneA_exists_positive_root
  have hrootAC :
      ((benchmarkSaddleOneA.realMatrix.map (algebraMap ℝ ℂ)).charpoly).eval
        (x : ℂ) = 0 := by
    rw [Matrix.charpoly_map]
    calc
      (benchmarkSaddleOneA.realMatrix.charpoly.map (algebraMap ℝ ℂ)).eval (x : ℂ) =
          ((benchmarkSaddleOneA.realMatrix.charpoly.eval x : ℝ) : ℂ) := by
            simpa using (Polynomial.eval_map_apply
              (p := benchmarkSaddleOneA.realMatrix.charpoly)
              (f := algebraMap ℝ ℂ) x)
      _ = 0 := by exact_mod_cast hroot
  have hrootBC : benchmarkSaddleOneBC.charpoly.eval (x : ℂ) = 0 := by
    rw [benchmarkSaddleOneBC_charpoly_eq_AC]
    exact hrootAC
  have hsimpleAC :
      ((benchmarkSaddleOneA.realMatrix.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
        (x : ℂ) ≠ 0 := by
    rw [← benchmarkSaddleOneBC_charpoly_eq_AC]
    exact benchmarkSaddleOne_simple_right (x : ℂ)
      (by exact_mod_cast hx.le) hrootBC
  refine ⟨x, hx, hroot, hsimpleAC, ?_⟩
  intro z hz
  by_cases hneg : z.re < 0
  · exact Or.inl hneg
  · right
    apply benchmarkSaddleOne_unique_right z (x : ℂ)
      (le_of_not_gt hneg) (by exact_mod_cast hx.le)
    · rw [benchmarkSaddleOneBC_charpoly_eq_AC]
      exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
    · exact hrootBC

end
end PhosphorylationStableCapacity
