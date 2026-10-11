module
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- An invertible finite matrix supplies the literal column-vector
linear equivalence used in an intertwining identity. -/
def matrixMulVecEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : IsUnit P) :
    (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) := by
  have hinj : Function.Injective P.toLin' := by
    intro x y hxy
    apply Matrix.mulVec_injective_of_isUnit hP
    simpa only [Matrix.toLin'_apply] using hxy
  exact LinearEquiv.ofBijective P.toLin'
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩

theorem matrixMulVecEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : IsUnit P) (z : ι → ℝ) :
    matrixMulVecEquiv P hP z = P.mulVec z := rfl

/-- Intertwining with an invertible column-vector map identifies the
complete characteristic polynomial, including all multiplicities. -/
theorem charpoly_of_matrix_intertwining
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (P F : Matrix ι ι ℝ) (hP : IsUnit P)
    (hintertwine : ∀ z : ι → ℝ,
      L (P.mulVec z) = P.mulVec (F.mulVec z)) :
    L.charpoly = F.charpoly := by
  let e := matrixMulVecEquiv P hP
  have hL : L = e.conj F.toLin' := by
    apply LinearMap.ext
    intro v
    obtain ⟨z, rfl⟩ := e.surjective v
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe]
    rw [e.symm_apply_apply]
    simpa only [Matrix.toLin'_apply, e, matrixMulVecEquiv_apply] using
      hintertwine z
  rw [hL, LinearEquiv.charpoly_conj, Matrix.charpoly_toLin']

end
end PhosphorylationStableCapacity
