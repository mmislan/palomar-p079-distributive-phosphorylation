module
public import proofs.PhosphorylationStableCapacity.LoadedJacobianBlockAction
public import proofs.PhosphorylationStableCapacity.FastBindingMatrixFactorization
public import proofs.PhosphorylationStableCapacity.LoadedFastBlockIdentification
public import proofs.PhosphorylationStableCapacity.FastSlowRealComplexMap

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix

/-- The loaded compatibility-class derivative in the standard slow/fast
product basis. -/
def loadedJacobianMatrix {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) :
    Matrix (Fin n ⊕ (Fin n ⊕ Fin n))
      (Fin n ⊕ (Fin n ⊕ Fin n)) ℝ :=
  LinearMap.toMatrix (coordinateBasis n) (coordinateBasis n)
    (fderiv ℝ (loadedRestrictedField ET FT ST k) u).toLinearMap

/-- The literal loaded derivative matrix is exactly the matrix assembled
from its four named Fréchet-derivative blocks. -/
theorem loadedJacobianMatrix_eq_fromBlocks {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    loadedJacobianMatrix ET FT ST k u =
      Matrix.fromBlocks
        (LinearMap.toMatrix (Pi.basisFun ℝ (Fin n))
          (Pi.basisFun ℝ (Fin n))
          (loadedBlockA ET FT ST k u).toLinearMap)
        (LinearMap.toMatrix (fastBasis n)
          (Pi.basisFun ℝ (Fin n))
          (loadedBlockB ET FT ST k u).toLinearMap)
        (LinearMap.toMatrix (Pi.basisFun ℝ (Fin n))
          (fastBasis n)
          (loadedBlockC ET FT ST k u).toLinearMap)
        (LinearMap.toMatrix (fastBasis n) (fastBasis n)
          (loadedBlockD ET FT ST k u).toLinearMap) := by
  ext i j
  cases i <;> cases j <;>
    simp [loadedJacobianMatrix, coordinateBasis, fastBasis,
      loadedBlockA, loadedBlockB, loadedBlockC, loadedBlockD,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      LinearMap.toMatrix_apply, Module.Basis.prod_repr_inl,
      Module.Basis.prod_repr_inr]

/-- At a positive equilibrium, the lower-right matrix block is exactly
the strictly analyzed fast binding matrix. -/
theorem loadedBlockD_toMatrix_eq_fastBinding {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u)) :
    LinearMap.toMatrix (fastBasis n) (fastBasis n)
      (loadedBlockD ET FT ST k u).toLinearMap =
        fastBindingMatrix n (stateFromLoaded ET FT ST u)
          (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
            (stateFromLoaded ET FT ST u).E)
          (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
            (stateFromLoaded ET FT ST u).F) := by
  congr 1
  apply LinearMap.ext
  intro v
  simpa [loadedBlockD, fastBindingMatrix, fastBindingEnd, fastEmbed] using
    loadedFastBlock_eq_fastBinding ET FT ST k u v hpos heq

/-- Binding relaxation gives exactly the real fast/slow block matrix in
the standard loaded-coordinate product basis. -/
theorem loadedJacobianMatrix_relax_eq_realFastSlow {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    {ε : ℝ} (hε : ε ≠ 0) :
    loadedJacobianMatrix ET FT ST (relaxRates k ε) u =
      realFastSlowMatrix
        (LinearMap.toMatrix (Pi.basisFun ℝ (Fin n))
          (Pi.basisFun ℝ (Fin n))
          (loadedBlockA ET FT ST k u).toLinearMap)
        (LinearMap.toMatrix (fastBasis n)
          (Pi.basisFun ℝ (Fin n))
          (loadedBlockB ET FT ST k u).toLinearMap)
        (LinearMap.toMatrix (Pi.basisFun ℝ (Fin n))
          (fastBasis n)
          (loadedBlockC ET FT ST k u).toLinearMap)
        (LinearMap.toMatrix (fastBasis n) (fastBasis n)
          (loadedBlockD ET FT ST k u).toLinearMap) ε := by
  rw [loadedJacobianMatrix_eq_fromBlocks]
  ext i j
  cases i <;> cases j <;>
    simp [realFastSlowMatrix, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, loadedBlockA_relax ET FT ST k u hε,
      loadedBlockB_relax ET FT ST k u hε,
      loadedBlockC_relax ET FT ST k u hε,
      loadedBlockD_relax ET FT ST k u hε,
      LinearMap.toMatrix_apply, Matrix.smul_apply]

end
end PhosphorylationStableCapacity
