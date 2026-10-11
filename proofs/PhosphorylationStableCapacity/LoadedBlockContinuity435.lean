module
public import proofs.PhosphorylationStableCapacity.LoadedJacobianCharpolyBridge
public import proofs.PhosphorylationStableCapacity.SplitJacobianContinuity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix
open scoped Topology

set_option maxHeartbeats 1000000 in
/-- The loaded-coordinate Jacobian matrix varies continuously with all
six literal rate arrays at a fixed loaded state. -/
theorem continuous_loadedJacobianMatrix_fromVector {n : ℕ}
    (ET FT ST : ℝ) (u : CoordinateSpace n) :
    Continuous (fun v : RateVector n =>
      loadedJacobianMatrix ET FT ST (ratesFromVector v) u) := by
  let T : CoordinateSpace n →L[ℝ] CoordinateSpace n := loadedCoordContinuous n
  let Tinv : CoordinateSpace n →L[ℝ] CoordinateSpace n :=
    (loadedCoordContinuous n).symm
  let compOp := ContinuousLinearMap.compL ℝ
    (CoordinateSpace n) (CoordinateSpace n) (CoordinateSpace n)
  have hres : Continuous (fun v : RateVector n =>
      restrictedJacobian ET FT ST (ratesFromVector v)
        (fromLoadedCoord u)) := by
    have hp : Continuous (fun v : RateVector n =>
        (v, fromLoadedCoord u)) := continuous_id.prodMk continuous_const
    have hsource : Continuous
        (fun p : RateVector n × CoordinateSpace n =>
          restrictedJacobian ET FT ST (ratesFromVector p.1) p.2) :=
      continuous_restrictedJacobian_fromVector (n := n) ET FT ST
    simpa only [Function.comp_def] using
      (Continuous.comp
        (f := fun v : RateVector n => (v, fromLoadedCoord u))
        (g := fun p : RateVector n × CoordinateSpace n =>
          restrictedJacobian ET FT ST (ratesFromVector p.1) p.2)
        hsource hp)
  have hright : Continuous (fun v : RateVector n =>
      (restrictedJacobian ET FT ST (ratesFromVector v)
        (fromLoadedCoord u)).comp Tinv) :=
    (compOp.flip Tinv).continuous.comp hres
  have hloaded : Continuous (fun v : RateVector n =>
      T.comp ((restrictedJacobian ET FT ST (ratesFromVector v)
        (fromLoadedCoord u)).comp Tinv)) :=
    (compOp T).continuous.comp hright
  have hmatrix := (continuous_coordinateJacobian_matrix n).comp hloaded
  have heq : (fun v : RateVector n =>
      loadedJacobianMatrix ET FT ST (ratesFromVector v) u) =
      (fun v : RateVector n => LinearMap.toMatrix
        (coordinateBasis n) (coordinateBasis n)
        (T.comp ((restrictedJacobian ET FT ST (ratesFromVector v)
          (fromLoadedCoord u)).comp Tinv)).toLinearMap) := by
    funext v
    simp only [loadedJacobianMatrix, loadedRestrictedFderiv_conjugate,
      loadedCoordContinuous_symm_apply, T, Tinv]
  rw [heq]
  exact hmatrix

/-- Every fast/slow block of the exact loaded Jacobian inherits joint
continuity from the literal rates. This avoids replacing the model by
an approximate block system. -/
theorem continuous_loadedJacobianBlocks_of_rateVector
    {α : Type*} [TopologicalSpace α] {n : ℕ}
    (ET FT ST : ℝ) (u : CoordinateSpace n)
    (k : α → Rates n)
    (hk : Continuous (fun a => rateVector (k a))) :
    Continuous (fun a => LinearMap.toMatrix
        (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n))
        (loadedBlockA ET FT ST (k a) u).toLinearMap) ∧
      Continuous (fun a => LinearMap.toMatrix
        (fastBasis n) (Pi.basisFun ℝ (Fin n))
        (loadedBlockB ET FT ST (k a) u).toLinearMap) ∧
      Continuous (fun a => LinearMap.toMatrix
        (Pi.basisFun ℝ (Fin n)) (fastBasis n)
        (loadedBlockC ET FT ST (k a) u).toLinearMap) ∧
      Continuous (fun a => LinearMap.toMatrix
        (fastBasis n) (fastBasis n)
        (loadedBlockD ET FT ST (k a) u).toLinearMap) := by
  have hmat : Continuous (fun a => loadedJacobianMatrix ET FT ST (k a) u) := by
    have h := (continuous_loadedJacobianMatrix_fromVector ET FT ST u).comp hk
    simpa only [Function.comp_def, ratesFromVector_rateVector] using h
  constructor
  · apply continuous_matrix
    intro i j
    have hentry : Continuous (fun a =>
        loadedJacobianMatrix ET FT ST (k a) u (Sum.inl i) (Sum.inl j)) :=
      hmat.matrix_elem (Sum.inl i) (Sum.inl j)
    simpa only [loadedJacobianMatrix_eq_fromBlocks,
      Matrix.fromBlocks_apply₁₁] using hentry
  constructor
  · apply continuous_matrix
    intro i j
    have hentry : Continuous (fun a =>
        loadedJacobianMatrix ET FT ST (k a) u (Sum.inl i) (Sum.inr j)) :=
      hmat.matrix_elem (Sum.inl i) (Sum.inr j)
    simpa only [loadedJacobianMatrix_eq_fromBlocks,
      Matrix.fromBlocks_apply₁₂] using hentry
  constructor
  · apply continuous_matrix
    intro i j
    have hentry : Continuous (fun a =>
        loadedJacobianMatrix ET FT ST (k a) u (Sum.inr i) (Sum.inl j)) :=
      hmat.matrix_elem (Sum.inr i) (Sum.inl j)
    simpa only [loadedJacobianMatrix_eq_fromBlocks,
      Matrix.fromBlocks_apply₂₁] using hentry
  · apply continuous_matrix
    intro i j
    have hentry : Continuous (fun a =>
        loadedJacobianMatrix ET FT ST (k a) u (Sum.inr i) (Sum.inr j)) :=
      hmat.matrix_elem (Sum.inr i) (Sum.inr j)
    simpa only [loadedJacobianMatrix_eq_fromBlocks,
      Matrix.fromBlocks_apply₂₂] using hentry

end

end PhosphorylationStableCapacity
