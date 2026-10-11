module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitJacobianDifferentiability
public import proofs.PhosphorylationStableCapacity.LoadedJacobianCharpolyBridge

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix

/-- A fixed linear change of class coordinates conjugates the literal
restricted Jacobian into the loaded representation. The conjugating
matrices are independent of the split distance and all currents. -/
theorem loadedJacobianMatrix_eq_fixed_conjugate {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    loadedJacobianMatrix ET FT ST k u =
      LinearMap.toMatrix (coordinateBasis n) (coordinateBasis n)
        (loadedCoordLinear n).toLinearMap *
      restrictedJacobianMatrix ET FT ST k (fromLoadedCoord u) *
      LinearMap.toMatrix (coordinateBasis n) (coordinateBasis n)
        (loadedCoordLinear n).symm.toLinearMap := by
  have hlin :
      (fderiv ℝ (loadedRestrictedField ET FT ST k) u).toLinearMap =
        (loadedCoordLinear n).toLinearMap.comp
          ((restrictedJacobian ET FT ST k (fromLoadedCoord u)).toLinearMap.comp
            (loadedCoordLinear n).symm.toLinearMap) := by
    apply LinearMap.ext
    intro v
    simp [loadedRestrictedFderiv_conjugate,
      loadedCoordContinuous_apply, loadedCoordContinuous_symm_apply,
      loadedCoordLinear_apply, loadedCoordLinear_symm_apply]
  rw [loadedJacobianMatrix, restrictedJacobianMatrix, hlin]
  rw [LinearMap.toMatrix_comp (coordinateBasis n) (coordinateBasis n)
    (coordinateBasis n) (loadedCoordLinear n).toLinearMap
    ((restrictedJacobian ET FT ST k (fromLoadedCoord u)).toLinearMap.comp
      (loadedCoordLinear n).symm.toLinearMap),
    LinearMap.toMatrix_comp (coordinateBasis n) (coordinateBasis n)
      (coordinateBasis n)
      (restrictedJacobian ET FT ST k (fromLoadedCoord u)).toLinearMap
      (loadedCoordLinear n).symm.toLinearMap]
  rw [Matrix.mul_assoc]

/-- The fixed-final-current loaded Jacobian is differentiable as a
finite matrix at coalescence, using the already verified derivative of
the actual restricted Jacobian and the fixed conjugacy above. -/
theorem arbitrarySplit_fixedLoadedJacobian_differentiableAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1)) :
    DifferentiableAt ℝ (fun δ =>
      loadedJacobianMatrix (2*r) 2 (2*(r+1))
        (arbitrarySplitRetunedRates m ξ r τ δ ε)
        (loadedCoordOfState
          (arbitrarySplitFiniteState (m+1) ξ r δ j))) 0 := by
  have hrestricted := arbitrarySplit_restrictedJacobianMatrix_differentiableAt
    m ξ r τ ε hr hD₀ hB₀ j
  have hcoord (δ : ℝ) :
      fromLoadedCoord (loadedCoordOfState
        (arbitrarySplitFiniteState (m+1) ξ r δ j)) =
      toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j)) :=
    from_toLoadedCoord _
  simp_rw [loadedJacobianMatrix_eq_fixed_conjugate, hcoord]
  let A (δ : ℝ) := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
    (arbitrarySplitRetunedRates m ξ r τ δ ε)
    (toCoordinateSpace (chart
      (arbitrarySplitFiniteState (m+1) ξ r δ j)))
  let L := LinearMap.toMatrix (coordinateBasis (m+2))
    (coordinateBasis (m+2)) (loadedCoordLinear (m+2)).toLinearMap
  let R := LinearMap.toMatrix (coordinateBasis (m+2))
    (coordinateBasis (m+2)) (loadedCoordLinear (m+2)).symm.toLinearMap
  have hentry (i q) : DifferentiableAt ℝ (fun δ => A δ i q) 0 :=
    (differentiableAt_pi.mp (differentiableAt_pi.mp hrestricted i)) q
  change DifferentiableAt ℝ (fun δ => L * A δ * R) 0
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro q
  simp only [Matrix.mul_apply]
  apply DifferentiableAt.fun_sum
  intro p hp
  apply DifferentiableAt.mul
  · apply DifferentiableAt.fun_sum
    intro l hl
    exact (differentiableAt_const _).mul (hentry l p)
  · exact differentiableAt_const _

end

end PhosphorylationStableCapacity
