module
public import proofs.PhosphorylationStableCapacity.ExactJacobianScalarMagnitude
public import proofs.PhosphorylationStableCapacity.RatioCurveMomentIdentities

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness

/-- Exact magnitude version of the model-specific moment-to-residual
slope step. The existing orientation theorem is its sign consequence. -/
theorem ratio_curve_moment_residual_magnitude
    {n : ℕ} (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u)
    (hroot : ratioEnzymeResidual k ET FT ST u = 0) :
    let x := ratioEquilibriumCurve k FT ST u
    let T0 := sourcePathZerothMoment (sourceAugmentedTotalRow x)
    let T1 := sourcePathFirstMoment (sourceAugmentedTotalRow x)
    let Q0 := sourcePathZerothMoment (sourceOccupancyDifference x)
    let Q1 := sourcePathFirstMoment (sourceOccupancyDifference x)
    let C := ∑ i : Fin n, x.C i
    let den := 1 + modelRatioSubstrateLevel k FT ST u *
      phosphataseComplexInventory k u
    totalE x * den * ((1-Q1)*T0+Q0*T1) =
      (T0-Q0*C)*u*deriv (ratioEnzymeResidual k ET FT ST) u := by
  dsimp only
  let x := ratioEquilibriumCurve k FT ST u
  let T0 := sourcePathZerothMoment (sourceAugmentedTotalRow x)
  let T1 := sourcePathFirstMoment (sourceAugmentedTotalRow x)
  let Q0 := sourcePathZerothMoment (sourceOccupancyDifference x)
  let Q1 := sourcePathFirstMoment (sourceOccupancyDifference x)
  let C := ∑ i : Fin n, x.C i
  let den := 1 + modelRatioSubstrateLevel k FT ST u *
    phosphataseComplexInventory k u
  let dET := deriv (ratioCurveKinaseTotal k FT ST) u
  let a := ratioCurveSubstrateLogSlope k FT ST u
  obtain ⟨hsubstrate, henzyme⟩ :=
    ratioCurve_exact_moment_slope_identities
      hn k hk FT ST u hFT hST hu
  have hmoment : totalE x * ((1-Q1)*T0+Q0*T1) =
      (T0-Q0*C)*u*dET :=
    moment_bracket_mul_total_eq_slope
      T0 T1 Q0 Q1 C a (totalE x) u dET
      hsubstrate henzyme
  have hres := ratioEnzymeResidual_deriv_at_root_eq_curve_total_deriv
    hn k hk ET FT ST u hST hu hroot
  change deriv (ratioEnzymeResidual k ET FT ST) u = den*dET at hres
  rw [hres]
  calc
    totalE x * den * ((1-Q1)*T0+Q0*T1) =
        den * (totalE x * ((1-Q1)*T0+Q0*T1)) := by ring
    _ = den * ((T0-Q0*C)*u*dET) := by rw [hmoment]
    _ = (T0-Q0*C)*u*(den*dET) := by ring

/-- The complete exact determinant-to-residual magnitude identity at a
positive scalar root. All omitted-looking factors are explicit physical
determinants and totals; no sign equivalence is used in this equality. -/
theorem ratio_curve_jacobian_residual_magnitude
    {n : ℕ} (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u)
    (hroot : ratioEnzymeResidual k ET FT ST u = 0) :
    let x := ratioEquilibriumCurve k FT ST u
    let v := loadedCoordOfState x
    let D := LinearMap.toMatrix (fastBasis n) (fastBasis n)
      (loadedBlockD (totalE x) (totalF x) (totalS x) k v).toLinearMap
    let M := sourceConstrainedBindingMass x
    let pivot := sourceAugmentedCurrentMatrix k x 0 0
    let T0 := sourcePathZerothMoment (sourceAugmentedTotalRow x)
    let Q0 := sourcePathZerothMoment (sourceOccupancyDifference x)
    let C := ∑ i : Fin n, x.C i
    let den := 1 + modelRatioSubstrateLevel k FT ST u *
      phosphataseComplexInventory k u
    (restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
      k (toCoordinateSpace (chart x))).det * M.det * pivot * totalE x * den =
      D.det *
        (∏ i : Fin (n+1), sourceAugmentedRowWeight k x i) *
          ((-1 : ℝ)^n * ((T0-Q0*C)*u*
            deriv (ratioEnzymeResidual k ET FT ST) u)) := by
  dsimp only
  let x := ratioEquilibriumCurve k FT ST u
  let v := loadedCoordOfState x
  let D := LinearMap.toMatrix (fastBasis n) (fastBasis n)
    (loadedBlockD (totalE x) (totalF x) (totalS x) k v).toLinearMap
  let M := sourceConstrainedBindingMass x
  let pivot := sourceAugmentedCurrentMatrix k x 0 0
  let T0 := sourcePathZerothMoment (sourceAugmentedTotalRow x)
  let T1 := sourcePathFirstMoment (sourceAugmentedTotalRow x)
  let Q0 := sourcePathZerothMoment (sourceOccupancyDifference x)
  let Q1 := sourcePathFirstMoment (sourceOccupancyDifference x)
  let C := ∑ i : Fin n, x.C i
  let den := 1 + modelRatioSubstrateLevel k FT ST u *
    phosphataseComplexInventory k u
  let bracket := (1-Q1)*T0+Q0*T1
  obtain ⟨hx, heq, _, _, _, _⟩ :=
    ratioEquilibriumCurve_positive_equilibrium_and_totals
      hn k hk FT ST u hFT hST hu
  have hchain := equilibrium_restricted_jacobian_det_magnitude_chain
    k x hk hx heq
  change (restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
      k (toCoordinateSpace (chart x))).det * M.det * pivot =
      D.det *
        (∏ i : Fin (n+1), sourceAugmentedRowWeight k x i) *
          ((-1 : ℝ)^n * bracket) at hchain
  have hmagn := ratio_curve_moment_residual_magnitude
    hn k hk ET FT ST u hFT hST hu hroot
  change totalE x * den * bracket =
      (T0-Q0*C)*u*deriv (ratioEnzymeResidual k ET FT ST) u at hmagn
  calc
    (restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
      k (toCoordinateSpace (chart x))).det * M.det * pivot * totalE x * den =
        (D.det *
          (∏ i : Fin (n+1), sourceAugmentedRowWeight k x i) *
            (-1 : ℝ)^n) * (totalE x * den * bracket) := by
          rw [hchain]
          ring
    _ = D.det *
        (∏ i : Fin (n+1), sourceAugmentedRowWeight k x i) *
          ((-1 : ℝ)^n * ((T0-Q0*C)*u*
            deriv (ratioEnzymeResidual k ET FT ST) u)) := by
          rw [hmagn]
          ring

end
end PhosphorylationStableCapacity
