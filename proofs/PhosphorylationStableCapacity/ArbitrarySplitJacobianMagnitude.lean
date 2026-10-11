module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitChartMomentMagnitude
public import proofs.PhosphorylationStableCapacity.ExactJacobianScalarMagnitude

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- The exact determinant magnitude is the physical chart slope times
explicit source and fast-block factors at every arbitrary-offset root. -/
theorem arbitrarySplit_jacobian_chart_magnitude
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (k : Rates (m+1)) (hk : k.Positive)
    (hD : DensePositive (arbitrarySplitRawD m ξ r δ) m)
    (hB : DensePositive (arbitrarySplitRawB m ξ r δ) m)
    (j : Fin (2*m+1))
    (hy : 1 < offsetSplitRoot ξ δ j.val)
    (hv : 0 < r-ratio (offsetSplitRoot ξ δ j.val))
    (heq : Equilibrium k (arbitrarySplitFiniteState m ξ r δ j)) :
    let x := arbitrarySplitFiniteState m ξ r δ j
    let u := loadedCoordOfState x
    let D := LinearMap.toMatrix (fastBasis (m+1)) (fastBasis (m+1))
      (loadedBlockD (totalE x) (totalF x) (totalS x) k u).toLinearMap
    let M := sourceConstrainedBindingMass x
    let pivot := sourceAugmentedCurrentMatrix k x 0 0
    let Q0 := sourcePathZerothMoment (sourceOccupancyDifference x)
    let y₀ := offsetSplitRoot ξ δ j.val
    let b := (y₀/4) / ratio y₀
    (restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
      k (toCoordinateSpace (chart x))).det * M.det * pivot * b =
      D.det *
        (∏ i : Fin (m+2), sourceAugmentedRowWeight k x i) *
          ((-1 : ℝ)^(m+1) *
            (Q0 * deriv (fun y => arbitrarySplitChartResidual m ξ r δ y) y₀)) := by
  dsimp only
  let x := arbitrarySplitFiniteState m ξ r δ j
  let u := loadedCoordOfState x
  let D := LinearMap.toMatrix (fastBasis (m+1)) (fastBasis (m+1))
    (loadedBlockD (totalE x) (totalF x) (totalS x) k u).toLinearMap
  let M := sourceConstrainedBindingMass x
  let pivot := sourceAugmentedCurrentMatrix k x 0 0
  let Q0 := sourcePathZerothMoment (sourceOccupancyDifference x)
  let y₀ := offsetSplitRoot ξ δ j.val
  let b := (y₀/4) / ratio y₀
  let bracket :=
    (1-sourcePathFirstMoment (sourceOccupancyDifference x)) *
      sourcePathZerothMoment (sourceAugmentedTotalRow x) +
      Q0 * sourcePathFirstMoment (sourceAugmentedTotalRow x)
  obtain ⟨_, hx, _, _, _, _⟩ :=
    arbitrarySplitFiniteState_source_of_conversion_positive
      m ξ r δ hD hB j hy
  have hchain := equilibrium_restricted_jacobian_det_magnitude_chain
    k x hk hx heq
  change (restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
      k (toCoordinateSpace (chart x))).det * M.det * pivot =
      D.det *
        (∏ i : Fin (m+2), sourceAugmentedRowWeight k x i) *
          ((-1 : ℝ)^(m+1) * bracket) at hchain
  have hmagn := arbitrarySplitChart_moment_magnitude_at_root
    m ξ r δ hD hB j hy hv
  change b * bracket = Q0 *
    deriv (fun y => arbitrarySplitChartResidual m ξ r δ y) y₀ at hmagn
  calc
    (restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
      k (toCoordinateSpace (chart x))).det * M.det * pivot * b =
        (D.det *
          (∏ i : Fin (m+2), sourceAugmentedRowWeight k x i) *
            (-1 : ℝ)^(m+1)) * (b * bracket) := by
          rw [hchain]
          ring
    _ = D.det *
        (∏ i : Fin (m+2), sourceAugmentedRowWeight k x i) *
          ((-1 : ℝ)^(m+1) *
            (Q0 * deriv (fun y => arbitrarySplitChartResidual m ξ r δ y) y₀)) := by
          rw [hmagn]
          ring

/-- Literal restricted-Jacobian determinant identity with the exact
`δ^(2m)` arbitrary-root gap factor, for any kinetics preserving the
constructed equilibrium. -/
theorem arbitrarySplit_jacobian_exact_root_gap
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (k : Rates (m+1)) (hk : k.Positive)
    (hD : DensePositive (arbitrarySplitRawD m ξ r δ) m)
    (hB : DensePositive (arbitrarySplitRawB m ξ r δ) m)
    (j : Fin (2*m+1))
    (hy : 1 < offsetSplitRoot ξ δ j.val)
    (hv : 0 < r-ratio (offsetSplitRoot ξ δ j.val))
    (heq : Equilibrium k (arbitrarySplitFiniteState m ξ r δ j)) :
    let x := arbitrarySplitFiniteState m ξ r δ j
    let u := loadedCoordOfState x
    let D := LinearMap.toMatrix (fastBasis (m+1)) (fastBasis (m+1))
      (loadedBlockD (totalE x) (totalF x) (totalS x) k u).toLinearMap
    let M := sourceConstrainedBindingMass x
    let pivot := sourceAugmentedCurrentMatrix k x 0 0
    let Q0 := sourcePathZerothMoment (sourceOccupancyDifference x)
    let y₀ := offsetSplitRoot ξ δ j.val
    let b := (y₀/4) / ratio y₀
    let chartFactor := chartConversionMultiplier y₀ (r-ratio y₀)
      ((arbitrarySplitRawB m ξ r δ).eval (ratio y₀) /
        (arbitrarySplitRawD m ξ r δ).eval (ratio y₀)-r)
      ((arbitrarySplitRawD m ξ r δ).eval (ratio y₀))
    let conversionFactor :=
      4*r*(arbitrarySplitPair m ξ δ).1.eval r+
        (y₀-1)*(arbitrarySplitPair m ξ δ).2.eval r
    (restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
      k (toCoordinateSpace (chart x))).det * M.det * pivot * b =
      D.det *
        (∏ i : Fin (m+2), sourceAugmentedRowWeight k x i) *
          ((-1 : ℝ)^(m+1) *
            (Q0 * chartFactor * conversionFactor *
              (δ^(2*m) *
                ∏ i ∈ (Finset.range (2*m+1)).erase j.val,
                  (ξ j.val-ξ i)))) := by
  dsimp only
  have hbase := arbitrarySplit_jacobian_chart_magnitude
    m ξ r δ k hk hD hB j hy hv heq
  have hderiv := arbitrarySplitChartResidual_deriv_at_root
    m ξ r δ j hD hy hv
  dsimp only at hbase hderiv
  rw [hderiv] at hbase
  convert hbase using 1; ring

end
end PhosphorylationStableCapacity
