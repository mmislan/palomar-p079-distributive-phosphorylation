module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitPhysicalChart
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitJacobianMagnitude
public import proofs.PhosphorylationStableCapacity.SourcePhysicalPrefactor

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- The common geometric factor in the manuscript determinant formula,
with its physical rate product supplied by any positive literal
kinetic realization preserving the same split equilibrium. -/
def arbitrarySplitGenericPhysicalPrefactor
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (k : Rates (m+2)) (j : Fin (2*(m+1)+1)) : ℝ :=
  let x := arbitrarySplitFiniteState (m+1) ξ r δ j
  let y := offsetSplitRoot ξ δ j.val
  let u := ratio y
  let d := (arbitrarySplitRawD (m+1) ξ r δ).eval u
  let ell := (arbitrarySplitRawB (m+1) ξ r δ).eval u / d - r
  let chartFactor := chartConversionMultiplier y (r-u) ell d
  let conversionFactor :=
    4*r*(arbitrarySplitPair (m+1) ξ δ).1.eval r+
      (y-1)*(arbitrarySplitPair (m+1) ξ δ).2.eval r
  let rateProduct := ∏ i : Fin (m+2),
    (k.b i+k.c i)*k.alpha i*k.gamma i
  ((2*r)*2*x.F^(m+2)*rateProduct/(x.S 0*x.E*x.F)) *
    ((x.E/(2*r)-x.F/2)*chartFactor*conversionFactor/((y/4)/u))

set_option maxHeartbeats 800000 in
theorem arbitrarySplitGeneric_restrictedJacobian_det_root_gap
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (k : Rates (m+2)) (hk : k.Positive)
    (hD : DensePositive (arbitrarySplitRawD (m+1) ξ r δ) (m+1))
    (hB : DensePositive (arbitrarySplitRawB (m+1) ξ r δ) (m+1))
    (j : Fin (2*(m+1)+1))
    (hy : 1 < offsetSplitRoot ξ δ j.val)
    (hv : 0 < r-ratio (offsetSplitRoot ξ δ j.val))
    (heq : Equilibrium k (arbitrarySplitFiniteState (m+1) ξ r δ j))
    (hET : totalE (arbitrarySplitFiniteState (m+1) ξ r δ j) = 2*r)
    (hFT : totalF (arbitrarySplitFiniteState (m+1) ξ r δ j) = 2)
    (hST : totalS (arbitrarySplitFiniteState (m+1) ξ r δ j) = 2*(r+1)) :
    (restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k
      (toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j)))).det =
      (-1 : ℝ)^(m+2) *
        arbitrarySplitGenericPhysicalPrefactor m ξ r δ k j *
          (δ^(2*(m+1)) *
            ∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
              (ξ j.val-ξ i)) := by
  let x := arbitrarySplitFiniteState (m+1) ξ r δ j
  let y := offsetSplitRoot ξ δ j.val
  let M := sourceConstrainedBindingMass x
  let pivot := sourceAugmentedCurrentMatrix k x 0 0
  let D := LinearMap.toMatrix (fastBasis (m+2)) (fastBasis (m+2))
    (loadedBlockD (totalE x) (totalF x) (totalS x) k
      (loadedCoordOfState x)).toLinearMap
  let rowprod := ∏ i : Fin (m+3), sourceAugmentedRowWeight k x i
  let rateprod := ∏ i : Fin (m+2),
    (k.b i+k.c i)*k.alpha i*k.gamma i
  let Q0 := sourcePathZerothMoment (sourceOccupancyDifference x)
  let b := (y/4)/ratio y
  let chartFactor := chartConversionMultiplier y (r-ratio y)
    ((arbitrarySplitRawB (m+1) ξ r δ).eval (ratio y) /
      (arbitrarySplitRawD (m+1) ξ r δ).eval (ratio y)-r)
    ((arbitrarySplitRawD (m+1) ξ r δ).eval (ratio y))
  let conversionFactor :=
    4*r*(arbitrarySplitPair (m+1) ξ δ).1.eval r+
      (y-1)*(arbitrarySplitPair (m+1) ξ δ).2.eval r
  let gap := δ^(2*(m+1)) *
    ∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
      (ξ j.val-ξ i)
  have hx : x.Positive :=
    (arbitrarySplitFiniteState_source_of_conversion_positive
      (m+1) ξ r δ hD hB j hy).2.1
  have hdet := arbitrarySplit_jacobian_exact_root_gap
    (m+1) ξ r δ k hk hD hB j hy hv heq
  change (restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
      k (toCoordinateSpace (chart x))).det * M.det * pivot * b =
    D.det * rowprod *
      ((-1 : ℝ)^(m+2) * (Q0 * chartFactor * conversionFactor * gap))
    at hdet
  have hquot := equilibrium_loaded_fast_prefactor_quotient k x hx heq
  change D.det * rowprod / (M.det * pivot) =
    totalE x * totalF x * x.F^(m+2) /
      (x.S 0 * x.E * x.F) * rateprod at hquot
  have hm : M.det ≠ 0 := ne_of_gt (sourceConstrainedBindingMass_det_pos x hx)
  have hp : pivot ≠ 0 :=
    ne_of_gt (sourceAugmentedCurrentMatrix_pivot_pos k x hx)
  have hb : b ≠ 0 := by
    dsimp [b]
    exact div_ne_zero (div_ne_zero (by linarith : y ≠ 0)
      (by norm_num : (4 : ℝ) ≠ 0)) (ne_of_gt (ratio_pos hy))
  have hQ : Q0 = x.E/(2*r)-x.F/2 := by
    change (∑ i, sourceOccupancyDifference x i) =
      x.E/(2*r)-x.F/2
    rw [sourceOccupancyDifference_sum x hx, hET, hFT]
  have hprod : D.det * rowprod =
      M.det * pivot *
        (totalE x * totalF x * x.F^(m+2) /
          (x.S 0 * x.E * x.F) * rateprod) := by
    have := (div_eq_iff (mul_ne_zero hm hp)).mp hquot
    nlinarith [this]
  have hfactor :
      (restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
        k (toCoordinateSpace (chart x))).det =
        (-1 : ℝ)^(m+2) *
          ((totalE x * totalF x * x.F^(m+2) /
            (x.S 0 * x.E * x.F) * rateprod) *
            (Q0 * chartFactor * conversionFactor / b)) * gap := by
    apply (mul_right_cancel₀ hb)
    apply (mul_left_cancel₀ (mul_ne_zero hm hp))
    calc
      (M.det * pivot) *
          ((restrictedJacobianMatrix (totalE x) (totalF x)
            (totalS x) k (toCoordinateSpace (chart x))).det * b) =
          (restrictedJacobianMatrix (totalE x) (totalF x)
            (totalS x) k (toCoordinateSpace (chart x))).det *
              M.det * pivot * b := by ring
      _ = D.det * rowprod *
          ((-1 : ℝ)^(m+2) *
            (Q0 * chartFactor * conversionFactor * gap)) := hdet
      _ = (M.det * pivot) *
          (((-1 : ℝ)^(m+2) *
            ((totalE x * totalF x * x.F^(m+2) /
              (x.S 0 * x.E * x.F) * rateprod) *
              (Q0 * chartFactor * conversionFactor / b)) * gap) * b) := by
        rw [hprod]
        have hcancel :
            (Q0 * chartFactor * conversionFactor / b) * b =
              Q0 * chartFactor * conversionFactor :=
          div_mul_cancel₀ _ hb
        symm
        calc
          _ = (M.det * pivot) *
              (((-1 : ℝ)^(m+2) *
                (totalE x * totalF x * x.F^(m+2) /
                  (x.S 0 * x.E * x.F) * rateprod)) * gap) *
                (Q0 * chartFactor * conversionFactor / b * b) := by ring
          _ = (M.det * pivot) *
              (((-1 : ℝ)^(m+2) *
                (totalE x * totalF x * x.F^(m+2) /
                  (x.S 0 * x.E * x.F) * rateprod)) * gap) *
                (Q0 * chartFactor * conversionFactor) := by rw [hcancel]
          _ = _ := by ring
  rw [hET, hFT, hST] at hfactor
  change (restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k
      (toCoordinateSpace (chart x))).det =
      (-1 : ℝ)^(m+2) *
        arbitrarySplitGenericPhysicalPrefactor m ξ r δ k j * gap
  rw [hQ] at hfactor
  convert hfactor using 1
  dsimp only [arbitrarySplitGenericPhysicalPrefactor, x, y,
    chartFactor, conversionFactor, gap, rateprod, b]
  ring

/-- The same physical factorization in characteristic-polynomial
constant-term form, valid for any positive kinetics preserving these
same literal split equilibria. -/
theorem arbitrarySplitGeneric_charpoly_constant_root_gap
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (k : Rates (m+2)) (hk : k.Positive)
    (hD : DensePositive (arbitrarySplitRawD (m+1) ξ r δ) (m+1))
    (hB : DensePositive (arbitrarySplitRawB (m+1) ξ r δ) (m+1))
    (j : Fin (2*(m+1)+1))
    (hy : 1 < offsetSplitRoot ξ δ j.val)
    (hv : 0 < r-ratio (offsetSplitRoot ξ δ j.val))
    (heq : Equilibrium k (arbitrarySplitFiniteState (m+1) ξ r δ j))
    (hET : totalE (arbitrarySplitFiniteState (m+1) ξ r δ j) = 2*r)
    (hFT : totalF (arbitrarySplitFiniteState (m+1) ξ r δ j) = 2)
    (hST : totalS (arbitrarySplitFiniteState (m+1) ξ r δ j) = 2*(r+1)) :
    (restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k
      (toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j)))).charpoly.coeff 0 =
      arbitrarySplitGenericPhysicalPrefactor m ξ r δ k j *
        (δ^(2*(m+1)) *
          ∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
            (ξ j.val-ξ i)) := by
  have hdet := arbitrarySplitGeneric_restrictedJacobian_det_root_gap
    m ξ r δ k hk hD hB j hy hv heq hET hFT hST
  rw [Matrix.det_eq_sign_charpoly_coeff] at hdet
  simp only [Fintype.card_sum, Fintype.card_fin] at hdet
  have hsign : (-1 : ℝ)^((m+2)+((m+2)+(m+2))) =
      (-1 : ℝ)^(m+2) := by
    calc
      (-1 : ℝ)^((m+2)+((m+2)+(m+2))) =
          (-1 : ℝ)^(m+2) * (-1 : ℝ)^(2*(m+2)) := by
        rw [← pow_add]
        congr 1
        omega
      _ = (-1 : ℝ)^(m+2) := by
        rw [pow_mul]
        norm_num
  rw [hsign] at hdet
  apply (mul_left_cancel₀ (pow_ne_zero (m+2)
    (by norm_num : (-1 : ℝ) ≠ 0)))
  calc
    (-1 : ℝ)^(m+2) *
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k
        (toCoordinateSpace (chart
          (arbitrarySplitFiniteState (m+1) ξ r δ j)))).charpoly.coeff 0 =
        (-1 : ℝ)^(m+2) *
          arbitrarySplitGenericPhysicalPrefactor m ξ r δ k j *
            (δ^(2*(m+1)) *
              ∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
                (ξ j.val-ξ i)) := hdet
    _ = _ := by ring

end

end PhosphorylationStableCapacity
