module
public import proofs.PhosphorylationStableCapacity.FiniteRationalJacobianAction
public import proofs.PhosphorylationStableCapacity.FiniteMomentExplicitRow

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

def rationalLevelC {n : ℕ} (u : RationalSiteCoordinate n) (j : Fin (n+1)) : ℚ :=
  ∑ i : Fin n, if i.castSucc = j then u.2.1 i else 0

def rationalLevelD {n : ℕ} (u : RationalSiteCoordinate n) (j : Fin (n+1)) : ℚ :=
  ∑ i : Fin n, if i.succ = j then u.2.2 i else 0

def rationalOccupancy {n : ℕ} (ET FT : ℚ)
    (u : RationalSiteCoordinate n) (j : Fin (n+1)) : ℚ :=
  rationalLevelD u j / FT - rationalLevelC u j / ET

def rationalPhysicalTotalRow {n : ℕ} (ET FT ST : ℚ)
    (u : RationalSiteCoordinate n) (j : Fin (n+1)) : ℚ :=
  rationalSiteS ST u j + rationalLevelC u j * rationalSiteE ET u / ET +
    rationalLevelD u j * rationalSiteF FT u / FT

/-- The four physical moments are computed in exact rational arithmetic.
Their connection to the actual determinant is proved separately. -/
def rationalPhysicalMomentBracket {n : ℕ} (ET FT ST : ℚ)
    (u : RationalSiteCoordinate n) : ℚ :=
  (1 - ∑ j : Fin (n+1), (j.val : ℚ)*rationalOccupancy ET FT u j) *
    (∑ j : Fin (n+1), rationalPhysicalTotalRow ET FT ST u j) +
  (∑ j : Fin (n+1), rationalOccupancy ET FT u j) *
    (∑ j : Fin (n+1), (j.val : ℚ)*rationalPhysicalTotalRow ET FT ST u j)

theorem rationalLevelC_cast {n : ℕ} (ET FT ST : ℚ)
    (u : RationalSiteCoordinate n) (j : Fin (n+1)) :
    (rationalLevelC u j : ℝ) =
      sourceLevelC (unChart (ET : ℝ) (FT : ℝ) (ST : ℝ)
        (ofCoordinateSpace u.toReal)) j := by
  simp [rationalLevelC, sourceLevelC, unChart, ofCoordinateSpace,
    RationalSiteCoordinate.toReal, apply_ite]

theorem rationalLevelD_cast {n : ℕ} (ET FT ST : ℚ)
    (u : RationalSiteCoordinate n) (j : Fin (n+1)) :
    (rationalLevelD u j : ℝ) =
      sourceLevelD (unChart (ET : ℝ) (FT : ℝ) (ST : ℝ)
        (ofCoordinateSpace u.toReal)) j := by
  simp [rationalLevelD, sourceLevelD, unChart, ofCoordinateSpace,
    RationalSiteCoordinate.toReal, apply_ite]

theorem rationalSiteS_unchart_cast {n : ℕ} (ET FT ST : ℚ)
    (u : RationalSiteCoordinate n) (j : Fin (n+1)) :
    (rationalSiteS ST u j : ℝ) =
      (unChart (ET : ℝ) (FT : ℝ) (ST : ℝ)
        (ofCoordinateSpace u.toReal)).S j := by
  cases j using Fin.cases with
  | zero => simp [rationalSiteS, unChart, ofCoordinateSpace,
      RationalSiteCoordinate.toReal]
  | succ j => rfl

/-- Positivity makes the physical augmented total row available. The
rational evaluator then computes exactly the determinant-orientation
bracket of the same state, including all reconstructed free species. -/
theorem rationalPhysicalMomentBracket_cast {n : ℕ} (ET FT ST : ℚ)
    (u : RationalSiteCoordinate n)
    (hx : (unChart (ET : ℝ) (FT : ℝ) (ST : ℝ)
      (ofCoordinateSpace u.toReal)).Positive) :
    (rationalPhysicalMomentBracket ET FT ST u : ℝ) =
      (1 - sourcePathFirstMoment (sourceOccupancyDifference
        (unChart (ET : ℝ) (FT : ℝ) (ST : ℝ) (ofCoordinateSpace u.toReal)))) *
        sourcePathZerothMoment (sourceAugmentedTotalRow
          (unChart (ET : ℝ) (FT : ℝ) (ST : ℝ) (ofCoordinateSpace u.toReal))) +
      sourcePathZerothMoment (sourceOccupancyDifference
        (unChart (ET : ℝ) (FT : ℝ) (ST : ℝ) (ofCoordinateSpace u.toReal))) *
        sourcePathFirstMoment (sourceAugmentedTotalRow
          (unChart (ET : ℝ) (FT : ℝ) (ST : ℝ) (ofCoordinateSpace u.toReal))) := by
  let x := unChart (ET : ℝ) (FT : ℝ) (ST : ℝ) (ofCoordinateSpace u.toReal)
  have hc := unChart_inClass (ET : ℝ) (FT : ℝ) (ST : ℝ) (ofCoordinateSpace u.toReal)
  have hocc (j : Fin (n+1)) : (rationalOccupancy ET FT u j : ℝ) =
      sourceOccupancyDifference x j := by
    simp only [rationalOccupancy, Rat.cast_sub, Rat.cast_div,
      rationalLevelC_cast ET FT ST, rationalLevelD_cast ET FT ST,
      sourceOccupancyDifference]
    rw [hc.1, hc.2.1]
  have hrow (j : Fin (n+1)) : (rationalPhysicalTotalRow ET FT ST u j : ℝ) =
      sourceAugmentedTotalRow x j := by
    rw [sourceAugmentedTotalRow_eq_physical x hx]
    simp only [rationalPhysicalTotalRow, Rat.cast_add, Rat.cast_mul,
      Rat.cast_div, rationalSiteS_unchart_cast ET FT ST,
      rationalLevelC_cast ET FT ST, rationalLevelD_cast ET FT ST]
    rw [hc.1, hc.2.1]
    simp [x, rationalSiteE, rationalSiteF, unChart, ofCoordinateSpace,
      RationalSiteCoordinate.toReal]
  simp only [rationalPhysicalMomentBracket, Rat.cast_add, Rat.cast_sub,
    Rat.cast_mul, Rat.cast_sum, Rat.cast_one, Rat.cast_natCast,
    hocc, hrow, sourcePathZerothMoment, sourcePathFirstMoment]
  rfl

end
end PhosphorylationStableCapacity
