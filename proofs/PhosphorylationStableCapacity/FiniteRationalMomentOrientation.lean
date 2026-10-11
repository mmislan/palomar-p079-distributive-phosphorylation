module
public import proofs.PhosphorylationStableCapacity.FiniteRationalPhysicalMoment
public import proofs.PhosphorylationStableCapacity.FiniteMomentDetSign
public import proofs.PhosphorylationStableCapacity.SourceJacobianAugmentedOrientation
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

theorem charpoly_coeff_zero_eq_parity_det
    {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (hcard : Fintype.card ι = 3*n) (A : Matrix ι ι ℝ) :
    A.charpoly.coeff 0 = (-1 : ℝ)^n * A.det := by
  have hd := Matrix.det_eq_sign_charpoly_coeff A
  rw [hcard] at hd
  have hp : (-1 : ℝ)^(3*n) = (-1 : ℝ)^n := by
    rw [pow_mul]
    norm_num
  have hsq : (-1 : ℝ)^n * (-1 : ℝ)^n = 1 := by
    rw [← pow_add, show n+n = 2*n by omega, pow_mul]
    norm_num
  rw [hd, hp, ← mul_assoc, hsq, one_mul]

theorem rationalPhysicalMomentBracket_cast_of_actual
    {n : ℕ} (ET FT ST : ℚ) (u : RationalSiteCoordinate n) (x : State n)
    (hx : x.Positive) (hclass : InClass (ET : ℝ) (FT : ℝ) (ST : ℝ) x)
    (hcoord : u.toReal = toCoordinateSpace (chart x)) :
    (rationalPhysicalMomentBracket ET FT ST u : ℝ) =
      (1-sourcePathFirstMoment (sourceOccupancyDifference x))*
        sourcePathZerothMoment (sourceAugmentedTotalRow x) +
      sourcePathZerothMoment (sourceOccupancyDifference x)*
        sourcePathFirstMoment (sourceAugmentedTotalRow x) := by
  have hback : unChart (ET : ℝ) (FT : ℝ) (ST : ℝ)
      (ofCoordinateSpace u.toReal) = x := by
    rw [hcoord, of_toCoordinateSpace]
    exact unChart_chart_of_inClass _ _ _ x hclass
  have hpositive : (unChart (ET : ℝ) (FT : ℝ) (ST : ℝ)
      (ofCoordinateSpace u.toReal)).Positive := by rw [hback]; exact hx
  simpa only [hback] using rationalPhysicalMomentBracket_cast ET FT ST u hpositive

/-- A closed exact rational moment sign determines the characteristic
constant of the same literal physical Jacobian. -/
theorem rational_moment_positive_charpoly_constant
    {n : ℕ} (ET FT ST : ℚ) (u : RationalSiteCoordinate n)
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive) (heq : Equilibrium k x)
    (hclass : InClass (ET : ℝ) (FT : ℝ) (ST : ℝ) x)
    (hcoord : u.toReal = toCoordinateSpace (chart x))
    (hpositive : 0 < rationalPhysicalMomentBracket ET FT ST u) :
    0 < (restrictedJacobianMatrix (ET : ℝ) (FT : ℝ) (ST : ℝ)
      k (toCoordinateSpace (chart x))).charpoly.coeff 0 := by
  have hcast : (0 : ℝ) < (rationalPhysicalMomentBracket ET FT ST u : ℝ) :=
    Rat.cast_pos.mpr hpositive
  rw [rationalPhysicalMomentBracket_cast_of_actual ET FT ST u x hx hclass hcoord]
    at hcast
  have hdet := (equilibrium_restricted_jacobian_parity_det_pos_iff_moment
    k x hk hx heq).2 hcast
  rw [hclass.1, hclass.2.1, hclass.2.2] at hdet
  rw [charpoly_coeff_zero_eq_parity_det n (by
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      (show n + (n+n) = 3*n by omega))]
  exact hdet

theorem rational_moment_negative_charpoly_constant
    {n : ℕ} (ET FT ST : ℚ) (u : RationalSiteCoordinate n)
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive) (heq : Equilibrium k x)
    (hclass : InClass (ET : ℝ) (FT : ℝ) (ST : ℝ) x)
    (hcoord : u.toReal = toCoordinateSpace (chart x))
    (hnegative : rationalPhysicalMomentBracket ET FT ST u < 0) :
    (restrictedJacobianMatrix (ET : ℝ) (FT : ℝ) (ST : ℝ)
      k (toCoordinateSpace (chart x))).charpoly.coeff 0 < 0 := by
  have hcast : (rationalPhysicalMomentBracket ET FT ST u : ℝ) < 0 :=
    Rat.cast_lt_zero.mpr hnegative
  rw [rationalPhysicalMomentBracket_cast_of_actual ET FT ST u x hx hclass hcoord]
    at hcast
  have hdet := (equilibrium_restricted_jacobian_parity_det_neg_iff_moment
    k x hk hx heq).2 hcast
  rw [hclass.1, hclass.2.1, hclass.2.2] at hdet
  rw [charpoly_coeff_zero_eq_parity_det n (by
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      (show n + (n+n) = 3*n by omega))]
  exact hdet

end
end PhosphorylationStableCapacity
