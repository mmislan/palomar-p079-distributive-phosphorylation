module
public import proofs.PhosphorylationStableCapacity.OneSiteLyapunovCertificate

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness
open scoped Matrix

noncomputable section

def oneSiteDisplacementField (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-v 0 + v 1 + 2*v 2 + v 0*v 2,
    -v 0 - 4*v 1 - v 2 + v 1*(v 0 + v 1 + v 2),
    v 0 - 3*v 2 - v 0*v 2]

def oneSiteEnergySlope (v : Fin 3 → ℝ) : ℝ :=
  2 * (star v ⬝ᵥ (oneSiteP *ᵥ oneSiteDisplacementField v))

theorem oneSite_energy_slope_formula (a b c : ℝ) :
    oneSiteEnergySlope ![a,b,c] =
      -(a^2 + b^2 + c^2) +
      (40*a^2*b + 96*a^2*c + 84*a*b^2 + 80*a*b*c +
        4*a*c^2 + 44*b^3 + 67*b^2*c + 23*b*c^2) / 136 := by
  simp [oneSiteEnergySlope, oneSiteDisplacementField,
    oneSiteP, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  ring

/-- The quadratic error in the literal unit-rate one-site field is
small enough on the coordinate box of radius `1/10` that the exact
Lyapunov energy still has a strictly negative derivative. This is
an algebraic bound on the cubic remainder, not yet a trajectory
stability theorem. -/
theorem oneSite_cubic_remainder_bound
    (a b c : ℝ)
    (ha : a ≤ 1/10) (hb : b ≤ 1/10)
    (hcl : -(1/10 : ℝ) ≤ c) (hcu : c ≤ 1/10) :
    (40*a^2*b + 96*a^2*c + 84*a*b^2 + 80*a*b*c +
      4*a*c^2 + 44*b^3 + 67*b^2*c + 23*b*c^2) / 136 ≤
      (a^2 + b^2 + c^2) / 2 := by
  have h1 : a^2*b ≤ a^2/10 := by
    nlinarith only [mul_nonneg (by linarith : 0 ≤ (1/10 : ℝ)-b) (sq_nonneg a)]
  have h2 : a^2*c ≤ a^2/10 := by
    nlinarith only [mul_nonneg (by linarith : 0 ≤ (1/10 : ℝ)-c) (sq_nonneg a)]
  have h3 : a*b^2 ≤ b^2/10 := by
    nlinarith only [mul_nonneg (by linarith : 0 ≤ (1/10 : ℝ)-a) (sq_nonneg b)]
  have h4 : a*c^2 ≤ c^2/10 := by
    nlinarith only [mul_nonneg (by linarith : 0 ≤ (1/10 : ℝ)-a) (sq_nonneg c)]
  have h5 : b^3 ≤ b^2/10 := by
    nlinarith only [mul_nonneg (by linarith : 0 ≤ (1/10 : ℝ)-b) (sq_nonneg b)]
  have h6 : b^2*c ≤ b^2/10 := by
    nlinarith only [mul_nonneg (by linarith : 0 ≤ (1/10 : ℝ)-c) (sq_nonneg b)]
  have h7 : b*c^2 ≤ c^2/10 := by
    nlinarith only [mul_nonneg (by linarith : 0 ≤ (1/10 : ℝ)-b) (sq_nonneg c)]
  have h8 : a*b*c ≤ (a^2+b^2)/20 := by
    by_cases hab : 0 ≤ a*b
    · calc
        a*b*c ≤ (a*b)/10 := by
          have hp := mul_le_mul_of_nonneg_left hcu hab
          nlinarith only [hp]
        _ ≤ (a^2+b^2)/20 := by
          nlinarith only [sq_nonneg (a-b)]
    · have hneg : a*b ≤ 0 := le_of_lt (lt_of_not_ge hab)
      calc
        a*b*c ≤ -(a*b)/10 := by
          have hp := mul_le_mul_of_nonpos_left hcl hneg
          nlinarith only [hp]
        _ ≤ (a^2+b^2)/20 := by
          nlinarith only [sq_nonneg (a+b)]
  linarith only [h1, h2, h3, h4, h5, h6, h7, h8,
    sq_nonneg a, sq_nonneg b, sq_nonneg c]

theorem oneSite_energy_slope_negative
    (a b c : ℝ)
    (ha : a ≤ 1/10) (hb : b ≤ 1/10)
    (hcl : -(1/10 : ℝ) ≤ c) (hcu : c ≤ 1/10) :
    oneSiteEnergySlope ![a,b,c] ≤
      -(a^2+b^2+c^2)/2 := by
  rw [oneSite_energy_slope_formula]
  have h := oneSite_cubic_remainder_bound a b c ha hb hcl hcu
  linarith

def oneSiteCoordinateVector (u : CoordinateSpace 1) : Fin 3 → ℝ :=
  ![u.1 0, u.2.1 0, u.2.2 0]

def oneSiteDisplacement (u : CoordinateSpace 1) : Fin 3 → ℝ :=
  oneSiteCoordinateVector u - ![1, (1/2 : ℝ), 1/2]

/-- The nonlinear displacement field used in the energy calculation
is exactly the literal one-site restricted mass-action field. -/
theorem oneSiteDisplacementField_eq_literal (u : CoordinateSpace 1) :
    oneSiteDisplacementField (oneSiteDisplacement u) =
      oneSiteCoordinateVector
        (restrictedFieldEuclid (3/2) (3/2) 3 oneRates u) := by
  rw [restrictedFieldEuclid_one]
  ext i
  fin_cases i <;>
    simp [oneSiteDisplacementField, oneSiteDisplacement,
      oneSiteCoordinateVector, oneField] <;> ring

end
end PhosphorylationStableCapacity
