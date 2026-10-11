module
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import proofs.PhosphorylationStableCapacity.GeneralEquilibriumPolynomialSigns

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Polynomial

set_option maxHeartbeats 1000000

/-- The coefficient immediately above the forced zero is negative.
This is the sign of the eliminant just to the left of `u=0`. -/
theorem equilibriumEliminationPoly_coeff_one {n : ℕ}
    (k : Rates n) (ET FT ST : ℝ) :
    (equilibriumEliminationPoly k ET FT ST).coeff 1 =
      -(ET*FT*(kinaseComplexPoly k).coeff 1) := by
  let T := freeSubstratePoly k
  let B := kinaseComplexPoly k
  let D := phosphataseComplexPoly k
  let A : ℝ[X] := C ET-C FT*X
  let Q : ℝ[X] := C FT*B-C ET*D
  let R : ℝ[X] := Q+A*D
  have hT0 : T.coeff 0 = 1 := freeSubstratePoly_coeff_zero k
  have hB0 : B.coeff 0 = 0 := kinaseComplexPoly_coeff_zero k
  have hD0 : D.coeff 0 = 0 := phosphataseComplexPoly_coeff_zero k
  have hA0 : A.coeff 0 = ET := by dsimp [A]; simp
  have hQ0 : Q.coeff 0 = 0 := by
    dsimp [Q]
    simp [hB0, hD0]
  have hR0 : R.coeff 0 = 0 := by
    dsimp [R]
    simp [hQ0, hA0, hD0]
  have hR1 : R.coeff 1 = FT*B.coeff 1 := by
    dsimp [R, Q]
    simp only [coeff_add, coeff_sub, mul_coeff_one,
      hB0, hD0, hA0, coeff_C_zero,
      mul_zero, add_zero]
    ring
  have hterm1 : (C ST*Q*R).coeff 1 = 0 := by
    rw [mul_coeff_one]
    simp [hQ0, hR0]
  have hterm2 : (A*T*R).coeff 1 = ET*FT*B.coeff 1 := by
    rw [mul_coeff_one, hR0, hR1]
    simp [hA0, hT0]
    ring
  have hterm3 : (C FT*A*(B+D)*Q).coeff 1 = 0 := by
    rw [mul_coeff_one]
    simp [hQ0, hB0, hD0]
  change (C ST*Q*R-A*T*R-C FT*A*(B+D)*Q).coeff 1 =
    -(ET*FT*B.coeff 1)
  rw [coeff_sub, coeff_sub, hterm1, hterm2, hterm3]
  ring

theorem equilibriumEliminationPoly_coeff_one_neg {n : ℕ}
    (k : Rates n) (hn : 0 < n) (hk : k.Positive)
    (ET FT ST : ℝ) (hET : 0 < ET) (hFT : 0 < FT) :
    (equilibriumEliminationPoly k ET FT ST).coeff 1 < 0 := by
  rw [equilibriumEliminationPoly_coeff_one,
    kinaseComplexPoly_coeff_one k hn]
  exact neg_lt_zero.mpr
    (mul_pos (mul_pos hET hFT)
      (kinaseBindingRatio_pos k hk _))

/-- In addition to the forced zero at `u=0`, the arbitrary-rate
eliminant has a strictly negative real root. This is the only
root-exclusion fact needed for the `2n` budget used by the index
arithmetic; it does not assert the sharper published `2n-1` bound. -/
theorem equilibriumEliminationPoly_negative_root {n : ℕ}
    (k : Rates n) (hn : 0 < n) (hk : k.Positive)
    (ET FT ST : ℝ) (hET : 0 < ET) (hFT : 0 < FT) :
    ∃ u : ℝ, u < 0 ∧
      (equilibriumEliminationPoly k ET FT ST).eval u = 0 := by
  let P := equilibriumEliminationPoly k ET FT ST
  let Q := P.divX
  have htop : P.coeff (2*n+2) < 0 :=
    equilibriumEliminationPoly_top_coeff_neg k hn hk ET FT ST hFT
  have hdeg : P.natDegree = 2*n+2 :=
    natDegree_eq_of_le_of_coeff_ne_zero
      (equilibriumEliminationPoly_natDegree_le k ET FT ST)
      (ne_of_lt htop)
  have hP0 : P.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    exact equilibriumEliminationPoly_zero_root k ET FT ST
  have hfactor : Q*X = P := by
    have h := divX_mul_X_add P
    rw [hP0, map_zero, add_zero] at h
    exact h
  have hQdeg : Q.natDegree = 2*n+1 := by
    change P.divX.natDegree = 2*n+1
    rw [natDegree_divX_eq_natDegree_tsub_one, hdeg]
    omega
  have hPlc : P.leadingCoeff < 0 := by
    simpa only [leadingCoeff, hdeg] using htop
  have hQlc : Q.leadingCoeff < 0 := by
    rw [← leadingCoeff_mul_X, hfactor]
    exact hPlc
  have hQ0 : Q.eval 0 < 0 := by
    rw [← coeff_zero_eq_eval_zero]
    change P.divX.coeff 0 < 0
    rw [coeff_divX]
    exact equilibriumEliminationPoly_coeff_one_neg
      k hn hk ET FT ST hET hFT
  let S := Q.comp (-X)
  have hsign : (-1 : ℝ)^(2*n+1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  have hSlc : 0 < S.leadingCoeff := by
    change 0 < (Q.comp (-X)).leadingCoeff
    rw [comp_neg_X_leadingCoeff_eq, hQdeg, hsign]
    linarith
  have hSdeg : 0 < S.degree := by
    change 0 < (Q.comp (-X)).degree
    rw [degree_comp_neg_X]
    exact natDegree_pos_iff_degree_pos.mp (by omega)
  have hsend : Filter.Tendsto (fun x : ℝ => S.eval x)
      Filter.atTop Filter.atTop :=
    S.tendsto_atTop_of_leadingCoeff_nonneg hSdeg hSlc.le
  obtain ⟨a, ha, hSa⟩ :=
    ((Filter.eventually_gt_atTop (0 : ℝ)).and
      (hsend.eventually_gt_atTop 0)).exists
  have hS0 : S.eval 0 < 0 := by
    simpa [S] using hQ0
  obtain ⟨r, hr, hSr⟩ :=
    (intermediate_value_Icc ha.le S.continuous.continuousOn)
      ⟨hS0.le, hSa.le⟩
  have hrpos : 0 < r := by
    have hrne : r ≠ 0 := by
      intro hzero
      subst r
      linarith
    exact lt_of_le_of_ne hr.1 (Ne.symm hrne)
  refine ⟨-r, by linarith, ?_⟩
  have hQr : Q.eval (-r) = 0 := by
    simpa [S] using hSr
  change P.eval (-r) = 0
  rw [← hfactor, eval_mul, eval_X, hQr, zero_mul]

end
end PhosphorylationStableCapacity
