module
public import proofs.PhosphorylationStableCapacity.FiniteTwoSitePaperTailGap
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/- Six fixed-size rational determinant evaluations, following the already
strictly checked FiniteTwoSiteSaddleCharpolyPilot kernel-computation method. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def twoSiteRoundedCenter (j : Fin 3) : ℚ :=
  ![-3 / 250, 1 / 200, -21 / 2500] j

private def twoSiteRoundedRationalMatrix (j : Fin 3) : Matrix (Fin 6) (Fin 6) ℚ :=
  ![manuscriptTwoSiteA0, manuscriptTwoSiteA1, manuscriptTwoSiteA2] j

private theorem twoSiteRoundedRationalMatrix_endpoint_signs (j : Fin 3) :
    (twoSiteRoundedRationalMatrix j).charpoly.eval
      (twoSiteRoundedCenter j - 1 / 20000) < 0 ∧
    0 < (twoSiteRoundedRationalMatrix j).charpoly.eval
      (twoSiteRoundedCenter j + 1 / 20000) := by
  fin_cases j
  all_goals constructor
  all_goals rw [Matrix.eval_charpoly]
  all_goals decide +kernel

private theorem twoSiteRoundedRationalMatrix_cast (j : Fin 3) :
    manuscriptTwoSiteMatrixFin j =
      (twoSiteRoundedRationalMatrix j).map (Rat.castHom ℝ) := by
  fin_cases j
  · change manuscriptTwoSiteMatrixFin 0 =
      (twoSiteRoundedRationalMatrix 0).map (Rat.castHom ℝ)
    rw [manuscriptTwoSiteMatrixFin_zero_eq]
    change manuscriptTwoSiteA0.map (fun q : ℚ => (q : ℝ)) =
      manuscriptTwoSiteA0.map (Rat.castHom ℝ)
    simp only [Rat.coe_castHom]
  · change manuscriptTwoSiteMatrixFin 1 =
      (twoSiteRoundedRationalMatrix 1).map (Rat.castHom ℝ)
    rw [manuscriptTwoSiteMatrixFin_one_eq]
    change manuscriptTwoSiteA1.map (fun q : ℚ => (q : ℝ)) =
      manuscriptTwoSiteA1.map (Rat.castHom ℝ)
    simp only [Rat.coe_castHom]
  · change manuscriptTwoSiteMatrixFin 2 =
      (twoSiteRoundedRationalMatrix 2).map (Rat.castHom ℝ)
    rw [manuscriptTwoSiteMatrixFin_two_eq]
    change manuscriptTwoSiteA2.map (fun q : ℚ => (q : ℝ)) =
      manuscriptTwoSiteA2.map (Rat.castHom ℝ)
    simp only [Rat.coe_castHom]

private theorem twoSiteRounded_real_endpoint_signs (j : Fin 3) :
    (manuscriptTwoSiteMatrixFin j).charpoly.eval
      ((twoSiteRoundedCenter j : ℝ) - 1 / 20000) < 0 ∧
    0 < (manuscriptTwoSiteMatrixFin j).charpoly.eval
      ((twoSiteRoundedCenter j : ℝ) + 1 / 20000) := by
  obtain ⟨hl, hu⟩ := twoSiteRoundedRationalMatrix_endpoint_signs j
  rw [twoSiteRoundedRationalMatrix_cast, Matrix.charpoly_map]
  constructor
  · have hcast :
        ((twoSiteRoundedRationalMatrix j).charpoly.map (Rat.castHom ℝ)).eval
          (((twoSiteRoundedCenter j - 1 / 20000 : ℚ) : ℝ)) < 0 := by
      have hmap :
          ((twoSiteRoundedRationalMatrix j).charpoly.map (Rat.castHom ℝ)).eval
            (((twoSiteRoundedCenter j - 1 / 20000 : ℚ) : ℝ)) =
              (((twoSiteRoundedRationalMatrix j).charpoly.eval
                (twoSiteRoundedCenter j - 1 / 20000) : ℚ) : ℝ) := by
        simpa only [Rat.coe_castHom] using Polynomial.eval_map_apply
          (p := (twoSiteRoundedRationalMatrix j).charpoly) (f := Rat.castHom ℝ)
          (twoSiteRoundedCenter j - 1 / 20000)
      rw [hmap]
      exact_mod_cast hl
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hcast
  · have hcast :
        0 < ((twoSiteRoundedRationalMatrix j).charpoly.map (Rat.castHom ℝ)).eval
          (((twoSiteRoundedCenter j + 1 / 20000 : ℚ) : ℝ)) := by
      have hmap :
          ((twoSiteRoundedRationalMatrix j).charpoly.map (Rat.castHom ℝ)).eval
            (((twoSiteRoundedCenter j + 1 / 20000 : ℚ) : ℝ)) =
              (((twoSiteRoundedRationalMatrix j).charpoly.eval
                (twoSiteRoundedCenter j + 1 / 20000) : ℚ) : ℝ) := by
        simpa only [Rat.coe_castHom] using Polynomial.eval_map_apply
          (p := (twoSiteRoundedRationalMatrix j).charpoly) (f := Rat.castHom ℝ)
          (twoSiteRoundedCenter j + 1 / 20000)
      rw [hmap]
      exact_mod_cast hu
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hcast

private theorem oneDominantTailGap_localized
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (c e : ℝ) (he : 0 < e)
    (hleft : -2 < c - e)
    (hl : A.charpoly.eval (c - e) < 0)
    (hu : 0 < A.charpoly.eval (c + e))
    (hgap : OneDominantTailGap A) :
    ∃ x : ℝ, -2 < x ∧ A.charpoly.IsRoot x ∧ |x - c| < e ∧
      ((A.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ, z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) →
        z.re < -2 ∨ z = (x : ℂ) := by
  obtain ⟨x, hx, hxroot, hsimple, hrest⟩ := hgap
  have hzero : (0 : ℝ) ∈ Set.Icc (A.charpoly.eval (c - e))
      (A.charpoly.eval (c + e)) := ⟨hl.le, hu.le⟩
  obtain ⟨y, hy, hyroot⟩ := (Set.mem_image _ _ _).mp
    (intermediate_value_Icc (by linarith : c - e ≤ c + e)
      A.charpoly.continuous.continuousOn hzero)
  have hylo : c - e < y := by
    apply lt_of_le_of_ne hy.1
    rintro rfl
    exact ne_of_lt hl hyroot
  have hyhi : y < c + e := by
    apply lt_of_le_of_ne hy.2
    rintro rfl
    exact ne_of_gt hu hyroot
  have hyspectrum : (y : ℂ) ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) := by
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    change (A.map (algebraMap ℝ ℂ)).charpoly.eval (y : ℂ) = 0
    rw [Matrix.charpoly_map]
    have hmap : (A.charpoly.map (algebraMap ℝ ℂ)).eval (y : ℂ) =
        ((A.charpoly.eval y : ℝ) : ℂ) := by
      simpa using Polynomial.eval_map_apply
        (p := A.charpoly) (f := algebraMap ℝ ℂ) y
    rw [hmap]
    exact_mod_cast hyroot
  have hyx : y = x := by
    rcases hrest (y : ℂ) hyspectrum with hbad | heq
    · have hbad' : y < -2 := by simpa only [Complex.ofReal_re] using hbad
      linarith
    · exact_mod_cast heq
  refine ⟨x, hx, hxroot, ?_, hsimple, hrest⟩
  rw [hyx] at hylo hyhi
  exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩

/-- The same actual simple dominant root lies strictly inside the decimal
rounding bin. This retains the existing five-root tail bound, not merely a
root of a separately constructed numerical polynomial. -/
theorem manuscriptTwoSiteMatrixFin_dominant_root_rounding (j : Fin 3) :
    ∃ x : ℝ, -2 < x ∧ (manuscriptTwoSiteMatrixFin j).charpoly.IsRoot x ∧
      |x - (twoSiteRoundedCenter j : ℝ)| < 1 / 20000 ∧
      (((manuscriptTwoSiteMatrixFin j).map (algebraMap ℝ ℂ)).charpoly).derivative.eval
        (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ, z ∈ spectrum ℂ ((manuscriptTwoSiteMatrixFin j).map
        (algebraMap ℝ ℂ)) → z.re < -2 ∨ z = (x : ℂ) := by
  obtain ⟨hl, hu⟩ := twoSiteRounded_real_endpoint_signs j
  apply oneDominantTailGap_localized _ _ _ (by norm_num) _ hl hu
    (manuscriptTwoSiteMatrixFin_all_tail_gap j)
  fin_cases j <;> norm_num [twoSiteRoundedCenter]

/-- Literal published rates, totals and states; all three displayed four-decimal
approximations have error strictly below half a unit in the last digit. -/
theorem manuscriptTwoSite_literal_dominant_root_rounding (j : Fin 3) :
    ∃ x : ℝ, -2 < x ∧
      (restrictedJacobianMatrix 4 2 6 manuscriptTwoSiteRates
        (toCoordinateSpace (chart (manuscriptTwoSiteStates j)))).charpoly.IsRoot x ∧
      |x - (twoSiteRoundedCenter j : ℝ)| < 1 / 20000 ∧
      (((restrictedJacobianMatrix 4 2 6 manuscriptTwoSiteRates
        (toCoordinateSpace (chart (manuscriptTwoSiteStates j)))).map
        (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ, z ∈ spectrum ℂ ((restrictedJacobianMatrix 4 2 6
        manuscriptTwoSiteRates (toCoordinateSpace (chart (manuscriptTwoSiteStates j)))).map
        (algebraMap ℝ ℂ)) → z.re < -2 ∨ z = (x : ℂ) := by
  obtain ⟨x, hx, hr, hround, hd, hrest⟩ :=
    manuscriptTwoSiteMatrixFin_dominant_root_rounding j
  have hchar :
      (restrictedJacobianMatrix 4 2 6 manuscriptTwoSiteRates
        (toCoordinateSpace (chart (manuscriptTwoSiteStates j)))).charpoly =
        (manuscriptTwoSiteMatrixFin j).charpoly := by
    rw [manuscriptTwoSiteMatrixFin]
    exact (Matrix.charpoly_reindex _ _).symm
  refine ⟨x, hx, ?_, hround, ?_, ?_⟩
  · simpa only [hchar] using hr
  · simpa only [Matrix.charpoly_map, hchar] using hd
  · intro z hz
    apply hrest z
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    have hzr := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
    simpa only [Matrix.charpoly_map, hchar] using hzr

end
end PhosphorylationStableCapacity
