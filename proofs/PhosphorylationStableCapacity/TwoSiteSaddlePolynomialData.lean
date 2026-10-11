module
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial

def twoSiteSaddlePolyQ : ℚ[X] :=
  X ^ 6 +
    C (10281201943 / 264067375 : ℚ) * X ^ 5 +
    C (1151169355838192287 / 2231410513260500 : ℚ) * X ^ 4 +
    C (652471337146385609400023 / 214270078830582882250 : ℚ) * X ^ 3 +
    C (110689383888327573125031207 / 13481873360020274951170 : ℚ) * X ^ 2 +
    C (318974692410214071924168 / 38785596547814369825 : ℚ) * X -
    C (786096736185600 / 19121983187021 : ℚ)

def twoSiteSaddlePolyR : ℝ[X] := twoSiteSaddlePolyQ.map (Rat.castHom ℝ)

theorem twoSiteSaddlePolyR_eval_zero_neg : twoSiteSaddlePolyR.eval 0 < 0 := by
  norm_num [twoSiteSaddlePolyR, twoSiteSaddlePolyQ]

theorem twoSiteSaddlePolyR_eval_one_pos : 0 < twoSiteSaddlePolyR.eval 1 := by
  norm_num [twoSiteSaddlePolyR, twoSiteSaddlePolyQ]

theorem twoSiteSaddlePolyR_derivative_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < twoSiteSaddlePolyR.derivative.eval x := by
  simp [twoSiteSaddlePolyR, twoSiteSaddlePolyQ,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    Polynomial.eval_add]
  positivity

theorem twoSiteSaddlePolyR_exists_positive_root :
    ∃ x : ℝ, 0 < x ∧ x < 1 ∧ twoSiteSaddlePolyR.eval x = 0 := by
  have hzero : (0 : ℝ) ∈ Set.Icc (twoSiteSaddlePolyR.eval 0)
      (twoSiteSaddlePolyR.eval 1) :=
    ⟨twoSiteSaddlePolyR_eval_zero_neg.le,
      twoSiteSaddlePolyR_eval_one_pos.le⟩
  obtain ⟨x, hx, hroot⟩ := (Set.mem_image _ _ _).mp
    (intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
      twoSiteSaddlePolyR.continuous.continuousOn hzero)
  refine ⟨x, ?_, ?_, hroot⟩
  · rcases hx with ⟨hx0, _⟩
    exact lt_of_le_of_ne hx0 (by
      intro h
      subst x
      exact ne_of_lt twoSiteSaddlePolyR_eval_zero_neg hroot)
  · rcases hx with ⟨_, hx1⟩
    exact lt_of_le_of_ne hx1 (by
      intro h
      subst x
      exact ne_of_gt twoSiteSaddlePolyR_eval_one_pos hroot)

end
end PhosphorylationStableCapacity
