module
public import proofs.PhosphorylationStableCapacity.QuadraticCoefficientMajorant435
public import proofs.PhosphorylationStableCapacity.ScalarSeriesDifferential435
public import Mathlib.Algebra.BigOperators.Fin
public import Lean.Elab.Tactic.Omega

@[expose] public section
namespace P079UnstableWorkbench
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Removing the two zero boundary coefficients leaves exactly the shifted
quadratic convolution in the recursive construction. -/
theorem parameterCoefficients_convolution
    (R : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (v : E) (n : ℕ) :
    (∑ i : Fin (n+2+1), Q (parameterCoefficients R Q v i.val)
      (parameterCoefficients R Q v (n+2-i.val))) =
      ∑ i : Fin (n+1), Q (quadraticCoefficients R Q v i.val)
        (quadraticCoefficients R Q v (n-i.val)) := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, parameterCoefficients_zero, map_zero,
    zero_apply, zero_add, Fin.val_succ]
  rw [Fin.sum_univ_castSucc]
  have hlast : n+2-((n+1)+1) = 0 := by omega
  simp only [Fin.val_last, hlast, parameterCoefficients_zero, map_zero, add_zero,
    Fin.val_castSucc]
  apply Finset.sum_congr rfl
  intro i _
  have hi : n+2-(i.val+1) = (n-i.val)+1 := by omega
  rw [hi, parameterCoefficients_succ, parameterCoefficients_succ]

theorem parameterSeries_coefficients_equation
    (R : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (v : E)
    (A : E →L[ℝ] E) (lam : ℝ) (heigen : A v = lam • v)
    (hR : ∀ n : ℕ, ∀ w : E,
      (((n+2 : ℕ) : ℝ)*lam) • R (n+2) w - A (R (n+2) w) = w)
    (n : ℕ) :
    ((n : ℝ)*lam) • (vectorSeries (parameterCoefficients R Q v)).coeff n =
      A ((vectorSeries (parameterCoefficients R Q v)).coeff n) +
      ∑ i : Fin (n+1),
        Q ((vectorSeries (parameterCoefficients R Q v)).coeff i.val)
          ((vectorSeries (parameterCoefficients R Q v)).coeff (n-i.val)) := by
  simp only [coeff_vectorSeries]
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero =>
          simpa [Fin.sum_univ_succ] using heigen.symm
      | succ n =>
          change (((n+2 : ℕ) : ℝ)*lam) • parameterCoefficients R Q v (n+2) = _
          rw [parameterCoefficients_convolution, parameterCoefficients_succ]
          have h := quadraticCoefficients_resolvent_equation R Q v A lam hR n
          rw [sub_eq_iff_eq_add] at h
          exact h.trans (add_comm _ _)

/-- The candidate constructed by the resolvent recursion actually satisfies
the nonlinear quadratic parameterization equation throughout its convergence
disk. No invariant-curve premise appears in this endpoint. -/
theorem constructed_parameterSeries_quadratic_invariance [CompleteSpace E]
    (R : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (v : E)
    (A : E →L[ℝ] E) (lam : ℝ) (heigen : A v = lam • v)
    (hR : ∀ n : ℕ, ∀ w : E,
      (((n+2 : ℕ) : ℝ)*lam) • R (n+2) w - A (R (n+2) w) = w)
    (s : ℝ) (hs : ‖s‖ₑ < (vectorSeries (parameterCoefficients R Q v)).radius) :
    (lam*s) • fderiv ℝ (vectorSeries (parameterCoefficients R Q v)).sum s 1 =
      A ((vectorSeries (parameterCoefficients R Q v)).sum s) +
      Q ((vectorSeries (parameterCoefficients R Q v)).sum s)
        ((vectorSeries (parameterCoefficients R Q v)).sum s) :=
  scalarSeries_quadratic_invariance _ A Q lam
    (parameterSeries_coefficients_equation R Q v A lam heigen hR) s hs

end P079UnstableWorkbench
