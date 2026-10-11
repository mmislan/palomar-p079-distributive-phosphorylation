module
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity.Basic
public import Lean.Elab.Tactic.Omega
public import Lean.Elab.Tactic.NormCast

@[expose] public section
namespace P079UnstableWorkbench
open scoped BigOperators NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- a_n is the coefficient of s^(n+1), so the quadratic convolution uses
only previously constructed coefficients. R(k) will be (klamI-A)⁻¹. -/
noncomputable def quadraticCoefficients
    (R : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (v : E) : ℕ → E
  | 0 => v
  | n + 1 => R (n + 2) (∑ i : Fin (n + 1),
      Q (quadraticCoefficients R Q v i.val)
        (quadraticCoefficients R Q v (n - i.val)))
termination_by n => n
decreasing_by all_goals omega

@[simp] theorem quadraticCoefficients_zero
    (R : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (v : E) :
    quadraticCoefficients R Q v 0 = v := by
  rw [quadraticCoefficients]

theorem quadraticCoefficients_succ
    (R : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (v : E) (n : ℕ) :
    quadraticCoefficients R Q v (n + 1) = R (n + 2)
      (∑ i : Fin (n + 1), Q (quadraticCoefficients R Q v i.val)
        (quadraticCoefficients R Q v (n - i.val))) := by
  rw [quadraticCoefficients]

theorem quadraticCoefficients_resolvent_equation
    (R : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (v : E)
    (A : E →L[ℝ] E) (lam : ℝ)
    (hR : ∀ n : ℕ, ∀ w : E,
      (((n + 2 : ℕ) : ℝ) * lam) • R (n + 2) w - A (R (n + 2) w) = w)
    (n : ℕ) :
    (((n + 2 : ℕ) : ℝ) * lam) • quadraticCoefficients R Q v (n + 1) -
        A (quadraticCoefficients R Q v (n + 1)) =
      ∑ i : Fin (n + 1), Q (quadraticCoefficients R Q v i.val)
        (quadraticCoefficients R Q v (n - i.val)) := by
  rw [quadraticCoefficients_succ]
  exact hR n _

theorem bilinear_norm_bound (Q : E →L[ℝ] E →L[ℝ] E) (x y : E) :
    ‖Q x y‖ ≤ ‖Q‖ * ‖x‖ * ‖y‖ := by
  exact ((Q x).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right (Q.le_opNorm x) (norm_nonneg y))

theorem quadraticCoefficients_norm_step
    (R : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (v : E)
    (M : ℝ) (hM : 0 ≤ M) (hR : ∀ n, ‖R (n + 2)‖ ≤ M) (n : ℕ) :
    ‖quadraticCoefficients R Q v (n + 1)‖ ≤
      (M * ‖Q‖) * ∑ i : Fin (n + 1),
        ‖quadraticCoefficients R Q v i.val‖ *
          ‖quadraticCoefficients R Q v (n - i.val)‖ := by
  rw [quadraticCoefficients_succ]
  calc
    _ ≤ ‖R (n + 2)‖ * ‖∑ i : Fin (n + 1),
        Q (quadraticCoefficients R Q v i.val)
          (quadraticCoefficients R Q v (n - i.val))‖ := (R (n + 2)).le_opNorm _
    _ ≤ M * ∑ i : Fin (n + 1),
        ‖Q (quadraticCoefficients R Q v i.val)
          (quadraticCoefficients R Q v (n - i.val))‖ :=
      (mul_le_mul_of_nonneg_right (hR n) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hM)
    _ ≤ M * ∑ i : Fin (n + 1),
        (‖Q‖ * ‖quadraticCoefficients R Q v i.val‖ *
          ‖quadraticCoefficients R Q v (n - i.val)‖) := by
      gcongr with i
      exact bilinear_norm_bound Q _ _
    _ = (M * ‖Q‖) * ∑ i : Fin (n + 1),
        ‖quadraticCoefficients R Q v i.val‖ *
          ‖quadraticCoefficients R Q v (n - i.val)‖ := by
      simp only [mul_assoc, Finset.mul_sum]

/-- A complete Catalan majorant for the genuinely constructed coefficients.
This proves convergence once a uniform resolvent norm bound is supplied; no
existence, smoothness or invariance of a curve is assumed. -/
theorem quadraticCoefficients_catalan_bound
    (R : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (v : E)
    (M : ℝ) (hM : 0 ≤ M) (hR : ∀ n, ‖R (n + 2)‖ ≤ M) (n : ℕ) :
    ‖quadraticCoefficients R Q v n‖ ≤
      (catalan n : ℝ) * (M * ‖Q‖)^n * ‖v‖^(n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      have hb : 0 ≤ M * ‖Q‖ := mul_nonneg hM (norm_nonneg Q)
      have hterm (i : Fin (n + 1)) :
          ‖quadraticCoefficients R Q v i.val‖ *
              ‖quadraticCoefficients R Q v (n - i.val)‖ ≤
            ((catalan i.val : ℝ) * (M * ‖Q‖)^i.val * ‖v‖^(i.val+1)) *
              ((catalan (n-i.val) : ℝ) * (M * ‖Q‖)^(n-i.val) * ‖v‖^(n-i.val+1)) := by
        apply mul_le_mul
        · exact ih i.val i.isLt
        · exact ih (n-i.val) (by omega)
        · exact norm_nonneg _
        · positivity
      have hexp (i : Fin (n + 1)) :
          ((catalan i.val : ℝ) * (M * ‖Q‖)^i.val * ‖v‖^(i.val+1)) *
              ((catalan (n-i.val) : ℝ) * (M * ‖Q‖)^(n-i.val) * ‖v‖^(n-i.val+1)) =
            ((catalan i.val : ℝ) * (catalan (n-i.val) : ℝ)) *
              (M * ‖Q‖)^n * ‖v‖^(n+2) := by
        have hsum : i.val + (n-i.val) = n := by omega
        have hsum' : (i.val+1)+(n-i.val+1) = n+2 := by omega
        calc
          _ = ((catalan i.val : ℝ) * (catalan (n-i.val) : ℝ)) *
              ((M * ‖Q‖)^i.val * (M * ‖Q‖)^(n-i.val)) *
              (‖v‖^(i.val+1) * ‖v‖^(n-i.val+1)) := by ring
          _ = _ := by rw [← pow_add, ← pow_add, hsum, hsum']
      calc
        _ ≤ (M * ‖Q‖) * ∑ i : Fin (n + 1),
          ‖quadraticCoefficients R Q v i.val‖ *
            ‖quadraticCoefficients R Q v (n-i.val)‖ :=
          quadraticCoefficients_norm_step R Q v M hM hR n
        _ ≤ (M * ‖Q‖) * ∑ i : Fin (n + 1),
          (((catalan i.val : ℝ) * (M * ‖Q‖)^i.val * ‖v‖^(i.val+1)) *
            ((catalan (n-i.val) : ℝ) * (M * ‖Q‖)^(n-i.val) * ‖v‖^(n-i.val+1))) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) hb
        _ = (M * ‖Q‖) * ((catalan (n+1) : ℝ) *
          (M * ‖Q‖)^n * ‖v‖^(n+2)) := by
          have hcat : (∑ i : Fin (n+1),
              (catalan i.val : ℝ) * (catalan (n-i.val) : ℝ)) =
              (catalan (n+1) : ℝ) := by
            exact_mod_cast (catalan_succ n).symm
          simp_rw [hexp]
          rw [← Finset.sum_mul, ← Finset.sum_mul, hcat]
        _ = _ := by simp only [pow_succ]; ring

theorem catalan_le_four_pow (n : ℕ) : catalan n ≤ 4^n := by
  rw [catalan_eq_centralBinom_div]
  exact (Nat.div_le_self _ _).trans (Nat.centralBinom_le_four_pow n)

theorem quadraticCoefficients_geometric_bound
    (R : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (v : E)
    (M : ℝ) (hM : 0 ≤ M) (hR : ∀ n, ‖R (n + 2)‖ ≤ M) (n : ℕ) :
    ‖quadraticCoefficients R Q v n‖ ≤ ‖v‖ * (4*M*‖Q‖*‖v‖)^n := by
  have hc : (catalan n : ℝ) ≤ (4 : ℝ)^n := by exact_mod_cast catalan_le_four_pow n
  calc
    _ ≤ (catalan n : ℝ) * (M * ‖Q‖)^n * ‖v‖^(n+1) :=
      quadraticCoefficients_catalan_bound R Q v M hM hR n
    _ ≤ (4 : ℝ)^n * (M * ‖Q‖)^n * ‖v‖^(n+1) := by gcongr
    _ = _ := by simp only [mul_pow, pow_succ]; ring

noncomputable def vectorSeries (a : ℕ → E) : FormalMultilinearSeries ℝ ℝ E :=
  fun n => ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (a n)

@[simp] theorem norm_vectorSeries (a : ℕ → E) (n : ℕ) :
    ‖vectorSeries a n‖ = ‖a n‖ := ContinuousMultilinearMap.norm_mkPiRing _

@[simp] theorem coeff_vectorSeries (a : ℕ → E) (n : ℕ) :
    (vectorSeries a).coeff n = a n := by
  simp [FormalMultilinearSeries.coeff, vectorSeries,
    ContinuousMultilinearMap.mkPiRing_apply]

/-- A geometric coefficient bound yields a real positive radius and a genuine
analytic sum in a complete target space. This is the convergence component of
the parameterization construction, not yet its nonlinear invariance equation. -/
theorem vectorSeries_radius_lower_bound (a : ℕ → E) (C B : ℝ)
    (hB : 0 ≤ B) (ha : ∀ n, ‖a n‖ ≤ C*B^n)
    (r : ℝ≥0) (hr : B*(r : ℝ) < 1) :
    (r : ℝ≥0∞) ≤ (vectorSeries a).radius := by
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have hgeom := (summable_geometric_of_lt_one (mul_nonneg hB r.coe_nonneg) hr).mul_left C
  apply hgeom.of_nonneg_of_le
  · intro n
    exact mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg n)
  · intro n
    simpa only [norm_vectorSeries, mul_pow, mul_assoc] using
      mul_le_mul_of_nonneg_right (ha n) (pow_nonneg r.coe_nonneg n)

theorem vectorSeries_analyticAt_zero [CompleteSpace E]
    (a : ℕ → E) (C B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ n, ‖a n‖ ≤ C*B^n) (r : ℝ≥0) (hrpos : 0 < r)
    (hr : B*(r : ℝ) < 1) :
    AnalyticAt ℝ (vectorSeries a).sum 0 := by
  have hrad : 0 < (vectorSeries a).radius :=
    lt_of_lt_of_le (by exact_mod_cast hrpos)
      (vectorSeries_radius_lower_bound a C B hB ha r hr)
  exact ((vectorSeries a).hasFPowerSeriesOnBall hrad).hasFPowerSeriesAt.analyticAt

/-- The full scalar power series has constant coefficient zero and linear
coefficient exactly the prescribed unstable eigenvector. -/
noncomputable def parameterCoefficients
    (R : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (v : E) : ℕ → E
  | 0 => 0
  | n+1 => quadraticCoefficients R Q v n

@[simp] theorem parameterCoefficients_zero
    (R : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (v : E) :
    parameterCoefficients R Q v 0 = 0 := rfl

@[simp] theorem parameterCoefficients_one
    (R : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (v : E) :
    parameterCoefficients R Q v 1 = v := quadraticCoefficients_zero R Q v

@[simp] theorem parameterCoefficients_succ
    (R : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (v : E) (n : ℕ) :
    parameterCoefficients R Q v (n+1) = quadraticCoefficients R Q v n := rfl

theorem parameterCoefficients_geometric_bound
    (R : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (v : E)
    (M : ℝ) (hM : 0 ≤ M) (hR : ∀ n, ‖R (n+2)‖ ≤ M) (n : ℕ) :
    ‖parameterCoefficients R Q v n‖ ≤
      ‖v‖ * (1 + 4*M*‖Q‖*‖v‖)^n := by
  have hb : 0 ≤ 4*M*‖Q‖*‖v‖ := by positivity
  cases n with
  | zero => simp
  | succ n =>
      change ‖quadraticCoefficients R Q v n‖ ≤ _
      calc
        _ ≤ ‖v‖ * (4*M*‖Q‖*‖v‖)^n :=
          quadraticCoefficients_geometric_bound R Q v M hM hR n
        _ ≤ ‖v‖ * (1+4*M*‖Q‖*‖v‖)^n := by gcongr; linarith
        _ ≤ ‖v‖ * (1+4*M*‖Q‖*‖v‖)^(n+1) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg v)
          rw [pow_succ]
          exact le_mul_of_one_le_right (pow_nonneg (by positivity) n) (by linarith)

/-- A constructed analytic candidate exists, with a positive explicit radius.
The theorem does not yet assert nonlinear invariance of its sum. -/
theorem parameterSeries_positive_radius
    (R : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (v : E)
    (M : ℝ) (hM : 0 ≤ M) (hR : ∀ n, ‖R (n+2)‖ ≤ M) :
    0 < (vectorSeries (parameterCoefficients R Q v)).radius := by
  let B : ℝ := 1+4*M*‖Q‖*‖v‖
  have hB : 0 < B := by dsimp [B]; positivity
  let r : ℝ≥0 := ⟨1/(2*(B+1)), by positivity⟩
  have hrpos : 0 < r := by change 0 < (1:ℝ)/(2*(B+1)); positivity
  have hr : B*(r : ℝ) < 1 := by
    change B*(1/(2*(B+1))) < 1
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    linarith
  exact lt_of_lt_of_le (by exact_mod_cast hrpos)
    (vectorSeries_radius_lower_bound (parameterCoefficients R Q v) ‖v‖ B hB.le
      (parameterCoefficients_geometric_bound R Q v M hM hR) r hr)

theorem parameterSeries_analyticAt_zero [CompleteSpace E]
    (R : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (v : E)
    (M : ℝ) (hM : 0 ≤ M) (hR : ∀ n, ‖R (n+2)‖ ≤ M) :
    AnalyticAt ℝ (vectorSeries (parameterCoefficients R Q v)).sum 0 :=
  ((vectorSeries (parameterCoefficients R Q v)).hasFPowerSeriesOnBall
    (parameterSeries_positive_radius R Q v M hM hR)).hasFPowerSeriesAt.analyticAt

theorem parameterSeries_sum_zero [CompleteSpace E]
    (R : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (v : E)
    (M : ℝ) (hM : 0 ≤ M) (hR : ∀ n, ‖R (n+2)‖ ≤ M) :
    (vectorSeries (parameterCoefficients R Q v)).sum 0 = 0 := by
  have h := (vectorSeries (parameterCoefficients R Q v)).hasFPowerSeriesOnBall
    (parameterSeries_positive_radius R Q v M hM hR)
  simpa [vectorSeries, ContinuousMultilinearMap.mkPiRing_apply] using
    (h.coeff_zero (fun _ => (0:ℝ))).symm

theorem parameterSeries_derivative_zero [CompleteSpace E]
    (R : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E) (v : E)
    (M : ℝ) (hM : 0 ≤ M) (hR : ∀ n, ‖R (n+2)‖ ≤ M) :
    fderiv ℝ (vectorSeries (parameterCoefficients R Q v)).sum 0 1 = v := by
  have h := (vectorSeries (parameterCoefficients R Q v)).hasFPowerSeriesOnBall
    (parameterSeries_positive_radius R Q v M hM hR)
  rw [h.hasFPowerSeriesAt.fderiv_eq]
  simp [vectorSeries, continuousMultilinearCurryFin1_apply,
    ContinuousMultilinearMap.mkPiRing_apply]

end P079UnstableWorkbench
