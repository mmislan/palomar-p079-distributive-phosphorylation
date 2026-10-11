module
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Order.Filter.AtTopBot.Field

@[expose] public section
namespace P079UnstableWorkbench
open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem backwardParameter_norm_le (lam s t : ℝ)
    (hlam : 0 ≤ lam) (ht : t ≤ 0) :
    ‖s * Real.exp (lam*t)‖ ≤ ‖s‖ := by
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos (lam*t)).le]
  exact mul_le_of_le_one_right (norm_nonneg s)
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hlam ht))

/-- The scalar parameter evolution remains within the original local curve
for every backward time, and solves the actual vector differential equation. -/
theorem backwardParameterTrajectory_hasDerivAt
    (h : ℝ → E) (F : E → E) (lam eps s t : ℝ)
    (hlam : 0 ≤ lam) (hs : ‖s‖ < eps) (ht : t ≤ 0)
    (hderiv : ∀ x : ℝ, ‖x‖ < eps → HasDerivAt h (deriv h x) x)
    (hinvariant : ∀ x : ℝ, ‖x‖ < eps → (lam*x) • deriv h x = F (h x)) :
    HasDerivAt (fun z : ℝ => h (s * Real.exp (lam*z)))
      (F (h (s * Real.exp (lam*t)))) t := by
  have hx : ‖s * Real.exp (lam*t)‖ < eps :=
    (backwardParameter_norm_le lam s t hlam ht).trans_lt hs
  have hp : HasDerivAt (fun z : ℝ => s * Real.exp (lam*z))
      (lam*(s * Real.exp (lam*t))) t := by
    simpa only [id_eq, mul_one, mul_assoc, mul_comm, mul_left_comm] using
      ((hasDerivAt_id t).const_mul lam).exp.const_mul s
  have h := (hderiv _ hx).scomp t hp
  simpa only [Function.comp_def, hinvariant _ hx] using h

omit [NormedSpace ℝ E] in
/-- Every point on the constructed curve converges to its central equilibrium
under the explicit backward trajectory. -/
theorem backwardParameterTrajectory_tendsto
    (h : ℝ → E) (lam s : ℝ) (hlam : 0 < lam) (hc : ContinuousAt h 0) :
    Tendsto (fun t : ℝ => h (s * Real.exp (lam*t))) atBot (𝓝 (h 0)) := by
  have htime : Tendsto (fun t : ℝ => lam*t) atBot atBot :=
    tendsto_id.const_mul_atBot hlam
  have hp : Tendsto (fun t : ℝ => s * Real.exp (lam*t)) atBot (𝓝 (0:ℝ)) := by
    simpa only [mul_zero, Function.comp_def] using
      (Real.tendsto_exp_atBot.comp htime).const_mul s
  exact hc.tendsto.comp hp

end P079UnstableWorkbench
