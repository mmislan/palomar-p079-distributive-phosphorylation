module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Order.Bornology
public import Mathlib.Topology.Bornology.Real
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Filter.AtTopBot.Field
public import Lean.Elab.Tactic.Omega

@[expose] public section

open Filter
open scoped Topology

namespace PhosphorylationStableCapacity.UnstableCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual real bounded-operator resolvent used by the homogeneous
coefficient recursion. Its value is a true inverse when the corresponding
operator is a unit; the solve lemmas below retain that hypothesis. -/
noncomputable def harmonicResolvent (A : E →L[ℝ] E) (lam : ℝ) (k : ℕ) : E →L[ℝ] E :=
  Ring.inverse (((k : ℝ) * lam) • (1 : E →L[ℝ] E) - A)

/-- The Neumann-series bound at large real spectral parameters implies the
discrete resolvents tend to zero. No finite-dimensionality or spectral
nonresonance assumption is needed for this asymptotic statement. -/
theorem harmonicResolvent_tendsto_zero (A : E →L[ℝ] E) (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (harmonicResolvent A lam) atTop (𝓝 0) := by
  have hnat : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hscalar : Tendsto (fun k : ℕ => (k : ℝ) * lam) atTop (Bornology.cobounded ℝ) :=
    (hnat.atTop_mul_const hlam).mono_right IsOrderBornology.atTop_le_cobounded
  change Tendsto (fun k : ℕ => Ring.inverse (((k : ℝ) * lam) • (1 : E →L[ℝ] E) - A))
    atTop (𝓝 0)
  simpa only [resolvent, Algebra.algebraMap_eq_smul_one, Function.comp_def] using
    (spectrum.resolvent_tendsto_cobounded (𝕜 := ℝ) A).comp hscalar

/-- One positive finite real constant bounds every inverse operator norm in
the shifted sequence used by the analytic-curve recursion. The bounded-range
lemma absorbs the finitely many parameters before the Neumann estimate applies.
At nonunits `Ring.inverse` is zero; invertibility is retained separately by the
combined endpoint and solve lemmas below. -/
theorem harmonicResolvent_uniform_norm_bound (A : E →L[ℝ] E) (lam : ℝ) (hlam : 0 < lam) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, ‖harmonicResolvent A lam (n + 2)‖ ≤ M := by
  have hnorm : Tendsto (fun k : ℕ => ‖harmonicResolvent A lam k‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using (harmonicResolvent_tendsto_zero A lam hlam).norm
  obtain ⟨B, hB⟩ := hnorm.bddAbove_range
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right B 1), ?_⟩
  intro n
  exact (hB ⟨n + 2, rfl⟩).trans (le_max_left B 1)

omit [CompleteSpace E] in
/-- Applying the genuine inverse solves the real homological equation.
This formulation consumes exactly the shifted nonresonance interface. -/
theorem harmonicResolvent_solve (A : E →L[ℝ] E) (lam : ℝ)
    (hinv : ∀ n : ℕ, IsUnit ((((n + 2 : ℕ) : ℝ) * lam) • (1 : E →L[ℝ] E) - A))
    (n : ℕ) (w : E) :
    (((n + 2 : ℕ) : ℝ) * lam) • harmonicResolvent A lam (n + 2) w -
      A (harmonicResolvent A lam (n + 2) w) = w := by
  have h := congrArg (fun T : E →L[ℝ] E => T w)
    (Ring.mul_inverse_cancel
      (((((n + 2 : ℕ) : ℝ) * lam) • (1 : E →L[ℝ] E)) - A) (hinv n))
  simpa only [harmonicResolvent, mul_apply_eq_comp, sub_apply,
    smul_apply, one_apply_eq_self] using h

/-- The uniform constant and all inverse identities refer to the same
literal resolvent family. This is the endpoint needed for the Catalan majorant. -/
theorem harmonicResolvent_uniform_bound_and_solve (A : E →L[ℝ] E) (lam : ℝ)
    (hlam : 0 < lam)
    (hinv : ∀ n : ℕ, IsUnit ((((n + 2 : ℕ) : ℝ) * lam) • (1 : E →L[ℝ] E) - A)) :
    ∃ M : ℝ, 0 < M ∧
      (∀ n : ℕ, ‖harmonicResolvent A lam (n + 2)‖ ≤ M) ∧
      ∀ (n : ℕ) (w : E),
        (((n + 2 : ℕ) : ℝ) * lam) • harmonicResolvent A lam (n + 2) w -
          A (harmonicResolvent A lam (n + 2) w) = w := by
  obtain ⟨M, hM, hbound⟩ := harmonicResolvent_uniform_norm_bound A lam hlam
  exact ⟨M, hM, hbound, harmonicResolvent_solve A lam hinv⟩

/-- Adapter for the unshifted integer nonresonance hypothesis. -/
theorem harmonicResolvent_uniform_bound_and_solve_of_ge_two
    (A : E →L[ℝ] E) (lam : ℝ) (hlam : 0 < lam)
    (hinv : ∀ k : ℕ, 2 ≤ k →
      IsUnit (((k : ℝ) * lam) • (1 : E →L[ℝ] E) - A)) :
    ∃ M : ℝ, 0 < M ∧
      (∀ n : ℕ, ‖harmonicResolvent A lam (n + 2)‖ ≤ M) ∧
      ∀ (n : ℕ) (w : E),
        (((n + 2 : ℕ) : ℝ) * lam) • harmonicResolvent A lam (n + 2) w -
          A (harmonicResolvent A lam (n + 2) w) = w := by
  exact harmonicResolvent_uniform_bound_and_solve A lam hlam (fun n => hinv (n + 2) (by omega))

end PhosphorylationStableCapacity.UnstableCurve
