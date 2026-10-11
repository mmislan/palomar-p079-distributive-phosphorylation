module
public import proofs.PhosphorylationStableCapacity.SplitJacobianContinuity
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness

attribute [local fun_prop] analyticAt_fst analyticAt_snd

@[fun_prop] private theorem analyticAt_pi_fixed {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → ι → F} {x : E}
    (hf : ∀ i, AnalyticAt ℝ (fun y => f y i) x) :
    AnalyticAt ℝ f x := analyticAt_pi_iff.mpr hf

@[fun_prop] private theorem analyticAt_pi_apply_fixed
    {ι : Type*} [Fintype ι]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : ι) (x : ι → F) :
    AnalyticAt ℝ (fun y : ι → F => y i) x :=
  (ContinuousLinearMap.proj (R := ℝ) i : (ι → F) →L[ℝ] F).analyticAt x

@[fun_prop] private theorem analyticAt_ite_fixed {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Prop) [Decidable p] {f g : E → ℝ} {x : E}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x) :
    AnalyticAt ℝ (fun y => if p then f y else g y) x := by
  by_cases hp : p <;> simp [hp, hf, hg]

@[fun_prop] private theorem analyticAt_fin_cases_fixed {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (i : Fin (n+1)) {f : E → ℝ} {g : E → Fin n → ℝ} {x : E}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x) :
    AnalyticAt ℝ
      (fun y => Fin.cases (motive := fun _ => ℝ) (f y) (g y) i) x := by
  cases i using Fin.cases with
  | zero => simpa using hf
  | succ j => simpa using (analyticAt_pi_iff.mp hg) j

/-- The literal joint mass-action field is real analytic in all six edge
rate arrays and all class coordinates. -/
theorem analyticAt_jointRestrictedField {n : ℕ} (ET FT ST : ℝ)
    (p : RateVector n × CoordinateSpace n) :
    AnalyticAt ℝ (jointRestrictedField ET FT ST) p := by
  classical
  unfold jointRestrictedField restrictedFieldEuclid restrictedField
    ratesFromVector toCoordinateSpace chart field unChart ofCoordinateSpace
    kinaseNet phosphataseNet
  dsimp
  refine AnalyticAt.prod ?_ (AnalyticAt.prod ?_ ?_)
  all_goals
    apply analyticAt_pi_iff.mpr
    intro i
    fun_prop

end
end PhosphorylationStableCapacity
