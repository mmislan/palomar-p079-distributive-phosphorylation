module
public import proofs.PhosphorylationStableCapacity.CertifiedContractionPersistence
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.Convex

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open NNReal

/-- Quantitative persistence from a uniform preconditioned derivative bound.
All bounds concern the actual field and its actual derivative. -/
theorem unique_zero_in_closedBall_of_preconditioned_contraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (R : E →L[ℝ] E) (hR : Function.Injective R)
    (x₀ : E) (ρ : ℝ) (hρ : 0 < ρ)
    (C : ℝ≥0) (hC : C < 1)
    (hf : ∀ x ∈ Metric.closedBall x₀ ρ, DifferentiableAt ℝ f x)
    (hder : ∀ x ∈ Metric.closedBall x₀ ρ,
      ‖ContinuousLinearMap.id ℝ E - R.comp (fderiv ℝ f x)‖ ≤ (C : ℝ))
    (hshift : ‖R (f x₀)‖ ≤ (1-(C : ℝ))*ρ/4) :
    ∃ x, x ∈ Metric.closedBall x₀ ρ ∧ f x = 0 ∧
      dist x x₀ ≤ ρ/4 ∧
      ∀ y ∈ Metric.closedBall x₀ ρ, f y = 0 → y = x := by
  let G : E → E := fun x => x - R (f x)
  have hGder (x : E) (hx : x ∈ Metric.closedBall x₀ ρ) :
      HasFDerivAt G (ContinuousLinearMap.id ℝ E - R.comp (fderiv ℝ f x)) x := by
    exact (hasFDerivAt_id x).sub (R.hasFDerivAt.comp x (hf x hx).hasFDerivAt)
  have hGlip : LipschitzOnWith C G (Metric.closedBall x₀ ρ) := by
    apply (convex_closedBall x₀ ρ).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun x hx => (hGder x hx).hasFDerivWithinAt)
    intro x hx
    exact NNReal.coe_le_coe.mp (hder x hx)
  have hGshift : dist (G x₀) x₀ ≤ (1-(C : ℝ))*ρ/4 := by
    simpa only [G, dist_eq_norm, sub_sub_cancel_left, norm_neg] using hshift
  obtain ⟨x, hx, hfix, hdist, hunique⟩ :=
    unique_fixedPoint_in_closedBall_of_contraction G x₀ ρ hρ C hC hGlip hGshift
  have hz : f x = 0 := by
    apply hR
    simp only [map_zero]
    change x - R (f x) = x at hfix
    exact (sub_eq_self.mp hfix)
  refine ⟨x, hx, hz, hdist, ?_⟩
  intro y hy hfy
  apply hunique y hy
  simp only [G, hfy, map_zero, sub_zero]


theorem unique_zero_in_closedBall_of_preconditioned_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (R : E →L[ℝ] E) (hR : Function.Injective R)
    (x₀ : E) (ρ : ℝ) (hρ : 0 < ρ)
    (hf : ∀ x ∈ Metric.closedBall x₀ ρ, DifferentiableAt ℝ f x)
    (hder : ∀ x ∈ Metric.closedBall x₀ ρ,
      ‖ContinuousLinearMap.id ℝ E - R.comp (fderiv ℝ f x)‖ ≤ (1/2 : ℝ))
    (hshift : ‖R (f x₀)‖ ≤ ρ/8) :
    ∃ x, x ∈ Metric.closedBall x₀ ρ ∧ f x = 0 ∧
      dist x x₀ ≤ ρ/4 ∧
      ∀ y ∈ Metric.closedBall x₀ ρ, f y = 0 → y = x := by
  let G : E → E := fun x => x - R (f x)
  have hGder (x : E) (hx : x ∈ Metric.closedBall x₀ ρ) :
      HasFDerivAt G (ContinuousLinearMap.id ℝ E - R.comp (fderiv ℝ f x)) x := by
    exact (hasFDerivAt_id x).sub (R.hasFDerivAt.comp x (hf x hx).hasFDerivAt)
  have hGlip : LipschitzOnWith (1/2 : ℝ≥0) G (Metric.closedBall x₀ ρ) := by
    apply (convex_closedBall x₀ ρ).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun x hx => (hGder x hx).hasFDerivWithinAt)
    intro x hx
    exact NNReal.coe_le_coe.mp (hder x hx)
  have hGshift : dist (G x₀) x₀ ≤ ρ/8 := by
    simpa only [G, dist_eq_norm, sub_sub_cancel_left, norm_neg] using hshift
  obtain ⟨x, hx, hfix, hdist, hunique⟩ :=
    unique_fixedPoint_in_closedBall_of_half_contraction G x₀ ρ hρ hGlip hGshift
  have hz : f x = 0 := by
    apply hR
    simp only [map_zero]
    change x - R (f x) = x at hfix
    exact (sub_eq_self.mp hfix)
  refine ⟨x, hx, hz, hdist, ?_⟩
  intro y hy hfy
  apply hunique y hy
  simp only [G, hfy, map_zero, sub_zero]

end
end PhosphorylationStableCapacity
