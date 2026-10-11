module
public import proofs.PhosphorylationStableCapacity.SplitQuantitativeSlowRoot
public import proofs.PhosphorylationStableCapacity.SplitEigenvalueAsymptoticBridge

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter Asymptotics Polynomial
open scoped Topology

/-- Differentiability at the coalesced family supplies an explicit local
    first-order absolute-value bound. -/
theorem differentiableAt_first_order_abs_bound
    (f : ℝ → ℝ) (hf : DifferentiableAt ℝ f 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ δ : ℝ in 𝓝 0, |f δ - f 0| ≤ C * |δ| := by
  obtain ⟨C, hCpos, hC⟩ := hf.isBigO_sub.exists_pos
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [hC.bound] with δ hb
  simpa only [sub_zero, Real.norm_eq_abs] using hb

/-- A bounded-degree characteristic polynomial with differentiable
    coefficients has a differentiable secant quotient jointly in the
    perturbation and spectral variables. -/
theorem constantTermSecant_joint_differentiableAt
    (P : ℝ → ℝ[X]) (N : ℕ)
    (hdegree : ∀ δ, (constantTermSecant (P δ)).natDegree < N)
    (hcoeff : ∀ k, DifferentiableAt ℝ (fun δ => (P δ).coeff k) 0) :
    DifferentiableAt ℝ
      (fun y : ℝ × ℝ => (constantTermSecant (P y.1)).eval y.2)
      (0, 0) := by
  have heval (δ x : ℝ) :
      (constantTermSecant (P δ)).eval x =
        ∑ k ∈ Finset.range N, (P δ).coeff (k+1) * x^k := by
    rw [Polynomial.eval_eq_sum_range' (hdegree δ)]
    simp only [constantTermSecant_coeff]
  simp_rw [heval]
  apply DifferentiableAt.fun_sum
  intro k hk
  have hfst : DifferentiableAt ℝ (fun y : ℝ × ℝ => y.1) (0, 0) :=
    differentiableAt_fst
  have hsnd : DifferentiableAt ℝ (fun y : ℝ × ℝ => y.2) (0, 0) :=
    differentiableAt_snd
  have hc : DifferentiableAt ℝ
      (fun y : ℝ × ℝ => (P y.1).coeff (k+1)) (0, 0) :=
    by simpa only [Function.comp_def] using
      ((hcoeff (k+1)).comp (0, 0) hfst)
  exact hc.mul (hsnd.pow k)

theorem constantTermSecant_joint_first_order_bound
    (P : ℝ → ℝ[X]) (N : ℕ)
    (hdegree : ∀ δ, (constantTermSecant (P δ)).natDegree < N)
    (hcoeff : ∀ k, DifferentiableAt ℝ (fun δ => (P δ).coeff k) 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ y : ℝ × ℝ in 𝓝 (0, 0),
        |(constantTermSecant (P y.1)).eval y.2 -
          (P 0).derivative.eval 0| ≤ C * (|y.1| + |y.2|) := by
  have hQ := constantTermSecant_joint_differentiableAt
    P N hdegree hcoeff
  obtain ⟨C, hCpos, hC⟩ := hQ.isBigO_sub.exists_pos
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [hC.bound] with y hy
  have hnorm : ‖y - ((0 : ℝ), (0 : ℝ))‖ ≤
      |y.1| + |y.2| := by
    simp [Prod.norm_def, Real.norm_eq_abs]
  have hQ0 : (constantTermSecant (P 0)).eval 0 =
      (P 0).derivative.eval 0 := constantTermSecant_eval_zero (P 0)
  simpa only [sub_zero, Real.norm_eq_abs, hQ0] using
    le_trans hy (mul_le_mul_of_nonneg_left hnorm hCpos.le)

/-- The local secant bound can be applied uniformly on a small rectangle
    around the coalesced parameter and neutral spectral value. -/
theorem constantTermSecant_rectangular_first_order_bound
    (P : ℝ → ℝ[X]) (N : ℕ)
    (hdegree : ∀ δ, (constantTermSecant (P δ)).natDegree < N)
    (hcoeff : ∀ k, DifferentiableAt ℝ (fun δ => (P δ).coeff k) 0) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ δ x : ℝ, |δ| < η → |x| < η →
        |(constantTermSecant (P δ)).eval x -
          (P 0).derivative.eval 0| ≤ C * (|δ| + |x|) := by
  obtain ⟨C, hC, hbound⟩ :=
    constantTermSecant_joint_first_order_bound P N hdegree hcoeff
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hbound
  refine ⟨η, C, hη, hC, ?_⟩
  intro δ x hδ hx
  have hpair : (δ, x) ∈ Metric.ball ((0 : ℝ), (0 : ℝ)) η := by
    have hmax : max |δ| |x| < η := max_lt hδ hx
    simpa [Metric.mem_ball, dist_eq_norm, Prod.norm_def,
      Real.norm_eq_abs] using hmax
  exact hball hpair

end
end PhosphorylationStableCapacity
