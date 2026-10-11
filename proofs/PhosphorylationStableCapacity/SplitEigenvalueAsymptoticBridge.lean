module
public import proofs.PhosphorylationStableCapacity.SplitSlowRootUniqueness

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open Polynomial Filter
open scoped Topology

/-- Divide away the constant term of a polynomial. The quotient evaluated
at the simple limiting root is its derivative there. -/
def constantTermSecant (p : ℝ[X]) : ℝ[X] :=
  (p - C (p.eval 0)) /ₘ X

theorem constantTermSecant_coeff (p : ℝ[X]) (i : ℕ) :
    (constantTermSecant p).coeff i = p.coeff (i+1) := by
  unfold constantTermSecant
  simpa using
    (coeff_divByMonic_X_sub_C_rec
      (p - C (p.eval 0)) (0 : ℝ) i)

theorem constantTermSecant_degree_lt (p : ℝ[X]) (N : ℕ)
    (hdegree : p.natDegree < N) :
    (constantTermSecant p).natDegree < N := by
  unfold constantTermSecant
  rw [natDegree_divByMonic _ monic_X, natDegree_X, natDegree_sub_C]
  omega

theorem constantTermSecant_eval_zero (p : ℝ[X]) :
    (constantTermSecant p).eval 0 = p.derivative.eval 0 := by
  rw [← coeff_zero_eq_eval_zero, constantTermSecant_coeff,
    ← coeff_zero_eq_eval_zero, coeff_derivative]
  simp

theorem constantTermSecant_eval_identity (p : ℝ[X]) (x : ℝ) :
    p.eval x = p.eval 0 + x * (constantTermSecant p).eval x := by
  have hroot : IsRoot (p - C (p.eval 0)) 0 := by
    simp [IsRoot]
  have hfactor :=
    (mul_divByMonic_eq_iff_isRoot (p := p - C (p.eval 0))
      (a := (0 : ℝ))).2 hroot
  have heval := congrArg (fun q : ℝ[X] => q.eval x) hfactor
  simp only [sub_zero, C_0, eval_mul, eval_X, eval_sub, eval_C] at heval
  dsimp [constantTermSecant]
  linarith

/-- Coefficientwise continuity of a bounded-degree characteristic polynomial
controls its secant quotient jointly in the parameter and spectral variable. -/
theorem constantTermSecant_joint_continuousAt
    (P : ℝ → ℝ[X]) (N : ℕ)
    (hdegree : ∀ δ, (constantTermSecant (P δ)).natDegree < N)
    (hcoeff : ∀ k, ContinuousAt (fun δ => (P δ).coeff k) 0) :
    ContinuousAt
      (fun y : ℝ × ℝ => (constantTermSecant (P y.1)).eval y.2) (0, 0) := by
  have heval (δ x : ℝ) :
      (constantTermSecant (P δ)).eval x =
        ∑ k ∈ Finset.range N, (P δ).coeff (k+1) * x^k := by
    rw [Polynomial.eval_eq_sum_range' (hdegree δ)]
    simp only [constantTermSecant_coeff]
  simp_rw [heval]
  apply tendsto_finsetSum (Finset.range N)
  intro k hk
  have hc : ContinuousAt
      (fun y : ℝ × ℝ => (P y.1).coeff (k+1)) (0, 0) :=
    ContinuousAt.comp (f := Prod.fst) (x := ((0 : ℝ), (0 : ℝ)))
      (hcoeff (k+1)) continuousAt_fst
  exact (hc.mul (continuousAt_snd.pow k)).tendsto

/-- A simple root approaching zero inherits its leading asymptotic from the
constant term. This is the analytic bridge needed after a network-specific
constant-term factorization supplies the common splitting coefficient. -/
theorem simple_root_asymptotic_of_constant_term
    (P : ℝ → ℝ[X]) (δ lam c : ℕ → ℝ) (N degreeBound : ℕ) (c₀ : ℝ)
    (hdegree : ∀ t, (P t).natDegree < degreeBound)
    (hcoeff : ∀ k, ContinuousAt (fun t => (P t).coeff k) 0)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hlam : Tendsto lam atTop (𝓝 0))
    (hc : Tendsto c atTop (𝓝 c₀))
    (hδne : ∀ k, δ k ≠ 0)
    (hroot : ∀ k, (P (δ k)).eval (lam k) = 0)
    (hconst : ∀ k, (P (δ k)).eval 0 = (δ k)^N * c k)
    (hsimple : (P 0).derivative.eval 0 ≠ 0) :
    Tendsto (fun k => lam k / (δ k)^N) atTop
      (𝓝 (-(c₀ / (P 0).derivative.eval 0))) := by
  let Q : ℕ → ℝ := fun k => (constantTermSecant (P (δ k))).eval (lam k)
  have hQ : Tendsto Q atTop (𝓝 ((P 0).derivative.eval 0)) := by
    have hpair : Tendsto (fun k => (δ k, lam k)) atTop (𝓝 ((0 : ℝ), (0 : ℝ))) := by
      simpa only [nhds_prod_eq] using hδ.prodMk hlam
    simpa only [Q, Function.comp_def, constantTermSecant_eval_zero] using
      (constantTermSecant_joint_continuousAt P degreeBound
        (fun t => constantTermSecant_degree_lt (P t) degreeBound (hdegree t))
        hcoeff).tendsto.comp hpair
  have hQne : ∀ᶠ k in atTop, Q k ≠ 0 :=
    (eventually_ne_nhds hsimple).filter_mono hQ
  have hratio : ∀ᶠ k in atTop, lam k / (δ k)^N = -(c k / Q k) := by
    filter_upwards [hQne] with k hq
    have hident := constantTermSecant_eval_identity (P (δ k)) (lam k)
    rw [hroot k, hconst k] at hident
    dsimp [Q] at hq ⊢
    field_simp [hδne k, hq]
    nlinarith
  have hlim : Tendsto (fun k => -(c k / Q k)) atTop
      (𝓝 (-(c₀ / (P 0).derivative.eval 0))) :=
    (hc.div hQ hsimple).neg
  exact hlim.congr' (hratio.mono (by intro k hk; exact hk.symm))

end
end PhosphorylationStableCapacity

