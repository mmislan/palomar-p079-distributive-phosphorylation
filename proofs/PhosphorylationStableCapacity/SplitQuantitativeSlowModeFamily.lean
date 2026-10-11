module
public import proofs.PhosphorylationStableCapacity.SplitSlowRootLinearBound
public import proofs.PhosphorylationStableCapacity.SplitQuantitativeSlowRoot

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter Polynomial
open scoped Topology

/-- A continuously selected simple slow mode with stable transverse
    spectrum inherits the exact multiplicative first-order splitting law
    from a factored characteristic constant term. The predicate `S` carries
    the transverse spectral certificate for the *same* selected root. -/
theorem quantitative_slow_mode_family_of_factored_constant_term
    (P : ℝ → ℝ[X]) (c : ℝ → ℝ) (S : ℝ → ℝ → Prop)
    (N degreeBound : ℕ) (gap c₀ p₁ : ℝ)
    (hgap : gap ≠ 0) (hc₀ : 0 < c₀) (hp₁ : 0 < p₁)
    (hdegree : ∀ δ, (constantTermSecant (P δ)).natDegree < degreeBound)
    (hcoeff : ∀ k, DifferentiableAt ℝ (fun δ => (P δ).coeff k) 0)
    (hc : DifferentiableAt ℝ c 0) (hcvalue : c 0 = c₀)
    (hpvalue : (P 0).derivative.eval 0 = p₁)
    (hconst : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      (P δ).eval 0 = c δ*δ^N*gap)
    (hslow : ∀ η : ℝ, 0 < η →
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        ∃ lam : ℝ, |lam| < η ∧ (P δ).IsRoot lam ∧ S δ lam)
    (hN : 1 ≤ N) :
    ∃ K : ℝ, 0 < K ∧
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        ∃ lam : ℝ,
          (P δ).IsRoot lam ∧ S δ lam ∧
            |lam / (-(c₀/p₁)*δ^N*gap)-1| ≤ K*|δ| := by
  obtain ⟨A, hA, hAbound⟩ := differentiableAt_first_order_abs_bound c hc
  obtain ⟨η, C, hη, hC, hrect⟩ :=
    constantTermSecant_rectangular_first_order_bound
      P degreeBound hdegree hcoeff
  let ρ := min η (p₁/(4*C))
  have hρ : 0 < ρ := lt_min hη (div_pos hp₁ (by positivity))
  have hρη : ρ ≤ η := min_le_left ..
  have hρp : ρ ≤ p₁/(4*C) := min_le_right ..
  have hnear := hslow ρ hρ
  have hδsmall : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      |δ| < min ρ 1 := by
    have hball : ∀ᶠ δ : ℝ in 𝓝 0, |δ| < min ρ 1 := by
      have hb : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ),
          δ ∈ Metric.ball (0 : ℝ) (min ρ 1) :=
        Metric.ball_mem_nhds (0 : ℝ) (lt_min hρ (by norm_num))
      filter_upwards [hb] with δ hδ
      simpa [Metric.mem_ball, Real.dist_eq] using hδ
    exact hball.filter_mono nhdsWithin_le_nhds
  let cmax := |c₀| + A + 1
  have hcmax : 0 ≤ cmax := by dsimp [cmax]; positivity
  let L := 2*cmax*|gap|/p₁
  let B := C*(1+L)
  have hB : 0 ≤ B := by
    have hL : 0 ≤ L := by dsimp [L]; positivity
    dsimp [B]
    positivity
  let K := ((A*p₁+|c₀| * B)/(p₁^2/2))/(c₀/p₁)+1
  have hK : 0 < K := by
    have hpden : 0 < p₁^2/2 := by positivity
    have hnum : 0 ≤ A*p₁+|c₀| * B := by positivity
    dsimp [K]
    have : 0 ≤ ((A*p₁+|c₀| * B)/(p₁^2/2))/(c₀/p₁) := by positivity
    linarith
  refine ⟨K, hK, ?_⟩
  filter_upwards [hAbound.filter_mono nhdsWithin_le_nhds,
    hconst, hnear, hδsmall, self_mem_nhdsWithin]
    with δ hcδ hconstδ hrootδ hδsmallδ hδpos
  obtain ⟨lam, hlamρ, hroot, hS⟩ := hrootδ
  have hδρ : |δ| < ρ := lt_of_lt_of_le hδsmallδ (min_le_left ..)
  have hδone : |δ| ≤ 1 := le_of_lt
    (lt_of_lt_of_le hδsmallδ (min_le_right ..))
  have hδne : δ ≠ 0 := by
    exact ne_of_gt hδpos
  have hqrect :
      |(constantTermSecant (P δ)).eval lam-p₁| ≤
        C*(|δ|+|lam|) := by
    rw [← hpvalue]
    exact hrect δ lam (lt_of_lt_of_le hδρ hρη)
      (lt_of_lt_of_le hlamρ hρη)
  have hq : p₁/2 ≤ (constantTermSecant (P δ)).eval lam := by
    have hsum : |δ|+|lam| ≤ 2*ρ := by linarith
    have hbound : C*(|δ|+|lam|) ≤ p₁/2 := by
      calc
        C*(|δ|+|lam|) ≤ C*(2*ρ) := by gcongr
        _ ≤ C*(2*(p₁/(4*C))) := by gcongr
        _ = p₁/2 := by field_simp [ne_of_gt hC]; ring
    have hlow := (abs_le.mp (hqrect.trans hbound)).1
    linarith
  have hcmaxδ : |c δ| ≤ cmax := by
    have htriangle : |c δ| ≤ |c δ-c₀|+|c₀| := by
      calc
        |c δ| = |(c δ-c₀)+c₀| := by congr 1; ring
        _ ≤ |c δ-c₀|+|c₀| := abs_add_le _ _
    have hcδ' : |c δ-c₀| ≤ A*|δ| := by
      simpa only [hcvalue] using hcδ
    have hAδ : A*|δ| ≤ A := by nlinarith [hδone]
    dsimp [cmax]
    linarith
  have hpow : |δ|^N ≤ |δ| := by
    have hNpred : N = (N-1)+1 := by omega
    conv_lhs => rw [hNpred, pow_succ]
    have hp : |δ|^(N-1) ≤ 1 :=
      pow_le_one₀ (abs_nonneg δ) hδone
    nlinarith [mul_le_mul_of_nonneg_right hp (abs_nonneg δ)]
  have hlin : |lam| ≤ L*|δ| := by
    dsimp [L]
    exact slow_root_linear_bound_of_factored_constant_term
      P c N gap cmax p₁ δ lam hcmax hp₁ hconstδ hroot hq
      hcmaxδ hpow
  have hqfirst : |(constantTermSecant (P δ)).eval lam-p₁| ≤
      B*|δ| := by
    calc
      |(constantTermSecant (P δ)).eval lam-p₁| ≤
          C*(|δ|+|lam|) := hqrect
      _ ≤ C*(|δ|+L*|δ|) := by gcongr
      _ = B*|δ| := by dsimp [B]; ring
  have hnumfirst : |c δ-c₀| ≤ A*|δ| := by
    simpa only [hcvalue] using hcδ
  have hmain := quantitative_slow_root_of_factored_constant_term
    P c N gap c₀ p₁ A B δ lam hc₀ hp₁ hA.le hB
    hδne hgap hconstδ hroot hq hnumfirst hqfirst
  refine ⟨lam, hroot, hS, ?_⟩
  exact hmain.trans (by
    dsimp [K]
    have hδabs : 0 ≤ |δ| := abs_nonneg δ
    nlinarith)

end
end PhosphorylationStableCapacity
