module
public import proofs.PhosphorylationStableCapacity.CompactQuantitativeSlowRoot435
public import proofs.PhosphorylationStableCapacity.SplitSlowRootLinearBound

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter Polynomial
open scoped Topology

/-- Uniform compact version of the factored-characteristic slow-mode
law. The same selected simple root and spectral certificate `S` are
retained for every parameter on one split interval. -/
theorem quantitative_slow_mode_compact_family_of_factored_constant_term
    {α : Type*} (K : Set α)
    (P : α → ℝ → ℝ[X]) (c : α → ℝ → ℝ)
    (S : α → ℝ → ℝ → Prop)
    (N : ℕ) (gap cmin cmax₀ pmin η A C : ℝ)
    (hgap : gap ≠ 0) (hN : 1 ≤ N)
    (hcmin : 0 < cmin) (hcmax₀ : 0 ≤ cmax₀)
    (hpmin : 0 < pmin) (hη : 0 < η)
    (hA : 0 < A) (hC : 0 < C)
    (hc0 : ∀ a ∈ K,
      cmin ≤ c a 0 ∧ |c a 0| ≤ cmax₀)
    (hp1 : ∀ a ∈ K,
      pmin ≤ (P a 0).derivative.eval 0)
    (hnum : ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ a ∈ K, |c a δ-c a 0| ≤ A*|δ|)
    (hrect : ∀ a ∈ K, ∀ δ x : ℝ,
      |δ| < η → |x| < η →
        |(constantTermSecant (P a δ)).eval x -
          (P a 0).derivative.eval 0| ≤ C*(|δ|+|x|))
    (hconst : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ a ∈ K,
        (P a δ).eval 0 = c a δ*δ^N*gap)
    (hslow : ∀ ρ : ℝ, 0 < ρ →
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        ∀ a ∈ K, ∃ lam : ℝ,
          |lam| < ρ ∧ (P a δ).IsRoot lam ∧ S a δ lam) :
    ∃ Q : ℝ, 0 < Q ∧
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        ∀ a ∈ K, ∃ lam : ℝ,
          (P a δ).IsRoot lam ∧ S a δ lam ∧
          |lam / (-(c a 0/(P a 0).derivative.eval 0) *
            δ^N*gap)-1| ≤ Q*|δ| := by
  let ρ := min η (pmin/(4*C))
  have hρ : 0 < ρ := lt_min hη (div_pos hpmin (by positivity))
  have hρη : ρ ≤ η := min_le_left ..
  have hρp : ρ ≤ pmin/(4*C) := min_le_right ..
  have hnear := hslow ρ hρ
  have hδsmall : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      |δ| < min ρ 1 := by
    have hball : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ),
        δ ∈ Metric.ball (0 : ℝ) (min ρ 1) :=
      Metric.ball_mem_nhds 0 (lt_min hρ (by norm_num))
    filter_upwards [hball.filter_mono nhdsWithin_le_nhds] with δ hδ
    simpa [Metric.mem_ball, Real.dist_eq] using hδ
  let cmax := cmax₀+A+1
  have hcmax : 0 ≤ cmax := by dsimp [cmax]; positivity
  let L := 2*cmax*|gap|/pmin
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let B := C*(1+L)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmain : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ a ∈ K, ∃ lam : ℝ,
        (P a δ).IsRoot lam ∧ S a δ lam ∧
        (P a δ).eval 0 = c a δ*δ^N*gap ∧
        (P a 0).derivative.eval 0/2 ≤
          (constantTermSecant (P a δ)).eval lam ∧
        |c a δ-c a 0| ≤ A*|δ| ∧
        |(constantTermSecant (P a δ)).eval lam-
          (P a 0).derivative.eval 0| ≤ B*|δ| := by
    filter_upwards [hnum.filter_mono nhdsWithin_le_nhds,
      hconst, hnear, hδsmall] with δ hnumδ hconstδ hnearδ hδsmallδ a ha
    obtain ⟨lam, hlamρ, hroot, hS⟩ := hnearδ a ha
    let p₁ := (P a 0).derivative.eval 0
    have hp₁ : 0 < p₁ := lt_of_lt_of_le hpmin (hp1 a ha)
    have hδρ : |δ| < ρ := lt_of_lt_of_le hδsmallδ (min_le_left ..)
    have hδone : |δ| ≤ 1 := le_of_lt
      (lt_of_lt_of_le hδsmallδ (min_le_right ..))
    have hqrect :
        |(constantTermSecant (P a δ)).eval lam-p₁| ≤
          C*(|δ|+|lam|) :=
      hrect a ha δ lam
        (lt_of_lt_of_le hδρ hρη)
        (lt_of_lt_of_le hlamρ hρη)
    have hq : p₁/2 ≤ (constantTermSecant (P a δ)).eval lam := by
      have hsum : |δ|+|lam| ≤ 2*ρ := by linarith
      have hbound : C*(|δ|+|lam|) ≤ pmin/2 := by
        calc
          C*(|δ|+|lam|) ≤ C*(2*ρ) := by gcongr
          _ ≤ C*(2*(pmin/(4*C))) := by gcongr
          _ = pmin/2 := by field_simp [ne_of_gt hC]; ring
      have hlow := (abs_le.mp (hqrect.trans hbound)).1
      have hpminle := hp1 a ha
      dsimp [p₁] at *
      linarith
    have hcmaxδ : |c a δ| ≤ cmax := by
      have htriangle : |c a δ| ≤ |c a δ-c a 0|+|c a 0| := by
        calc
          |c a δ| = |(c a δ-c a 0)+c a 0| := by congr 1; ring
          _ ≤ |c a δ-c a 0|+|c a 0| := abs_add_le _ _
      have hAδ : A*|δ| ≤ A := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hδone hA.le
      dsimp [cmax]
      linarith [hnumδ a ha, (hc0 a ha).2]
    have hpow : |δ|^N ≤ |δ| := by
      have hNpred : N = (N-1)+1 := by omega
      conv_lhs => rw [hNpred, pow_succ]
      have hp : |δ|^(N-1) ≤ 1 :=
        pow_le_one₀ (abs_nonneg δ) hδone
      nlinarith [mul_le_mul_of_nonneg_right hp (abs_nonneg δ)]
    have hlinpoint : |lam| ≤
        (2*cmax*|gap|/p₁)*|δ| :=
      slow_root_linear_bound_of_factored_constant_term
        (P a) (c a) N gap cmax p₁ δ lam hcmax hp₁
        (hconstδ a ha) hroot hq hcmaxδ hpow
    have hLbound : 2*cmax*|gap|/p₁ ≤ L := by
      dsimp [L]
      apply div_le_div_of_nonneg_left (by positivity) hpmin (hp1 a ha)
    have hlin : |lam| ≤ L*|δ| :=
      hlinpoint.trans
        (mul_le_mul_of_nonneg_right hLbound (abs_nonneg δ))
    have hqfirst :
        |(constantTermSecant (P a δ)).eval lam-p₁| ≤
          B*|δ| := by
      calc
        _ ≤ C*(|δ|+|lam|) := hqrect
        _ ≤ C*(|δ|+L*|δ|) := by gcongr
        _ = B*|δ| := by dsimp [B]; ring
    exact ⟨lam, hroot, hS, hconstδ a ha, hq,
      hnumδ a ha, hqfirst⟩
  obtain ⟨Q, hQ, hfinish⟩ :=
    quantitative_slow_root_uniform_of_factored_constant_term
      K P c S N gap cmin pmin A B
      hgap hcmin hpmin hA.le hB
      (fun a ha => (hc0 a ha).1) hp1 hmain
  exact ⟨Q, hQ, hfinish⟩

end

end PhosphorylationStableCapacity
