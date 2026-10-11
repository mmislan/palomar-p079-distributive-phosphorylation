module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitSecondOrder435
public import Mathlib.Analysis.Calculus.Taylor

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Filter
open scoped Topology

/-- On a right interval where a scalar function is C², its first-order
Taylor remainder is bounded by a constant times the squared distance. -/
theorem contDiffOn_two_quadratic_remainder
    (f : ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (hf : ContDiffOn ℝ 2 f (Set.Icc 0 b))
    (hf0 : DifferentiableAt ℝ f 0) :
    ∃ C : ℝ, ∀ δ ∈ Set.Icc 0 b,
      |f δ - f 0 - δ * deriv f 0| ≤ C * δ^2 := by
  obtain ⟨C, hC⟩ :=
    exists_taylor_mean_remainder_bound (f := f)
      (a := 0) (b := b) (n := 1) hb.le hf
  have hunique : UniqueDiffWithinAt ℝ (Set.Icc 0 b) 0 :=
    (uniqueDiffOn_Icc hb).uniqueDiffWithinAt
      (Set.left_mem_Icc.mpr hb.le)
  have hder : derivWithin f (Set.Icc 0 b) 0 = deriv f 0 := by
    rw [derivWithin_subset (Set.subset_univ _) hunique
      hf0.differentiableWithinAt]
    simp
  have htaylor (δ : ℝ) :
      taylorWithinEval f 1 (Set.Icc 0 b) 0 δ =
        f 0 + δ * deriv f 0 := by
    rw [show (1 : ℕ) = 0+1 by omega, taylorWithinEval_succ,
      taylor_within_zero_eval]
    simp [iteratedDerivWithin_one, hder, smul_eq_mul]
  refine ⟨C, ?_⟩
  intro δ hδ
  have h := hC δ hδ
  rw [htaylor] at h
  simpa [Real.norm_eq_abs, sub_add_eq_sub_sub,
    sub_zero, Nat.factorial_one] using h

/-- A local C² hypothesis at coalescence supplies a genuine quadratic
remainder on some positive split interval. -/
theorem contDiffAt_two_quadratic_remainder
    (f : ℝ → ℝ) (hf : ContDiffAt ℝ 2 f 0) :
    ∃ b C : ℝ, 0 < b ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ b →
        |f δ - f 0 - δ * deriv f 0| ≤ C * δ^2 := by
  obtain ⟨u, hu, hcont⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hu
  let b := ε / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hsub : Set.Icc (0 : ℝ) b ⊆ u := by
    intro δ hδ
    apply hball
    have hδlt : δ < ε := lt_of_le_of_lt hδ.2 (by dsimp [b]; linarith)
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_nonneg hδ.1] using hδlt
  have hcont' : ContDiffOn ℝ 2 f (Set.Icc 0 b) := hcont.mono hsub
  have hf0 : DifferentiableAt ℝ f 0 :=
    (hf.of_le (by norm_num)).differentiableAt_one
  obtain ⟨C, hC⟩ := contDiffOn_two_quadratic_remainder f b hb hcont' hf0
  exact ⟨b, C, hb, fun δ hδ0 hδb => hC δ ⟨hδ0, hδb⟩⟩

/-- The printed O(δ²) readout expansion for two arbitrary prescribed
roots, with the common conversion polynomial and its derivative cancellation. -/
theorem arbitrarySplitReadout_scalar_quadratic_remainder
    (m : ℕ) (ξ : ℕ → ℝ) (r a b : ℝ) (hr : r ≠ 0)
    (hD₀ : (coalescedRawD m r).eval 1 ≠ 0) :
    ∃ δ₀ C : ℝ, 0 < δ₀ ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ₀ →
        |(splitReadoutScalar m (arbitrarySplitRawD m ξ r δ) (3+δ*a) -
            splitReadoutScalar m (arbitrarySplitRawD m ξ r δ) (3+δ*b)) -
          (a-b) * deriv (splitReadoutScalar m (coalescedRawD m r)) 3 * δ| ≤
          C * δ^2 := by
  let f : ℝ → ℝ := fun δ =>
    splitReadoutScalar m (arbitrarySplitRawD m ξ r δ) (3+δ*a) -
      splitReadoutScalar m (arbitrarySplitRawD m ξ r δ) (3+δ*b)
  have hsmooth : ContDiffAt ℝ 2 f 0 :=
    arbitrarySplitReadout_scalar_difference_contDiffAt_two
      m ξ r a b hr hD₀
  obtain ⟨δ₀, C, hδ₀, hbound⟩ :=
    contDiffAt_two_quadratic_remainder f hsmooth
  have hzero : f 0 = 0 := by simp [f]
  have hder : deriv f 0 =
      (a-b) * deriv (splitReadoutScalar m (coalescedRawD m r)) 3 :=
    (arbitrarySplitReadout_scalar_difference_hasDerivAt_zero
      m ξ r a b hr hD₀).deriv
  refine ⟨δ₀, C, hδ₀, ?_⟩
  intro δ hδpos hδle
  specialize hbound δ hδpos hδle
  change |f δ - f 0 - δ * deriv f 0| ≤ C * δ^2 at hbound
  rw [hzero, hder] at hbound
  simpa only [f, sub_zero, mul_comm, mul_left_comm, mul_assoc]
    using hbound

end

end PhosphorylationStableCapacity
