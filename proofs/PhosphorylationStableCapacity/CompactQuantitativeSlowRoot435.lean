module
public import proofs.PhosphorylationStableCapacity.SplitQuantitativeSlowRoot

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter Polynomial
open scoped Topology

/-- Once the numerator and secant characteristic factor have common
first-order bounds on a current family, the printed relative splitting
error has one common constant. The root and any additional spectral
certificate `S` are preserved verbatim. -/
theorem quantitative_slow_root_uniform_of_factored_constant_term
    {α : Type*} (K : Set α)
    (P : α → ℝ → ℝ[X]) (c : α → ℝ → ℝ)
    (S : α → ℝ → ℝ → Prop)
    (N : ℕ) (gap cmin pmin A B : ℝ)
    (hgap : gap ≠ 0) (hcmin : 0 < cmin) (hpmin : 0 < pmin)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc0 : ∀ a ∈ K, cmin ≤ c a 0)
    (hp1 : ∀ a ∈ K,
      pmin ≤ (P a 0).derivative.eval 0)
    (hmain : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ a ∈ K,
        ∃ lam : ℝ,
          (P a δ).IsRoot lam ∧ S a δ lam ∧
          (P a δ).eval 0 = c a δ*δ^N*gap ∧
          (P a 0).derivative.eval 0/2 ≤
            (constantTermSecant (P a δ)).eval lam ∧
          |c a δ-c a 0| ≤ A*|δ| ∧
          |(constantTermSecant (P a δ)).eval lam-
            (P a 0).derivative.eval 0| ≤ B*|δ|) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        ∀ a ∈ K,
          ∃ lam : ℝ,
            (P a δ).IsRoot lam ∧ S a δ lam ∧
            |lam / (-(c a 0 / (P a 0).derivative.eval 0) *
                δ^N*gap)-1| ≤ C*|δ| := by
  let C := 2*A/cmin + 2*B/pmin + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmain, self_mem_nhdsWithin] with δ hδ hδpos a ha
  obtain ⟨lam, hroot, hS, hconst, hsecant, hnum, hq⟩ := hδ a ha
  let c₀ := c a 0
  let p₁ := (P a 0).derivative.eval 0
  have hc₀ : 0 < c₀ := lt_of_lt_of_le hcmin (hc0 a ha)
  have hp₁ : 0 < p₁ := lt_of_lt_of_le hpmin (hp1 a ha)
  have hδne : δ ≠ 0 := ne_of_gt hδpos
  have hpoint := quantitative_slow_root_of_factored_constant_term
    (P a) (c a) N gap c₀ p₁ A B δ lam
    hc₀ hp₁ hA hB hδne hgap hconst hroot hsecant hnum hq
  have hformula :
      ((A*p₁+|c₀| *B)/(p₁^2/2))/(c₀/p₁) =
        2*A/c₀ + 2*B/p₁ := by
    rw [abs_of_pos hc₀]
    field_simp [ne_of_gt hc₀, ne_of_gt hp₁]
  have hAterm : 2*A/c₀ ≤ 2*A/cmin := by
    apply div_le_div_of_nonneg_left (by positivity) hcmin (hc0 a ha)
  have hBterm : 2*B/p₁ ≤ 2*B/pmin := by
    apply div_le_div_of_nonneg_left (by positivity) hpmin (hp1 a ha)
  refine ⟨lam, hroot, hS, ?_⟩
  calc
    _ ≤ ((A*p₁+|c₀| *B)/(p₁^2/2))/(c₀/p₁)*|δ| := hpoint
    _ = (2*A/c₀+2*B/p₁)*|δ| := by rw [hformula]
    _ ≤ C*|δ| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg δ)
      dsimp [C]
      linarith

end

end PhosphorylationStableCapacity
