module
public import proofs.PhosphorylationStableCapacity.FiniteMatrixFirstOrder435
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter Matrix
open scoped Topology Matrix.Norms.Elementwise

/-- Finitely many concrete matrix probes admit one signed first-order
matrix-norm constant. This packages the all-one and two-at-site checks
without changing any kinetic witness. -/
theorem finite_matrix_probe_uniform_first_order
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι]
    (F : α → ℝ → Matrix ι ι ℝ)
    (hF : ∀ a, DifferentiableAt ℝ (F a) 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), ∀ a : α,
        ‖F a δ - F a 0‖ ≤ C * |δ| := by
  classical
  choose c hc hEv using fun a =>
    finite_matrix_entry_first_order_bound (F a) (hF a)
  let C := 1 + ∑ a : α, c a
  have hC : 0 < C := by
    dsimp [C]
    have hsum : 0 ≤ ∑ a : α, c a :=
      Finset.sum_nonneg (fun a ha => (hc a).le)
    linarith
  have hle (a : α) : c a ≤ C := by
    have hsingle : c a ≤ ∑ p : α, c p :=
      Finset.single_le_sum (fun p hp => (hc p).le)
        (Finset.mem_univ a)
    dsimp [C]
    linarith
  have hall : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ),
      ∀ a : α, ∀ i j : ι,
        |F a δ i j - F a 0 i j| ≤ c a * |δ| :=
    Filter.eventually_all.mpr hEv
  refine ⟨C, hC, ?_⟩
  filter_upwards [hall] with δ hδ a
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  have hbound := hδ a i j
  have hbound' := hbound.trans
    (mul_le_mul_of_nonneg_right (hle a) (abs_nonneg δ))
  simpa only [Real.norm_eq_abs, Matrix.sub_apply] using hbound'

end

end PhosphorylationStableCapacity
