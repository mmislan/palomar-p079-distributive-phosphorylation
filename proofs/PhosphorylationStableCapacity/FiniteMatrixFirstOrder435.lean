module
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise

/-- One first-order constant controls every entry of a finite matrix
family differentiable at the coalesced parameter. -/
theorem finite_matrix_entry_first_order_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ℝ → Matrix ι ι ℝ)
    (hJ : DifferentiableAt ℝ J 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ δ : ℝ in 𝓝 0,
        ∀ i j : ι, |J δ i j - J 0 i j| ≤ C*|δ| := by
  have hper (i j : ι) : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ δ : ℝ in 𝓝 0,
        |J δ i j - J 0 i j| ≤ C*|δ| := by
    have hf := (differentiableAt_pi.mp (differentiableAt_pi.mp hJ i)) j
    obtain ⟨C, hCpos, hC⟩ := hf.isBigO_sub.exists_pos
    refine ⟨C, hCpos, ?_⟩
    filter_upwards [hC.bound] with δ hb
    simpa only [sub_zero, Real.norm_eq_abs] using hb
  choose C hC hEv using hper
  let Call := 1 + ∑ i : ι, ∑ j : ι, C i j
  have hinner (i : ι) : 0 ≤ ∑ j : ι, C i j :=
    Finset.sum_nonneg (fun j _ => (hC i j).le)
  have hsum : 0 ≤ ∑ i : ι, ∑ j : ι, C i j :=
    Finset.sum_nonneg (fun i _ => hinner i)
  have hCall : 0 < Call := by
    dsimp [Call]
    linarith
  have hCbound (i j : ι) : C i j ≤ Call := by
    have h₁ : C i j ≤ ∑ q : ι, C i q :=
      Finset.single_le_sum (fun q hq => (hC i q).le)
        (Finset.mem_univ j)
    have h₂ : (∑ q : ι, C i q) ≤ ∑ p : ι, ∑ q : ι, C p q :=
      Finset.single_le_sum (fun q hq => hinner q)
        (Finset.mem_univ i)
    have h₃ : (∑ p : ι, ∑ q : ι, C p q) ≤ Call := by
      dsimp [Call]
      linarith
    exact h₁.trans (h₂.trans h₃)
  refine ⟨Call, hCall, ?_⟩
  have hEvAll : ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ i j : ι, |J δ i j-J 0 i j| ≤ C i j*|δ| := by
    exact Filter.eventually_all.mpr
      (fun i => Filter.eventually_all.mpr (hEv i))
  filter_upwards [hEvAll] with δ hδ i j
  exact (hδ i j).trans
    (mul_le_mul_of_nonneg_right (hCbound i j) (abs_nonneg δ))

end

end PhosphorylationStableCapacity
