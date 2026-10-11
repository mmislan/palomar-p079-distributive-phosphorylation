module
public import proofs.PhosphorylationStableCapacity.LoadedFastBalance

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Perturbations of the two complex families with every loaded level fixed. -/
abbrev FastSpace (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ)

def fastDeltaS {n : ℕ} (v : FastSpace n) (j : Fin (n + 1)) : ℝ :=
  -boundComplexAt v.1 v.2 j

def fastDeltaE {n : ℕ} (v : FastSpace n) : ℝ := -∑ i, v.1 i
def fastDeltaF {n : ℕ} (v : FastSpace n) : ℝ := -∑ i, v.2 i

/-- The diagonal concentration metric pulled back to fixed-loaded-level
complex perturbations. -/
def fastBindingEnergy {n : ℕ} (x : State n) (v : FastSpace n) : ℝ :=
  (∑ j, fastDeltaS v j ^ 2 / x.S j) +
  fastDeltaE v ^ 2 / x.E + fastDeltaF v ^ 2 / x.F +
  (∑ i, v.1 i ^ 2 / x.C i) + (∑ i, v.2 i ^ 2 / x.D i)

theorem weightedSquares_nonneg {ι : Type*} [Fintype ι]
    (v w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    0 ≤ ∑ i, v i ^ 2 / w i := by
  exact Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (hw i).le)

theorem weightedSquares_pos {ι : Type*} [Fintype ι]
    (v w : ι → ℝ) (hw : ∀ i, 0 < w i) (hv : v ≠ 0) :
    0 < ∑ i, v i ^ 2 / w i := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_pos'
    (fun j _ => div_nonneg (sq_nonneg _) (hw j).le)
    ⟨i, Finset.mem_univ i, div_pos (sq_pos_of_ne_zero hi) (hw i)⟩

/-- The fast binding metric is strictly positive on every nonzero complex
direction at every positive literal state. -/
theorem fastBindingEnergy_pos {n : ℕ} (x : State n)
    (hx : x.Positive) (v : FastSpace n) (hv : v ≠ 0) :
    0 < fastBindingEnergy x v := by
  rcases hx with ⟨hS, hE, hF, hC, hD⟩
  have hS0 := weightedSquares_nonneg (fastDeltaS v) x.S hS
  have hE0 : 0 ≤ fastDeltaE v ^ 2 / x.E :=
    div_nonneg (sq_nonneg _) hE.le
  have hF0 : 0 ≤ fastDeltaF v ^ 2 / x.F :=
    div_nonneg (sq_nonneg _) hF.le
  have hC0 := weightedSquares_nonneg v.1 x.C hC
  have hD0 := weightedSquares_nonneg v.2 x.D hD
  by_cases hvC : v.1 = 0
  · have hvD : v.2 ≠ 0 := by
      intro h
      apply hv
      exact Prod.ext hvC h
    have hDpos := weightedSquares_pos v.2 x.D hD hvD
    unfold fastBindingEnergy
    exact add_pos_of_nonneg_of_pos
      (add_nonneg (add_nonneg (add_nonneg hS0 hE0) hF0) hC0)
      hDpos
  · have hCpos := weightedSquares_pos v.1 x.C hC hvC
    unfold fastBindingEnergy
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_nonneg_of_pos
        (add_nonneg (add_nonneg hS0 hE0) hF0) hCpos)
      hD0

end
end PhosphorylationStableCapacity
