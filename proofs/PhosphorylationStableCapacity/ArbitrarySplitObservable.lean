module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitSource

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- The observable used to label the manuscript's split equilibria is
    exactly the prescribed arbitrary-offset root. -/
theorem arbitrarySplitFiniteState_sqrt_observable_eq_root
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (j : Fin (2*m+1))
    (hy : 1 < offsetSplitRoot ξ δ j.val) :
    Real.sqrt (1+8*
      (arbitrarySplitFiniteState m ξ r δ j).E /
        (arbitrarySplitFiniteState m ξ r δ j).F) =
      offsetSplitRoot ξ δ j.val := by
  let y := offsetSplitRoot ξ δ j.val
  let D := arbitrarySplitRawD m ξ r δ
  let B := arbitrarySplitRawB m ξ r δ
  have hyF : rootF y ≠ 0 := by
    dsimp [rootF]
    exact div_ne_zero (by norm_num) (by linarith)
  have hratio :
      (arbitrarySplitFiniteState m ξ r δ j).E /
        (arbitrarySplitFiniteState m ξ r δ j).F = ratio y := by
    exact reconstruct_ratio
      (fun i : Fin (m+2) => ((1+X)*D).coeff i)
      (fun i : Fin (m+1) => B.coeff i)
      (fun i : Fin (m+1) => D.coeff i)
      (ratio y) (rootS y (D.eval (ratio y))) (rootF y) hyF
  rw [mul_div_assoc, hratio]
  have halg : 1+8*ratio y = y^2 := by
    dsimp [ratio]
    ring
  rw [halg, Real.sqrt_sq_eq_abs, abs_of_pos (by linarith : 0 < y)]

theorem arbitrarySplitFiniteState_sqrt_observable_eq_offset
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (j : Fin (2*m+1))
    (hy : 1 < offsetSplitRoot ξ δ j.val) :
    Real.sqrt (1+8*
      (arbitrarySplitFiniteState m ξ r δ j).E /
        (arbitrarySplitFiniteState m ξ r δ j).F) =
      3+δ*ξ j.val := by
  simpa only [offsetSplitRoot] using
    arbitrarySplitFiniteState_sqrt_observable_eq_root
      m ξ r δ j hy

/-- Positive splitting separates all prescribed equilibria because their
    observable labels are strictly ordered. -/
theorem arbitrarySplitFiniteState_injective_of_positive_split
    (m : ℕ) (ξ : ℕ → ℝ) (hξ : StrictMono ξ)
    (r δ : ℝ) (hδ : 0 < δ)
    (hy : ∀ j : Fin (2*m+1),
      1 < offsetSplitRoot ξ δ j.val) :
    Function.Injective
      (arbitrarySplitFiniteState m ξ r δ) := by
  intro i j hij
  have hi := arbitrarySplitFiniteState_sqrt_observable_eq_offset
    m ξ r δ i (hy i)
  have hj := arbitrarySplitFiniteState_sqrt_observable_eq_offset
    m ξ r δ j (hy j)
  rw [hij] at hi
  have hmul : δ*ξ i.val = δ*ξ j.val := by linarith
  have hξeq : ξ i.val = ξ j.val :=
    mul_left_cancel₀ (ne_of_gt hδ) hmul
  exact Fin.ext (hξ.injective hξeq)

end
end PhosphorylationStableCapacity
