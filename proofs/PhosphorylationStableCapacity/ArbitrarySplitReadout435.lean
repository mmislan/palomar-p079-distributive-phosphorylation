module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitSource

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- Literal fully phosphorylated free plus enzyme-bound substrate. -/
def fullyPhosphorylatedReadout (m : ℕ) (s : State (m+1)) : ℝ :=
  s.S (Fin.last (m+1)) + s.D (Fin.last m)

/-- The manuscript's readout formula holds for every arbitrary-offset
equilibrium state, using the actual reconstructed species. -/
theorem arbitrarySplitReadout_closed_form
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (hD : DensePositive (arbitrarySplitRawD m ξ r δ) m)
    (j : Fin (2*m+1))
    (hx : 1 < offsetSplitRoot ξ δ j.val) :
    let x := offsetSplitRoot ξ δ j.val
    let D := arbitrarySplitRawD m ξ r δ
    fullyPhosphorylatedReadout m (arbitrarySplitFiniteState m ξ r δ j) =
      (D.coeff m / 2) *
        ((ratio x)^m / D.eval (ratio x)) *
          ((x-1)*(x+5)/(x+1)) := by
  intro x D
  have hu : ratio x ≠ 0 := ne_of_gt (ratio_pos hx)
  have hDen : D.eval (ratio x) ≠ 0 :=
    ne_of_gt (hD.eval_pos (ratio_pos hx))
  have hx1 : x+1 ≠ 0 := by linarith
  have hcoeff : ((1+X)*D : ℝ[X]).coeff (m+1) = D.coeff m := by
    have hzero : D.coeff (m+1) = 0 := hD.2 (m+1) (by omega)
    simp [add_mul, coeff_add, coeff_X_mul, hzero]
  change ((1+X)*D : ℝ[X]).coeff (m+1) *
      (ratio x)^(m+1) * rootS x (D.eval (ratio x)) +
      D.coeff m * (ratio x)^(m+1) *
        rootS x (D.eval (ratio x)) * rootF x = _
  rw [hcoeff]
  unfold rootS rootF
  rw [pow_succ]
  field_simp [hu, hDen, hx1]
  ring

end

end PhosphorylationStableCapacity
