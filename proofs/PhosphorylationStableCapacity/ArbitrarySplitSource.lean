module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitConversion
public import proofs.PhosphorylationStableCapacity.SplitSource

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- A single kinetic realization of the arbitrary-offset source pair. -/
def arbitrarySplitFiniteRates (m : ℕ) (ξ : ℕ → ℝ)
    (r δ : ℝ) : Rates (m+1) :=
  realize
    (fun i : Fin (m+2) => ((1+X)*arbitrarySplitRawD m ξ r δ).coeff i)
    (fun i : Fin (m+1) => (arbitrarySplitRawB m ξ r δ).coeff i)
    (fun i : Fin (m+1) => (arbitrarySplitRawD m ξ r δ).coeff i)

/-- All prescribed states use exactly the same rate list. -/
def arbitrarySplitFiniteState (m : ℕ) (ξ : ℕ → ℝ)
    (r δ : ℝ) (j : Fin (2*m+1)) : State (m+1) :=
  let x := offsetSplitRoot ξ δ j.val
  reconstruct
    (fun i : Fin (m+2) => ((1+X)*arbitrarySplitRawD m ξ r δ).coeff i)
    (fun i : Fin (m+1) => (arbitrarySplitRawB m ξ r δ).coeff i)
    (fun i : Fin (m+1) => (arbitrarySplitRawD m ξ r δ).coeff i)
    (ratio x) (rootS x ((arbitrarySplitRawD m ξ r δ).eval (ratio x)))
    (rootF x)

/-- The arbitrary-root construction satisfies the literal mass-action
equilibrium equations, positivity, and the same three totals whenever
its converted coefficient lists are positive. -/
theorem arbitrarySplitFiniteState_source_of_conversion_positive
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (hD : DensePositive (arbitrarySplitRawD m ξ r δ) m)
    (hB : DensePositive (arbitrarySplitRawB m ξ r δ) m)
    (j : Fin (2*m+1))
    (hx : 1 < offsetSplitRoot ξ δ j.val) :
    (arbitrarySplitFiniteRates m ξ r δ).Positive ∧
      (arbitrarySplitFiniteState m ξ r δ j).Positive ∧
      Equilibrium (arbitrarySplitFiniteRates m ξ r δ)
        (arbitrarySplitFiniteState m ξ r δ j) ∧
      totalE (arbitrarySplitFiniteState m ξ r δ j) = 2*r ∧
      totalF (arbitrarySplitFiniteState m ξ r δ j) = 2 ∧
      totalS (arbitrarySplitFiniteState m ξ r δ j) = 2*(r+1) := by
  let x := offsetSplitRoot ξ δ j.val
  let B := arbitrarySplitRawB m ξ r δ
  let D := arbitrarySplitRawD m ξ r δ
  have hzero : arbitrarySplitConversionResidual m ξ r δ x = 0 := by
    rw [arbitrarySplitConversionResidual_factor,
      arbitrarySplitScalarProduct_eq_prod_range]
    have hj : j.val ∈ Finset.range (2*m+1) := Finset.mem_range.mpr j.isLt
    rw [Finset.prod_eq_zero hj (by simp [x])]
    ring
  have hrel : (x-1)*(B.eval (ratio x)-r*D.eval (ratio x)) =
      2*(r-ratio x)*D.eval (ratio x) := by
    dsimp [arbitrarySplitConversionResidual, B, D] at hzero
    linarith
  have hstate := source_from_coefficients B D hB hD r x hx hrel
  have hA := dense_inventory_product hD
  have hrate : (arbitrarySplitFiniteRates m ξ r δ).Positive := by
    apply realize_positive
    · intro i
      exact hA.1 i (by omega)
    · intro i
      exact hB.1 i (by omega)
    · intro i
      exact hD.1 i (by omega)
  exact ⟨hrate,
    by simpa only [arbitrarySplitFiniteState, x, B, D] using hstate.1,
    by simpa only [arbitrarySplitFiniteRates, arbitrarySplitFiniteState,
        x, B, D] using hstate.2.1,
    by simpa only [arbitrarySplitFiniteState, x, B, D] using hstate.2.2.1,
    by simpa only [arbitrarySplitFiniteState, x, B, D] using hstate.2.2.2.1,
    by simpa only [arbitrarySplitFiniteState, x, B, D] using hstate.2.2.2.2⟩

end
end PhosphorylationStableCapacity
