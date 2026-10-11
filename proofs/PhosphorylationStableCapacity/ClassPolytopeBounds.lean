module
public import proofs.PhosphorylationStableCapacity.BoundaryEquilibrium

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The nonnegative compatibility class lies in an explicit finite
coordinate box determined only by its three conserved totals. -/
theorem nonnegative_class_species_bounds {n : ℕ}
    (ET FT ST : ℝ) (x : State n)
    (hx : NonnegativeState x) (hclass : InClass ET FT ST x) :
    (∀ j : Fin (n+1), x.S j ≤ ST) ∧
      x.E ≤ ET ∧ x.F ≤ FT ∧
      (∀ i : Fin n, x.C i ≤ min ET ST) ∧
      (∀ i : Fin n, x.D i ≤ min FT ST) := by
  have hS0 : 0 ≤ ∑ j : Fin (n+1), x.S j :=
    Finset.sum_nonneg (fun j _ => hx.1 j)
  have hC0 : 0 ≤ ∑ i : Fin n, x.C i :=
    Finset.sum_nonneg (fun i _ => hx.2.2.2.1 i)
  have hD0 : 0 ≤ ∑ i : Fin n, x.D i :=
    Finset.sum_nonneg (fun i _ => hx.2.2.2.2 i)
  rcases hclass with ⟨hET, hFT, hST⟩
  dsimp [totalE] at hET
  dsimp [totalF] at hFT
  dsimp [totalS] at hST
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    have hj : x.S j ≤ ∑ l : Fin (n+1), x.S l :=
      Finset.single_le_sum (fun l _ => hx.1 l) (Finset.mem_univ j)
    linarith
  · linarith
  · linarith
  · intro i
    have hi : x.C i ≤ ∑ l : Fin n, x.C l :=
      Finset.single_le_sum (fun l _ => hx.2.2.2.1 l) (Finset.mem_univ i)
    apply le_min
    · linarith [hx.2.1]
    · linarith
  · intro i
    have hi : x.D i ≤ ∑ l : Fin n, x.D l :=
      Finset.single_le_sum (fun l _ => hx.2.2.2.2 l) (Finset.mem_univ i)
    apply le_min
    · linarith [hx.2.2.1]
    · linarith

end
end PhosphorylationStableCapacity
