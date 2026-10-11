module
public import Mathlib.Tactic.LinearCombination
public import proofs.PhosphorylationStableCapacity.ClassBoundaryInward

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Every class with positive conserved totals contains a strictly
positive literal state. Together with the coordinate box this is the
nonempty-interior input to the class-polytope degree argument. -/
theorem positive_class_nonempty (n : ℕ)
    (ET FT ST : ℝ) (hET : 0 < ET) (hFT : 0 < FT) (hST : 0 < ST) :
    ∃ x : State n, x.Positive ∧ InClass ET FT ST x := by
  have hm : 0 < min (min ET FT) ST :=
    lt_min (lt_min hET hFT) hST
  obtain ⟨θ, hθ, hsmall⟩ :=
    exists_pos_mul_lt hm (2*(n:ℝ)+1)
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hθET : (n:ℝ)*θ < ET := by
    have h : (n:ℝ)*θ ≤ (2*(n:ℝ)+1)*θ := by
      apply mul_le_mul_of_nonneg_right _ hθ.le
      nlinarith
    exact lt_of_le_of_lt h
      (lt_of_lt_of_le hsmall (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hθFT : (n:ℝ)*θ < FT := by
    have h : (n:ℝ)*θ ≤ (2*(n:ℝ)+1)*θ := by
      apply mul_le_mul_of_nonneg_right _ hθ.le
      nlinarith
    exact lt_of_le_of_lt h
      (lt_of_lt_of_le hsmall (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hθST : 2*(n:ℝ)*θ < ST := by
    have h : 2*(n:ℝ)*θ ≤ (2*(n:ℝ)+1)*θ := by
      nlinarith [hθ.le]
    exact lt_of_le_of_lt h
      (lt_of_lt_of_le hsmall (min_le_right _ _))
  let s : ℝ := (ST-2*(n:ℝ)*θ)/((n:ℝ)+1)
  have hs : 0 < s := by
    apply div_pos
    · linarith
    · positivity
  have hsident : ((n:ℝ)+1)*s = ST-2*(n:ℝ)*θ := by
    dsimp [s]
    field_simp
  let x : State n :=
    { S := fun _ => s
      E := ET-(n:ℝ)*θ
      F := FT-(n:ℝ)*θ
      C := fun _ => θ
      D := fun _ => θ }
  have hx : x.Positive := by
    refine ⟨fun _ => hs, ?_, ?_, fun _ => hθ, fun _ => hθ⟩
    · dsimp [x]
      linarith
    · dsimp [x]
      linarith
  refine ⟨x, hx, ?_⟩
  constructor
  · simp [totalE, x]
  constructor
  · simp [totalF, x]
  · simp [totalS, x]
    linear_combination hsident

end
end PhosphorylationStableCapacity
