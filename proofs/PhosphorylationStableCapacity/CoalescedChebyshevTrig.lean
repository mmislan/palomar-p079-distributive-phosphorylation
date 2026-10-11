module
public import proofs.PhosphorylationStableCapacity.CoalescedChebyshevScale

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

theorem sin_two_step (a h : ℝ) :
    2 * Real.cos h * Real.sin (a + h) - Real.sin a =
      Real.sin (a + 2 * h) := by
  have hsub : Real.sin a =
      Real.sin (a + h) * Real.cos h -
        Real.cos (a + h) * Real.sin h := by
    convert Real.sin_sub (a + h) h using 1
    ring
  have hadd : Real.sin (a + 2 * h) =
      Real.sin (a + h) * Real.cos h +
        Real.cos (a + h) * Real.sin h := by
    convert Real.sin_add (a + h) h using 1
    ring
  rw [hsub, hadd]
  ring

/-- The Chebyshev-type sequence is a Dirichlet-kernel quotient, stated
without division so it also holds at zeros of `sin (θ/2)`. -/
theorem coalescedChebF_cos (m : ℕ) (θ : ℝ) :
    coalescedChebF m (Real.cos θ) * Real.sin (θ / 2) =
      Real.sin (((2 * m + 1 : ℕ) : ℝ) * θ / 2) := by
  induction m using Nat.twoStepInduction with
  | zero =>
      simp [coalescedChebF]
  | one =>
      change (2 * Real.cos θ + 1) * Real.sin (θ / 2) =
        Real.sin (3 * θ / 2)
      have hcos : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
        conv_lhs => rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul]
      have hsin : Real.sin θ =
          2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
        conv_lhs => rw [show θ = 2 * (θ / 2) by ring, Real.sin_two_mul]
      calc
        (2 * Real.cos θ + 1) * Real.sin (θ / 2) =
            Real.sin (θ / 2) * Real.cos θ +
              Real.cos (θ / 2) * Real.sin θ := by
                rw [hcos, hsin]
                ring
        _ = Real.sin (θ / 2 + θ) := (Real.sin_add (θ / 2) θ).symm
        _ = Real.sin (3 * θ / 2) := by congr 1; ring
  | more m ih0 ih1 =>
      change (2 * Real.cos θ * coalescedChebF (m + 1) (Real.cos θ) -
        coalescedChebF m (Real.cos θ)) * Real.sin (θ / 2) =
        Real.sin (((2 * (m + 2) + 1 : ℕ) : ℝ) * θ / 2)
      calc
        (2 * Real.cos θ * coalescedChebF (m + 1) (Real.cos θ) -
          coalescedChebF m (Real.cos θ)) * Real.sin (θ / 2) =
          2 * Real.cos θ *
            (coalescedChebF (m + 1) (Real.cos θ) * Real.sin (θ / 2)) -
            coalescedChebF m (Real.cos θ) * Real.sin (θ / 2) := by ring
        _ = 2 * Real.cos θ *
              Real.sin (((2 * (m + 1) + 1 : ℕ) : ℝ) * θ / 2) -
            Real.sin (((2 * m + 1 : ℕ) : ℝ) * θ / 2) := by
              rw [ih1, ih0]
        _ = Real.sin (((2 * (m + 2) + 1 : ℕ) : ℝ) * θ / 2) := by
          convert sin_two_step (((2 * m + 1 : ℕ) : ℝ) * θ / 2) θ using 1 <;>
            push_cast <;> ring

end
end PhosphorylationStableCapacity
