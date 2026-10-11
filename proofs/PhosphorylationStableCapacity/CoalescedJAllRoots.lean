module
public import proofs.PhosphorylationStableCapacity.CoalescedJOuterInterval

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial PhosphorylationSharpness

noncomputable section

/-- One companion zero from each interval cut out by consecutive numerator
zeros, including the interval from the rightmost numerator zero to zero. -/
def coalescedJRoot (m : ℕ) (j : Fin m) : ℝ :=
  if h : j.val = 0 then
    Classical.choose (coalescedJ_zero_above_first_N_root m (by omega))
  else
    Classical.choose (coalescedJ_zero_between_adjacent m (j.val - 1) (by omega))

theorem coalescedJRoot_bounds (m : ℕ) (j : Fin m) :
    coalescedRoot m j.val < coalescedJRoot m j ∧
      coalescedJRoot m j <
        (if j.val = 0 then 0 else coalescedRoot m (j.val - 1)) ∧
      (coalescedPair m).2.eval (coalescedJRoot m j) = 0 := by
  by_cases hj : j.val = 0
  · have hs := Classical.choose_spec
      (coalescedJ_zero_above_first_N_root m (by omega))
    unfold coalescedJRoot
    simp only [hj, ↓reduceDIte, ↓reduceIte]
    simpa [hj] using hs
  · have hpred : j.val - 1 + 1 = j.val := by omega
    have hs := Classical.choose_spec
      (coalescedJ_zero_between_adjacent m (j.val - 1) (by omega))
    unfold coalescedJRoot
    simp only [hj, ↓reduceDIte, ↓reduceIte]
    simpa only [hpred] using hs

theorem coalescedJRoot_strictAnti (m : ℕ) :
    StrictAnti (coalescedJRoot m) := by
  intro j k hjk
  have hjk' : j.val < k.val := Fin.lt_def.mp hjk
  have hk0 : k.val ≠ 0 := by omega
  have hku := (coalescedJRoot_bounds m k).2.1
  simp only [hk0, ↓reduceIte] at hku
  have hjl := (coalescedJRoot_bounds m j).1
  have hindex : j.val ≤ k.val - 1 := by omega
  rcases eq_or_lt_of_le hindex with he | hlt
  · rw [← he] at hku
    exact lt_trans hku hjl
  · have hroot : coalescedRoot m (k.val - 1) <
        coalescedRoot m j.val :=
      coalescedRoot_strictAnti m j.val (k.val - 1)
        j.isLt (by omega) hlt
    exact lt_trans hku (lt_trans hroot hjl)

def coalescedJRootSet (m : ℕ) : Finset ℝ :=
  Finset.univ.image (coalescedJRoot m)

theorem coalescedJRootSet_card (m : ℕ) :
    (coalescedJRootSet m).card = m := by
  classical
  unfold coalescedJRootSet
  rw [Finset.card_image_of_injective _
    (coalescedJRoot_strictAnti m).injective]
  simp

/-- Every companion root, counted with multiplicity, lies in exactly one
of the explicit intervals between successive numerator roots or the origin. -/
theorem coalescedJ_roots_eq (m : ℕ) :
    (coalescedPair m).2.roots = (coalescedJRootSet m).val := by
  classical
  have hd := (coalescedPair_dense m).2
  have hp : (coalescedPair m).2 ≠ 0 := by
    intro h
    have hpos := hd.1 m le_rfl
    rw [h, coeff_zero] at hpos
    exact (not_lt_of_ge le_rfl) hpos
  apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
    exact (coalescedJRoot_bounds m j).2.2
  · rw [coalescedJRootSet_card, hd.degree_eq]
  · exact hp

end
end PhosphorylationStableCapacity
