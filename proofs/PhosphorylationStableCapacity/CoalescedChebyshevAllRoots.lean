module
public import proofs.PhosphorylationStableCapacity.CoalescedChebyshevRootOrder

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial PhosphorylationSharpness

noncomputable section

def coalescedRootSet (m : ℕ) : Finset ℝ :=
  (Finset.range m).image (coalescedRoot m)

theorem coalescedRootSet_card (m : ℕ) :
    (coalescedRootSet m).card = m := by
  classical
  unfold coalescedRootSet
  rw [Finset.card_image_of_injOn]
  · simp
  · intro j hj k hk heq
    have hjm := Finset.mem_range.mp hj
    have hkm := Finset.mem_range.mp hk
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · exact False.elim ((ne_of_lt (coalescedRoot_strictAnti m j k hjm hkm hjk)) heq.symm)
    · rfl
    · exact False.elim ((ne_of_lt (coalescedRoot_strictAnti m k j hkm hjm hkj)) heq)

/-- Every root, counted with multiplicity, is one of the explicit negative
real numbers indexed by `Finset.range m`. -/
theorem coalescedN_roots_eq (m : ℕ) :
    (coalescedPair m).1.roots = (coalescedRootSet m).val := by
  classical
  have hd := (coalescedPair_dense m).1
  have hp : (coalescedPair m).1 ≠ 0 := by
    intro h
    have hpos := hd.1 m le_rfl
    rw [h, coeff_zero] at hpos
    exact (not_lt_of_ge le_rfl) hpos
  apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    exact coalescedN_eval_root m j (Finset.mem_range.mp hj)
  · rw [coalescedRootSet_card, hd.degree_eq]
  · exact hp

end
end PhosphorylationStableCapacity
