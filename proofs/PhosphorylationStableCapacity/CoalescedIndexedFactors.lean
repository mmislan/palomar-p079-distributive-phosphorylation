module
public import proofs.PhosphorylationStableCapacity.IndexedFactorProduct

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial PhosphorylationSharpness

noncomputable section

def coalescedFactorIndices (m : ℕ) : List (Fin m) :=
  (Finset.univ : Finset (Fin m)).val.toList

def coalescedNFactors (m : ℕ) : List ℝ :=
  (coalescedFactorIndices m).map fun j => -coalescedRoot m j.val

def coalescedJFactors (m : ℕ) : List ℝ :=
  (coalescedFactorIndices m).map fun j => -coalescedJRoot m j

theorem coalescedFactorIndices_length (m : ℕ) :
    (coalescedFactorIndices m).length = m := by
  simp [coalescedFactorIndices]

theorem coalescedNFactors_pos (m : ℕ) :
    ∀ a ∈ coalescedNFactors m, 0 < a := by
  intro a ha
  rcases List.mem_map.mp ha with ⟨j, _, rfl⟩
  exact neg_pos.mpr (coalescedRoot_neg m j.val j.isLt)

theorem coalescedJFactors_pos (m : ℕ) :
    ∀ b ∈ coalescedJFactors m, 0 < b := by
  intro b hb
  rcases List.mem_map.mp hb with ⟨j, _, rfl⟩
  exact (coalescedFactor_magnitude_order m j).1

theorem coalescedFactors_pairwise (m : ℕ) :
    List.Forall₂ (fun a b => b ≤ a)
      (coalescedNFactors m) (coalescedJFactors m) := by
  have h : ∀ is : List (Fin m),
      List.Forall₂ (fun a b => b ≤ a)
        (is.map fun j => -coalescedRoot m j.val)
        (is.map fun j => -coalescedJRoot m j) := by
    intro is
    induction is with
    | nil => exact .nil
    | cons j js ih =>
        exact .cons (coalescedFactor_magnitude_order m j).2.le ih
  exact h (coalescedFactorIndices m)

theorem coalescedNRootFin_strictAnti (m : ℕ) :
    StrictAnti (fun j : Fin m => coalescedRoot m j.val) := by
  intro j k hjk
  exact coalescedRoot_strictAnti m j.val k.val
    j.isLt k.isLt (Fin.lt_def.mp hjk)

theorem coalescedNRootFinset_eq (m : ℕ) :
    (Finset.univ : Finset (Fin m)).image
      (fun j => coalescedRoot m j.val) = coalescedRootSet m := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
    apply Finset.mem_image.mpr
    exact ⟨j.val, Finset.mem_range.mpr j.isLt, rfl⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    apply Finset.mem_image.mpr
    exact ⟨⟨j, Finset.mem_range.mp hj⟩, Finset.mem_univ _, rfl⟩

theorem coalescedN_indexed_factorization (m : ℕ) :
    C (coalescedPair m).1.leadingCoeff *
        positiveFactorProduct (coalescedNFactors m) =
      (coalescedPair m).1 := by
  have hp := positiveFactorProduct_finset
    (Finset.univ : Finset (Fin m))
    (fun j => coalescedRoot m j.val)
    (coalescedNRootFin_strictAnti m).injective.injOn
  rw [coalescedNRootFinset_eq] at hp
  rw [show coalescedNFactors m =
      ((Finset.univ : Finset (Fin m)).val.toList.map
        fun j => -coalescedRoot m j.val) by rfl]
  rw [hp]
  exact coalescedN_factorization m

theorem coalescedJ_indexed_factorization (m : ℕ) :
    C (coalescedPair m).2.leadingCoeff *
        positiveFactorProduct (coalescedJFactors m) =
      (coalescedPair m).2 := by
  have hp := positiveFactorProduct_finset
    (Finset.univ : Finset (Fin m))
    (coalescedJRoot m)
    (coalescedJRoot_strictAnti m).injective.injOn
  change positiveFactorProduct (coalescedJFactors m) =
    ((coalescedJRootSet m).val.map fun r : ℝ => X - C r).prod at hp
  rw [hp]
  exact coalescedJ_factorization m

end
end PhosphorylationStableCapacity
