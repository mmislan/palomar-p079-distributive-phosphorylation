module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitInterlacing435
public import proofs.PhosphorylationStableCapacity.InterlacingPositivePartialFractions435
public import proofs.PhosphorylationStableCapacity.CoalescedCoefficientRatioOrder
public import proofs.PhosphorylationStableCapacity.NegativeRootStrictLogConcavity
public import Mathlib.Order.Interval.Set.Monotone

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity
noncomputable section
open Polynomial PhosphorylationSharpness
open scoped BigOperators

def arbitrarySplitNFactorList (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) : List ℝ :=
  (Finset.univ : Finset (Fin m)).val.toList.map fun j => -arbitrarySplitNRoot m ξ δ hroot j

def arbitrarySplitJFactorList (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) : List ℝ :=
  (Finset.univ : Finset (Fin m)).val.toList.map fun j => -arbitrarySplitJRoot m ξ δ hroot j

private theorem indexed_nodal_eq_root_product {m : ℕ} (v : Fin m → ℝ)
    (hinj : Function.Injective v) :
    Lagrange.nodal Finset.univ v =
      (((Finset.univ : Finset (Fin m)).image v).val.map fun r : ℝ => X-C r).prod := by
  classical
  rw [Lagrange.nodal, Finset.prod_eq_multiset_prod, Finset.image_val_of_injOn hinj.injOn]
  simp only [Multiset.map_map, Function.comp_def]

def arbitrarySplit_interlacing_factorization
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) :
    NegativeInterlacingFactorization (arbitrarySplitPair m ξ δ).1
      (arbitrarySplitPair m ξ δ).2 m := by
  classical
  let ν := arbitrarySplitNRoot m ξ δ hroot
  let ζ := arbitrarySplitJRoot m ξ δ hroot
  have hd := arbitrarySplitPair_dense m ξ δ hroot
  have hroots := arbitrarySplitPair_roots_eq_interlacing_sets m ξ δ hroot
  have hcardN : (arbitrarySplitPair m ξ δ).1.roots.card =
      (arbitrarySplitPair m ξ δ).1.natDegree := by
    rw [hroots.1, Finset.card_val, Finset.card_image_of_injective _
      (arbitrarySplitNRoot_strictAnti m ξ δ hroot).injective, hd.1.degree_eq]
    simp
  have hcardJ : (arbitrarySplitPair m ξ δ).2.roots.card =
      (arbitrarySplitPair m ξ δ).2.natDegree := by
    rw [hroots.2, Finset.card_val, Finset.card_image_of_injective _
      (arbitrarySplitJRoot_strictAnti m ξ δ hroot).injective, hd.2.degree_eq]
    simp
  refine {
    numeratorRoots := ν
    denominatorRoots := ζ
    numerator_strictAnti := arbitrarySplitNRoot_strictAnti m ξ δ hroot
    denominator_strictAnti := arbitrarySplitJRoot_strictAnti m ξ δ hroot
    matched_lt := fun i => (arbitrarySplitJRoot_bounds m ξ δ hroot i).1
    cross_lt := ?_
    denominator_neg := arbitrarySplitJRoot_neg m ξ δ hroot
    numerator_leading_pos := ?_
    denominator_leading_pos := ?_
    numerator_factorization := ?_
    denominator_factorization := ?_ }
  · intro i j hij
    have hj0 : j.val ≠ 0 := by have := Fin.lt_def.mp hij; omega
    have hu := (arbitrarySplitJRoot_bounds m ξ δ hroot j).2.1
    simp only [hj0, ↓reduceDIte] at hu
    have hidx : i.val ≤ j.val-1 := by have := Fin.lt_def.mp hij; omega
    rcases eq_or_lt_of_le hidx with he | hlt
    · have hefin : i = (⟨j.val-1,by omega⟩ : Fin m) := Fin.ext he
      simpa only [hefin] using hu
    · exact lt_trans hu (arbitrarySplitNRoot_strictAnti m ξ δ hroot (Fin.lt_def.mpr hlt))
  · rw [Polynomial.leadingCoeff, hd.1.degree_eq]
    exact hd.1.1 m le_rfl
  · rw [Polynomial.leadingCoeff, hd.2.degree_eq]
    exact hd.2.1 m le_rfl
  · have he := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcardN
    rw [hroots.1, ← indexed_nodal_eq_root_product _
      (arbitrarySplitNRoot_strictAnti m ξ δ hroot).injective] at he
    exact he.symm
  · have he := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcardJ
    rw [hroots.2, ← indexed_nodal_eq_root_product _
      (arbitrarySplitJRoot_strictAnti m ξ δ hroot).injective] at he
    exact he.symm

/-- Both actual source ratios have the stated finite partial fractions,
with strictly positive derivative residues. No interlacing assumption is an input. -/
theorem arbitrarySplit_positive_partial_fractions
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) :
    ∃ σ τ : Fin m → ℝ,
      (∀ i, 0 < σ i ∧ 0 < τ i) ∧
      (∀ i, σ i = (arbitrarySplitPair m ξ δ).1.eval (arbitrarySplitJRoot m ξ δ hroot i) /
        (arbitrarySplitPair m ξ δ).2.derivative.eval (arbitrarySplitJRoot m ξ δ hroot i)) ∧
      (∀ i, τ i = -(arbitrarySplitPair m ξ δ).2.eval (arbitrarySplitNRoot m ξ δ hroot i) /
        (arbitrarySplitPair m ξ δ).1.derivative.eval (arbitrarySplitNRoot m ξ δ hroot i)) ∧
      (∀ u, (∀ i, u ≠ arbitrarySplitJRoot m ξ δ hroot i) →
        (arbitrarySplitPair m ξ δ).1.eval u/(arbitrarySplitPair m ξ δ).2.eval u =
          (arbitrarySplitPair m ξ δ).1.leadingCoeff/(arbitrarySplitPair m ξ δ).2.leadingCoeff +
            ∑ i, σ i/(u-arbitrarySplitJRoot m ξ δ hroot i)) ∧
      (∀ u, (∀ i, u ≠ arbitrarySplitNRoot m ξ δ hroot i) →
        (arbitrarySplitPair m ξ δ).2.eval u/(arbitrarySplitPair m ξ δ).1.eval u =
          (arbitrarySplitPair m ξ δ).2.leadingCoeff/(arbitrarySplitPair m ξ δ).1.leadingCoeff -
            ∑ i, τ i/(u-arbitrarySplitNRoot m ξ δ hroot i)) := by
  let h := arbitrarySplit_interlacing_factorization m ξ δ hroot
  refine ⟨h.numeratorResidue, h.denominatorResidue, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact ⟨h.numeratorResidue_pos i, h.denominatorResidue_pos i⟩
  · exact h.numeratorResidue_eq_derivative
  · exact h.denominatorResidue_eq_derivative
  · exact h.numerator_partial_fractions
  · exact h.denominator_partial_fractions

theorem arbitrarySplitJ_coeff_strict_logconcave
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) :
    CoeffStrictLogConcave (arbitrarySplitPair m ξ δ).2 m := by
  classical
  have h := arbitrarySplit_interlacing_factorization m ξ δ hroot
  have hd := (arbitrarySplitPair_dense m ξ δ hroot).2
  have hroots := (arbitrarySplitPair_roots_eq_interlacing_sets m ξ δ hroot).2
  have hcard : (arbitrarySplitPair m ξ δ).2.roots.card =
      (arbitrarySplitPair m ξ δ).2.natDegree := by
    rw [hroots, Finset.card_val, Finset.card_image_of_injective _
      (arbitrarySplitJRoot_strictAnti m ξ δ hroot).injective, hd.degree_eq]
    simp
  have hneg : ∀ r ∈ (arbitrarySplitPair m ξ δ).2.roots, r < 0 := by
    intro r hr
    rw [hroots] at hr
    have hr' : r ∈ (Finset.univ : Finset (Fin m)).image (arbitrarySplitJRoot m ξ δ hroot) := by
      simpa using hr
    rcases Finset.mem_image.mp hr' with ⟨i,_,rfl⟩
    exact arbitrarySplitJRoot_neg m ξ δ hroot i
  simpa only [hd.degree_eq] using
    coeffStrictLogConcave_of_negative_roots hcard hneg h.denominator_leading_pos

def coefficientPreviousRatio (p : ℝ[X]) (i : ℕ) : ℝ :=
  (if i = 0 then 0 else p.coeff (i-1))/p.coeff i

theorem arbitrarySplitJ_coefficientPreviousRatio_adjacent
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j)
    (i : ℕ) (hi : i < m) :
    coefficientPreviousRatio (arbitrarySplitPair m ξ δ).2 i <
      coefficientPreviousRatio (arbitrarySplitPair m ξ δ).2 (i+1) := by
  have hd := (arbitrarySplitPair_dense m ξ δ hroot).2
  by_cases hzero : i = 0
  · subst i
    simpa [coefficientPreviousRatio] using
      div_pos (hd.1 0 (by omega)) (hd.1 1 (by omega))
  · have hpos : 0 < i := by omega
    have hnext : i+1 ≠ 0 := by omega
    simp only [coefficientPreviousRatio, hzero, hnext, ↓reduceIte, Nat.add_sub_cancel]
    apply (div_lt_div_iff₀ (hd.1 i (by omega)) (hd.1 (i+1) (by omega))).mpr
    simpa only [pow_two] using arbitrarySplitJ_coeff_strict_logconcave m ξ δ hroot i hpos hi

theorem arbitrarySplitJ_coefficientPreviousRatio_strictMonoOn
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) :
    StrictMonoOn (coefficientPreviousRatio (arbitrarySplitPair m ξ δ).2) (Set.Iic m) := by
  apply strictMonoOn_Iic_of_lt_succ
  intro i hi
  exact arbitrarySplitJ_coefficientPreviousRatio_adjacent m ξ δ hroot i hi

theorem arbitrarySplitJN_coeff_ratio_mono
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) :
    CoeffRatioMono (arbitrarySplitPair m ξ δ).1 (arbitrarySplitPair m ξ δ).2 m := by
  classical
  let h := arbitrarySplit_interlacing_factorization m ξ δ hroot
  have hNpos : ∀ a ∈ arbitrarySplitNFactorList m ξ δ hroot, 0 < a := by
    intro a ha
    rcases List.mem_map.mp ha with ⟨i,_,rfl⟩
    exact neg_pos.mpr (arbitrarySplitNRoot_neg m ξ δ hroot i)
  have hJpos : ∀ a ∈ arbitrarySplitJFactorList m ξ δ hroot, 0 < a := by
    intro a ha
    rcases List.mem_map.mp ha with ⟨i,_,rfl⟩
    exact neg_pos.mpr (arbitrarySplitJRoot_neg m ξ δ hroot i)
  have hpair : List.Forall₂ (fun a b : ℝ => b ≤ a)
      (arbitrarySplitNFactorList m ξ δ hroot) (arbitrarySplitJFactorList m ξ δ hroot) := by
    have hall : ∀ is : List (Fin m), List.Forall₂ (fun a b : ℝ => b ≤ a)
        (is.map fun i => -arbitrarySplitNRoot m ξ δ hroot i)
        (is.map fun i => -arbitrarySplitJRoot m ξ δ hroot i) := by
      intro is
      induction is with
      | nil => exact .nil
      | cons i is ih => exact .cons (neg_le_neg ((arbitrarySplitJRoot_bounds m ξ δ hroot i).1.le)) ih
    exact hall _
  have hlen : (arbitrarySplitNFactorList m ξ δ hroot).length = m := by
    simp [arbitrarySplitNFactorList]
  have hmono := positiveFactorProduct_ratio_mono _ _ hpair hNpos hJpos
  have hdense := positiveFactorProduct_dense _ hNpos
  rw [hlen] at hmono hdense
  have hscaled := coeffRatioMono_C_mul hdense hmono h.numerator_leading_pos h.denominator_leading_pos
  have hNfac : C (arbitrarySplitPair m ξ δ).1.leadingCoeff *
      positiveFactorProduct (arbitrarySplitNFactorList m ξ δ hroot) = (arbitrarySplitPair m ξ δ).1 := by
    rw [arbitrarySplitNFactorList, positiveFactorProduct_finset _ _
      (arbitrarySplitNRoot_strictAnti m ξ δ hroot).injective.injOn,
      ← indexed_nodal_eq_root_product _ (arbitrarySplitNRoot_strictAnti m ξ δ hroot).injective]
    exact h.numerator_factorization.symm
  have hJfac : C (arbitrarySplitPair m ξ δ).2.leadingCoeff *
      positiveFactorProduct (arbitrarySplitJFactorList m ξ δ hroot) = (arbitrarySplitPair m ξ δ).2 := by
    rw [arbitrarySplitJFactorList, positiveFactorProduct_finset _ _
      (arbitrarySplitJRoot_strictAnti m ξ δ hroot).injective.injOn,
      ← indexed_nodal_eq_root_product _ (arbitrarySplitJRoot_strictAnti m ξ δ hroot).injective]
    exact h.denominator_factorization.symm
  rw [hNfac, hJfac] at hscaled
  exact hscaled

end
end PhosphorylationStableCapacity
