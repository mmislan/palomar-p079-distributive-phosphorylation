module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitPhaseProduct435
public import proofs.PhosphorylationStableCapacity.CoalescedJInterlacingIntervals
public import proofs.PhosphorylationStableCapacity.NegativeRootStrictLogConcavity
public import proofs.PhosphorylationStableCapacity.PositiveFactorPairRatioOrder
public import proofs.PhosphorylationStableCapacity.IndexedFactorProduct
public import Mathlib.Algebra.Polynomial.Eval.Coeff

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial PhosphorylationSharpness
open scoped BigOperators

theorem arbitrarySplit_positive_roots_of_above_one
    {m : ℕ} {ξ : ℕ → ℝ} {δ : ℝ}
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) :
    ∀ j, j ≤ 2*m → 0 < offsetSplitRoot ξ δ j :=
  fun j hj => lt_trans zero_lt_one (hroot j hj)

def arbitrarySplitNRoot (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) (j : Fin m) : ℝ :=
  arbitrarySplitPhaseNRoot m ξ δ (arbitrarySplit_positive_roots_of_above_one hroot) j

theorem arbitrarySplitNRoot_strictAnti (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) :
    StrictAnti (arbitrarySplitNRoot m ξ δ hroot) :=
  arbitrarySplitPhaseNRoot_strictAnti m ξ δ _

theorem arbitrarySplitNRoot_neg (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) (j : Fin m) :
    arbitrarySplitNRoot m ξ δ hroot j < 0 := by
  have h := arbitrarySplitPhaseNRoot_lt_neg_one_eighth m ξ δ
    (arbitrarySplit_positive_roots_of_above_one hroot) j
  exact lt_trans h (by norm_num)

theorem arbitrarySplitNRoot_spec (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) (j : Fin m) :
    (arbitrarySplitPair m ξ δ).1.eval (arbitrarySplitNRoot m ξ δ hroot j) = 0 ∧
      0 < (-1 : ℝ)^(j.val+1) *
        (arbitrarySplitPair m ξ δ).2.eval (arbitrarySplitNRoot m ξ δ hroot j) :=
  arbitrarySplitPhaseNRoot_isRoot_and_J_alternating m ξ δ _ j

theorem arbitrarySplitJ_adjacent_opposite (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j)
    (j : ℕ) (hj : j+1 < m) :
    (arbitrarySplitPair m ξ δ).2.eval (arbitrarySplitNRoot m ξ δ hroot ⟨j+1,hj⟩) *
      (arbitrarySplitPair m ξ δ).2.eval (arbitrarySplitNRoot m ξ δ hroot ⟨j,by omega⟩) < 0 := by
  have h1 := (arbitrarySplitNRoot_spec m ξ δ hroot ⟨j,by omega⟩).2
  have h2 := (arbitrarySplitNRoot_spec m ξ δ hroot ⟨j+1,hj⟩).2
  have hpow : (-1 : ℝ)^((j+1)+1) = -((-1 : ℝ)^(j+1)) := by rw [pow_succ]; ring
  rw [hpow] at h2
  by_cases he : Even (j+1)
  · rw [Even.neg_one_pow he] at h1 h2
    nlinarith [mul_neg_of_neg_of_pos (show
      (arbitrarySplitPair m ξ δ).2.eval (arbitrarySplitNRoot m ξ δ hroot ⟨j+1,hj⟩) < 0 by
        nlinarith [h2]) (show 0 <
      (arbitrarySplitPair m ξ δ).2.eval (arbitrarySplitNRoot m ξ δ hroot ⟨j,by omega⟩) by
        simpa using h1)]
  · rw [Odd.neg_one_pow (Nat.not_even_iff_odd.mp he)] at h1 h2
    exact mul_neg_of_pos_of_neg (by nlinarith [h2]) (by nlinarith [h1])

theorem arbitrarySplitJ_zero_between (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j)
    (j : ℕ) (hj : j+1 < m) :
    ∃ x : ℝ, arbitrarySplitNRoot m ξ δ hroot ⟨j+1,hj⟩ < x ∧
      x < arbitrarySplitNRoot m ξ δ hroot ⟨j,by omega⟩ ∧
      (arbitrarySplitPair m ξ δ).2.eval x = 0 :=
  polynomial_zero_between_of_opposite
    (arbitrarySplitNRoot_strictAnti m ξ δ hroot
      (Fin.lt_def.mpr (show j < j+1 from Nat.lt_succ_self j)))
    (arbitrarySplitJ_adjacent_opposite m ξ δ hroot j hj)

theorem arbitrarySplitJ_zero_above_first (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) (hm : 0 < m) :
    ∃ x : ℝ, arbitrarySplitNRoot m ξ δ hroot ⟨0,hm⟩ < x ∧ x < 0 ∧
      (arbitrarySplitPair m ξ δ).2.eval x = 0 := by
  have hsign := (arbitrarySplitNRoot_spec m ξ δ hroot ⟨0,hm⟩).2
  have hneg : (arbitrarySplitPair m ξ δ).2.eval
      (arbitrarySplitNRoot m ξ δ hroot ⟨0,hm⟩) < 0 := by
    norm_num at hsign
    linarith
  have hzero : 0 < (arbitrarySplitPair m ξ δ).2.eval 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact (arbitrarySplitPair_dense m ξ δ hroot).2.1 0 (Nat.zero_le m)
  exact polynomial_zero_between_of_opposite
    (arbitrarySplitNRoot_neg m ξ δ hroot ⟨0,hm⟩) (mul_neg_of_neg_of_pos hneg hzero)

def arbitrarySplitJRoot (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) (j : Fin m) : ℝ :=
  if h : j.val = 0 then
    Classical.choose (arbitrarySplitJ_zero_above_first m ξ δ hroot (by omega))
  else
    Classical.choose (arbitrarySplitJ_zero_between m ξ δ hroot (j.val-1) (by omega))

theorem arbitrarySplitJRoot_bounds (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) (j : Fin m) :
    arbitrarySplitNRoot m ξ δ hroot j < arbitrarySplitJRoot m ξ δ hroot j ∧
      arbitrarySplitJRoot m ξ δ hroot j <
        (if h : j.val = 0 then 0 else arbitrarySplitNRoot m ξ δ hroot ⟨j.val-1,by omega⟩) ∧
      (arbitrarySplitPair m ξ δ).2.eval (arbitrarySplitJRoot m ξ δ hroot j) = 0 := by
  by_cases hj : j.val = 0
  · have hs := Classical.choose_spec (arbitrarySplitJ_zero_above_first m ξ δ hroot (by omega))
    simp only [arbitrarySplitJRoot, hj, ↓reduceDIte]
    have hjfin : j = ⟨0,by omega⟩ := Fin.ext hj
    simpa only [hjfin] using hs
  · have hs := Classical.choose_spec
      (arbitrarySplitJ_zero_between m ξ δ hroot (j.val-1) (by omega))
    simp only [arbitrarySplitJRoot, hj, ↓reduceDIte]
    have hjfin : (⟨j.val-1+1,by omega⟩ : Fin m) = j :=
      Fin.ext (by change j.val-1+1 = j.val; omega)
    simpa only [hjfin] using hs

theorem arbitrarySplitJRoot_neg (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) (j : Fin m) :
    arbitrarySplitJRoot m ξ δ hroot j < 0 := by
  have hu := (arbitrarySplitJRoot_bounds m ξ δ hroot j).2.1
  by_cases hj : j.val = 0
  · simpa only [hj, ↓reduceDIte] using hu
  · simp only [hj, ↓reduceDIte] at hu
    exact lt_trans hu (arbitrarySplitNRoot_neg m ξ δ hroot ⟨j.val-1,by omega⟩)

theorem arbitrarySplitJRoot_strictAnti (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) :
    StrictAnti (arbitrarySplitJRoot m ξ δ hroot) := by
  intro j k hjk
  have hjk' := Fin.lt_def.mp hjk
  have hk0 : k.val ≠ 0 := by omega
  have hku := (arbitrarySplitJRoot_bounds m ξ δ hroot k).2.1
  simp only [hk0, ↓reduceDIte] at hku
  have hjl := (arbitrarySplitJRoot_bounds m ξ δ hroot j).1
  have hindex : j.val ≤ k.val-1 := by omega
  rcases eq_or_lt_of_le hindex with he | hlt
  · have hefin : j = (⟨k.val-1,by omega⟩ : Fin m) := Fin.ext he
    rw [← hefin] at hku
    exact lt_trans hku hjl
  · exact lt_trans hku (lt_trans
      (arbitrarySplitNRoot_strictAnti m ξ δ hroot (Fin.lt_def.mpr hlt)) hjl)

/-- The complete real root multisets are finite sets: every root has
multiplicity one, and the two root lists strictly interlace below zero. -/
theorem arbitrarySplitPair_roots_eq_interlacing_sets
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) :
    (arbitrarySplitPair m ξ δ).1.roots =
        ((Finset.univ : Finset (Fin m)).image (arbitrarySplitNRoot m ξ δ hroot)).val ∧
      (arbitrarySplitPair m ξ δ).2.roots =
        ((Finset.univ : Finset (Fin m)).image (arbitrarySplitJRoot m ξ δ hroot)).val := by
  classical
  have hd := arbitrarySplitPair_dense m ξ δ hroot
  have hNcard : ((Finset.univ : Finset (Fin m)).image
      (arbitrarySplitNRoot m ξ δ hroot)).card = m := by
    rw [Finset.card_image_of_injective _ (arbitrarySplitNRoot_strictAnti m ξ δ hroot).injective]
    simp
  have hJcard : ((Finset.univ : Finset (Fin m)).image
      (arbitrarySplitJRoot m ξ δ hroot)).card = m := by
    rw [Finset.card_image_of_injective _ (arbitrarySplitJRoot_strictAnti m ξ δ hroot).injective]
    simp
  constructor
  · apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨j,_,rfl⟩
      exact (arbitrarySplitNRoot_spec m ξ δ hroot j).1
    · rw [hNcard, hd.1.degree_eq]
    · intro hz
      have hpos := hd.1.1 m le_rfl
      rw [hz, coeff_zero] at hpos
      exact (not_lt_of_ge le_rfl) hpos
  · apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨j,_,rfl⟩
      exact (arbitrarySplitJRoot_bounds m ξ δ hroot j).2.2
    · rw [hJcard, hd.2.degree_eq]
    · intro hz
      have hpos := hd.2.1 m le_rfl
      rw [hz, coeff_zero] at hpos
      exact (not_lt_of_ge le_rfl) hpos

/-- Native form of the paper's complete arbitrary-source interlacing lemma.
The roots of N and J, counted with multiplicity, are exactly the two strict
negative interlacing lists. No distinctness of prescribed roots is required. -/
theorem arbitrarySplitPair_complete_negative_interlacing
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) :
    ∃ ν ζ : Fin m → ℝ,
      StrictAnti ν ∧ StrictAnti ζ ∧
      (∀ j, ν j < ζ j ∧ ζ j < 0) ∧
      (∀ i j, i < j → ζ j < ν i) ∧
      (arbitrarySplitPair m ξ δ).1.roots = ((Finset.univ : Finset (Fin m)).image ν).val ∧
      (arbitrarySplitPair m ξ δ).2.roots = ((Finset.univ : Finset (Fin m)).image ζ).val := by
  classical
  refine ⟨arbitrarySplitNRoot m ξ δ hroot, arbitrarySplitJRoot m ξ δ hroot,
    arbitrarySplitNRoot_strictAnti m ξ δ hroot,
    arbitrarySplitJRoot_strictAnti m ξ δ hroot, ?_, ?_,
    (arbitrarySplitPair_roots_eq_interlacing_sets m ξ δ hroot).1,
    (arbitrarySplitPair_roots_eq_interlacing_sets m ξ δ hroot).2⟩
  · intro j
    exact ⟨(arbitrarySplitJRoot_bounds m ξ δ hroot j).1,
      arbitrarySplitJRoot_neg m ξ δ hroot j⟩
  · intro i j hij
    have hij' := Fin.lt_def.mp hij
    have hj0 : j.val ≠ 0 := by omega
    have hupper := (arbitrarySplitJRoot_bounds m ξ δ hroot j).2.1
    simp only [hj0, ↓reduceDIte] at hupper
    have horder : i ≤ (⟨j.val-1,by omega⟩ : Fin m) :=
      Fin.le_def.mpr (by change i.val ≤ j.val-1; omega)
    exact lt_of_lt_of_le hupper
      ((arbitrarySplitNRoot_strictAnti m ξ δ hroot).antitone horder)

end
end PhosphorylationStableCapacity
