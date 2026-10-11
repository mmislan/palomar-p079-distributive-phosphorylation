module
public import proofs.PhosphorylationStableCapacity.ComplementaryBindingDeterminant
public import Mathlib.Tactic.FinCases

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open Matrix
open scoped BigOperators

def bindingFreeIncidence {ι ℓ : Type*} [DecidableEq ℓ]
    (p q : ι → ℓ) : Matrix (ℓ ⊕ Fin 2) (ι ⊕ ι) ℝ :=
  Matrix.of fun a b => match a, b with
    | Sum.inl j, Sum.inl i => if p i = j then 1 else 0
    | Sum.inl j, Sum.inr i => if q i = j then 1 else 0
    | Sum.inr j, Sum.inl _ => if j = 0 then 1 else 0
    | Sum.inr j, Sum.inr _ => if j = 1 then 1 else 0

def bindingLevelInventory {ι ℓ : Type*} [Fintype ι] [DecidableEq ℓ]
    (p : ι → ℓ) (C : ι → ℝ) (j : ℓ) : ℝ :=
  ∑ i, if p i = j then C i else 0

private theorem weighted_attachment_diagonal
    {ι ℓ : Type*} [Fintype ι] [DecidableEq ℓ]
    (p : ι → ℓ) (C : ι → ℝ) (a b : ℓ) :
    (∑ i, (if p i = a then 1 else 0) * C i *
      (if p i = b then 1 else 0)) =
      if a = b then bindingLevelInventory p C a else 0 := by
  by_cases hab : a = b
  · subst b
    simp only [ite_true, bindingLevelInventory]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : p i = a <;> simp [hi]
  · rw [ite_eq_right hab]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : p i = a
    · simp [hi, hab]
    · simp [hi]

/-- Each binding edge contributes to one free substrate and one enzyme.
Its covariance therefore has diagonal substrate inventory and only the
two explicit enzyme coupling columns. -/
theorem binding_free_covariance_eq_blocks
    {ι ℓ : Type*} [Fintype ι] [Fintype ℓ]
    [DecidableEq ι] [DecidableEq ℓ]
    (p q : ι → ℓ) (S : ℓ → ℝ) (C Y : ι → ℝ) (E F : ℝ) :
    let K := bindingFreeIncidence p q
    let Df := diagonal (Sum.elim S ![E, F])
    let Dc := diagonal (Sum.elim C Y)
    let CL := bindingLevelInventory p C
    let YL := bindingLevelInventory q Y
    let U : Matrix ℓ (Fin 2) ℝ := Matrix.of fun j => ![CL j, YL j]
    Df + K * Dc * K.transpose =
      fromBlocks (diagonal (fun j => S j + CL j + YL j)) U U.transpose
        (diagonal ![E + ∑ i, C i, F + ∑ i, Y i]) := by
  dsimp only
  ext a b
  simp only [Matrix.add_apply]
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal]
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      simp only [diagonal_apply, Fintype.sum_sum_type,
        Matrix.transpose_apply, bindingFreeIncidence, Matrix.of_apply,
        Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, fromBlocks_apply₁₁]
      rw [weighted_attachment_diagonal, weighted_attachment_diagonal]
      by_cases hab : a = b
      · subst b
        simp [add_assoc]
      · simp [hab]
    | inr b =>
      fin_cases b <;>
        simp [bindingFreeIncidence, Fintype.sum_sum_type,
          bindingLevelInventory]
  | inr a =>
    cases b with
    | inl b =>
      fin_cases a <;>
        simp [bindingFreeIncidence, Fintype.sum_sum_type,
          bindingLevelInventory]
    | inr b =>
      fin_cases a <;> fin_cases b <;>
        simp [bindingFreeIncidence, Fintype.sum_sum_type]

/-- Exact affinity determinant in terms of the enzyme-corrected inventory.
The formula is uniform in the number and attachment pattern of complexes. -/
theorem binding_affinity_inventory_determinant
    {ι ℓ : Type*} [Fintype ι] [Fintype ℓ]
    [DecidableEq ι] [DecidableEq ℓ]
    (p q : ι → ℓ) (S : ℓ → ℝ) (C Y : ι → ℝ) (E F : ℝ)
    (hS : ∀ j, S j ≠ 0) (hC : ∀ i, C i ≠ 0) (hY : ∀ i, Y i ≠ 0)
    (hE : E ≠ 0) (hF : F ≠ 0)
    (hET : E + ∑ i, C i ≠ 0) (hFT : F + ∑ i, Y i ≠ 0) :
    let K := bindingFreeIncidence p q
    let Df := diagonal (Sum.elim S ![E, F])
    let Dc := diagonal (Sum.elim C Y)
    let CL := bindingLevelInventory p C
    let YL := bindingLevelInventory q Y
    (Dc⁻¹ + K.transpose * Df⁻¹ * K).det *
        ((∏ j, S j) * E * F) * ((∏ i, C i) * ∏ i, Y i) =
      (E + ∑ i, C i) * (F + ∑ i, Y i) *
        Matrix.det (fun i j =>
          (if i = j then S i + CL i + YL i else 0) -
            CL i * CL j / (E + ∑ a, C a) -
            YL i * YL j / (F + ∑ a, Y a)) := by
  dsimp only
  let K := bindingFreeIncidence p q
  let Df : Matrix (ℓ ⊕ Fin 2) (ℓ ⊕ Fin 2) ℝ :=
    diagonal (Sum.elim S ![E, F])
  let Dc : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ := diagonal (Sum.elim C Y)
  have hdf : Df.det = (∏ j, S j) * E * F := by
    simp [Df, det_diagonal, Fintype.prod_sum_type, Fin.prod_univ_two, mul_assoc]
  have hdc : Dc.det = (∏ i, C i) * ∏ i, Y i := by
    simp [Dc, det_diagonal, Fintype.prod_sum_type]
  have hfunit : IsUnit Df.det := by
    rw [isUnit_iff_ne_zero, hdf]
    exact mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _ => hS j)) hE) hF
  have hcunit : IsUnit Dc.det := by
    rw [isUnit_iff_ne_zero, hdc]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hC i))
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hY i))
  have hmain := complementary_binding_determinant Df Dc K hfunit hcunit
  have hcov := binding_free_covariance_eq_blocks p q S C Y E F
  have hschur := enzyme_corrected_covariance_determinant
    S (bindingLevelInventory p C) (bindingLevelInventory q Y)
    (E + ∑ i, C i) (F + ∑ i, Y i) hET hFT
  rw [hdf, hdc] at hmain
  rw [hmain]
  change (diagonal (Sum.elim S ![E, F]) +
    bindingFreeIncidence p q * diagonal (Sum.elim C Y) *
      (bindingFreeIncidence p q).transpose).det = _
  rw [hcov]
  exact hschur

end
end PhosphorylationStableCapacity
