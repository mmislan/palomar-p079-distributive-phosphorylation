module
public import proofs.PhosphorylationStableCapacity.ExplicitDiagonalLyapunov435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The finite Z-matrix comparison principle for a positive strict
supersolution. -/
theorem positive_path_zmatrix_solution_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (D : Matrix ι ι ℝ) (w x b : ι → ℝ)
    (hoff : ∀ i j, i ≠ j → D i j ≤ 0)
    (hw : ∀ i, 0 < w i)
    (hDw : ∀ i, 0 < ∑ j, D i j * w j)
    (hb : ∀ i, 0 ≤ b i)
    (hsolve : ∀ i, ∑ j, D i j * x j = b i) :
    ∀ i, 0 ≤ x i := by
  by_contra hnot
  push Not at hnot
  let ratio : ι → ℝ := fun i => x i / w i
  obtain ⟨k, _, hkmin⟩ := Finset.exists_min_image Finset.univ ratio
    Finset.univ_nonempty
  obtain ⟨i, hi⟩ := hnot
  have hrneg : ratio k < 0 := by
    have hri : ratio i < 0 := div_neg_of_neg_of_pos hi (hw i)
    exact lt_of_le_of_lt (hkmin i (Finset.mem_univ i)) hri
  have hxk : x k = ratio k * w k := by
    dsimp [ratio]
    field_simp [ne_of_gt (hw k)]
  have hterm : ∀ j, D k j * x j ≤ ratio k * (D k j * w j) := by
    intro j
    by_cases hj : j = k
    · subst j
      rw [hxk]
      ring_nf
      exact le_rfl
    · have hratio : ratio k ≤ ratio j := hkmin j (Finset.mem_univ j)
      have hxj : ratio k * w j ≤ x j := by
        dsimp [ratio] at hratio
        exact (le_div_iff₀ (hw j)).mp hratio
      have hD := hoff k j (Ne.symm hj)
      have hmul := mul_le_mul_of_nonpos_left hxj hD
      nlinarith
  have hsum :
      ∑ j, D k j * x j ≤ ratio k * ∑ j, D k j * w j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hterm j
  have hnegative : ratio k * ∑ j, D k j * w j < 0 :=
    mul_neg_of_neg_of_pos hrneg (hDw k)
  rw [hsolve k] at hsum
  exact (not_lt_of_ge (hb k)) (lt_of_le_of_lt hsum hnegative)

/-- The weighted path matrix is symmetric. -/
theorem pathH_symmetric {m : ℕ} (d : Fin (m+1) → ℝ) :
    ∀ i j, pathH d i j = pathH d j i := by
  have ht : (pathH d).transpose = pathH d := by
    rw [pathH_eq_incidence]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    have hdiag : (Matrix.diagonal fun k : Fin (m+1) => (d k)⁻¹).transpose =
        Matrix.diagonal (fun k : Fin (m+1) => (d k)⁻¹) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij, Ne.symm hij]
    rw [hdiag]
    rw [Matrix.mul_assoc]
  intro i j
  simpa only [Matrix.transpose_apply] using
    congrArg (fun A : Matrix (Fin m) (Fin m) ℝ => A j i) ht

/-- A positive weighted path has an invertible positive-definite matrix.
The proof uses its already established positive Poisson solution. -/
theorem pathH_posDef_of_positive {m : ℕ} (hm : 0 < m)
    (d : Fin (m+1) → ℝ) (hd : ∀ k, 0 < d k) :
    (pathH d).PosDef := by
  obtain ⟨z, hz, hHz⟩ := pathH_positive_solution hm d hd
  have hpos : (-(-(pathH d))).PosDef := by
    refine symmetric_metzler_neg_posDef (-(pathH d)) ?_ ?_ z hz ?_
    · intro i j
      simp only [Matrix.neg_apply]
      exact congrArg Neg.neg (pathH_symmetric d i j)
    · intro i j hij
      exact neg_nonneg.mpr (pathH_offdiag_nonpos d hd i j hij)
    · intro i
      have hHi : (∑ j, pathH d i j * z j) = 1 := by
        simpa [Matrix.mulVec, dotProduct] using hHz i
      simp only [Matrix.neg_apply, neg_mul]
      rw [Finset.sum_neg_distrib]
      rw [hHi]
      norm_num
  simpa using hpos

/-- For a strictly positive forcing, the unique weighted-path Poisson
solution is strictly positive. -/
theorem pathH_inverse_positive_forcing {m : ℕ} (hm : 0 < m)
    (d : Fin (m+1) → ℝ) (hd : ∀ k, 0 < d k)
    (f : Fin m → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ w : Fin m → ℝ,
      w = (pathH d)⁻¹.mulVec f ∧
      (∀ i, 0 < w i) ∧
      (∀ i, ∑ j, pathH d i j * w j = f i) := by
  let H := pathH d
  have hHpos := pathH_posDef_of_positive hm d hd
  have hunit : IsUnit H.det :=
    isUnit_iff_ne_zero.mpr hHpos.det_pos.ne'
  let w : Fin m → ℝ := H⁻¹.mulVec f
  have hsolve : ∀ i, ∑ j, H i j * w j = f i := by
    intro i
    have hvec : H.mulVec w = f := by
      dsimp [w]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H hunit,
        Matrix.one_mulVec]
    exact congrFun hvec i
  obtain ⟨z, hz, hHz⟩ := pathH_positive_solution hm d hd
  have hHzsum : ∀ i, (∑ j, H i j * z j) = 1 := by
    intro i
    simpa [H, Matrix.mulVec, dotProduct] using hHz i
  have hFinNonempty : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  obtain ⟨k, _, hkmin⟩ := Finset.exists_min_image Finset.univ f
    hFinNonempty
  let c := f k
  have hc : 0 < c := hf k
  have hbelow : ∀ i, c ≤ f i :=
    fun i => hkmin i (Finset.mem_univ i)
  let y : Fin m → ℝ := fun i => w i - c * z i
  have hySolve : ∀ i, ∑ j, H i j * y j = f i - c := by
    intro i
    dsimp [y]
    simp only [mul_sub, Finset.sum_sub_distrib]
    have hfactor : (∑ j, H i j * (c * z j)) =
        c * (∑ j, H i j * z j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hfactor, hsolve i, hHzsum i]
    ring
  have hyNonneg : ∀ i, 0 ≤ y i :=
    @positive_path_zmatrix_solution_nonneg (Fin m) _ _
      ⟨⟨0, hm⟩⟩ H z y (fun i => f i - c)
      (fun i j hij => pathH_offdiag_nonpos d hd i j hij)
      hz (fun i => by rw [hHzsum i]; norm_num)
      (fun i => sub_nonneg.mpr (hbelow i)) hySolve
  refine ⟨w, rfl, ?_, ?_⟩
  · intro i
    have hy := hyNonneg i
    dsimp [y] at hy
    nlinarith [mul_pos hc (hz i)]
  · exact hsolve

end

end PhosphorylationStableCapacity
