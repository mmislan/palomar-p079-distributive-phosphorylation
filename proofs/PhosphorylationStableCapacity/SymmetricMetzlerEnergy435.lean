module
public import proofs.PhosphorylationStableCapacity.P079AnalyticalCorollaries435
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The weighted square estimate for a symmetric Metzler matrix. -/
theorem symmetric_metzler_energy_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : ∀ i j, Q i j = Q j i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ Q i j)
    (z : ι → ℝ) (hz : ∀ i, 0 < z i) (a : ι → ℝ) :
    (∑ i, a i * ∑ j, Q i j * a j) ≤
      ∑ i, ((∑ j, Q i j * z j) / z i) * (a i)^2 := by
  have hpair : ∀ i j,
      2 * Q i j * a i * a j ≤
        Q i j * ((z j / z i) * (a i)^2 +
          (z i / z j) * (a j)^2) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [div_self (ne_of_gt (hz i))]
      nlinarith
    · have hcoef : 0 ≤ Q i j / (z i * z j) :=
        div_nonneg (hoff i j hij) (mul_pos (hz i) (hz j)).le
      have hsquare := mul_nonneg hcoef
        (sq_nonneg (a i * z j - a j * z i))
      have heq :
          Q i j / (z i * z j) * (a i * z j - a j * z i)^2 =
            Q i j * ((z j / z i) * (a i)^2 +
              (z i / z j) * (a j)^2) -
                2 * Q i j * a i * a j := by
        field_simp [ne_of_gt (hz i), ne_of_gt (hz j)]
        ring
      rw [heq] at hsquare
      linarith
  have hsum :
      (∑ i, ∑ j, 2 * Q i j * a i * a j) ≤
        ∑ i, ∑ j, Q i j * ((z j / z i) * (a i)^2 +
          (z i / z j) * (a j)^2) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact hpair i j
  have hswap :
      (∑ i, ∑ j, Q i j * ((z i / z j) * (a j)^2)) =
        ∑ i, ∑ j, Q i j * ((z j / z i) * (a i)^2) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hQ j i]
  have hleft :
      (∑ i, ∑ j, 2 * Q i j * a i * a j) =
        2 * (∑ i, a i * ∑ j, Q i j * a j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hright :
      (∑ i, ∑ j, Q i j * ((z j / z i) * (a i)^2 +
          (z i / z j) * (a j)^2)) =
        2 * (∑ i, ((∑ j, Q i j * z j) / z i) * (a i)^2) := by
    simp_rw [mul_add, Finset.sum_add_distrib, hswap]
    have hfirst :
        (∑ i, ∑ j, Q i j * ((z j / z i) * (a i)^2)) =
          ∑ i, ((∑ j, Q i j * z j) / z i) * (a i)^2 := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        (∑ j, Q i j * ((z j / z i) * (a i)^2)) =
            ∑ j, (Q i j * z j) * ((a i)^2 / z i) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = (∑ j, Q i j * z j) * ((a i)^2 / z i) := by
          rw [Finset.sum_mul]
        _ = ((∑ j, Q i j * z j) / z i) * (a i)^2 := by ring
    rw [hfirst]
    ring
  rw [hleft, hright] at hsum
  linarith

/-- A symmetric Metzler matrix with a positive vector of strictly negative
action has a strictly negative quadratic form. -/
theorem symmetric_metzler_neg_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : ∀ i j, Q i j = Q j i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ Q i j)
    (z : ι → ℝ) (hz : ∀ i, 0 < z i)
    (hcert : ∀ i, (∑ j, Q i j * z j) < 0) :
    (-Q).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, star_trivial]
    exact congrArg Neg.neg (hQ j i)
  · intro a ha
    have henergy := symmetric_metzler_energy_le Q hQ hoff z hz a
    have hcoord : ∃ i, a i ≠ 0 := by
      by_contra h
      push Not at h
      exact ha (funext h)
    obtain ⟨i₀, hi₀⟩ := hcoord
    have hweighted :
        (∑ i, ((∑ j, Q i j * z j) / z i) * (a i)^2) < 0 := by
      have hs :
          (∑ i, ((∑ j, Q i j * z j) / z i) * (a i)^2) <
            ∑ _i : ι, (0 : ℝ) := by
        apply Finset.sum_lt_sum
        · intro i _
          exact mul_nonpos_of_nonpos_of_nonneg
            (div_nonpos_of_nonpos_of_nonneg (hcert i).le (hz i).le)
            (sq_nonneg _)
        · refine ⟨i₀, Finset.mem_univ i₀, ?_⟩
          exact mul_neg_of_neg_of_pos
            (div_neg_of_neg_of_pos (hcert i₀) (hz i₀))
            (sq_pos_of_ne_zero hi₀)
      simpa using hs
    have hnegative : (∑ i, a i * ∑ j, Q i j * a j) < 0 :=
      lt_of_le_of_lt henergy hweighted
    change 0 < ∑ i, a i * ∑ j, (-Q) i j * a j
    have heq : (∑ i, a i * ∑ j, (-Q) i j * a j) =
        -(∑ i, a i * ∑ j, Q i j * a j) := by
      simp [Matrix.neg_apply, Finset.sum_neg_distrib]
    rw [heq]
    exact neg_pos.mpr hnegative

end

end PhosphorylationStableCapacity
