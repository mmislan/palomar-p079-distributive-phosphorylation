module
public import proofs.PhosphorylationStableCapacity.MatrixCharpolyDifferentiability
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix Polynomial
open scoped Matrix.Norms.Elementwise

/-- Each characteristic-polynomial coefficient is a smooth polynomial
in the finitely many real matrix entries. -/
theorem contDiff_matrix_charpoly_coeff
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    ContDiff ℝ 1
      (fun A : Matrix ι ι ℝ => A.charpoly.coeff k) := by
  have hdet (s : Finset ι)
      (J : Matrix ι ι ℝ → Matrix s s ℝ)
      (hentry : ∀ i j,
        ContDiff ℝ 1 (fun A : Matrix ι ι ℝ => J A i j)) :
      ContDiff ℝ 1 (fun A : Matrix ι ι ℝ => (J A).det) := by
    simp_rw [Matrix.det_apply']
    apply ContDiff.sum
    intro σ hσ
    exact (contDiff_const.mul
      (contDiff_prod fun i hi => hentry (σ i) i))
  by_cases hk : k ≤ Fintype.card ι
  · have hminor (s : Finset ι) : ContDiff ℝ 1
        (fun A : Matrix ι ι ℝ =>
          (A.submatrix (Subtype.val : s → ι)
            (Subtype.val : s → ι)).det) := by
      apply hdet s
      intro i j
      change ContDiff ℝ 1 (fun A : Matrix ι ι ℝ => A i.val j.val)
      fun_prop
    have hsum : ContDiff ℝ 1 (fun A : Matrix ι ι ℝ =>
        (-1 : ℝ)^(Fintype.card ι-k) *
          ∑ s ∈ Finset.univ.powersetCard (Fintype.card ι-k),
            (A.submatrix (Subtype.val : s → ι)
              (Subtype.val : s → ι)).det) := by
      apply ContDiff.mul contDiff_const
      apply ContDiff.sum
      intro s hs
      exact hminor s
    convert hsum using 1
    funext A
    simpa [Nat.sub_sub_self hk] using
      (Matrix.charpoly_coeff_eq_sum_minors A
        (Fintype.card ι-k) (Nat.sub_le _ _))
  · have hzero (A : Matrix ι ι ℝ) : A.charpoly.coeff k = 0 := by
      have hdegree := A.charpoly_natDegree_eq_dim
      exact coeff_eq_zero_of_natDegree_lt (by omega)
    simp_rw [hzero]
    exact contDiff_const

/-- On any closed finite-dimensional matrix ball, one constant gives
a Lipschitz estimate for a chosen characteristic coefficient. -/
theorem matrix_charpoly_coeff_lipschitzOn_closedBall
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (R : ℝ) :
    ∃ C : NNReal,
      LipschitzOnWith C
        (fun A : Matrix ι ι ℝ => A.charpoly.coeff k)
        (Metric.closedBall (0 : Matrix ι ι ℝ) R) := by
  exact (contDiff_matrix_charpoly_coeff (ι := ι) k).contDiffOn
    |>.exists_lipschitzOnWith (by norm_num)
      (convex_closedBall (0 : Matrix ι ι ℝ) R)
      (isCompact_closedBall (0 : Matrix ι ι ℝ) R)

end

end PhosphorylationStableCapacity
