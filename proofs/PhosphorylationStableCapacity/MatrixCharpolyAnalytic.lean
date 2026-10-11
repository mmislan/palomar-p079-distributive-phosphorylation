module
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix Polynomial

/-- Finite determinant algebra preserves analyticity of a parameterized
real matrix. -/
theorem matrix_det_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ℝ → Matrix ι ι ℝ)
    (hentry : ∀ i j, AnalyticAt ℝ (fun δ => J δ i j) 0) :
    AnalyticAt ℝ (fun δ => (J δ).det) 0 := by
  simp_rw [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ hσ
  exact analyticAt_const.mul
    (Finset.analyticAt_fun_prod _ fun i hi => hentry (σ i) i)

/-- Every characteristic-polynomial coefficient is analytic whenever all
matrix entries are analytic. -/
theorem matrix_charpoly_coeff_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ℝ → Matrix ι ι ℝ)
    (hentry : ∀ i j, AnalyticAt ℝ (fun δ => J δ i j) 0)
    (k : ℕ) :
    AnalyticAt ℝ (fun δ => (J δ).charpoly.coeff k) 0 := by
  by_cases hk : k ≤ Fintype.card ι
  · have hminor (s : Finset ι) : AnalyticAt ℝ
        (fun δ => ((J δ).submatrix
          (Subtype.val : s → ι) (Subtype.val : s → ι)).det) 0 := by
      apply matrix_det_analyticAt
      intro i j
      exact hentry i.val j.val
    have hsum : AnalyticAt ℝ (fun δ =>
        (-1 : ℝ)^(Fintype.card ι-k) *
          ∑ s ∈ Finset.univ.powersetCard (Fintype.card ι-k),
            ((J δ).submatrix
              (Subtype.val : s → ι) (Subtype.val : s → ι)).det) 0 := by
      exact analyticAt_const.mul
        (Finset.analyticAt_fun_sum _ fun s hs => hminor s)
    convert hsum using 1
    funext δ
    simpa [Nat.sub_sub_self hk] using
      (Matrix.charpoly_coeff_eq_sum_minors (J δ)
        (Fintype.card ι-k) (Nat.sub_le _ _))
  · have hzero (δ : ℝ) : (J δ).charpoly.coeff k = 0 := by
      have hdegree := (J δ).charpoly_natDegree_eq_dim
      exact coeff_eq_zero_of_natDegree_lt (by omega)
    simp_rw [hzero]
    exact analyticAt_const

/-- Bounded-degree polynomial evaluation is analytic jointly in its
parameter and evaluation variable when each coefficient is analytic. -/
theorem boundedPolynomial_eval_joint_analyticAt
    (p : ℝ → ℝ[X]) (N : ℕ)
    (hdegree : ∀ δ, (p δ).natDegree < N)
    (hcoeff : ∀ k, AnalyticAt ℝ (fun δ => (p δ).coeff k) 0) :
    AnalyticAt ℝ (fun q : ℝ × ℝ => (p q.1).eval q.2) (0, 0) := by
  have hsum : AnalyticAt ℝ (fun q : ℝ × ℝ =>
      ∑ k ∈ Finset.range N, (p q.1).coeff k * q.2^k) (0, 0) := by
    apply Finset.analyticAt_fun_sum
    intro k hk
    exact ((hcoeff k).comp (x := (0, 0)) (f := fun q : ℝ × ℝ => q.1)
      analyticAt_fst).mul
      (analyticAt_snd.pow k)
  convert hsum using 1
  funext q
  exact eval_eq_sum_range' (hdegree q.1) q.2

end
end PhosphorylationStableCapacity
