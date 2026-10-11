module
public import proofs.PhosphorylationStableCapacity.SplitFirstOrderBound

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial

/-- A uniform first-order estimate on finitely many characteristic
coefficients gives a uniform rectangular estimate for the polynomial
secant around its neutral root. This is the coefficientwise form needed
for compact independent-current families. -/
theorem constantTermSecant_uniform_rectangular_of_coefficients
    {α : Type*} (K : Set α) (P : α → ℝ → ℝ[X])
    (N : ℕ) (η A M : ℝ) (_hη : 0 < η)
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hdegree : ∀ a ∈ K, ∀ δ : ℝ,
      (constantTermSecant (P a δ)).natDegree < N)
    (hcoeff : ∀ a ∈ K, ∀ δ : ℝ, |δ| ≤ η →
      ∀ k < N,
        |(P a δ).coeff (k+1)-(P a 0).coeff (k+1)| ≤ A*|δ|)
    (hbase : ∀ a ∈ K, ∀ k < N,
      |(P a 0).coeff (k+1)| ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a ∈ K, ∀ δ x : ℝ, |δ| ≤ η → |x| ≤ 1 →
        |(constantTermSecant (P a δ)).eval x -
          (P a 0).derivative.eval 0| ≤ C*(|δ|+|x|) := by
  let C := (N : ℝ)*(A+M)+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro a ha δ x hδ hx
  have hrep (t y : ℝ) :
      (constantTermSecant (P a t)).eval y =
        ∑ k ∈ Finset.range N, (P a t).coeff (k+1)*y^k := by
    rw [Polynomial.eval_eq_sum_range' (hdegree a ha t)]
    simp only [constantTermSecant_coeff]
  have hQ0 : (constantTermSecant (P a 0)).eval 0 =
      (P a 0).derivative.eval 0 :=
    constantTermSecant_eval_zero (P a 0)
  have hxpow (k : ℕ) : |x|^k ≤ 1 :=
    pow_le_one₀ (abs_nonneg x) hx
  have hxpowlin (k : ℕ) : |x^k-(0 : ℝ)^k| ≤ |x| := by
    by_cases hk : k = 0
    · subst k
      norm_num
    · obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      simp only [pow_succ, zero_pow (by omega : q+1 ≠ 0), sub_zero,
        abs_mul, abs_pow]
      have hq := hxpow q
      nlinarith [mul_le_mul_of_nonneg_right hq (abs_nonneg x)]
  have hdelta :
      |(constantTermSecant (P a δ)).eval x -
        (constantTermSecant (P a 0)).eval x| ≤
          (N : ℝ)*A*|δ| := by
    rw [hrep δ x, hrep 0 x]
    have hsum :
        (∑ k ∈ Finset.range N, (P a δ).coeff (k+1)*x^k) -
          (∑ k ∈ Finset.range N, (P a 0).coeff (k+1)*x^k) =
        ∑ k ∈ Finset.range N,
          ((P a δ).coeff (k+1)-(P a 0).coeff (k+1))*x^k := by
      simp [← Finset.sum_sub_distrib, sub_mul]
    rw [hsum]
    calc
      _ ≤ ∑ k ∈ Finset.range N,
          |((P a δ).coeff (k+1)-(P a 0).coeff (k+1))*x^k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range N, A*|δ| := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul, abs_pow]
        calc
          _ ≤ (A*|δ|)*|x|^k :=
            mul_le_mul_of_nonneg_right
              (hcoeff a ha δ hδ k (Finset.mem_range.mp hk))
              (pow_nonneg (abs_nonneg x) k)
          _ ≤ A*|δ| :=
            mul_le_of_le_one_right (by positivity) (hxpow k)
      _ = (N : ℝ)*A*|δ| := by simp [mul_assoc]
  have hspatial :
      |(constantTermSecant (P a 0)).eval x -
        (constantTermSecant (P a 0)).eval 0| ≤
          (N : ℝ)*M*|x| := by
    rw [hrep 0 x, hrep 0 0]
    have hsum :
        (∑ k ∈ Finset.range N, (P a 0).coeff (k+1)*x^k) -
          (∑ k ∈ Finset.range N, (P a 0).coeff (k+1)*(0 : ℝ)^k) =
        ∑ k ∈ Finset.range N,
          (P a 0).coeff (k+1)*(x^k-(0 : ℝ)^k) := by
      simp [← Finset.sum_sub_distrib, mul_sub]
    rw [hsum]
    calc
      _ ≤ ∑ k ∈ Finset.range N,
          |(P a 0).coeff (k+1)*(x^k-(0 : ℝ)^k)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range N, M*|x| := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        exact mul_le_mul (hbase a ha k (Finset.mem_range.mp hk))
          (hxpowlin k) (abs_nonneg _) hM
      _ = (N : ℝ)*M*|x| := by simp [mul_assoc]
  rw [← hQ0]
  have htri :
      |(constantTermSecant (P a δ)).eval x -
        (constantTermSecant (P a 0)).eval 0| ≤
        |(constantTermSecant (P a δ)).eval x -
          (constantTermSecant (P a 0)).eval x| +
        |(constantTermSecant (P a 0)).eval x -
          (constantTermSecant (P a 0)).eval 0| := by
    calc
      _ = |((constantTermSecant (P a δ)).eval x -
          (constantTermSecant (P a 0)).eval x) +
          ((constantTermSecant (P a 0)).eval x -
          (constantTermSecant (P a 0)).eval 0)| := by
        congr 1
        ring
      _ ≤ _ := abs_add_le _ _
  have hnon : 0 ≤ |δ|+|x| := by positivity
  have hcrossA : 0 ≤ (N : ℝ)*A*|x| := by positivity
  have hcrossM : 0 ≤ (N : ℝ)*M*|δ| := by positivity
  dsimp [C]
  nlinarith [htri, hdelta, hspatial, hnon, hcrossA, hcrossM]

end

end PhosphorylationStableCapacity
