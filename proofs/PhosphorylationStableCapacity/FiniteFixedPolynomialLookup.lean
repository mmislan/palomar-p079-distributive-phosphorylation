module
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open Polynomial

/-- An exact finite coefficient table and a proved tail bound determine every
evaluation of a fixed polynomial. This lets grouped printed-state bridges
reuse one coefficient certificate instead of reducing the source recurrence
at every state. -/
theorem polynomial_eval_of_finite_lookup (m : ℕ) (p : ℝ[X])
    (c : Fin (m + 1) → ℝ)
    (htail : ∀ i : ℕ, m < i → p.coeff i = 0)
    (hlookup : ∀ i : Fin (m + 1), p.coeff i.val = c i)
    (x : ℝ) :
    p.eval x = ∑ i : Fin (m + 1), c i * x ^ i.val := by
  have hdegree : p.natDegree < m + 1 :=
    Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr htail)
  calc
    p.eval x = ∑ i ∈ Finset.range (m + 1), p.coeff i * x ^ i :=
      Polynomial.eval_eq_sum_range' hdegree x
    _ = ∑ i : Fin (m + 1), p.coeff i.val * x ^ i.val := by
      exact Finset.sum_range (fun i : ℕ => p.coeff i * x ^ i)
    _ = ∑ i : Fin (m + 1), c i * x ^ i.val := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hlookup i]

/-- The inventory coefficient at the left endpoint is the first D
coefficient. -/
theorem one_add_X_mul_coeff_zero (p : ℝ[X]) :
    ((1 + Polynomial.X) * p).coeff 0 = p.coeff 0 := by
  rw [add_mul, one_mul, Polynomial.coeff_add,
    Polynomial.coeff_X_mul_zero, add_zero]

/-- Every remaining inventory coefficient is the sum of neighboring D
coefficients, so a finite D lookup also controls the state reconstruction. -/
theorem one_add_X_mul_coeff_succ (p : ℝ[X]) (i : ℕ) :
    ((1 + Polynomial.X) * p).coeff (i + 1) =
      p.coeff (i + 1) + p.coeff i := by
  rw [add_mul, one_mul, Polynomial.coeff_add,
    Polynomial.coeff_X_mul]

end
end PhosphorylationStableCapacity
