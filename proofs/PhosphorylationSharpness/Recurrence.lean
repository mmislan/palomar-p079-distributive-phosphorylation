module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega
public import Lean.Elab.Tactic.NormCast

@[expose] public section

namespace PhosphorylationSharpness
noncomputable section
open Polynomial

def DensePositive (p : ℝ[X]) (m : ℕ) : Prop :=
  (∀ i ≤ m, 0 < p.coeff i) ∧ (∀ i, m < i → p.coeff i = 0)

theorem DensePositive.nonneg {p : ℝ[X]} {m : ℕ} (h : DensePositive p m) (i : ℕ) :
    0 ≤ p.coeff i := by
  by_cases hi : i ≤ m
  · exact (h.1 i hi).le
  · rw [h.2 i (by omega)]

theorem dense_constant (c : ℝ) (hc : 0 < c) : DensePositive (C c) 0 := by
  constructor
  · intro i hi
    have : i = 0 := by omega
    subst i
    simpa using hc
  · intro i hi
    simp [coeff_C, show i ≠ 0 by omega]

theorem dense_step {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    DensePositive (C a*p + C b*(X*p) + C c*q + C d*(X*q)) (m+1) := by
  constructor
  · intro i hi
    cases i with
    | zero =>
      simp only [coeff_add, coeff_C_mul, coeff_X_mul_zero, mul_zero, add_zero]
      exact add_pos_of_pos_of_nonneg (mul_pos ha (hp.1 0 (by omega)))
        (mul_nonneg hc (hq.nonneg 0))
    | succ i =>
      simp only [coeff_add, coeff_C_mul, coeff_X_mul]
      have h1 := mul_nonneg ha.le (hp.nonneg (i+1))
      have h2 := mul_pos hb (hp.1 i (by omega))
      have h3 := mul_nonneg hc (hq.nonneg (i+1))
      have h4 := mul_nonneg hd (hq.nonneg i)
      linarith
  · intro i hi
    cases i with
    | zero => omega
    | succ i =>
      simp only [coeff_add, coeff_C_mul, coeff_X_mul]
      rw [hp.2 (i+1) (by omega), hp.2 i (by omega),
        hq.2 (i+1) (by omega), hq.2 i (by omega)]
      ring

def nextN (a b : ℝ) (p q : ℝ[X]) : ℝ[X] :=
  C ((a+1)*(b+1))*p + C 8*(X*p) + C (2*(a+b))*q

def nextJ (a b : ℝ) (p q : ℝ[X]) : ℝ[X] :=
  C ((a-1)*(b-1))*q + C 8*(X*q) + C (4*(a+b))*(X*p)

theorem next_dense {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m)
    {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    DensePositive (nextN a b p q) (m+1) ∧
      DensePositive (nextJ a b p q) (m+1) := by
  constructor
  · simpa [nextN] using dense_step hp hq ((a+1)*(b+1)) 8 (2*(a+b)) 0
      (by positivity) (by norm_num) (by positivity) (by norm_num)
  · simpa [nextJ] using dense_step hq hp ((a-1)*(b-1)) 8 0 (4*(a+b))
      (mul_pos (by linarith) (by linarith)) (by norm_num) (by norm_num) (by positivity)

def ratio (x : ℝ) : ℝ := (x^2-1)/8

theorem next_identity (a b x : ℝ) (p q : ℝ[X]) :
    (x-1)*(nextN a b p q).eval (ratio x) - 2*(nextJ a b p q).eval (ratio x) =
    (x-a)*(x-b)*((x-1)*p.eval (ratio x)-2*q.eval (ratio x)) := by
  simp only [nextN, nextJ, eval_add, eval_mul, eval_C, eval_X]
  dsimp [ratio]
  ring

def pair : ℕ → ℝ[X] × ℝ[X]
  | 0 => (1, C (1/2))
  | m+1 =>
    let pq := pair m
    (nextN (2*m+3) (2*m+4) pq.1 pq.2,
     nextJ (2*m+3) (2*m+4) pq.1 pq.2)

theorem pair_dense (m : ℕ) :
    DensePositive (pair m).1 m ∧ DensePositive (pair m).2 m := by
  induction m with
  | zero =>
    exact ⟨by simpa [pair] using dense_constant 1 (by norm_num),
      by simpa [pair] using dense_constant (1/2) (by norm_num)⟩
  | succ m ih =>
    exact next_dense ih.1 ih.2 (by nlinarith [Nat.cast_nonneg (α := ℝ) m])
      (by nlinarith [Nat.cast_nonneg (α := ℝ) m])

theorem pair_roots (m j : ℕ) (hj : j ≤ 2*m) :
    ((j:ℝ)+2-1)*(pair m).1.eval (ratio ((j:ℝ)+2)) -
      2*(pair m).2.eval (ratio ((j:ℝ)+2)) = 0 := by
  induction m with
  | zero =>
    have : j = 0 := by omega
    subst j
    norm_num [pair]
  | succ m ih =>
    change _*(nextN _ _ _ _).eval _ - 2*(nextJ _ _ _ _).eval _ = 0
    rw [next_identity]
    by_cases h : j ≤ 2*m
    · rw [ih h]
      ring
    · have hcases : j = 2*m+1 ∨ j = 2*m+2 := by omega
      rcases hcases with h | h <;> subst j <;> push_cast <;> ring

theorem ratio_pos {x : ℝ} (hx : 1 < x) : 0 < ratio x := by
  dsimp [ratio]
  nlinarith

theorem ratio_injective {x y : ℝ} (hx : 1 < x) (hy : 1 < y)
    (h : ratio x = ratio y) : x = y := by
  dsimp [ratio] at h
  nlinarith

end
end PhosphorylationSharpness
