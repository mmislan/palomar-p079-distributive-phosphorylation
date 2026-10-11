module
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import proofs.PhosphorylationSharpness.PublicationAlgebra

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
open scoped BigOperators

/-- Turning off the final current leaves precisely one zero factor. -/
theorem slow_link_charpoly {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin 1) (Fin m) ℝ) :
    (Matrix.fromBlocks A 0 C (0 : Matrix (Fin 1) (Fin 1) ℝ)).charpoly =
      A.charpoly * Polynomial.X := by
  simp [Matrix.charpoly_fromBlocks_zero₁₂, Matrix.charpoly_zero]

/-- The positive-vector certificate reduces exactly to the scalar feedback gain. -/
theorem feedback_vector {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ)
    (f z : Fin m → ℝ) (h : ∀ i, ∑ j, H i j*z j=1) (i : Fin m) :
    (∑ j, (-H i j+f j)*z j) = -1+∑ j, f j*z j := by
  simp_rw [add_mul, neg_mul]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, h]

/-- The inherited arbitrary-pair identity also gives exact high contact. -/
theorem coalesced_identity (m : ℕ) (x : ℝ) :
    (x-1)*(prescribedPair 3 (List.replicate m (3,3))).1.eval (ratio x) -
      2*(prescribedPair 3 (List.replicate m (3,3))).2.eval (ratio x) =
      (x-3)^(2*m+1) := by
  rw [prescribedPair_identity]
  simp only [List.map_replicate, List.prod_replicate]
  rw [← pow_two, ← pow_mul, pow_succ]
  ring

/-- The source-preserving relaxation changes no complex-balance equation. -/
theorem relaxation_balance (a b c s e z ε : ℝ) (hε : ε ≠ 0)
    (h : a*s*e=(b+c)*z) :
    (a/ε)*s*e=(((b+c)/ε-c)+c)*z := by
  field_simp
  nlinarith [h]

theorem relaxation_positive (b c ε : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hε : 0 < ε) (hε1 : ε ≤ 1) : 0 < (b+c)/ε-c := by
  have h : c*ε ≤ c := by nlinarith
  have hdiv : c < (b+c)/ε := (lt_div_iff₀ hε).2 (by linarith)
  linarith

/-- A coefficient-ratio step used for the rank-one feedback sign. -/
theorem feedback_ratio_step (a b p q v : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hp : 0 < p) (hpq : p ≤ q)
    (hv : 0 < v) :
    (10*a+(2+v))*p < (10*b+(2+v))*q := by
  have h1 : 0 < 10*b+(2+v) := by linarith
  have h2 : (10*b+(2+v))*p ≤ (10*b+(2+v))*q :=
    mul_le_mul_of_nonneg_left hpq (le_of_lt h1)
  have h3 : (10*a+(2+v))*p < (10*b+(2+v))*p :=
    mul_lt_mul_of_pos_right (by linarith) hp
  exact lt_of_lt_of_le h3 h2

/-- Exact Schur-elimination identity in the loaded large-r limit. -/
theorem loaded_feedback_elimination (v T U a b : ℝ)
    (htotal : (3*T/2+U)+(7-3*v)*a/2+3*v*b/2=0)
    (hlast : (4-v)*b=T+(1-v)*a) :
    2*(7-4*v)*(2*b-a)=10*T+(2+v)*U := by
  linear_combination -(2+v)*htotal + ((14-3*v)/2)*hlast

/-- Closed form of the feedback gain after inserting the coalesced moments. -/
theorem feedback_gain_identity (n v : ℝ) (hv : 14-8*v ≠ 0) :
    1-(10*((4:ℝ)/3-v*(n-(4*n-3)/9))+(2+v)/3)/(14-8*v) =
      v*(50*n-45)/(9*(14-8*v)) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num : (9:ℝ) ≠ 0) hv)).2
  have hc := div_mul_cancel₀
    (10*((4:ℝ)/3-v*(n-(4*n-3)/9))+(2+v)/3) hv
  linear_combination -9*hc

/-- The decisive all-n gap is strictly positive; no spectral premise is assumed. -/
theorem feedback_gap_positive (n : ℕ) (hn : 2 ≤ n) (v : ℝ)
    (hv : 0 < v) (hv1 : v < 1) :
    0 < v*(50*(n:ℝ)-45)/(9*(14-8*v)) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  apply div_pos
  · exact mul_pos hv (by linarith)
  · nlinarith

theorem feedback_gain_lt_one (n : ℕ) (hn : 2 ≤ n) (v : ℝ)
    (hv : 0 < v) (hv1 : v < 1) :
    (10*((4:ℝ)/3-v*((n:ℝ)-(4*(n:ℝ)-3)/9))+(2+v)/3)/(14-8*v) < 1 := by
  have hd : 14-8*v ≠ 0 := by linarith
  have hi := feedback_gain_identity (n:ℝ) v hd
  have hp := feedback_gap_positive n hn v hv hv1
  linarith

end
end PhosphorylationStableCapacity
