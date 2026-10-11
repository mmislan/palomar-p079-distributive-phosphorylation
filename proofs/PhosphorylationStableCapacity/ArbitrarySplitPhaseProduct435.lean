module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitPhase435
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial PhosphorylationSharpness Finset
open scoped BigOperators

/-- Conjugate unit phase, expressed using real trigonometric functions. -/
def arbitraryPhaseUnit (θ : ℝ) : ℂ :=
  (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I

theorem arbitraryPhaseUnit_add (a b : ℝ) :
    arbitraryPhaseUnit (a+b) = arbitraryPhaseUnit a * arbitraryPhaseUnit b := by
  apply Complex.ext <;>
    simp [arbitraryPhaseUnit, Real.cos_add, Real.sin_add,
      Complex.mul_re, Complex.mul_im]

theorem arbitraryPhaseUnit_sum {ι : Type*} (s : Finset ι) (θ : ι → ℝ) :
    arbitraryPhaseUnit (∑ i ∈ s, θ i) = ∏ i ∈ s, arbitraryPhaseUnit (θ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [arbitraryPhaseUnit]
  | @insert a s ha ih =>
      rw [sum_insert ha, prod_insert ha, arbitraryPhaseUnit_add, ih]

/-- A positive amplitude for the linear factor. This avoids choosing complex
arguments or square roots; it equals the ordinary Euclidean amplitude. -/
def arbitraryPhaseAmplitude (x y : ℝ) : ℝ :=
  x / Real.cos (Real.arctan (y/x))

theorem arbitraryPhaseAmplitude_pos {x : ℝ} (hx : 0 < x) (y : ℝ) :
    0 < arbitraryPhaseAmplitude x y :=
  div_pos hx (Real.cos_arctan_pos _)

theorem arbitraryPhase_linear_factor {x : ℝ} (hx : 0 < x) (y : ℝ) :
    (y : ℂ)*Complex.I - x =
      -(arbitraryPhaseAmplitude x y : ℂ) *
        arbitraryPhaseUnit (Real.arctan (y/x)) := by
  have hc := Real.cos_arctan_pos (y/x)
  have ht := Real.tan_arctan (y/x)
  rw [Real.tan_eq_sin_div_cos] at ht
  field_simp [hx.ne', hc.ne'] at ht
  apply Complex.ext <;>
    simp [-Complex.ofReal_cos, -Complex.ofReal_sin, arbitraryPhaseUnit,
      Complex.mul_re, Complex.mul_im]
  · unfold arbitraryPhaseAmplitude
    field_simp [hc.ne']
  · unfold arbitraryPhaseAmplitude
    field_simp [hc.ne']
    nlinarith [ht]

def arbitrarySplitProductAmplitude (m : ℕ) (ξ : ℕ → ℝ) (δ y : ℝ) : ℝ :=
  ∏ j ∈ range (2*m+1), arbitraryPhaseAmplitude (offsetSplitRoot ξ δ j) y

theorem arbitrarySplitProductAmplitude_pos
    (m : ℕ) (ξ : ℕ → ℝ) (δ y : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 0 < offsetSplitRoot ξ δ j) :
    0 < arbitrarySplitProductAmplitude m ξ δ y := by
  apply Finset.prod_pos
  intro j hj
  exact arbitraryPhaseAmplitude_pos
    (hroot j (by have := Finset.mem_range.mp hj; omega)) y

/-- Literal polar product identity for arbitrary positive prescribed roots,
including arbitrary repetitions. -/
theorem arbitrarySplitProduct_imaginary_phase
    (m : ℕ) (ξ : ℕ → ℝ) (δ y : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 0 < offsetSplitRoot ξ δ j) :
    (∏ j ∈ range (2*m+1), ((y : ℂ)*Complex.I - offsetSplitRoot ξ δ j)) =
      -(arbitrarySplitProductAmplitude m ξ δ y : ℂ) *
        arbitraryPhaseUnit (arbitrarySplitPhase m ξ δ y) := by
  have hf (j : ℕ) (hj : j ∈ range (2*m+1)) :=
    arbitraryPhase_linear_factor
      (hroot j (by have := Finset.mem_range.mp hj; omega)) y
  have hprod :
      (∏ j ∈ range (2*m+1), ((y : ℂ)*Complex.I - offsetSplitRoot ξ δ j)) =
        ∏ j ∈ range (2*m+1),
          ((-1 : ℂ)*(arbitraryPhaseAmplitude (offsetSplitRoot ξ δ j) y : ℂ)) *
            arbitraryPhaseUnit (Real.arctan (y / offsetSplitRoot ξ δ j)) := by
    apply Finset.prod_congr rfl
    intro j hj
    simpa only [neg_one_mul] using hf j hj
  rw [hprod]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rw [← arbitraryPhaseUnit_sum]
  have hodd : (-1 : ℂ) ^ (2*m+1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  simp only [Finset.prod_const, Finset.card_range, hodd]
  simp [arbitrarySplitProductAmplitude, arbitrarySplitPhase,
    Complex.ofReal_prod]

/-- The real prescribed-root identity as an actual polynomial identity, so
evaluation at nonreal points is justified by algebra. -/
theorem arbitrarySplitPair_polynomial_identity (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ) :
    (X-1) * (arbitrarySplitPair m ξ δ).1.comp (C (1/8 : ℝ)*(X^2-1)) -
      C 2 * (arbitrarySplitPair m ξ δ).2.comp (C (1/8 : ℝ)*(X^2-1)) =
        ∏ j ∈ range (2*m+1), (X-C (offsetSplitRoot ξ δ j)) := by
  apply Polynomial.funext
  intro x
  have hid := arbitrarySplitPair_scalar_identity m ξ δ x
  rw [arbitrarySplitScalarProduct_eq_prod_range] at hid
  simpa [Polynomial.eval_comp, Polynomial.eval_prod, ratio, div_eq_mul_inv, mul_comm] using hid

/-- The two real components of the actual imaginary-axis product evaluation.
They state the trigonometric identities without division by y. -/
theorem arbitrarySplitPair_imaginary_phase_components
    (m : ℕ) (ξ : ℕ → ℝ) (δ y : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 0 < offsetSplitRoot ξ δ j) :
    y * (arbitrarySplitPair m ξ δ).1.eval (-(1+y^2)/8) =
        arbitrarySplitProductAmplitude m ξ δ y *
          Real.sin (arbitrarySplitPhase m ξ δ y) ∧
      (arbitrarySplitPair m ξ δ).1.eval (-(1+y^2)/8) +
        2 * (arbitrarySplitPair m ξ δ).2.eval (-(1+y^2)/8) =
        arbitrarySplitProductAmplitude m ξ δ y *
          Real.cos (arbitrarySplitPhase m ξ δ y) := by
  let z : ℂ := (y : ℂ)*Complex.I
  let u : ℝ := -(1+y^2)/8
  have hu : (C (1/8 : ℝ)*(X^2-1) : ℝ[X]).eval₂ Complex.ofRealHom z = (u : ℂ) := by
    apply Complex.ext <;>
      simp [z, u, pow_two, Complex.mul_re, Complex.mul_im]
    ring
  have hid := congrArg (fun p : ℝ[X] => p.eval₂ Complex.ofRealHom z)
    (arbitrarySplitPair_polynomial_identity m ξ δ)
  have hp : ((arbitrarySplitPair m ξ δ).1.comp (C (1/8 : ℝ)*(X^2-1))).eval₂
      Complex.ofRealHom z = (↑((arbitrarySplitPair m ξ δ).1.eval u) : ℂ) := by
    rw [eval₂_comp, hu]
    exact eval₂_at_apply Complex.ofRealHom u
  have hq : ((arbitrarySplitPair m ξ δ).2.comp (C (1/8 : ℝ)*(X^2-1))).eval₂
      Complex.ofRealHom z = (↑((arbitrarySplitPair m ξ δ).2.eval u) : ℂ) := by
    rw [eval₂_comp, hu]
    exact eval₂_at_apply Complex.ofRealHom u
  simp only [eval₂_sub, eval₂_mul, hp, hq, eval₂_X, eval₂_one,
    eval₂_C, eval₂_finsetProd, Complex.ofRealHom_eq_coe, Complex.ofReal_ofNat] at hid
  have hprod := arbitrarySplitProduct_imaginary_phase m ξ δ y hroot
  change (z-1)*(↑((arbitrarySplitPair m ξ δ).1.eval u) : ℂ) -
      2*(↑((arbitrarySplitPair m ξ δ).2.eval u) : ℂ) =
        (∏ j ∈ range (2*m+1), (z-(offsetSplitRoot ξ δ j : ℂ))) at hid
  rw [show (∏ j ∈ range (2*m+1), (z-(offsetSplitRoot ξ δ j : ℂ))) =
      -(arbitrarySplitProductAmplitude m ξ δ y : ℂ) *
        arbitraryPhaseUnit (arbitrarySplitPhase m ξ δ y) from hprod] at hid
  have hi := congrArg Complex.im hid
  have hr := congrArg Complex.re hid
  simp [-Complex.ofReal_cos, -Complex.ofReal_sin, z, arbitraryPhaseUnit,
    Complex.mul_re, Complex.mul_im] at hi hr
  constructor
  · simpa [u] using hi
  · dsimp [u] at hr
    linarith

theorem arbitrarySplitPhaseNRoot_isRoot_and_J_alternating
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 0 < offsetSplitRoot ξ δ j)
    (j : Fin m) :
    (arbitrarySplitPair m ξ δ).1.eval (arbitrarySplitPhaseNRoot m ξ δ hroot j) = 0 ∧
      (-1 : ℝ) ^ (j.val+1) *
        (arbitrarySplitPair m ξ δ).2.eval (arbitrarySplitPhaseNRoot m ξ δ hroot j) > 0 := by
  let y := arbitrarySplitPhaseAbscissa m ξ δ hroot j
  have hy := arbitrarySplitPhaseAbscissa_spec m ξ δ hroot j
  have hid := arbitrarySplitPair_imaginary_phase_components m ξ δ y hroot
  rw [show arbitrarySplitPhase m ξ δ y = ((j.val+1 : ℕ) : ℝ)*Real.pi from hy.2,
    Real.sin_nat_mul_pi, Real.cos_nat_mul_pi] at hid
  have hN : (arbitrarySplitPair m ξ δ).1.eval (-(1+y^2)/8) = 0 := by
    exact (mul_eq_zero.mp (by simpa using hid.1)).resolve_left (ne_of_gt hy.1)
  have hrho := arbitrarySplitProductAmplitude_pos m ξ δ y hroot
  have hsignsq : ((-1 : ℝ)^(j.val+1))^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [hN, zero_add] at hid
  have hmul := congrArg (fun a : ℝ => (-1 : ℝ)^(j.val+1)*a) hid.2
  have hweighted : 2*((-1 : ℝ)^(j.val+1)*
      (arbitrarySplitPair m ξ δ).2.eval (-(1+y^2)/8)) =
        arbitrarySplitProductAmplitude m ξ δ y := by
    calc
      _ = (-1 : ℝ)^(j.val+1)*(2*(arbitrarySplitPair m ξ δ).2.eval (-(1+y^2)/8)) := by ring
      _ = (-1 : ℝ)^(j.val+1)*(arbitrarySplitProductAmplitude m ξ δ y * (-1 : ℝ)^(j.val+1)) := hmul
      _ = arbitrarySplitProductAmplitude m ξ δ y * ((-1 : ℝ)^(j.val+1))^2 := by ring
      _ = _ := by rw [hsignsq, mul_one]
  constructor
  · exact hN
  · change 0 < (-1 : ℝ)^(j.val+1)*
      (arbitrarySplitPair m ξ δ).2.eval (-(1+y^2)/8)
    linarith

end
end PhosphorylationStableCapacity
