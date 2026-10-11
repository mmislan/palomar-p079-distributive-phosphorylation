module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitEvaluation

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- The quantitative splitting law needs a first-order coefficient bound;
coefficientwise differentiability supplies it. -/
def RealCoeffDifferentiable (p : ℝ → ℝ[X]) : Prop :=
  ∀ i : ℕ, Differentiable ℝ fun δ => (p δ).coeff i

private theorem coeffDifferentiable_const (p : ℝ[X]) :
    RealCoeffDifferentiable (fun _ => p) := by
  intro i
  exact differentiable_const _

private theorem coeffDifferentiable_C {g : ℝ → ℝ}
    (hg : Differentiable ℝ g) :
    RealCoeffDifferentiable (fun δ => Polynomial.C (g δ)) := by
  intro i
  cases i with
  | zero => simpa using hg
  | succ i => simp

private theorem coeffDifferentiable_add {p q : ℝ → ℝ[X]}
    (hp : RealCoeffDifferentiable p) (hq : RealCoeffDifferentiable q) :
    RealCoeffDifferentiable (fun δ => p δ + q δ) := by
  intro i
  have heq : (fun δ => (p δ + q δ).coeff i) =
      (fun δ => (p δ).coeff i) + (fun δ => (q δ).coeff i) := by
    funext δ
    simp [Pi.add_apply]
  rw [heq]
  exact (hp i).add (hq i)

private theorem coeffDifferentiable_mul {p q : ℝ → ℝ[X]}
    (hp : RealCoeffDifferentiable p) (hq : RealCoeffDifferentiable q) :
    RealCoeffDifferentiable (fun δ => p δ * q δ) := by
  intro i
  have h : Differentiable ℝ (fun δ : ℝ =>
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal i,
        (p δ).coeff ij.1 * (q δ).coeff ij.2) := by
    apply Differentiable.fun_sum
    intro ij hij
    exact (hp ij.1).mul (hq ij.2)
  simpa only [Polynomial.coeff_mul] using h

theorem arbitrarySplitPair_coeff_differentiable
    (m : ℕ) (ξ : ℕ → ℝ) :
    RealCoeffDifferentiable (fun δ => (arbitrarySplitPair m ξ δ).1) ∧
      RealCoeffDifferentiable (fun δ => (arbitrarySplitPair m ξ δ).2) := by
  induction m with
  | zero =>
      have hroot : Differentiable ℝ (fun δ : ℝ =>
          (offsetSplitRoot ξ δ 0 - 1) / 2) := by
        dsimp [offsetSplitRoot]
        fun_prop
      exact ⟨coeffDifferentiable_const 1,
        coeffDifferentiable_C hroot⟩
  | succ m ih =>
      let a : ℝ → ℝ := fun δ => offsetSplitRoot ξ δ (2*m+1)
      let b : ℝ → ℝ := fun δ => offsetSplitRoot ξ δ (2*m+2)
      have ha : Differentiable ℝ a := by
        dsimp [a, offsetSplitRoot]
        fun_prop
      have hb : Differentiable ℝ b := by
        dsimp [b, offsetSplitRoot]
        fun_prop
      have hab : Differentiable ℝ
          (fun δ => (a δ + 1) * (b δ + 1)) :=
        (ha.add (differentiable_const _)).mul
          (hb.add (differentiable_const _))
      have habm : Differentiable ℝ
          (fun δ => (a δ - 1) * (b δ - 1)) :=
        (ha.sub (differentiable_const _)).mul
          (hb.sub (differentiable_const _))
      have hsum : Differentiable ℝ (fun δ => a δ + b δ) := ha.add hb
      have htwo : Differentiable ℝ (fun δ => 2 * (a δ + b δ)) :=
        (differentiable_const _).mul hsum
      have hfour : Differentiable ℝ (fun δ => 4 * (a δ + b δ)) :=
        (differentiable_const _).mul hsum
      have hp := ih.1
      have hq := ih.2
      constructor
      · change RealCoeffDifferentiable (fun δ =>
          nextN (a δ) (b δ) (arbitrarySplitPair m ξ δ).1
            (arbitrarySplitPair m ξ δ).2)
        simpa only [nextN] using
          coeffDifferentiable_add
            (coeffDifferentiable_add
              (coeffDifferentiable_mul (coeffDifferentiable_C hab) hp)
              (coeffDifferentiable_mul
                (coeffDifferentiable_const (Polynomial.C (8 : ℝ)))
                (coeffDifferentiable_mul
                  (coeffDifferentiable_const Polynomial.X) hp)))
            (coeffDifferentiable_mul (coeffDifferentiable_C htwo) hq)
      · change RealCoeffDifferentiable (fun δ =>
          nextJ (a δ) (b δ) (arbitrarySplitPair m ξ δ).1
            (arbitrarySplitPair m ξ δ).2)
        simpa only [nextJ] using
          coeffDifferentiable_add
            (coeffDifferentiable_add
              (coeffDifferentiable_mul (coeffDifferentiable_C habm) hq)
              (coeffDifferentiable_mul
                (coeffDifferentiable_const (Polynomial.C (8 : ℝ)))
                (coeffDifferentiable_mul
                  (coeffDifferentiable_const Polynomial.X) hq)))
            (coeffDifferentiable_mul (coeffDifferentiable_C hfour)
              (coeffDifferentiable_mul
                (coeffDifferentiable_const Polynomial.X) hp))

theorem arbitrarySplitPair_eval_differentiable
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) :
    Differentiable ℝ (fun δ => (arbitrarySplitPair m ξ δ).1.eval r) ∧
      Differentiable ℝ (fun δ => (arbitrarySplitPair m ξ δ).2.eval r) := by
  have hp := (arbitrarySplitPair_coeff_differentiable m ξ).1
  have hq := (arbitrarySplitPair_coeff_differentiable m ξ).2
  constructor
  · have hsum : Differentiable ℝ (fun δ : ℝ =>
        ∑ i ∈ Finset.range (m+1),
          (arbitrarySplitPair m ξ δ).1.coeff i * r^i) := by
      apply Differentiable.fun_sum
      intro i hi
      exact (hp i).mul (differentiable_const _)
    convert hsum using 1
    funext δ
    exact eval_eq_sum_range'
      (show (arbitrarySplitPair m ξ δ).1.natDegree < m+1 by
        have hle := natDegree_le_iff_coeff_eq_zero.mpr
          (arbitrarySplitPair_coeff_zero_above m ξ δ).1
        omega) r
  · have hsum : Differentiable ℝ (fun δ : ℝ =>
        ∑ i ∈ Finset.range (m+1),
          (arbitrarySplitPair m ξ δ).2.coeff i * r^i) := by
      apply Differentiable.fun_sum
      intro i hi
      exact (hq i).mul (differentiable_const _)
    convert hsum using 1
    funext δ
    exact eval_eq_sum_range'
      (show (arbitrarySplitPair m ξ δ).2.natDegree < m+1 by
        have hle := natDegree_le_iff_coeff_eq_zero.mpr
          (arbitrarySplitPair_coeff_zero_above m ξ δ).2
        omega) r

theorem arbitrarySplitPair_quotient_coeff_differentiable
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    Differentiable ℝ (fun δ =>
      (quotient (arbitrarySplitPair m ξ δ).1
        (arbitrarySplitPair m ξ δ).2 r).coeff i) := by
  induction i with
  | zero =>
      have h := (arbitrarySplitPair_eval_differentiable m ξ r).1.mul
        ((arbitrarySplitPair_coeff_differentiable m ξ).2 0)
      convert h using 1
      funext δ
      exact quotient_zero (arbitrarySplitPair m ξ δ).1
        (arbitrarySplitPair m ξ δ).2 hr
  | succ i ih =>
      have hpEval := (arbitrarySplitPair_eval_differentiable m ξ r).1
      have hqEval := (arbitrarySplitPair_eval_differentiable m ξ r).2
      have hpCoeff := (arbitrarySplitPair_coeff_differentiable m ξ).1 i
      have hqCoeff := (arbitrarySplitPair_coeff_differentiable m ξ).2 (i+1)
      have h := (hpEval.mul hqCoeff).add
        ((ih.sub (hqEval.mul hpCoeff)).div_const r)
      convert h using 1
      funext δ
      exact quotient_succ (arbitrarySplitPair m ξ δ).1
        (arbitrarySplitPair m ξ δ).2 hr i

theorem arbitrarySplitRawD_coeff_differentiable
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    Differentiable ℝ (fun δ =>
      (arbitrarySplitRawD m ξ r δ).coeff i) := by
  have h := (arbitrarySplitPair_quotient_coeff_differentiable
    m ξ r hr i).const_mul 4
  simpa only [arbitrarySplitRawD, rawD, Polynomial.coeff_C_mul] using h

theorem arbitrarySplitRawB_coeff_differentiable
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    Differentiable ℝ (fun δ =>
      (arbitrarySplitRawB m ξ r δ).coeff i) := by
  have hpEval := (arbitrarySplitPair_eval_differentiable m ξ r).1
  have hqEval := (arbitrarySplitPair_eval_differentiable m ξ r).2
  have hpCoeff := (arbitrarySplitPair_coeff_differentiable m ξ).1 i
  have hqCoeff := (arbitrarySplitPair_coeff_differentiable m ξ).2 i
  have hD := arbitrarySplitRawD_coeff_differentiable m ξ r hr i
  have h1 : Differentiable ℝ
      (fun δ => r * (arbitrarySplitRawD m ξ r δ).coeff i) :=
    (differentiable_const _).mul hD
  have hscale : Differentiable ℝ (fun δ =>
      4*r*(arbitrarySplitPair m ξ δ).1.eval r -
        2*(arbitrarySplitPair m ξ δ).2.eval r) :=
    ((differentiable_const _).mul hpEval).sub
      ((differentiable_const _).mul hqEval)
  have h2 : Differentiable ℝ (fun δ =>
      (4*r*(arbitrarySplitPair m ξ δ).1.eval r -
        2*(arbitrarySplitPair m ξ δ).2.eval r) *
          (arbitrarySplitPair m ξ δ).1.coeff i) := hscale.mul hpCoeff
  have h3 : Differentiable ℝ (fun δ =>
      (2*(arbitrarySplitPair m ξ δ).2.eval r) *
        (arbitrarySplitPair m ξ δ).2.coeff i) :=
    ((differentiable_const _).mul hqEval).mul hqCoeff
  have h := (h1.add h2).sub h3
  convert h using 1
  funext δ
  simp only [arbitrarySplitRawB, rawB, Polynomial.coeff_add,
    Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  simp [arbitrarySplitRawD]

end
end PhosphorylationStableCapacity
