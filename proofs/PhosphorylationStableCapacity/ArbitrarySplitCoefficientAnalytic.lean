module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitEvaluation
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

def RealCoeffAnalyticAt (p : ℝ → ℝ[X]) : Prop :=
  ∀ i : ℕ, AnalyticAt ℝ (fun δ => (p δ).coeff i) 0

private theorem coeffAnalytic_const (p : ℝ[X]) :
    RealCoeffAnalyticAt (fun _ => p) := by
  intro i
  exact analyticAt_const

private theorem coeffAnalytic_C {g : ℝ → ℝ}
    (hg : AnalyticAt ℝ g 0) :
    RealCoeffAnalyticAt (fun δ => Polynomial.C (g δ)) := by
  intro i
  cases i with
  | zero => simpa using hg
  | succ i =>
      simpa using (analyticAt_const :
        AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) 0)

private theorem coeffAnalytic_add {p q : ℝ → ℝ[X]}
    (hp : RealCoeffAnalyticAt p) (hq : RealCoeffAnalyticAt q) :
    RealCoeffAnalyticAt (fun δ => p δ + q δ) := by
  intro i
  have heq : (fun δ => (p δ + q δ).coeff i) =
      (fun δ => (p δ).coeff i) + (fun δ => (q δ).coeff i) := by
    funext δ
    simp [Pi.add_apply]
  rw [heq]
  exact (hp i).add (hq i)

private theorem coeffAnalytic_mul {p q : ℝ → ℝ[X]}
    (hp : RealCoeffAnalyticAt p) (hq : RealCoeffAnalyticAt q) :
    RealCoeffAnalyticAt (fun δ => p δ * q δ) := by
  intro i
  have h : AnalyticAt ℝ (fun δ : ℝ =>
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal i,
        (p δ).coeff ij.1 * (q δ).coeff ij.2) 0 := by
    apply Finset.analyticAt_fun_sum
    intro ij _
    exact (hp ij.1).mul (hq ij.2)
  simpa only [Polynomial.coeff_mul] using h

/-- The arbitrary prescribed-root recurrence has analytic coefficients in
the splitting parameter, uniformly at the coalesced point. -/
theorem arbitrarySplitPair_coeff_analyticAt
    (m : ℕ) (ξ : ℕ → ℝ) :
    RealCoeffAnalyticAt (fun δ => (arbitrarySplitPair m ξ δ).1) ∧
      RealCoeffAnalyticAt (fun δ => (arbitrarySplitPair m ξ δ).2) := by
  induction m with
  | zero =>
      have hroot : AnalyticAt ℝ (fun δ : ℝ =>
          (offsetSplitRoot ξ δ 0 - 1) / 2) 0 := by
        dsimp [offsetSplitRoot]
        fun_prop
      exact ⟨coeffAnalytic_const 1, coeffAnalytic_C hroot⟩
  | succ m ih =>
      let a : ℝ → ℝ := fun δ => offsetSplitRoot ξ δ (2*m+1)
      let b : ℝ → ℝ := fun δ => offsetSplitRoot ξ δ (2*m+2)
      have ha : AnalyticAt ℝ a 0 := by
        dsimp [a, offsetSplitRoot]
        fun_prop
      have hb : AnalyticAt ℝ b 0 := by
        dsimp [b, offsetSplitRoot]
        fun_prop
      have hab : AnalyticAt ℝ
          (fun δ => (a δ + 1) * (b δ + 1)) 0 :=
        (ha.add analyticAt_const).mul (hb.add analyticAt_const)
      have habm : AnalyticAt ℝ
          (fun δ => (a δ - 1) * (b δ - 1)) 0 :=
        (ha.sub analyticAt_const).mul (hb.sub analyticAt_const)
      have hsum : AnalyticAt ℝ (fun δ => a δ + b δ) 0 := ha.add hb
      have htwo : AnalyticAt ℝ (fun δ => 2 * (a δ + b δ)) 0 :=
        analyticAt_const.mul hsum
      have hfour : AnalyticAt ℝ (fun δ => 4 * (a δ + b δ)) 0 :=
        analyticAt_const.mul hsum
      have hp := ih.1
      have hq := ih.2
      constructor
      · change RealCoeffAnalyticAt (fun δ =>
          nextN (a δ) (b δ) (arbitrarySplitPair m ξ δ).1
            (arbitrarySplitPair m ξ δ).2)
        simpa only [nextN] using
          coeffAnalytic_add
            (coeffAnalytic_add
              (coeffAnalytic_mul (coeffAnalytic_C hab) hp)
              (coeffAnalytic_mul
                (coeffAnalytic_const (Polynomial.C (8 : ℝ)))
                (coeffAnalytic_mul
                  (coeffAnalytic_const Polynomial.X) hp)))
            (coeffAnalytic_mul (coeffAnalytic_C htwo) hq)
      · change RealCoeffAnalyticAt (fun δ =>
          nextJ (a δ) (b δ) (arbitrarySplitPair m ξ δ).1
            (arbitrarySplitPair m ξ δ).2)
        simpa only [nextJ] using
          coeffAnalytic_add
            (coeffAnalytic_add
              (coeffAnalytic_mul (coeffAnalytic_C habm) hq)
              (coeffAnalytic_mul
                (coeffAnalytic_const (Polynomial.C (8 : ℝ)))
                (coeffAnalytic_mul
                  (coeffAnalytic_const Polynomial.X) hq)))
            (coeffAnalytic_mul (coeffAnalytic_C hfour)
              (coeffAnalytic_mul
                (coeffAnalytic_const Polynomial.X) hp))

theorem arbitrarySplitPair_eval_analyticAt
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) :
    AnalyticAt ℝ (fun δ => (arbitrarySplitPair m ξ δ).1.eval r) 0 ∧
      AnalyticAt ℝ (fun δ => (arbitrarySplitPair m ξ δ).2.eval r) 0 := by
  have hp := (arbitrarySplitPair_coeff_analyticAt m ξ).1
  have hq := (arbitrarySplitPair_coeff_analyticAt m ξ).2
  constructor
  · have hsum : AnalyticAt ℝ (fun δ : ℝ =>
        ∑ i ∈ Finset.range (m+1),
          (arbitrarySplitPair m ξ δ).1.coeff i * r^i) 0 := by
      apply Finset.analyticAt_fun_sum
      intro i _
      exact (hp i).mul analyticAt_const
    convert hsum using 1
    funext δ
    exact eval_eq_sum_range'
      (show (arbitrarySplitPair m ξ δ).1.natDegree < m+1 by
        have hle := natDegree_le_iff_coeff_eq_zero.mpr
          (arbitrarySplitPair_coeff_zero_above m ξ δ).1
        omega) r
  · have hsum : AnalyticAt ℝ (fun δ : ℝ =>
        ∑ i ∈ Finset.range (m+1),
          (arbitrarySplitPair m ξ δ).2.coeff i * r^i) 0 := by
      apply Finset.analyticAt_fun_sum
      intro i _
      exact (hq i).mul analyticAt_const
    convert hsum using 1
    funext δ
    exact eval_eq_sum_range'
      (show (arbitrarySplitPair m ξ δ).2.natDegree < m+1 by
        have hle := natDegree_le_iff_coeff_eq_zero.mpr
          (arbitrarySplitPair_coeff_zero_above m ξ δ).2
        omega) r

theorem arbitrarySplitPair_quotient_coeff_analyticAt
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    AnalyticAt ℝ (fun δ =>
      (quotient (arbitrarySplitPair m ξ δ).1
        (arbitrarySplitPair m ξ δ).2 r).coeff i) 0 := by
  induction i with
  | zero =>
      have h := (arbitrarySplitPair_eval_analyticAt m ξ r).1.mul
        ((arbitrarySplitPair_coeff_analyticAt m ξ).2 0)
      convert h using 1
      funext δ
      exact quotient_zero (arbitrarySplitPair m ξ δ).1
        (arbitrarySplitPair m ξ δ).2 hr
  | succ i ih =>
      have hpEval := (arbitrarySplitPair_eval_analyticAt m ξ r).1
      have hqEval := (arbitrarySplitPair_eval_analyticAt m ξ r).2
      have hpCoeff := (arbitrarySplitPair_coeff_analyticAt m ξ).1 i
      have hqCoeff := (arbitrarySplitPair_coeff_analyticAt m ξ).2 (i+1)
      have h := (hpEval.mul hqCoeff).add
        ((ih.sub (hqEval.mul hpCoeff)).div analyticAt_const hr)
      convert h using 1
      funext δ
      exact quotient_succ (arbitrarySplitPair m ξ δ).1
        (arbitrarySplitPair m ξ δ).2 hr i

theorem arbitrarySplitRawD_coeff_analyticAt
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    AnalyticAt ℝ (fun δ =>
      (arbitrarySplitRawD m ξ r δ).coeff i) 0 := by
  have h : AnalyticAt ℝ (fun δ : ℝ =>
      4 * (quotient (arbitrarySplitPair m ξ δ).1
        (arbitrarySplitPair m ξ δ).2 r).coeff i) 0 :=
    analyticAt_const.mul
      (arbitrarySplitPair_quotient_coeff_analyticAt m ξ r hr i)
  simpa only [arbitrarySplitRawD, rawD, Polynomial.coeff_C_mul] using h

theorem arbitrarySplitRawB_coeff_analyticAt
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    AnalyticAt ℝ (fun δ =>
      (arbitrarySplitRawB m ξ r δ).coeff i) 0 := by
  have hpEval := (arbitrarySplitPair_eval_analyticAt m ξ r).1
  have hqEval := (arbitrarySplitPair_eval_analyticAt m ξ r).2
  have hpCoeff := (arbitrarySplitPair_coeff_analyticAt m ξ).1 i
  have hqCoeff := (arbitrarySplitPair_coeff_analyticAt m ξ).2 i
  have hD := arbitrarySplitRawD_coeff_analyticAt m ξ r hr i
  have h1 : AnalyticAt ℝ
      (fun δ => r * (arbitrarySplitRawD m ξ r δ).coeff i) 0 :=
    analyticAt_const.mul hD
  have hscale : AnalyticAt ℝ (fun δ =>
      4*r*(arbitrarySplitPair m ξ δ).1.eval r -
        2*(arbitrarySplitPair m ξ δ).2.eval r) 0 :=
    (analyticAt_const.mul hpEval).sub
      (analyticAt_const.mul hqEval)
  have h2 : AnalyticAt ℝ (fun δ =>
      (4*r*(arbitrarySplitPair m ξ δ).1.eval r -
        2*(arbitrarySplitPair m ξ δ).2.eval r) *
          (arbitrarySplitPair m ξ δ).1.coeff i) 0 :=
    hscale.mul hpCoeff
  have h3 : AnalyticAt ℝ (fun δ =>
      (2*(arbitrarySplitPair m ξ δ).2.eval r) *
        (arbitrarySplitPair m ξ δ).2.coeff i) 0 :=
    (analyticAt_const.mul hqEval).mul hqCoeff
  have h := (h1.add h2).sub h3
  convert h using 1
  funext δ
  simp only [arbitrarySplitRawB, rawB, Polynomial.coeff_add,
    Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  simp [arbitrarySplitRawD]

end
end PhosphorylationStableCapacity
