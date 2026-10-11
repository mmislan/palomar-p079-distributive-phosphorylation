module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitReadoutSpacing435

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- Uniform finite polynomial support lets second-order smoothness be
tracked coefficient by coefficient through the split recurrence. -/
def RealCoeffContDiffTwo (p : ℝ → ℝ[X]) : Prop :=
  ∀ i : ℕ, ContDiff ℝ 2 (fun δ => (p δ).coeff i)

private theorem coeffContDiffTwo_const (p : ℝ[X]) :
    RealCoeffContDiffTwo (fun _ => p) := by
  intro i
  exact contDiff_const

private theorem coeffContDiffTwo_C {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) :
    RealCoeffContDiffTwo (fun δ => Polynomial.C (g δ)) := by
  intro i
  cases i with
  | zero => simpa using hg
  | succ i =>
      simpa using (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => (0 : ℝ)))

private theorem coeffContDiffTwo_add {p q : ℝ → ℝ[X]}
    (hp : RealCoeffContDiffTwo p) (hq : RealCoeffContDiffTwo q) :
    RealCoeffContDiffTwo (fun δ => p δ + q δ) := by
  intro i
  have heq : (fun δ => (p δ + q δ).coeff i) =
      (fun δ => (p δ).coeff i) + (fun δ => (q δ).coeff i) := by
    funext δ
    simp [Pi.add_apply]
  rw [heq]
  exact (hp i).add (hq i)

private theorem coeffContDiffTwo_mul {p q : ℝ → ℝ[X]}
    (hp : RealCoeffContDiffTwo p) (hq : RealCoeffContDiffTwo q) :
    RealCoeffContDiffTwo (fun δ => p δ * q δ) := by
  intro i
  have h : ContDiff ℝ 2 (fun δ : ℝ =>
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal i,
        (p δ).coeff ij.1 * (q δ).coeff ij.2) := by
    apply ContDiff.sum
    intro ij hij
    exact (hp ij.1).mul (hq ij.2)
  simpa only [Polynomial.coeff_mul] using h

/-- Every coefficient of the paired split source polynomials is twice
continuously differentiable in the root splitting parameter. -/
theorem arbitrarySplitPair_coeff_contDiff_two
    (m : ℕ) (ξ : ℕ → ℝ) :
    RealCoeffContDiffTwo (fun δ => (arbitrarySplitPair m ξ δ).1) ∧
      RealCoeffContDiffTwo (fun δ => (arbitrarySplitPair m ξ δ).2) := by
  induction m with
  | zero =>
      have hroot : ContDiff ℝ 2 (fun δ : ℝ =>
          (offsetSplitRoot ξ δ 0 - 1) / 2) := by
        dsimp [offsetSplitRoot]
        fun_prop
      exact ⟨coeffContDiffTwo_const 1,
        coeffContDiffTwo_C hroot⟩
  | succ m ih =>
      let a : ℝ → ℝ := fun δ => offsetSplitRoot ξ δ (2*m+1)
      let b : ℝ → ℝ := fun δ => offsetSplitRoot ξ δ (2*m+2)
      have ha : ContDiff ℝ 2 a := by
        dsimp [a, offsetSplitRoot]
        fun_prop
      have hb : ContDiff ℝ 2 b := by
        dsimp [b, offsetSplitRoot]
        fun_prop
      have hab : ContDiff ℝ 2
          (fun δ => (a δ + 1) * (b δ + 1)) :=
        (ha.add contDiff_const).mul (hb.add contDiff_const)
      have habm : ContDiff ℝ 2
          (fun δ => (a δ - 1) * (b δ - 1)) :=
        (ha.sub contDiff_const).mul (hb.sub contDiff_const)
      have hsum : ContDiff ℝ 2 (fun δ => a δ + b δ) := ha.add hb
      have htwo : ContDiff ℝ 2 (fun δ => 2 * (a δ + b δ)) :=
        contDiff_const.mul hsum
      have hfour : ContDiff ℝ 2 (fun δ => 4 * (a δ + b δ)) :=
        contDiff_const.mul hsum
      have hp := ih.1
      have hq := ih.2
      constructor
      · change RealCoeffContDiffTwo (fun δ =>
          nextN (a δ) (b δ) (arbitrarySplitPair m ξ δ).1
            (arbitrarySplitPair m ξ δ).2)
        simpa only [nextN] using
          coeffContDiffTwo_add
            (coeffContDiffTwo_add
              (coeffContDiffTwo_mul (coeffContDiffTwo_C hab) hp)
              (coeffContDiffTwo_mul
                (coeffContDiffTwo_const (Polynomial.C (8 : ℝ)))
                (coeffContDiffTwo_mul
                  (coeffContDiffTwo_const Polynomial.X) hp)))
            (coeffContDiffTwo_mul (coeffContDiffTwo_C htwo) hq)
      · change RealCoeffContDiffTwo (fun δ =>
          nextJ (a δ) (b δ) (arbitrarySplitPair m ξ δ).1
            (arbitrarySplitPair m ξ δ).2)
        simpa only [nextJ] using
          coeffContDiffTwo_add
            (coeffContDiffTwo_add
              (coeffContDiffTwo_mul (coeffContDiffTwo_C habm) hq)
              (coeffContDiffTwo_mul
                (coeffContDiffTwo_const (Polynomial.C (8 : ℝ)))
                (coeffContDiffTwo_mul
                  (coeffContDiffTwo_const Polynomial.X) hq)))
            (coeffContDiffTwo_mul (coeffContDiffTwo_C hfour)
              (coeffContDiffTwo_mul
                (coeffContDiffTwo_const Polynomial.X) hp))

theorem arbitrarySplitPair_eval_contDiff_two
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) :
    ContDiff ℝ 2 (fun δ => (arbitrarySplitPair m ξ δ).1.eval r) ∧
      ContDiff ℝ 2 (fun δ => (arbitrarySplitPair m ξ δ).2.eval r) := by
  have hp := (arbitrarySplitPair_coeff_contDiff_two m ξ).1
  have hq := (arbitrarySplitPair_coeff_contDiff_two m ξ).2
  constructor
  · have hsum : ContDiff ℝ 2 (fun δ : ℝ =>
        ∑ i ∈ Finset.range (m+1),
          (arbitrarySplitPair m ξ δ).1.coeff i * r^i) := by
      apply ContDiff.sum
      intro i hi
      exact (hp i).mul contDiff_const
    convert hsum using 1
    funext δ
    exact eval_eq_sum_range'
      (show (arbitrarySplitPair m ξ δ).1.natDegree < m+1 by
        have hle := natDegree_le_iff_coeff_eq_zero.mpr
          (arbitrarySplitPair_coeff_zero_above m ξ δ).1
        omega) r
  · have hsum : ContDiff ℝ 2 (fun δ : ℝ =>
        ∑ i ∈ Finset.range (m+1),
          (arbitrarySplitPair m ξ δ).2.coeff i * r^i) := by
      apply ContDiff.sum
      intro i hi
      exact (hq i).mul contDiff_const
    convert hsum using 1
    funext δ
    exact eval_eq_sum_range'
      (show (arbitrarySplitPair m ξ δ).2.natDegree < m+1 by
        have hle := natDegree_le_iff_coeff_eq_zero.mpr
          (arbitrarySplitPair_coeff_zero_above m ξ δ).2
        omega) r

theorem arbitrarySplitPair_quotient_coeff_contDiff_two
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    ContDiff ℝ 2 (fun δ =>
      (quotient (arbitrarySplitPair m ξ δ).1
        (arbitrarySplitPair m ξ δ).2 r).coeff i) := by
  induction i with
  | zero =>
      have h := (arbitrarySplitPair_eval_contDiff_two m ξ r).1.mul
        ((arbitrarySplitPair_coeff_contDiff_two m ξ).2 0)
      convert h using 1
      funext δ
      exact quotient_zero (arbitrarySplitPair m ξ δ).1
        (arbitrarySplitPair m ξ δ).2 hr
  | succ i ih =>
      have hpEval := (arbitrarySplitPair_eval_contDiff_two m ξ r).1
      have hqEval := (arbitrarySplitPair_eval_contDiff_two m ξ r).2
      have hpCoeff := (arbitrarySplitPair_coeff_contDiff_two m ξ).1 i
      have hqCoeff := (arbitrarySplitPair_coeff_contDiff_two m ξ).2 (i+1)
      have h := (hpEval.mul hqCoeff).add
        ((ih.sub (hqEval.mul hpCoeff)).div_const r)
      convert h using 1
      funext δ
      exact quotient_succ (arbitrarySplitPair m ξ δ).1
        (arbitrarySplitPair m ξ δ).2 hr i

theorem arbitrarySplitRawD_coeff_contDiff_two
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    ContDiff ℝ 2 (fun δ =>
      (arbitrarySplitRawD m ξ r δ).coeff i) := by
  have h := (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => (4 : ℝ))).mul
    (arbitrarySplitPair_quotient_coeff_contDiff_two m ξ r hr i)
  simpa only [arbitrarySplitRawD, rawD, Polynomial.coeff_C_mul] using h

theorem arbitrarySplitRawD_eval_contDiff_two
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 2
      (fun δ => (arbitrarySplitRawD m ξ r δ).eval (u δ)) := by
  have hdeg (δ : ℝ) : (arbitrarySplitRawD m ξ r δ).natDegree < m+1 := by
    have hle := natDegree_le_iff_coeff_eq_zero.mpr
      (fun i hi => (arbitrarySplitRaw_coeff_zero_above m ξ r δ i hi).1)
    omega
  have hsum : ContDiff ℝ 2 (fun δ : ℝ =>
      ∑ i ∈ Finset.range (m+1),
        (arbitrarySplitRawD m ξ r δ).coeff i * (u δ)^i) := by
    apply ContDiff.sum
    intro i hi
    exact (arbitrarySplitRawD_coeff_contDiff_two m ξ r hr i).mul
      (hu.pow i)
  convert hsum using 1
  funext δ
  exact eval_eq_sum_range' (hdeg δ) (u δ)

/-- The manuscript's scalar fully phosphorylated readout is twice
continuously differentiable in the split parameter near coalescence. -/
theorem arbitrarySplitReadout_scalar_contDiffAt_two
    (m : ℕ) (ξ : ℕ → ℝ) (r a : ℝ) (hr : r ≠ 0)
    (hD₀ : (coalescedRawD m r).eval 1 ≠ 0) :
    ContDiffAt ℝ 2 (fun δ : ℝ =>
      splitReadoutScalar m (arbitrarySplitRawD m ξ r δ) (3+δ*a)) 0 := by
  let x : ℝ → ℝ := fun δ => 3+δ*a
  let u : ℝ → ℝ := fun δ => ratio (x δ)
  let D : ℝ → ℝ[X] := fun δ => arbitrarySplitRawD m ξ r δ
  have hx : ContDiff ℝ 2 x := by
    dsimp [x]
    fun_prop
  have hu : ContDiff ℝ 2 u := by
    dsimp [u, x, ratio]
    fun_prop
  have hcoeff : ContDiff ℝ 2 (fun δ => (D δ).coeff m / 2) :=
    (arbitrarySplitRawD_coeff_contDiff_two m ξ r hr m).div_const 2
  have hden : ContDiff ℝ 2 (fun δ => (D δ).eval (u δ)) :=
    arbitrarySplitRawD_eval_contDiff_two m ξ r hr u hu
  have hden0 : (D 0).eval (u 0) ≠ 0 := by
    have hu0 : u 0 = 1 := by norm_num [u, x, ratio]
    rw [hu0]
    simpa [D, arbitrarySplitRawD, coalescedRawD,
      arbitrarySplitPair_zero_eq_coalesced] using hD₀
  have hquot : ContDiffAt ℝ 2 (fun δ => (u δ)^m / (D δ).eval (u δ)) 0 :=
    (hu.pow m).contDiffAt.div hden.contDiffAt hden0
  have hxden : x 0 + 1 ≠ 0 := by
    norm_num [x]
  have hnum : ContDiffAt ℝ 2
      (fun δ => (x δ-1)*(x δ+5)/(x δ+1)) 0 := by
    exact ((hx.contDiffAt.sub contDiffAt_const).mul
      (hx.contDiffAt.add contDiffAt_const)).div
      (hx.contDiffAt.add contDiffAt_const) hxden
  have h := (hcoeff.contDiffAt.mul hquot).mul hnum
  convert h using 1
  funext δ
  simp only [splitReadoutScalar, D, x, u]

theorem arbitrarySplitReadout_scalar_difference_contDiffAt_two
    (m : ℕ) (ξ : ℕ → ℝ) (r a b : ℝ) (hr : r ≠ 0)
    (hD₀ : (coalescedRawD m r).eval 1 ≠ 0) :
    ContDiffAt ℝ 2 (fun δ : ℝ =>
      splitReadoutScalar m (arbitrarySplitRawD m ξ r δ) (3+δ*a) -
        splitReadoutScalar m (arbitrarySplitRawD m ξ r δ) (3+δ*b)) 0 :=
  (arbitrarySplitReadout_scalar_contDiffAt_two m ξ r a hr hD₀).sub
    (arbitrarySplitReadout_scalar_contDiffAt_two m ξ r b hr hD₀)

end

end PhosphorylationStableCapacity
