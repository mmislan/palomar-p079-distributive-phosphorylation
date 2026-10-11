module
public import proofs.PhosphorylationStableCapacity.SplitSource

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial
open scoped Topology

/-- Coefficientwise continuity is the finite-degree topology actually needed
for the split polynomial family. -/
def RealCoeffContinuous (p : ℝ → ℝ[X]) : Prop :=
  ∀ i : ℕ, Continuous fun δ => (p δ).coeff i

private theorem realCoeffContinuous_const (p : ℝ[X]) :
    RealCoeffContinuous (fun _ => p) := by
  intro i
  exact continuous_const

private theorem realCoeffContinuous_C {g : ℝ → ℝ}
    (hg : Continuous g) :
    RealCoeffContinuous (fun δ => Polynomial.C (g δ)) := by
  intro i
  cases i with
  | zero => simpa using hg
  | succ i => simpa using (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))

private theorem realCoeffContinuous_add {p q : ℝ → ℝ[X]}
    (hp : RealCoeffContinuous p) (hq : RealCoeffContinuous q) :
    RealCoeffContinuous (fun δ => p δ + q δ) := by
  intro i
  have heq : (fun δ => (p δ + q δ).coeff i) =
      (fun δ => (p δ).coeff i) + (fun δ => (q δ).coeff i) := by
    funext δ
    simp [Pi.add_apply]
  rw [heq]
  exact (hp i).add (hq i)

private theorem realCoeffContinuous_mul {p q : ℝ → ℝ[X]}
    (hp : RealCoeffContinuous p) (hq : RealCoeffContinuous q) :
    RealCoeffContinuous (fun δ => p δ * q δ) := by
  intro i
  have h : Continuous (fun δ : ℝ =>
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal i,
        (p δ).coeff ij.1 * (q δ).coeff ij.2) := by
    apply continuous_finsetSum
    intro ij hij
    exact (hp ij.1).mul (hq ij.2)
  simpa only [Polynomial.coeff_mul] using h

/-- Every coefficient of both prescribed source polynomials depends
continuously on the common split parameter. -/
theorem splitPair_coeff_continuous (m : ℕ) :
    RealCoeffContinuous (fun δ => (splitPair m δ).1) ∧
      RealCoeffContinuous (fun δ => (splitPair m δ).2) := by
  induction m with
  | zero =>
      exact ⟨realCoeffContinuous_const 1,
        realCoeffContinuous_const 1⟩
  | succ m ih =>
      let a : ℝ → ℝ := fun δ => splitRoot δ (2*m+1)
      let b : ℝ → ℝ := fun δ => splitRoot δ (2*m+2)
      have ha : Continuous a := by
        dsimp [a, splitRoot]
        fun_prop
      have hb : Continuous b := by
        dsimp [b, splitRoot]
        fun_prop
      have hab : Continuous (fun δ => (a δ + 1) * (b δ + 1)) :=
        (ha.add continuous_const).mul (hb.add continuous_const)
      have habm : Continuous (fun δ => (a δ - 1) * (b δ - 1)) :=
        (ha.sub continuous_const).mul (hb.sub continuous_const)
      have hsum : Continuous (fun δ => a δ + b δ) := ha.add hb
      have htwo : Continuous (fun δ => 2 * (a δ + b δ)) := by
        convert (continuous_const.mul hsum : Continuous
          ((fun _ : ℝ => (2 : ℝ)) * fun δ => a δ + b δ)) using 1
      have hfour : Continuous (fun δ => 4 * (a δ + b δ)) := by
        convert (continuous_const.mul hsum : Continuous
          ((fun _ : ℝ => (4 : ℝ)) * fun δ => a δ + b δ)) using 1
      have hp := ih.1
      have hq := ih.2
      constructor
      · change RealCoeffContinuous (fun δ =>
          nextN (a δ) (b δ) (splitPair m δ).1 (splitPair m δ).2)
        simpa only [nextN] using
          realCoeffContinuous_add
            (realCoeffContinuous_add
              (realCoeffContinuous_mul
                (realCoeffContinuous_C hab) hp)
              (realCoeffContinuous_mul
                (realCoeffContinuous_const (Polynomial.C (8 : ℝ)))
                (realCoeffContinuous_mul
                  (realCoeffContinuous_const Polynomial.X) hp)))
            (realCoeffContinuous_mul
              (realCoeffContinuous_C htwo) hq)
      · change RealCoeffContinuous (fun δ =>
          nextJ (a δ) (b δ) (splitPair m δ).1 (splitPair m δ).2)
        simpa only [nextJ] using
          realCoeffContinuous_add
            (realCoeffContinuous_add
              (realCoeffContinuous_mul
                (realCoeffContinuous_C habm) hq)
              (realCoeffContinuous_mul
                (realCoeffContinuous_const (Polynomial.C (8 : ℝ)))
                (realCoeffContinuous_mul
                  (realCoeffContinuous_const Polynomial.X) hq)))
            (realCoeffContinuous_mul
              (realCoeffContinuous_C hfour)
              (realCoeffContinuous_mul
                (realCoeffContinuous_const Polynomial.X) hp))

/-- The prescribed recurrence never creates coefficients above degree `m`,
even when the splitting parameter is negative. -/
theorem splitPair_coeff_zero_above (m : ℕ) (δ : ℝ) :
    (∀ i, m < i → (splitPair m δ).1.coeff i = 0) ∧
      (∀ i, m < i → (splitPair m δ).2.coeff i = 0) := by
  induction m with
  | zero =>
      constructor <;> intro i hi <;>
        simp [splitPair, coeff_one, Nat.ne_of_gt hi]
  | succ m ih =>
      constructor
      · intro i hi
        cases i with
        | zero => omega
        | succ i =>
            change (nextN _ _ _ _).coeff (i+1) = 0
            simp only [nextN, coeff_add, coeff_C_mul, coeff_X_mul]
            rw [ih.1 (i+1) (by omega), ih.1 i (by omega),
              ih.2 (i+1) (by omega)]
            ring
      · intro i hi
        cases i with
        | zero => omega
        | succ i =>
            change (nextJ _ _ _ _).coeff (i+1) = 0
            simp only [nextJ, coeff_add, coeff_C_mul, coeff_X_mul]
            rw [ih.2 (i+1) (by omega), ih.2 i (by omega),
              ih.1 i (by omega)]
            ring

/-- Evaluation at a fixed conversion parameter is continuous in the
splitting parameter, because only finitely many coefficients occur. -/
theorem splitPair_eval_continuous (m : ℕ) (r : ℝ) :
    Continuous (fun δ => (splitPair m δ).1.eval r) ∧
      Continuous (fun δ => (splitPair m δ).2.eval r) := by
  have hp := (splitPair_coeff_continuous m).1
  have hq := (splitPair_coeff_continuous m).2
  constructor
  · have hsum : Continuous (fun δ : ℝ =>
        ∑ i ∈ Finset.range (m+1), (splitPair m δ).1.coeff i * r^i) := by
      apply continuous_finsetSum
      intro i hi
      exact (hp i).mul continuous_const
    convert hsum using 1
    funext δ
    exact eval_eq_sum_range'
      (show (splitPair m δ).1.natDegree < m+1 by
        have hle := natDegree_le_iff_coeff_eq_zero.mpr
          (splitPair_coeff_zero_above m δ).1
        omega) r
  · have hsum : Continuous (fun δ : ℝ =>
        ∑ i ∈ Finset.range (m+1), (splitPair m δ).2.coeff i * r^i) := by
      apply continuous_finsetSum
      intro i hi
      exact (hq i).mul continuous_const
    convert hsum using 1
    funext δ
    exact eval_eq_sum_range'
      (show (splitPair m δ).2.natDegree < m+1 by
        have hle := natDegree_le_iff_coeff_eq_zero.mpr
          (splitPair_coeff_zero_above m δ).2
        omega) r

/-- Division by the fixed monic `X-r` remains coefficientwise continuous.
The recursive quotient identity supplies an elementary proof without a
topology on the entire polynomial ring. -/
theorem splitPair_quotient_coeff_continuous (m : ℕ) (r : ℝ)
    (hr : r ≠ 0) (i : ℕ) :
    Continuous (fun δ =>
      (quotient (splitPair m δ).1 (splitPair m δ).2 r).coeff i) := by
  induction i with
  | zero =>
      have h := (splitPair_eval_continuous m r).1.mul
        ((splitPair_coeff_continuous m).2 0)
      convert h using 1
      funext δ
      exact quotient_zero (splitPair m δ).1 (splitPair m δ).2 hr
  | succ i ih =>
      have hpEval := (splitPair_eval_continuous m r).1
      have hqEval := (splitPair_eval_continuous m r).2
      have hpCoeff := (splitPair_coeff_continuous m).1 i
      have hqCoeff := (splitPair_coeff_continuous m).2 (i+1)
      have h := (hpEval.mul hqCoeff).add
        ((ih.sub (hqEval.mul hpCoeff)).div_const r)
      convert h using 1
      funext δ
      exact quotient_succ (splitPair m δ).1 (splitPair m δ).2 hr i

/-- The converted complex coefficients vary continuously with splitting
when the conversion parameter is fixed and nonzero. -/
theorem splitRawD_coeff_continuous (m : ℕ) (r : ℝ)
    (hr : r ≠ 0) (i : ℕ) :
    Continuous (fun δ => (splitRawD m r δ).coeff i) := by
  have h := (splitPair_quotient_coeff_continuous m r hr i).const_mul 4
  simpa only [splitRawD, rawD, Polynomial.coeff_C_mul] using h

theorem splitRawB_coeff_continuous (m : ℕ) (r : ℝ)
    (hr : r ≠ 0) (i : ℕ) :
    Continuous (fun δ => (splitRawB m r δ).coeff i) := by
  have hpEval := (splitPair_eval_continuous m r).1
  have hqEval := (splitPair_eval_continuous m r).2
  have hpCoeff := (splitPair_coeff_continuous m).1 i
  have hqCoeff := (splitPair_coeff_continuous m).2 i
  have hD := splitRawD_coeff_continuous m r hr i
  have h1 : Continuous (fun δ => r * (splitRawD m r δ).coeff i) :=
    continuous_const.mul hD
  have hscale : Continuous (fun δ =>
      4*r*(splitPair m δ).1.eval r - 2*(splitPair m δ).2.eval r) :=
    (continuous_const.mul hpEval).sub (continuous_const.mul hqEval)
  have h2 : Continuous (fun δ =>
      (4*r*(splitPair m δ).1.eval r - 2*(splitPair m δ).2.eval r) *
        (splitPair m δ).1.coeff i) := hscale.mul hpCoeff
  have h3 : Continuous (fun δ =>
      (2*(splitPair m δ).2.eval r) * (splitPair m δ).2.coeff i) :=
    (continuous_const.mul hqEval).mul hqCoeff
  have h := (h1.add h2).sub h3
  convert h using 1
  funext δ
  simp only [splitRawB, rawB, Polynomial.coeff_add,
    Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  simp [splitRawD]

/-- The converted polynomials have degree at most `m` for every real
splitting parameter, independently of positivity. -/
theorem splitRaw_coeff_zero_above (m : ℕ) (r δ : ℝ) (i : ℕ)
    (hi : m < i) :
    (splitRawD m r δ).coeff i = 0 ∧
      (splitRawB m r δ).coeff i = 0 := by
  let p := (splitPair m δ).1
  let q := (splitPair m δ).2
  have hsupport := splitPair_coeff_zero_above m δ
  have hnum : (conversionNumerator p q r).natDegree ≤ m+1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    cases j with
    | zero => omega
    | succ j =>
        simp only [conversionNumerator, coeff_sub, coeff_C_mul, coeff_X_mul]
        rw [hsupport.1 j (by omega), hsupport.2 (j+1) (by omega)]
        ring
  have hquot : (quotient p q r).natDegree ≤ m := by
    rw [quotient, natDegree_divByMonic _ (monic_X_sub_C r),
      natDegree_X_sub_C]
    omega
  have hh : (quotient p q r).coeff i = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hquot hi)
  dsimp [p, q] at hh
  simp only [splitRawD, splitRawB, rawD, rawB,
    coeff_sub, coeff_add, coeff_C_mul, hh,
    hsupport.1 i hi, hsupport.2 i hi]
  constructor <;> ring

/-- Evaluate either converted polynomial at a continuously moving scalar
argument. Its finite degree makes the evaluation jointly continuous in the
split parameter and the scalar argument. -/
theorem splitRawD_eval_continuous (m : ℕ) (r : ℝ)
    (hr : r ≠ 0) (u : ℝ → ℝ) (hu : Continuous u) :
    Continuous (fun δ => (splitRawD m r δ).eval (u δ)) := by
  have hsum : Continuous (fun δ : ℝ =>
      ∑ i ∈ Finset.range (m+1),
        (splitRawD m r δ).coeff i * (u δ)^i) := by
    apply continuous_finsetSum
    intro i hi
    exact (splitRawD_coeff_continuous m r hr i).mul (hu.pow i)
  convert hsum using 1
  funext δ
  exact eval_eq_sum_range'
    (show (splitRawD m r δ).natDegree < m+1 by
      have hle := natDegree_le_iff_coeff_eq_zero.mpr
        (fun i hi => (splitRaw_coeff_zero_above m r δ i hi).1)
      omega) (u δ)

theorem splitRawB_eval_continuous (m : ℕ) (r : ℝ)
    (hr : r ≠ 0) (u : ℝ → ℝ) (hu : Continuous u) :
    Continuous (fun δ => (splitRawB m r δ).eval (u δ)) := by
  have hsum : Continuous (fun δ : ℝ =>
      ∑ i ∈ Finset.range (m+1),
        (splitRawB m r δ).coeff i * (u δ)^i) := by
    apply continuous_finsetSum
    intro i hi
    exact (splitRawB_coeff_continuous m r hr i).mul (hu.pow i)
  convert hsum using 1
  funext δ
  exact eval_eq_sum_range'
    (show (splitRawB m r δ).natDegree < m+1 by
      have hle := natDegree_le_iff_coeff_eq_zero.mpr
        (fun i hi => (splitRaw_coeff_zero_above m r δ i hi).2)
      omega) (u δ)

theorem splitInventory_coeff_continuous (m : ℕ) (r : ℝ)
    (hr : r ≠ 0) (i : ℕ) :
    Continuous (fun δ =>
      (((1 + Polynomial.X) * splitRawD m r δ : ℝ[X]).coeff i)) := by
  exact realCoeffContinuous_mul
    (realCoeffContinuous_const (1 + Polynomial.X))
    (fun i => splitRawD_coeff_continuous m r hr i) i

/-- The *same fixed* conversion parameter stays admissible under a small
positive split whenever the coalesced converted coefficients are positive.
No refitting of `r` is hidden in this eventual statement. -/
theorem split_conversion_positive_near_zero (m : ℕ) (r : ℝ)
    (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD m r) m)
    (hB₀ : DensePositive (coalescedRawB m r) m) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      DensePositive (splitRawD m r δ) m ∧
        DensePositive (splitRawB m r δ) m := by
  have hD (i : Fin (m+1)) :
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        0 < (splitRawD m r δ).coeff i := by
    have hzero : 0 < (splitRawD m r 0).coeff i := by
      simpa [splitRawD, coalescedRawD, splitPair_zero_eq_coalesced]
        using hD₀.1 i (by omega)
    exact ((splitRawD_coeff_continuous m r hr i).tendsto 0).eventually
      (Ioi_mem_nhds hzero) |>.filter_mono nhdsWithin_le_nhds
  have hB (i : Fin (m+1)) :
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        0 < (splitRawB m r δ).coeff i := by
    have hzero : 0 < (splitRawB m r 0).coeff i := by
      simpa [splitRawB, coalescedRawB, splitPair_zero_eq_coalesced]
        using hB₀.1 i (by omega)
    exact ((splitRawB_coeff_continuous m r hr i).tendsto 0).eventually
      (Ioi_mem_nhds hzero) |>.filter_mono nhdsWithin_le_nhds
  have hDall := Filter.eventually_all.mpr hD
  have hBall := Filter.eventually_all.mpr hB
  have hδ : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ :=
    self_mem_nhdsWithin
  filter_upwards [hDall, hBall, hδ] with δ hd hb hδ
  have hpq := splitPair_dense m hδ.le
  constructor
  · exact ⟨fun i hi => hd ⟨i, by omega⟩,
      fun i hi => (raw_support hpq.1 hpq.2 r i hi).1⟩
  · exact ⟨fun i hi => hb ⟨i, by omega⟩,
      fun i hi => (raw_support hpq.1 hpq.2 r i hi).2⟩

end
end PhosphorylationStableCapacity
