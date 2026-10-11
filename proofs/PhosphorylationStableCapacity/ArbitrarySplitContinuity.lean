module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitSource
public import proofs.PhosphorylationStableCapacity.SplitSourceContinuity

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Filter
open scoped Topology

private theorem arbitraryCoeffContinuous_const (p : ℝ[X]) :
    RealCoeffContinuous (fun _ => p) := by
  intro i
  exact continuous_const

private theorem arbitraryCoeffContinuous_C {g : ℝ → ℝ}
    (hg : Continuous g) :
    RealCoeffContinuous (fun δ => Polynomial.C (g δ)) := by
  intro i
  cases i with
  | zero => simpa using hg
  | succ i => simpa using (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))

private theorem arbitraryCoeffContinuous_add {p q : ℝ → ℝ[X]}
    (hp : RealCoeffContinuous p) (hq : RealCoeffContinuous q) :
    RealCoeffContinuous (fun δ => p δ + q δ) := by
  intro i
  have heq : (fun δ => (p δ + q δ).coeff i) =
      (fun δ => (p δ).coeff i) + (fun δ => (q δ).coeff i) := by
    funext δ
    simp [Pi.add_apply]
  rw [heq]
  exact (hp i).add (hq i)

private theorem arbitraryCoeffContinuous_mul {p q : ℝ → ℝ[X]}
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

/-- Every coefficient of the arbitrary-offset paired-root recurrence varies
continuously with its common splitting parameter. -/
theorem arbitrarySplitPair_coeff_continuous (m : ℕ) (ξ : ℕ → ℝ) :
    RealCoeffContinuous (fun δ => (arbitrarySplitPair m ξ δ).1) ∧
      RealCoeffContinuous (fun δ => (arbitrarySplitPair m ξ δ).2) := by
  induction m with
  | zero =>
      have hroot : Continuous (fun δ : ℝ =>
          (offsetSplitRoot ξ δ 0 - 1) / 2) := by
        dsimp [offsetSplitRoot]
        fun_prop
      exact ⟨arbitraryCoeffContinuous_const 1,
        arbitraryCoeffContinuous_C hroot⟩
  | succ m ih =>
      let a : ℝ → ℝ := fun δ => offsetSplitRoot ξ δ (2*m+1)
      let b : ℝ → ℝ := fun δ => offsetSplitRoot ξ δ (2*m+2)
      have ha : Continuous a := by
        dsimp [a, offsetSplitRoot]
        fun_prop
      have hb : Continuous b := by
        dsimp [b, offsetSplitRoot]
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
          nextN (a δ) (b δ) (arbitrarySplitPair m ξ δ).1
            (arbitrarySplitPair m ξ δ).2)
        simpa only [nextN] using
          arbitraryCoeffContinuous_add
            (arbitraryCoeffContinuous_add
              (arbitraryCoeffContinuous_mul
                (arbitraryCoeffContinuous_C hab) hp)
              (arbitraryCoeffContinuous_mul
                (arbitraryCoeffContinuous_const (Polynomial.C (8 : ℝ)))
                (arbitraryCoeffContinuous_mul
                  (arbitraryCoeffContinuous_const Polynomial.X) hp)))
            (arbitraryCoeffContinuous_mul
              (arbitraryCoeffContinuous_C htwo) hq)
      · change RealCoeffContinuous (fun δ =>
          nextJ (a δ) (b δ) (arbitrarySplitPair m ξ δ).1
            (arbitrarySplitPair m ξ δ).2)
        simpa only [nextJ] using
          arbitraryCoeffContinuous_add
            (arbitraryCoeffContinuous_add
              (arbitraryCoeffContinuous_mul
                (arbitraryCoeffContinuous_C habm) hq)
              (arbitraryCoeffContinuous_mul
                (arbitraryCoeffContinuous_const (Polynomial.C (8 : ℝ)))
                (arbitraryCoeffContinuous_mul
                  (arbitraryCoeffContinuous_const Polynomial.X) hq)))
            (arbitraryCoeffContinuous_mul
              (arbitraryCoeffContinuous_C hfour)
              (arbitraryCoeffContinuous_mul
                (arbitraryCoeffContinuous_const Polynomial.X) hp))

/-- Both recurrence polynomials have degree at most the recursion depth. -/
theorem arbitrarySplitPair_coeff_zero_above (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ) :
    (∀ i, m < i → (arbitrarySplitPair m ξ δ).1.coeff i = 0) ∧
      (∀ i, m < i → (arbitrarySplitPair m ξ δ).2.coeff i = 0) := by
  induction m with
  | zero =>
      constructor <;> intro i hi <;>
        simp [arbitrarySplitPair, coeff_one, coeff_C, Nat.ne_of_gt hi]
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

theorem arbitrarySplitPair_eval_continuous (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) :
    Continuous (fun δ => (arbitrarySplitPair m ξ δ).1.eval r) ∧
      Continuous (fun δ => (arbitrarySplitPair m ξ δ).2.eval r) := by
  have hp := (arbitrarySplitPair_coeff_continuous m ξ).1
  have hq := (arbitrarySplitPair_coeff_continuous m ξ).2
  constructor
  · have hsum : Continuous (fun δ : ℝ =>
        ∑ i ∈ Finset.range (m+1),
          (arbitrarySplitPair m ξ δ).1.coeff i * r^i) := by
      apply continuous_finsetSum
      intro i hi
      exact (hp i).mul continuous_const
    convert hsum using 1
    funext δ
    exact eval_eq_sum_range'
      (show (arbitrarySplitPair m ξ δ).1.natDegree < m+1 by
        have hle := natDegree_le_iff_coeff_eq_zero.mpr
          (arbitrarySplitPair_coeff_zero_above m ξ δ).1
        omega) r
  · have hsum : Continuous (fun δ : ℝ =>
        ∑ i ∈ Finset.range (m+1),
          (arbitrarySplitPair m ξ δ).2.coeff i * r^i) := by
      apply continuous_finsetSum
      intro i hi
      exact (hq i).mul continuous_const
    convert hsum using 1
    funext δ
    exact eval_eq_sum_range'
      (show (arbitrarySplitPair m ξ δ).2.natDegree < m+1 by
        have hle := natDegree_le_iff_coeff_eq_zero.mpr
          (arbitrarySplitPair_coeff_zero_above m ξ δ).2
        omega) r

theorem arbitrarySplitPair_quotient_coeff_continuous (m : ℕ)
    (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    Continuous (fun δ =>
      (quotient (arbitrarySplitPair m ξ δ).1
        (arbitrarySplitPair m ξ δ).2 r).coeff i) := by
  induction i with
  | zero =>
      have h := (arbitrarySplitPair_eval_continuous m ξ r).1.mul
        ((arbitrarySplitPair_coeff_continuous m ξ).2 0)
      convert h using 1
      funext δ
      exact quotient_zero (arbitrarySplitPair m ξ δ).1
        (arbitrarySplitPair m ξ δ).2 hr
  | succ i ih =>
      have hpEval := (arbitrarySplitPair_eval_continuous m ξ r).1
      have hqEval := (arbitrarySplitPair_eval_continuous m ξ r).2
      have hpCoeff := (arbitrarySplitPair_coeff_continuous m ξ).1 i
      have hqCoeff := (arbitrarySplitPair_coeff_continuous m ξ).2 (i+1)
      have h := (hpEval.mul hqCoeff).add
        ((ih.sub (hqEval.mul hpCoeff)).div_const r)
      convert h using 1
      funext δ
      exact quotient_succ (arbitrarySplitPair m ξ δ).1
        (arbitrarySplitPair m ξ δ).2 hr i

theorem arbitrarySplitRawD_coeff_continuous (m : ℕ) (ξ : ℕ → ℝ)
    (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    Continuous (fun δ => (arbitrarySplitRawD m ξ r δ).coeff i) := by
  have h := (arbitrarySplitPair_quotient_coeff_continuous m ξ r hr i).const_mul 4
  simpa only [arbitrarySplitRawD, rawD, Polynomial.coeff_C_mul] using h

theorem arbitrarySplitRawB_coeff_continuous (m : ℕ) (ξ : ℕ → ℝ)
    (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    Continuous (fun δ => (arbitrarySplitRawB m ξ r δ).coeff i) := by
  have hpEval := (arbitrarySplitPair_eval_continuous m ξ r).1
  have hqEval := (arbitrarySplitPair_eval_continuous m ξ r).2
  have hpCoeff := (arbitrarySplitPair_coeff_continuous m ξ).1 i
  have hqCoeff := (arbitrarySplitPair_coeff_continuous m ξ).2 i
  have hD := arbitrarySplitRawD_coeff_continuous m ξ r hr i
  have h1 : Continuous (fun δ => r * (arbitrarySplitRawD m ξ r δ).coeff i) :=
    continuous_const.mul hD
  have hscale : Continuous (fun δ =>
      4*r*(arbitrarySplitPair m ξ δ).1.eval r -
        2*(arbitrarySplitPair m ξ δ).2.eval r) :=
    (continuous_const.mul hpEval).sub (continuous_const.mul hqEval)
  have h2 : Continuous (fun δ =>
      (4*r*(arbitrarySplitPair m ξ δ).1.eval r -
        2*(arbitrarySplitPair m ξ δ).2.eval r) *
          (arbitrarySplitPair m ξ δ).1.coeff i) := hscale.mul hpCoeff
  have h3 : Continuous (fun δ =>
      (2*(arbitrarySplitPair m ξ δ).2.eval r) *
        (arbitrarySplitPair m ξ δ).2.coeff i) :=
    (continuous_const.mul hqEval).mul hqCoeff
  have h := (h1.add h2).sub h3
  convert h using 1
  funext δ
  simp only [arbitrarySplitRawB, rawB, Polynomial.coeff_add,
    Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  simp [arbitrarySplitRawD]

/-- A fixed admissible coalesced conversion parameter remains coefficientwise
positive after any sufficiently small arbitrary-offset split. -/
theorem arbitrarySplit_conversion_positive_near_zero
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ)
    (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD m r) m)
    (hB₀ : DensePositive (coalescedRawB m r) m) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      DensePositive (arbitrarySplitRawD m ξ r δ) m ∧
        DensePositive (arbitrarySplitRawB m ξ r δ) m := by
  have hD (i : Fin (m+1)) :
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        0 < (arbitrarySplitRawD m ξ r δ).coeff i := by
    have hzero : 0 < (arbitrarySplitRawD m ξ r 0).coeff i := by
      simpa [arbitrarySplitRawD, coalescedRawD,
        arbitrarySplitPair_zero_eq_coalesced] using hD₀.1 i (by omega)
    exact ((arbitrarySplitRawD_coeff_continuous m ξ r hr i).tendsto 0).eventually
      (Ioi_mem_nhds hzero) |>.filter_mono nhdsWithin_le_nhds
  have hB (i : Fin (m+1)) :
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        0 < (arbitrarySplitRawB m ξ r δ).coeff i := by
    have hzero : 0 < (arbitrarySplitRawB m ξ r 0).coeff i := by
      simpa [arbitrarySplitRawB, coalescedRawB,
        arbitrarySplitPair_zero_eq_coalesced] using hB₀.1 i (by omega)
    exact ((arbitrarySplitRawB_coeff_continuous m ξ r hr i).tendsto 0).eventually
      (Ioi_mem_nhds hzero) |>.filter_mono nhdsWithin_le_nhds
  have hDall := Filter.eventually_all.mpr hD
  have hBall := Filter.eventually_all.mpr hB
  have hpqevent : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      DensePositive (arbitrarySplitPair m ξ δ).1 m ∧
        DensePositive (arbitrarySplitPair m ξ δ).2 m :=
    (arbitrarySplitPair_dense_eventually m ξ).filter_mono nhdsWithin_le_nhds
  filter_upwards [hDall, hBall, hpqevent] with δ hd hb hpq
  constructor
  · exact ⟨fun i hi => hd ⟨i, by omega⟩,
      fun i hi => (raw_support hpq.1 hpq.2 r i hi).1⟩
  · exact ⟨fun i hi => hb ⟨i, by omega⟩,
      fun i hi => (raw_support hpq.1 hpq.2 r i hi).2⟩

end
end PhosphorylationStableCapacity
