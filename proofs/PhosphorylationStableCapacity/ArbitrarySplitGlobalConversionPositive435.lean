module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitConversion
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Polynomial

def ConversionKernelCoeffNonnegative (p : ℝ[X]) : Prop := ∀ i, 0 ≤ p.coeff i

private theorem conversionKernel_nonneg_add {p q : ℝ[X]}
    (hp : ConversionKernelCoeffNonnegative p) (hq : ConversionKernelCoeffNonnegative q) :
    ConversionKernelCoeffNonnegative (p+q) := by
  intro i
  simpa only [coeff_add] using add_nonneg (hp i) (hq i)

private theorem conversionKernel_nonneg_cmul {p : ℝ[X]} {c : ℝ}
    (hp : ConversionKernelCoeffNonnegative p) (hc : 0 ≤ c) :
    ConversionKernelCoeffNonnegative (C c*p) := by
  intro i
  simpa only [coeff_C_mul] using mul_nonneg hc (hp i)

private theorem conversionKernel_nonneg_xmul {p : ℝ[X]}
    (hp : ConversionKernelCoeffNonnegative p) :
    ConversionKernelCoeffNonnegative (X*p) := by
  intro i
  cases i with
  | zero => simp
  | succ i => simpa only [coeff_X_mul] using hp i

/-- Two simultaneous positive-kernel recurrences for the original paired
root step. The second kernel retains the extra sign information that
positivity of the first quotient alone would discard. -/
def nextPositiveConversionK (a b r : ℝ) (p q K L : ℝ[X]) : ℝ[X] :=
  let B := (a-1)*(b-1)
  let c := 2*(a+b)
  let T := B+8*r
  C (T*B+c*B)*K + C (8*T)*(X*K) + C (c*B*q.eval r)*q +
    C (16*c*r*p.eval r)*(X*p) + C (2*c*(c-4)*r)*(X*L)

def nextPositiveConversionL (a b r : ℝ) (p q K L : ℝ[X]) : ℝ[X] :=
  let B := (a-1)*(b-1)
  let c := 2*(a+b)
  let T := B+8*r
  C (T*B+c*T)*L + C (8*T)*(X*L) + C (8*c*(p.eval r+q.eval r))*q +
    C (2*c*B*p.eval r+2*c^2*p.eval r)*p + C (2*c^2)*K

theorem nextPositiveConversionK_identity (a b r : ℝ) (p q K L : ℝ[X])
    (hK : (X-C r)*K = C (q.eval r)*(X*p)-C (r*p.eval r)*q)
    (hL : (X-C r)*L = C (p.eval r)*q-C (q.eval r)*p) :
    (X-C r)*nextPositiveConversionK a b r p q K L =
      C ((nextJ a b p q).eval r)*(X*nextN a b p q)-
        C (r*(nextN a b p q).eval r)*nextJ a b p q := by
  simp only [nextPositiveConversionK, nextN, nextJ, eval_add, eval_mul,
    eval_sub, eval_one, eval_ofNat, eval_C, eval_X,
    C_add, C_sub, C_mul, C_1, map_ofNat] at hK hL ⊢
  linear_combination
    (((C a-1)*(C b-1)+8*C r)*((C a-1)*(C b-1)) +
      2*(C a+C b)*((C a-1)*(C b-1)) +
      8*((C a-1)*(C b-1)+8*C r)*X)*hK +
    (2*(2*(C a+C b))*(2*(C a+C b)-4)*C r*X)*hL

theorem nextPositiveConversionL_identity (a b r : ℝ) (p q K L : ℝ[X])
    (hK : (X-C r)*K = C (q.eval r)*(X*p)-C (r*p.eval r)*q)
    (hL : (X-C r)*L = C (p.eval r)*q-C (q.eval r)*p) :
    (X-C r)*nextPositiveConversionL a b r p q K L =
      C ((nextN a b p q).eval r)*nextJ a b p q-
        C ((nextJ a b p q).eval r)*nextN a b p q := by
  simp only [nextPositiveConversionL, nextN, nextJ, eval_add, eval_mul,
    eval_sub, eval_one, eval_ofNat, eval_C, eval_X,
    C_add, C_sub, C_mul, C_pow, C_1, map_ofNat] at hK hL ⊢
  linear_combination
    ((((C a-1)*(C b-1)+8*C r)*((C a-1)*(C b-1)) +
      2*(C a+C b)*((C a-1)*(C b-1)+8*C r) +
      8*((C a-1)*(C b-1)+8*C r)*X))*hL +
    (2*(2*(C a+C b))^2)*hK

private theorem conversionKernel_eq_quotient (p q K : ℝ[X]) (r : ℝ)
    (hK : (X-C r)*K = C (q.eval r)*(X*p)-C (r*p.eval r)*q) :
    K = quotient p q r := by
  have hfactor : (X-C r : ℝ[X]) ≠ 0 := by
    intro hz
    have h := congrArg (fun f : ℝ[X] => f.coeff 1) hz
    simp at h
  apply mul_left_cancel₀ hfactor
  simpa only [conversionNumerator] using hK.trans (quotient_identity p q r).symm

def PositiveConversionKernelCertificate (p q : ℝ[X]) (m : ℕ) (r : ℝ) : Prop :=
  ∃ K L : ℝ[X], DensePositive K m ∧ ConversionKernelCoeffNonnegative L ∧
    (X-C r)*K = C (q.eval r)*(X*p)-C (r*p.eval r)*q ∧
    (X-C r)*L = C (p.eval r)*q-C (q.eval r)*p

theorem positiveConversionKernelCertificate_step {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m)
    {a b r : ℝ} (ha : 1 < a) (hb : 1 < b) (hr : 0 < r)
    (hcert : PositiveConversionKernelCertificate p q m r) :
    PositiveConversionKernelCertificate (nextN a b p q) (nextJ a b p q) (m+1) r := by
  obtain ⟨K, L, hK, hL, hKi, hLi⟩ := hcert
  let B := (a-1)*(b-1)
  let c := 2*(a+b)
  let T := B+8*r
  have hB : 0 < B := mul_pos (by linarith) (by linarith)
  have hc : 4 < c := by dsimp [c]; linarith
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hcm4 : 0 < c-4 := sub_pos.mpr hc
  have hT : 0 < T := by dsimp [T]; positivity
  have hpval : 0 < p.eval r := hp.eval_pos hr
  have hqval : 0 < q.eval r := hq.eval_pos hr
  have hKnonneg : ConversionKernelCoeffNonnegative K := hK.nonneg
  have hpnonneg : ConversionKernelCoeffNonnegative p := hp.nonneg
  have hqnonneg : ConversionKernelCoeffNonnegative q := hq.nonneg
  have hKfirst : DensePositive (C (T*B+c*B)*K+C (8*T)*(X*K)) (m+1) := by
    simpa only [C_0, zero_mul, add_zero] using
      dense_step hK hK (T*B+c*B) (8*T) 0 0 (by positivity)
        (by positivity) (by norm_num) (by norm_num)
  have hKtail : ConversionKernelCoeffNonnegative
      (C (c*B*q.eval r)*q+C (16*c*r*p.eval r)*(X*p)+C (2*c*(c-4)*r)*(X*L)) := by
    apply conversionKernel_nonneg_add
    · apply conversionKernel_nonneg_add
      · exact conversionKernel_nonneg_cmul hqnonneg (by positivity)
      · exact conversionKernel_nonneg_cmul (conversionKernel_nonneg_xmul hpnonneg) (by positivity)
    · exact conversionKernel_nonneg_cmul (conversionKernel_nonneg_xmul hL) (by positivity)
  have hLnext : ConversionKernelCoeffNonnegative (nextPositiveConversionL a b r p q K L) := by
    change ConversionKernelCoeffNonnegative
      (C (T*B+c*T)*L+C (8*T)*(X*L)+C (8*c*(p.eval r+q.eval r))*q+
        C (2*c*B*p.eval r+2*c^2*p.eval r)*p+C (2*c^2)*K)
    apply conversionKernel_nonneg_add
    · apply conversionKernel_nonneg_add
      · apply conversionKernel_nonneg_add
        · apply conversionKernel_nonneg_add
          · exact conversionKernel_nonneg_cmul hL (by positivity)
          · exact conversionKernel_nonneg_cmul (conversionKernel_nonneg_xmul hL) (by positivity)
        · exact conversionKernel_nonneg_cmul hqnonneg (by positivity)
      · exact conversionKernel_nonneg_cmul hpnonneg (by positivity)
    · exact conversionKernel_nonneg_cmul hKnonneg (by positivity)
  have hKnextId := nextPositiveConversionK_identity a b r p q K L hKi hLi
  have hLnextId := nextPositiveConversionL_identity a b r p q K L hKi hLi
  have hKeq := conversionKernel_eq_quotient (nextN a b p q) (nextJ a b p q)
    (nextPositiveConversionK a b r p q K L) r hKnextId
  have hnext := next_dense hp hq ha hb
  refine ⟨nextPositiveConversionK a b r p q K L,
    nextPositiveConversionL a b r p q K L, ⟨?_, ?_⟩, hLnext, hKnextId, hLnextId⟩
  · intro i hi
    have hfirst := hKfirst.1 i hi
    have htail := hKtail i
    have heq : nextPositiveConversionK a b r p q K L =
        (C (T*B+c*B)*K+C (8*T)*(X*K)) +
        (C (c*B*q.eval r)*q+C (16*c*r*p.eval r)*(X*p)+C (2*c*(c-4)*r)*(X*L)) := by
      dsimp [nextPositiveConversionK, T, B, c]
      ring
    rw [heq, coeff_add]
    exact add_pos_of_pos_of_nonneg hfirst htail
  · intro i hi
    rw [hKeq]
    exact coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (quotient_degree hnext.1 hnext.2 r) hi)

/-- Uniform kernel certificate at every positive source parameter, for
arbitrary prescribed roots above one. No interlacing or large-source
limit is assumed. -/
theorem arbitrarySplitPair_positive_conversion_kernels
    (m : ℕ) (ξ : ℕ → ℝ) (δ r : ℝ) (hr : 0 < r)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) :
    PositiveConversionKernelCertificate
      (arbitrarySplitPair m ξ δ).1 (arbitrarySplitPair m ξ δ).2 m r := by
  induction m with
  | zero =>
    have hq0 : 0 < (offsetSplitRoot ξ δ 0-1)/2 := by
      have hx := hroot 0 (by omega)
      linarith
    refine ⟨C ((offsetSplitRoot ξ δ 0-1)/2), 0,
      dense_constant _ hq0, ?_, ?_, ?_⟩
    · intro i; simp
    · simp only [arbitrarySplitPair, eval_one, eval_C, mul_one]
      ring
    · simp only [arbitrarySplitPair, eval_one, eval_C, mul_zero, C_1, mul_one]
      ring
  | succ m ih =>
    have hold : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j := by
      intro j hj; exact hroot j (by omega)
    have hdense := arbitrarySplitPair_dense m ξ δ hold
    exact positiveConversionKernelCertificate_step hdense.1 hdense.2
      (hroot (2*m+1) (by omega)) (hroot (2*m+2) (by omega)) hr (ih hold)

/-- The exact global positivity assertion for the quotient Q in part
(i) of the manuscript's coefficient-positivity theorem. -/
theorem arbitrarySplit_quotient_dense_every_positive_source
    (m : ℕ) (ξ : ℕ → ℝ) (δ r : ℝ) (hr : 0 < r)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) :
    DensePositive (quotient (arbitrarySplitPair m ξ δ).1
      (arbitrarySplitPair m ξ δ).2 r) m := by
  obtain ⟨K, L, hK, _hL, hKi, _hLi⟩ :=
    arbitrarySplitPair_positive_conversion_kernels m ξ δ r hr hroot
  rw [← conversionKernel_eq_quotient _ _ K r hKi]
  exact hK

/-- The actual converted D polynomial has every coefficient through its
full degree positive at every r>0, not only eventually in r. -/
theorem arbitrarySplitRawD_dense_every_positive_source
    (m : ℕ) (ξ : ℕ → ℝ) (δ r : ℝ) (hr : 0 < r)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) :
    DensePositive (arbitrarySplitRawD m ξ r δ) m := by
  have hQ := arbitrarySplit_quotient_dense_every_positive_source m ξ δ r hr hroot
  constructor
  · intro i hi
    simpa only [arbitrarySplitRawD, rawD, coeff_C_mul] using
      mul_pos (by norm_num : 0 < (4 : ℝ)) (hQ.1 i hi)
  · intro i hi
    simp only [arbitrarySplitRawD, rawD, coeff_C_mul, hQ.2 i hi, mul_zero]

end
end PhosphorylationStableCapacity
