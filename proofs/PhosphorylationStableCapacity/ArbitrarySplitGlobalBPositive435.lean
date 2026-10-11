module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitGlobalConversionPositive435
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Polynomial
open scoped BigOperators

def arbitrarySplitRootExcess (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (2*m+1), offsetSplitRoot ξ δ j) - 1

def arbitrarySplitLeadingRatio (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ) : ℝ :=
  2 / arbitrarySplitRootExcess m ξ δ

theorem arbitrarySplitRootExcess_succ (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ) :
    arbitrarySplitRootExcess (m+1) ξ δ = arbitrarySplitRootExcess m ξ δ +
      offsetSplitRoot ξ δ (2*m+1) + offsetSplitRoot ξ δ (2*m+2) := by
  unfold arbitrarySplitRootExcess
  have hn : 2*(m+1)+1 = (2*m+1+1)+1 := by omega
  rw [hn, Finset.sum_range_succ, Finset.sum_range_succ]
  ring

theorem arbitrarySplitRootExcess_pos (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) :
    0 < arbitrarySplitRootExcess m ξ δ := by
  induction m with
  | zero =>
    have h := hroot 0 (by omega)
    simpa [arbitrarySplitRootExcess] using sub_pos.mpr h
  | succ m ih =>
    have hold : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j := by
      intro j hj; exact hroot j (by omega)
    rw [arbitrarySplitRootExcess_succ]
    have ha := hroot (2*m+1) (by omega)
    have hb := hroot (2*m+2) (by omega)
    linarith [ih hold]

theorem arbitrarySplitLeadingRatio_pos (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) :
    0 < arbitrarySplitLeadingRatio m ξ δ :=
  div_pos (by norm_num) (arbitrarySplitRootExcess_pos m ξ δ hroot)

theorem arbitrarySplitPair_global_leading_coefficients
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) :
    (arbitrarySplitPair m ξ δ).1.coeff m = 8^m ∧
      (arbitrarySplitPair m ξ δ).2.coeff m =
        8^m*arbitrarySplitRootExcess m ξ δ/2 := by
  induction m with
  | zero => simp [arbitrarySplitPair, arbitrarySplitRootExcess]
  | succ m ih =>
    have hold : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j := by
      intro j hj; exact hroot j (by omega)
    have hdense := arbitrarySplitPair_dense m ξ δ hold
    have hlead := ih hold
    change (nextN _ _ (arbitrarySplitPair m ξ δ).1
      (arbitrarySplitPair m ξ δ).2).coeff (m+1) = _ ∧
      (nextJ _ _ (arbitrarySplitPair m ξ δ).1
      (arbitrarySplitPair m ξ δ).2).coeff (m+1) = _
    simp only [nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul]
    rw [hdense.1.2 (m+1) (by omega), hdense.2.2 (m+1) (by omega),
      hlead.1, hlead.2, arbitrarySplitRootExcess_succ, pow_succ]
    constructor <;> ring

theorem arbitrarySplitLeadingRatio_eq_leading_coeff_ratio
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) :
    arbitrarySplitLeadingRatio m ξ δ =
      (arbitrarySplitPair m ξ δ).1.coeff m / (arbitrarySplitPair m ξ δ).2.coeff m := by
  have hlead := arbitrarySplitPair_global_leading_coefficients m ξ δ hroot
  have ht := arbitrarySplitRootExcess_pos m ξ δ hroot
  rw [hlead.1, hlead.2]
  unfold arbitrarySplitLeadingRatio
  field_simp [pow_ne_zero m (by norm_num : (8 : ℝ) ≠ 0), ne_of_gt ht]

private theorem globalCone_add {p q : ℝ[X]}
    (hp : ConversionKernelCoeffNonnegative p) (hq : ConversionKernelCoeffNonnegative q) :
    ConversionKernelCoeffNonnegative (p+q) := by
  intro i; simpa only [coeff_add] using add_nonneg (hp i) (hq i)

private theorem globalCone_cmul {p : ℝ[X]} {c : ℝ}
    (hp : ConversionKernelCoeffNonnegative p) (hc : 0 ≤ c) :
    ConversionKernelCoeffNonnegative (C c*p) := by
  intro i; simpa only [coeff_C_mul] using mul_nonneg hc (hp i)

private theorem globalCone_xmul {p : ℝ[X]}
    (hp : ConversionKernelCoeffNonnegative p) :
    ConversionKernelCoeffNonnegative (X*p) := by
  intro i
  cases i with
  | zero => simp
  | succ i => simpa only [coeff_X_mul] using hp i

private theorem globalCone_eval_nonneg {p : ℝ[X]}
    (hp : ConversionKernelCoeffNonnegative p) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ p.eval r := by
  rw [eval_eq_sum_range]
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hp i) (pow_nonneg hr i)

private theorem globalCone_of_positive_scale {p : ℝ[X]} {d : ℝ}
    (hd : 0 < d) (hp : ConversionKernelCoeffNonnegative (C d*p)) :
    ConversionKernelCoeffNonnegative p := by
  intro i
  have h := hp i
  simp only [coeff_C_mul] at h
  exact nonneg_of_mul_nonneg_right h hd

private theorem globalKernel_eq_quotient (p q K : ℝ[X]) (r : ℝ)
    (hK : (X-C r)*K = C (q.eval r)*(X*p)-C (r*p.eval r)*q) :
    K = quotient p q r := by
  have hfactor : (X-C r : ℝ[X]) ≠ 0 := by
    intro h
    have hh := congrArg (fun f : ℝ[X] => f.coeff 1) h
    simp at hh
  apply mul_left_cancel₀ hfactor
  simpa only [conversionNumerator] using hK.trans (quotient_identity p q r).symm

private theorem globalKernel_links (p q K L : ℝ[X]) (r : ℝ)
    (hK : (X-C r)*K = C (q.eval r)*(X*p)-C (r*p.eval r)*q)
    (hL : (X-C r)*L = C (p.eval r)*q-C (q.eval r)*p) :
    K = C (q.eval r)*p-C r*L ∧ K = C (p.eval r)*q-X*L := by
  have hfactor : (X-C r : ℝ[X]) ≠ 0 := by
    intro h
    have hh := congrArg (fun f : ℝ[X] => f.coeff 1) h
    simp at hh
  constructor
  · apply mul_left_cancel₀ hfactor
    simp only [C_mul] at hK
    linear_combination hK + C r*hL
  · apply mul_left_cancel₀ hfactor
    simp only [C_mul] at hK
    linear_combination hK + X*hL

/-- The coefficient residual after subtracting the leading ratio is itself
positive under the original paired-root recursion. -/
theorem globalConversion_scaled_source_residual (a b α β : ℝ) (p q : ℝ[X])
    (hβ : (4+2*(a+b)*α)*β = 4*α) :
    let B := (a-1)*(b-1)
    let c := 2*(a+b)
    let D := 4+c*α
    let R := p-C α*q
    C D*(nextN a b p q-C β*nextJ a b p q) =
      C (c*α^2*B+D*c*(α+1))*q + C (D*(B+c))*R + C 32*(X*R) := by
  dsimp
  have hscale : C (4+2*(a+b)*α)*C β = C (4*α) := by
    rw [← C_mul, hβ]
  rw [mul_sub, ← mul_assoc, hscale]
  simp only [nextN, nextJ, C_add, C_sub, C_mul, C_pow, C_1, map_ofNat]
  ring

/-- The exact kernel residual has a positive recursive decomposition.
This is the uniform rank-one lower bound, proved algebraically rather
than assuming a partial-fraction or interlacing criterion. -/
theorem globalConversion_scaled_kernel_residual
    (a b r α β : ℝ) (p q K L : ℝ[X])
    (hβ : (4+2*(a+b)*α)*β = 4*α)
    (hleft : K = C (q.eval r)*p-C r*L)
    (hright : K = C (p.eval r)*q-X*L) :
    let B := (a-1)*(b-1)
    let c := 2*(a+b)
    let D := 4+c*α
    let R := p-C α*q
    let H := K-C (α*q.eval r)*q
    C D*(nextPositiveConversionK a b r p q K L -
        C (β*(nextJ a b p q).eval r)*nextJ a b p q) =
      C ((c*α^2*B^2+D*c*B*(α+1))*q.eval r)*q +
      C (64*c*r*R.eval r)*(X*R) +
      C (D*(B^2+c*B)+32*B*r)*H + C (32*B+64*D*r)*(X*H) +
      C (2*c*r*(D*(c-4)-8*α*B))*(X*L) := by
  dsimp
  have hscale : C (4+2*(a+b)*α)*C (β*(nextJ a b p q).eval r) =
      C (4*α*(nextJ a b p q).eval r) := by
    rw [← C_mul]
    congr 1
    calc
      (4+2*(a+b)*α)*(β*(nextJ a b p q).eval r) =
          ((4+2*(a+b)*α)*β)*(nextJ a b p q).eval r := by ring
      _ = _ := by rw [hβ]
  rw [mul_sub, ← mul_assoc, hscale]
  simp only [nextPositiveConversionK, nextJ, eval_add, eval_sub,
    eval_mul, eval_one, eval_ofNat, eval_C, eval_X,
    C_add, C_sub, C_mul, C_pow, C_1, map_ofNat] at hleft hright ⊢
  linear_combination
    (8*(2*(C a+C b))*C α*((C a-1)*(C b-1))*X)*hleft +
    (8*(2*(C a+C b))*C α*((C a-1)*(C b-1))*C r)*hright

theorem positiveConversionKernelBounds_step {p q : ℝ[X]} {m : ℕ}
    (_hp : DensePositive p m) (hq : DensePositive q m)
    {a b r α β : ℝ} (ha : 1 < a) (hb : 1 < b) (hr : 0 < r)
    (hα : 0 < α) (hβ : (4+2*(a+b)*α)*β = 4*α)
    (hcert : PositiveConversionKernelCertificate p q m r)
    (hR : ConversionKernelCoeffNonnegative (p-C α*q))
    (hH : ConversionKernelCoeffNonnegative (quotient p q r-C (α*q.eval r)*q)) :
    ConversionKernelCoeffNonnegative (nextN a b p q-C β*nextJ a b p q) ∧
      ConversionKernelCoeffNonnegative (quotient (nextN a b p q) (nextJ a b p q) r -
        C (β*(nextJ a b p q).eval r)*nextJ a b p q) := by
  obtain ⟨K, L, _hKdense, hL, hKi, hLi⟩ := hcert
  have hKq := globalKernel_eq_quotient p q K r hKi
  rw [← hKq] at hH
  let B := (a-1)*(b-1)
  let c := 2*(a+b)
  let D := 4+c*α
  let R := p-C α*q
  let H := K-C (α*q.eval r)*q
  have hB : 0 < B := mul_pos (by linarith) (by linarith)
  have hc : 4 < c := by dsimp [c]; linarith
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hD : 0 < D := by dsimp [D]; positivity
  have hqnonneg : ConversionKernelCoeffNonnegative q := hq.nonneg
  have hRnonneg : ConversionKernelCoeffNonnegative R := hR
  have hHnonneg : ConversionKernelCoeffNonnegative H := hH
  have hRval : 0 ≤ R.eval r := globalCone_eval_nonneg hRnonneg hr.le
  have hqval : 0 < q.eval r := hq.eval_pos hr
  have hlarge : 0 < c*(c-4)-8*B := by
    have ha2 : 1 < a^2 := by nlinarith [sq_nonneg (a-1)]
    have hb2 : 1 < b^2 := by nlinarith [sq_nonneg (b-1)]
    dsimp [c, B]
    nlinarith
  have hθ : 0 < D*(c-4)-8*α*B := by
    have heq : D*(c-4)-8*α*B = 4*(c-4)+α*(c*(c-4)-8*B) := by dsimp [D]; ring
    rw [heq]
    exact add_pos (mul_pos (by norm_num) (by linarith)) (mul_pos hα hlarge)
  constructor
  · apply globalCone_of_positive_scale hD
    rw [globalConversion_scaled_source_residual a b α β p q hβ]
    apply globalCone_add
    · apply globalCone_add
      · exact globalCone_cmul hqnonneg (by positivity)
      · exact globalCone_cmul hRnonneg (by positivity)
    · exact globalCone_cmul (globalCone_xmul hRnonneg) (by norm_num)
  · have hlinks := globalKernel_links p q K L r hKi hLi
    have hnextKi := nextPositiveConversionK_identity a b r p q K L hKi hLi
    have hnextKq := globalKernel_eq_quotient (nextN a b p q) (nextJ a b p q)
      (nextPositiveConversionK a b r p q K L) r hnextKi
    rw [← hnextKq]
    apply globalCone_of_positive_scale hD
    rw [globalConversion_scaled_kernel_residual a b r α β p q K L hβ hlinks.1 hlinks.2]
    change ConversionKernelCoeffNonnegative
      (C ((c*α^2*B^2+D*c*B*(α+1))*q.eval r)*q +
       C (64*c*r*R.eval r)*(X*R) + C (D*(B^2+c*B)+32*B*r)*H +
       C (32*B+64*D*r)*(X*H) + C (2*c*r*(D*(c-4)-8*α*B))*(X*L))
    apply globalCone_add
    · apply globalCone_add
      · apply globalCone_add
        · apply globalCone_add
          · exact globalCone_cmul hqnonneg (by positivity)
          · exact globalCone_cmul (globalCone_xmul hRnonneg) (by positivity)
        · exact globalCone_cmul hHnonneg (by positivity)
      · exact globalCone_cmul (globalCone_xmul hHnonneg) (by positivity)
    · exact globalCone_cmul (globalCone_xmul hL) (by positivity)

/-- Both rank-one residual bounds hold for the actual paired-root family
at every positive source parameter, including repeated roots. -/
theorem arbitrarySplitPair_global_conversion_residual_bounds
    (m : ℕ) (ξ : ℕ → ℝ) (δ r : ℝ) (hr : 0 < r)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) :
    let p := (arbitrarySplitPair m ξ δ).1
    let q := (arbitrarySplitPair m ξ δ).2
    let α := arbitrarySplitLeadingRatio m ξ δ
    ConversionKernelCoeffNonnegative (p-C α*q) ∧
      ConversionKernelCoeffNonnegative (quotient p q r-C (α*q.eval r)*q) := by
  induction m with
  | zero =>
    let c := (offsetSplitRoot ξ δ 0-1)/2
    have hc : 0 < c := by
      have h := hroot 0 (by omega); dsimp [c]; linarith
    have hαc : arbitrarySplitLeadingRatio 0 ξ δ*c = 1 := by
      dsimp [arbitrarySplitLeadingRatio, arbitrarySplitRootExcess, c]
      simp only [Finset.sum_singleton]
      rw [div_mul_div_cancel₀ (show offsetSplitRoot ξ δ 0-1 ≠ 0 by
        linarith [hroot 0 (by omega)])]
      norm_num
    have hpq : arbitrarySplitPair 0 ξ δ = (1, C c) := rfl
    have hQ : quotient 1 (C c) r = C c := by
      symm
      apply globalKernel_eq_quotient
      simp only [eval_C, eval_one, C_mul, C_1]
      ring
    rw [hpq]
    dsimp only
    constructor
    · intro i
      have heq : (1 : ℝ[X])-C (arbitrarySplitLeadingRatio 0 ξ δ)*C c = 0 := by
        rw [← C_mul, hαc, C_1]; ring
      rw [heq]; simp
    · intro i
      rw [hQ]
      simp only [eval_C]
      have heq : C c-C (arbitrarySplitLeadingRatio 0 ξ δ*c)*C c = 0 := by
        rw [hαc, C_1]; ring
      rw [heq]; simp
  | succ m ih =>
    have hold : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j := by
      intro j hj; exact hroot j (by omega)
    have hdense := arbitrarySplitPair_dense m ξ δ hold
    have hα := arbitrarySplitLeadingRatio_pos m ξ δ hold
    have ht := arbitrarySplitRootExcess_pos m ξ δ hold
    have htnext := arbitrarySplitRootExcess_pos (m+1) ξ δ hroot
    have hβ : (4+2*(offsetSplitRoot ξ δ (2*m+1)+offsetSplitRoot ξ δ (2*m+2))*
        arbitrarySplitLeadingRatio m ξ δ)*arbitrarySplitLeadingRatio (m+1) ξ δ =
        4*arbitrarySplitLeadingRatio m ξ δ := by
      unfold arbitrarySplitLeadingRatio
      rw [arbitrarySplitRootExcess_succ]
      have hn : arbitrarySplitRootExcess m ξ δ + offsetSplitRoot ξ δ (2*m+1) +
          offsetSplitRoot ξ δ (2*m+2) ≠ 0 := by
        rw [← arbitrarySplitRootExcess_succ]
        exact ne_of_gt htnext
      field_simp [ne_of_gt ht, hn]; ring
    have hcert := arbitrarySplitPair_positive_conversion_kernels m ξ δ r hr hold
    have hbounds := ih hold
    exact positiveConversionKernelBounds_step hdense.1 hdense.2
      (hroot (2*m+1) (by omega)) (hroot (2*m+2) (by omega)) hr hα hβ
      hcert hbounds.1 hbounds.2

theorem globalConversion_positive_scalar
    (r ρ S pval qval α : ℝ) (_hr : 0 < r) (hρ : 1 < ρ)
    (hρsq : ρ^2 = 1+8*r) (hS : 1 < S) (hsum : S ≤ 4*r+ρ)
    (hp : 0 < pval) (hq : 0 < qval)
    (hres : 0 < (ρ-1)*pval-2*qval) (hα : α*(S-1) = 2) :
    0 < 4*r*pval-2*qval ∧
      0 < 4*r*α*(qval+pval)-2*qval*(α+1) := by
  have h4r : ρ-1 < 4*r := by
    have hsq : 0 < (ρ-1)^2 := sq_pos_of_pos (by linarith)
    nlinarith
  constructor
  · have hgap := mul_pos (sub_pos.mpr h4r) hp
    nlinarith
  · have h8r : 8*r = ρ^2-1 := by linarith
    have heq : (S-1)*(4*r*α*(qval+pval)-2*qval*(α+1)) =
        (ρ+1)*((ρ-1)*pval-2*qval)+2*qval*(4*r+ρ-S) := by
      have hscaled := congrArg (fun z : ℝ => z*(4*r*(qval+pval)-2*qval)) hα
      linear_combination hscaled + pval*h8r
    have hpositive : 0 < (ρ+1)*((ρ-1)*pval-2*qval)+2*qval*(4*r+ρ-S) :=
      add_pos_of_pos_of_nonneg (mul_pos (by linarith) hres)
        (mul_nonneg (by positivity) (sub_nonneg.mpr hsum))
    rw [← heq] at hpositive
    exact pos_of_mul_pos_right hpositive (sub_nonneg.mpr hS.le)

/-- Part (ii) of the paper's global coefficient-positivity theorem, with
its exact root and sum inequalities. No eventual-in-r or near-coalescent
positivity premise is substituted for those inequalities. -/
theorem arbitrarySplitRawB_dense_of_global_paper_bounds
    (m : ℕ) (ξ : ℕ → ℝ) (δ r : ℝ) (hr : 0 < r)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j)
    (hfar : ∀ j, j ≤ 2*m → offsetSplitRoot ξ δ j < Real.sqrt (1+8*r))
    (hsum : (∑ j ∈ Finset.range (2*m+1), offsetSplitRoot ξ δ j) ≤
      4*r+Real.sqrt (1+8*r)) :
    DensePositive (arbitrarySplitRawB m ξ r δ) m := by
  let p := (arbitrarySplitPair m ξ δ).1
  let q := (arbitrarySplitPair m ξ δ).2
  let α := arbitrarySplitLeadingRatio m ξ δ
  let ρ := Real.sqrt (1+8*r)
  let S := ∑ j ∈ Finset.range (2*m+1), offsetSplitRoot ξ δ j
  let R := p-C α*q
  let H := quotient p q r-C (α*q.eval r)*q
  have hdense := arbitrarySplitPair_dense m ξ δ hroot
  have hp : DensePositive p m := hdense.1
  have hq : DensePositive q m := hdense.2
  have hbnds := arbitrarySplitPair_global_conversion_residual_bounds m ξ δ r hr hroot
  have hR : ConversionKernelCoeffNonnegative R := hbnds.1
  have hH : ConversionKernelCoeffNonnegative H := hbnds.2
  have hρsq : ρ^2 = 1+8*r := Real.sq_sqrt (by positivity)
  have hρnonneg : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ : 1 < ρ := by nlinarith
  have hratio : ratio ρ = r := by unfold ratio; nlinarith
  have hprod : 0 < arbitrarySplitScalarProduct m ξ δ ρ := by
    rw [arbitrarySplitScalarProduct_eq_prod_range]
    apply Finset.prod_pos
    intro j hj
    exact sub_pos.mpr (hfar j (by have hj' := Finset.mem_range.mp hj; omega))
  have hres : 0 < (ρ-1)*p.eval r-2*q.eval r := by
    have hid := arbitrarySplitPair_scalar_identity m ξ δ ρ
    rw [hratio] at hid
    exact hid.symm ▸ hprod
  have ht : 0 < S-1 := arbitrarySplitRootExcess_pos m ξ δ hroot
  have hαT : α*(S-1) = 2 := by
    dsimp [α, arbitrarySplitLeadingRatio, arbitrarySplitRootExcess, S]
    exact div_mul_cancel₀ _ (ne_of_gt (arbitrarySplitRootExcess_pos m ξ δ hroot))
  have hscalars := globalConversion_positive_scalar r ρ S (p.eval r) (q.eval r) α
    hr hρ hρsq (by linarith) hsum (hp.eval_pos hr) (hq.eval_pos hr) hres hαT
  let κ := 4*r*α*(q.eval r+p.eval r)-2*q.eval r*(α+1)
  have hκ : 0 < κ := hscalars.2
  have hBdecomp : arbitrarySplitRawB m ξ r δ =
      C κ*q+C (4*r)*H+C (4*r*p.eval r-2*q.eval r)*R := by
    dsimp [arbitrarySplitRawB, rawB, rawD, κ, H, R, p, q]
    simp only [C_add, C_sub, C_mul, C_1, map_ofNat]
    ring
  constructor
  · intro i hi
    rw [hBdecomp, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul, coeff_C_mul]
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (mul_pos hκ (hq.1 i hi))
        (mul_nonneg (by positivity) (hH i)))
      (mul_nonneg hscalars.1.le (hR i))
  · intro i hi
    exact (raw_support hp hq r i hi).2

end
end PhosphorylationStableCapacity
