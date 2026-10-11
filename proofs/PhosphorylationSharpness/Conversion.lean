module
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Tactic.LinearCombination
public import proofs.PhosphorylationSharpness.Recurrence

@[expose] public section

namespace PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology

theorem DensePositive.degree_eq {p : ℝ[X]} {m : ℕ} (hp : DensePositive p m) :
    p.natDegree = m :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr hp.2)
    (ne_of_gt (hp.1 m le_rfl))

theorem DensePositive.eval_pos {p : ℝ[X]} {m : ℕ} (hp : DensePositive p m)
    {u : ℝ} (hu : 0 < u) : 0 < p.eval u := by
  rw [eval_eq_sum_range]
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (hp.nonneg i) (pow_nonneg hu.le _)
  · refine ⟨0, by simp, ?_⟩
    simpa using hp.1 0 (by omega)

theorem DensePositive.scaled_limit {p : ℝ[X]} {m : ℕ} (hp : DensePositive p m) :
    Tendsto (fun r : ℝ => p.eval r / r^m) atTop (𝓝 (p.coeff m)) := by
  have hp0 : p ≠ 0 := by
    intro h
    have := hp.1 0 (by omega)
    simp [h] at this
  have hd : p.degree = (X^m : ℝ[X]).degree := by
    rw [degree_eq_natDegree hp0, hp.degree_eq, degree_X_pow]
  have h := p.div_tendsto_atTop_leadingCoeff_div_of_degree_eq (X^m) hd
  simpa [leadingCoeff, hp.degree_eq] using h

def conversionNumerator (p q : ℝ[X]) (r : ℝ) : ℝ[X] :=
  C (q.eval r)*(X*p) - C (r*p.eval r)*q

def quotient (p q : ℝ[X]) (r : ℝ) : ℝ[X] :=
  conversionNumerator p q r /ₘ (X-C r)

theorem quotient_identity (p q : ℝ[X]) (r : ℝ) :
    (X-C r)*quotient p q r = conversionNumerator p q r := by
  apply mul_divByMonic_eq_iff_isRoot.mpr
  simp [IsRoot, conversionNumerator]
  ring

theorem quotient_zero (p q : ℝ[X]) {r : ℝ} (hr : r ≠ 0) :
    (quotient p q r).coeff 0 = p.eval r*q.coeff 0 := by
  have h := congrArg (fun f : ℝ[X] => f.coeff 0) (quotient_identity p q r)
  simp only [sub_mul, coeff_sub, coeff_X_mul_zero, coeff_C_mul,
    conversionNumerator] at h
  have hh : r*((quotient p q r).coeff 0-p.eval r*q.coeff 0)=0 := by linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hr)

theorem quotient_succ (p q : ℝ[X]) {r : ℝ} (hr : r ≠ 0) (i : ℕ) :
    (quotient p q r).coeff (i+1) = p.eval r*q.coeff (i+1) +
      ((quotient p q r).coeff i-q.eval r*p.coeff i)/r := by
  have h := coeff_divByMonic_X_sub_C_rec (conversionNumerator p q r) r i
  change (quotient p q r).coeff i = _ + r*(quotient p q r).coeff (i+1) at h
  simp only [conversionNumerator, coeff_sub, coeff_C_mul, coeff_X_mul] at h
  field_simp
  nlinarith [h]

theorem quotient_degree {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m) (r : ℝ) :
    (quotient p q r).natDegree ≤ m := by
  have hd : (conversionNumerator p q r).natDegree ≤ m+1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    cases i with
    | zero => omega
    | succ i =>
      simp only [conversionNumerator, coeff_sub, coeff_C_mul, coeff_X_mul]
      rw [hp.2 i (by omega), hq.2 (i+1) (by omega)]
      ring
  rw [quotient, natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C]
  omega

theorem quotient_scaled_limit {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m) (i : ℕ) :
    Tendsto (fun r : ℝ => (quotient p q r).coeff i / r^m) atTop
      (𝓝 (p.coeff m*q.coeff i)) := by
  induction i with
  | zero =>
    have h := hp.scaled_limit.mul_const (q.coeff 0)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    rw [quotient_zero p q (ne_of_gt hr)]
    ring
  | succ i ih =>
    have h := (hp.scaled_limit.mul_const (q.coeff (i+1))).add
      ((ih.sub (hq.scaled_limit.mul_const (p.coeff i))).mul tendsto_inv_atTop_zero)
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    rw [quotient_succ p q (ne_of_gt hr)]
    field_simp

def rawD (p q : ℝ[X]) (r : ℝ) : ℝ[X] := C 4*quotient p q r

def rawB (p q : ℝ[X]) (r : ℝ) : ℝ[X] :=
  C r*rawD p q r + C (4*r*p.eval r-2*q.eval r)*p - C (2*q.eval r)*q

theorem rawD_scaled_limit {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m) (i : ℕ) :
    Tendsto (fun r : ℝ => (rawD p q r).coeff i/r^m) atTop
      (𝓝 (4*p.coeff m*q.coeff i)) := by
  have h := (quotient_scaled_limit hp hq i).const_mul 4
  convert h using 1 <;> simp [rawD, mul_div_assoc, mul_assoc]

theorem rawB_scaled_limit {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m) (i : ℕ) :
    Tendsto (fun r : ℝ => (rawB p q r).coeff i/r^(m+1)) atTop
      (𝓝 (4*p.coeff m*(q.coeff i+p.coeff i))) := by
  have h := ((rawD_scaled_limit hp hq i).add
      ((hp.scaled_limit.mul_const (p.coeff i)).const_mul 4)).sub
    (((hq.scaled_limit.mul_const (p.coeff i+q.coeff i)).const_mul 2).mul
      tendsto_inv_atTop_zero)
  have he : 4*p.coeff m*q.coeff i+4*(p.coeff m*p.coeff i)-
      2*(q.coeff m*(p.coeff i+q.coeff i))*0 =
      4*p.coeff m*(q.coeff i+p.coeff i) := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
  simp only [rawB, rawD, coeff_add, coeff_sub, coeff_C_mul, pow_succ]
  field_simp
  ring

theorem raw_support {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m) (r : ℝ)
    (i : ℕ) (hi : m < i) :
    (rawD p q r).coeff i=0 ∧ (rawB p q r).coeff i=0 := by
  have hh : (quotient p q r).coeff i=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (quotient_degree hp hq r) hi)
  simp only [rawD, rawB, coeff_sub, coeff_add, coeff_C_mul, hh, hp.2 i hi, hq.2 i hi]
  constructor <;> ring

theorem conversion_eventually_positive {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m) :
    ∀ᶠ r : ℝ in atTop, DensePositive (rawD p q r) m ∧ DensePositive (rawB p q r) m := by
  have hd (i : Fin (m+1)) : ∀ᶠ r : ℝ in atTop, 0 < (rawD p q r).coeff i := by
    have hl := rawD_scaled_limit hp hq i
    have hz : 0 < 4*p.coeff m*q.coeff i := by
      exact mul_pos (mul_pos (by norm_num) (hp.1 m le_rfl)) (hq.1 i (by omega))
    filter_upwards [hl.eventually (Ioi_mem_nhds hz), eventually_gt_atTop (0:ℝ)] with r h hr
    exact (div_pos_iff_of_pos_right (pow_pos hr m)).mp h
  have hb (i : Fin (m+1)) : ∀ᶠ r : ℝ in atTop, 0 < (rawB p q r).coeff i := by
    have hl := rawB_scaled_limit hp hq i
    have hz : 0 < 4*p.coeff m*(q.coeff i+p.coeff i) := by
      exact mul_pos (mul_pos (by norm_num) (hp.1 m le_rfl))
        (add_pos (hq.1 i (by omega)) (hp.1 i (by omega)))
    filter_upwards [hl.eventually (Ioi_mem_nhds hz), eventually_gt_atTop (0:ℝ)] with r h hr
    exact (div_pos_iff_of_pos_right (pow_pos hr (m+1))).mp h
  have hdall := Filter.eventually_all.mpr hd
  have hball := Filter.eventually_all.mpr hb
  filter_upwards [hdall, hball] with r hd hb
  constructor
  · exact ⟨fun i hi => hd ⟨i, by omega⟩, fun i hi => (raw_support hp hq r i hi).1⟩
  · exact ⟨fun i hi => hb ⟨i, by omega⟩, fun i hi => (raw_support hp hq r i hi).2⟩

theorem conversion_root (p q : ℝ[X]) (r x : ℝ)
    (hx : (x-1)*p.eval (ratio x)-2*q.eval (ratio x)=0) :
    (x-1)*((rawB p q r).eval (ratio x)-r*(rawD p q r).eval (ratio x)) =
      2*(r-ratio x)*(rawD p q r).eval (ratio x) := by
  have h := congrArg (fun z : ℝ[X] => z.eval (ratio x)) (quotient_identity p q r)
  simp only [eval_mul, eval_sub, eval_X, eval_C, conversionNumerator] at h
  simp only [rawB, rawD, eval_add, eval_sub, eval_mul, eval_C]
  dsimp [ratio] at h hx ⊢
  linear_combination 8*h + (q.eval r*x+4*r*p.eval r-q.eval r)*hx

end
end PhosphorylationSharpness
