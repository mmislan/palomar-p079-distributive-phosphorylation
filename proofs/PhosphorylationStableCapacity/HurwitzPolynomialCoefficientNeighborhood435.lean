module
public import proofs.PhosphorylationStableCapacity.HurwitzPolynomialRightHalfPlaneBound435
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

open Polynomial Filter
open scoped Topology BigOperators

noncomputable section

private theorem left_root_factor_uniform_margin (w : ℂ) (hw : w.re < 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.re →
      c * (1 + ‖z‖) ≤ ‖z-w‖ := by
  let a : ℝ := -w.re
  have ha : 0 < a := neg_pos.mpr hw
  have hden : 0 < 1 + ‖w‖ + a := by positivity
  refine ⟨a / (1 + ‖w‖ + a), div_pos ha hden, ?_⟩
  intro z hz
  have hdist : a ≤ ‖z-w‖ := by
    calc
      a ≤ (z-w).re := by simp only [Complex.sub_re]; dsimp [a]; linarith
      _ ≤ ‖z-w‖ := Complex.re_le_norm _
  have htriangle : ‖z‖ ≤ ‖z-w‖ + ‖w‖ := by
    simpa only [sub_add_cancel] using norm_add_le (z-w) w
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  have hmul := mul_le_mul_of_nonneg_left htriangle ha.le
  have hbase := mul_le_mul_of_nonneg_right hdist
    (show 0 ≤ 1 + ‖w‖ by positivity)
  nlinarith

private theorem root_product_uniform_margin (s : Multiset ℂ)
    (hs : ∀ w ∈ s, w.re < 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.re →
      c * (1 + ‖z‖) ^ s.card ≤ ‖(s.map (fun w => z-w)).prod‖ := by
  revert hs
  induction s using Multiset.induction_on with
  | empty =>
      intro _
      exact ⟨1, zero_lt_one, by simp⟩
  | cons w s ih =>
      intro hs
      obtain ⟨cw, hcw, hw⟩ := left_root_factor_uniform_margin w (hs w (by simp))
      obtain ⟨cs, hcs, hrest⟩ := ih (fun u hu => hs u (by simp [hu]))
      refine ⟨cw*cs, mul_pos hcw hcs, ?_⟩
      intro z hz
      calc
        (cw*cs)*(1+‖z‖)^(w ::ₘ s).card =
            (cw*(1+‖z‖))*(cs*(1+‖z‖)^s.card) := by
          rw [Multiset.card_cons, pow_succ]
          ring
        _ ≤ ‖z-w‖ * ‖(s.map (fun u => z-u)).prod‖ :=
          mul_le_mul (hw z hz) (hrest z hz) (by positivity) (norm_nonneg _)
        _ = ‖((w ::ₘ s).map (fun u => z-u)).prod‖ := by
          simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]

/-- A strict Hurwitz polynomial has a positive uniform evaluation margin
on the entire closed right half-plane, including points of unbounded norm. -/
theorem monic_hurwitz_uniform_evaluation_margin (p : ℂ[X]) (hp : p.Monic)
    (hroots : ∀ w ∈ p.roots, w.re < 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℂ, 0 ≤ z.re →
      c * (1 + ‖z‖) ^ p.natDegree ≤ ‖p.eval z‖ := by
  have hsplit : p.Splits := IsAlgClosed.splits p
  obtain ⟨c, hc, hbound⟩ := root_product_uniform_margin p.roots hroots
  refine ⟨c, hc, ?_⟩
  intro z hz
  rw [hsplit.eval_eq_prod_roots_of_monic hp z]
  simpa only [hsplit.natDegree_eq_card_roots] using hbound z hz

/-- A coefficient bound controls evaluations uniformly after division by
the natural degree-dependent growth factor. -/
theorem polynomial_eval_norm_le_of_coeff_bound (p : ℂ[X]) (d : ℕ)
    (hd : p.natDegree ≤ d) (ε : ℝ) (hε : 0 ≤ ε)
    (hcoeff : ∀ i ≤ d, ‖p.coeff i‖ ≤ ε) (z : ℂ) :
    ‖p.eval z‖ ≤ ((d+1 : ℕ) : ℝ) * ε * (1+‖z‖)^d := by
  rw [p.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hd) z]
  calc
    ‖∑ i ∈ Finset.range (d+1), p.coeff i * z^i‖ ≤
        ∑ i ∈ Finset.range (d+1), ‖p.coeff i * z^i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (d+1), ε*(1+‖z‖)^d := by
      apply Finset.sum_le_sum
      intro i hi
      have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hpow : ‖z‖^i ≤ (1+‖z‖)^d :=
        (pow_le_pow_left₀ (norm_nonneg z) (by linarith) i).trans
          (pow_le_pow_right₀ (by linarith [norm_nonneg z]) hid)
      rw [norm_mul, norm_pow]
      exact mul_le_mul (hcoeff i hid) hpow (by positivity) hε
    _ = ((d+1 : ℕ) : ℝ)*ε*(1+‖z‖)^d := by simp; ring

/-- Explicit coefficient neighborhoods preserve strict Hurwitz stability.
Perturbed polynomials may have smaller degree; no simple-root hypothesis
or pre-existing Routh criterion is used. -/
theorem monic_hurwitz_coefficient_neighborhood (p : ℂ[X]) (hp : p.Monic)
    (hroots : ∀ w ∈ p.roots, w.re < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℂ[X], q.natDegree ≤ p.natDegree →
      (∀ i ≤ p.natDegree, ‖q.coeff i-p.coeff i‖ ≤ ε) →
      ∀ z : ℂ, q.eval z = 0 → z.re < 0 := by
  obtain ⟨c, hc, hmargin⟩ := monic_hurwitz_uniform_evaluation_margin p hp hroots
  let N : ℝ := ((p.natDegree+1 : ℕ) : ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  refine ⟨c/(2*N), div_pos hc (mul_pos (by norm_num) hN), ?_⟩
  intro q hq hcoeff z hz
  by_contra hneg
  have hright : 0 ≤ z.re := le_of_not_gt hneg
  have hd : (q-p).natDegree ≤ p.natDegree :=
    (natDegree_sub_le q p).trans (max_le hq le_rfl)
  have hbound := polynomial_eval_norm_le_of_coeff_bound (q-p) p.natDegree hd
    (c/(2*N)) (by positivity) (by simpa only [coeff_sub] using hcoeff) z
  have heval : ‖(q-p).eval z‖ = ‖p.eval z‖ := by
    simp only [eval_sub, hz, zero_sub, norm_neg]
  rw [heval] at hbound
  have hscale : N*(c/(2*N)) = c/2 := by field_simp [hN.ne']
  change ‖p.eval z‖ ≤ N*(c/(2*N))*(1+‖z‖)^p.natDegree at hbound
  rw [hscale] at hbound
  have hgrowth : 0 < (1+‖z‖)^p.natDegree := by positivity
  have hprod : 0 < c*(1+‖z‖)^p.natDegree := mul_pos hc hgrowth
  have hlow := hmargin z hright
  nlinarith

end
end PhosphorylationStableCapacity
