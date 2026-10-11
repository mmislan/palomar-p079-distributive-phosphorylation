module
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open Set Filter

/-- The certified quadratic energy bounds imply the manuscript's explicit
Euclidean recovery envelope on any forward interval where the certificate
applies. The finite benchmark supplies the energy and derivative premises. -/
theorem quantitative_recovery_envelope
    (g g' d : ℝ → ℝ) (p c M ρ T : ℝ)
    (hp : 0 < p) (hc : 0 < c) (hM : 0 < M) (hρ : 0 < ρ)
    (hcont : ContinuousOn g (Icc (0 : ℝ) T))
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt g (g' t) (Ici t) t)
    (hslope : ∀ t ∈ Ico (0 : ℝ) T, g' t ≤ -(c/M) * g t)
    (hinit : g 0 ≤ p * (ρ/2)^2)
    (hlower : ∀ t ∈ Icc (0 : ℝ) T, p * (d t)^2 ≤ g t)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ d t) :
    ∀ t ∈ Icc (0 : ℝ) T,
      d t ≤ (ρ/2) * Real.exp (-(c/(2*M))*t) := by
  have hG := le_gronwallBound_of_liminf_deriv_right_le
    (δ := g 0) (K := -(c/M)) (ε := 0)
    (a := 0) (b := T) (f := g) (f' := g') hcont
    (fun t ht r hr => (hderiv t ht).liminf_right_slope_le hr)
    (le_refl (g 0)) (by
      intro t ht
      simpa only [neg_mul, add_zero] using hslope t ht)
  intro t ht
  have hdecay : g t ≤ g 0 * Real.exp (-(c/M)*t) := by
    simpa only [gronwallBound_ε0, sub_zero] using hG t ht
  let E := Real.exp (-(c/(2*M))*t)
  have hE : 0 < E := Real.exp_pos _
  have hsplit : Real.exp (-(c/M)*t) = E^2 := by
    dsimp only [E]
    rw [sq, ← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hsplit] at hdecay
  have hbound := mul_le_mul_of_nonneg_right hinit (sq_nonneg E)
  have hsq : (d t)^2 ≤ ((ρ/2)*E)^2 := by
    have h := (hlower t ht).trans (hdecay.trans hbound)
    have heq : p * (ρ/2)^2 * E^2 = p * (((ρ/2)*E)^2) := by ring
    rw [heq] at h
    exact le_of_mul_le_mul_left h hp
  exact (sq_le_sq₀ (hd t ht) (mul_nonneg (by linarith) hE.le)).mp hsq

/-- The explicit model time `6M/c` reduces the exponential envelope by
more than tenfold. This proves the conversion to the paper's `60M/c`
seconds when the declared time unit is ten seconds. -/
theorem recovery_envelope_tenfold_at_certified_time
    (c M T : ℝ) (hc : 0 < c) (hM : 0 < M) (hT : 6*M/c ≤ T) :
    Real.exp (-(c/(2*M))*T) < (1:ℝ)/10 := by
  have htime : 6*M ≤ T*c := (div_le_iff₀ hc).mp hT
  have hprod : 3 ≤ (c/(2*M))*T := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0 < 2*M)).mpr
    nlinarith
  have hseries := Real.sum_le_exp_of_nonneg (x := (3:ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hseries
  have hexp : Real.exp (-3) < (1:ℝ)/10 := by
    rw [Real.exp_neg, inv_lt_iff_one_lt_mul₀ (Real.exp_pos 3)]
    nlinarith
  exact (Real.exp_le_exp.mpr (by linarith : -(c/(2*M))*T ≤ -3)).trans_lt hexp

end
end PhosphorylationStableCapacity
