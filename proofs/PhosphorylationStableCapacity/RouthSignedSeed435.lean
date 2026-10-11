module
public import proofs.PhosphorylationStableCapacity.RouthHurwitzMinorNecessity435
public import proofs.PhosphorylationStableCapacity.RouthSignedFamilyTopology435
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial Filter
open scoped Topology

private theorem signedSeed_eval_map_real (p : ℝ[X]) (u : ℝ) :
    (p.map (algebraMap ℝ ℂ)).eval (u : ℂ) = ((p.eval u : ℝ) : ℂ) := by
  simpa only [Complex.coe_algebraMap] using
    (Polynomial.eval_map_apply (p := p) (f := algebraMap ℝ ℂ) u)

/-- A real Hurwitz polynomial with positive leading coefficient evaluates
positively on the whole nonnegative real axis. The constant sign is derived
from the proved minor necessity, and IVT excludes any later sign change. -/
theorem hurwitzPolynomial_eval_pos_of_nonneg
    (q : ℝ[X]) (hleading : 0 < q.leadingCoeff)
    (hstable : ∀ z : ℂ, (q.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0)
    (x : ℝ) (hx : 0 ≤ x) : 0 < q.eval x := by
  have hzero : 0 < q.eval 0 := by
    simpa only [← Polynomial.coeff_zero_eq_eval_zero] using
      hurwitzPolynomial_constantCoeff_pos q hleading hstable
  by_contra hpos
  have hxvalue : q.eval x ≤ 0 := le_of_not_gt hpos
  obtain ⟨v, hv, hroot⟩ := intermediate_value_Icc' hx q.continuous.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (q.eval x) (q.eval 0) from ⟨hxvalue, hzero.le⟩)
  have hcomplexroot : (q.map (algebraMap ℝ ℂ)).eval (v : ℂ) = 0 := by
    simp only [signedSeed_eval_map_real, hroot, Complex.ofReal_zero]
  have hnegative : v < 0 := by
    simpa only [Complex.ofReal_re] using hstable (v : ℂ) hcomplexroot
  exact (not_lt_of_ge hv.1) hnegative

/-- The neutral boundary polynomial X*q has strictly positive evaluation
at every positive real bracket endpoint. These signs supply the arbitrarily
small upper brackets in the one-sided positive-root limit argument. -/
theorem neutral_hurwitz_factor_positive_brackets
    (p q : ℝ[X]) (hfactor : p = X*q) (hleading : 0 < q.leadingCoeff)
    (hstable : ∀ z : ℂ, (q.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0) :
    ∀ x : ℝ, 0 < x → 0 < p.eval x := by
  intro x hx
  rw [hfactor, eval_mul, eval_X]
  exact mul_pos hx (hurwitzPolynomial_eval_pos_of_nonneg q hleading hstable x hx.le)

/-- Once the literal boundary tail is proved Hurwitz and the real root
tends to that boundary root, small positive selected roots give actual
one-positive-root/Hurwitz-tail factorizations. All polynomial witnesses
are the original family's literal deflations. -/
theorem signed_factorization_eventually_of_boundary_tail
    {ι : Type*} (l : Filter ι) (P : ι → ℂ[X]) (p₀ : ℂ[X]) (d : ℕ) (hd : 1 ≤ d)
    (hmonic : ∀ i, (P i).Monic) (hdegree : ∀ i, (P i).natDegree = d)
    (hdegree₀ : p₀.natDegree = d) (hmonic₀ : p₀.Monic)
    (hcoeff : ∀ n ≤ d, Tendsto (fun i => (P i).coeff n) l (𝓝 (p₀.coeff n)))
    (u : ι → ℝ) (u₀ : ℝ) (hu : Tendsto u l (𝓝 u₀))
    (hroot : ∀ i, (P i).eval (u i : ℂ) = 0)
    (hupos : ∀ᶠ i in l, 0 < u i)
    (hroot₀ : p₀.eval (u₀ : ℂ) = 0)
    (htail₀ : ∀ z : ℂ, (p₀ /ₘ (X-C (u₀ : ℂ))).eval z = 0 → z.re < 0) :
    ∀ᶠ i in l, PositiveRealRootHurwitzFactorization d (P i) := by
  have htail := linear_deflation_hurwitz_eventually_of_tendsto l P p₀ d
    hdegree hdegree₀ hcoeff u u₀ hu hmonic₀ hroot₀ htail₀
  filter_upwards [htail, hupos] with i hi hpositive
  obtain ⟨hq, hqdegree, hfactor⟩ := monic_linear_deflation_factorization
    (P i) (hmonic i) d (hdegree i) (u i) (hroot i)
  refine ⟨hd, u i, hpositive, (P i) /ₘ (X-C (u i : ℂ)), hq, hqdegree, ?_, hfactor⟩
  intro z hz
  exact hi z (Polynomial.isRoot_of_mem_roots hz)

end
end PhosphorylationStableCapacity
