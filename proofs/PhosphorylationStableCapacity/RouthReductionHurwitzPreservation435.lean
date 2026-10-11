module
public import proofs.PhosphorylationStableCapacity.RouthReductionImaginaryAxis435
public import proofs.PhosphorylationStableCapacity.RouthHurwitzFirstPivot435
public import proofs.PhosphorylationStableCapacity.HurwitzPolynomialNoCrossing435
public import proofs.PhosphorylationStableCapacity.HurwitzPolynomialReflection435
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial Filter
open scoped Topology

noncomputable section

/-- A genuine Routh homotopy preserves Hurwitz stability before its
degree-dropping endpoint. This specializes the proved monic no-crossing
theorem on the connected interval t < a0/a1. -/
theorem routhPolynomialHomotopy_hurwitz_interior
    (d : ℕ) (hd : 0 < d) (p : ℝ[X]) (hdegree : p.natDegree ≤ d)
    (hleading : 0 < p.coeff d) (hpivot : 0 < p.coeff (d-1))
    (hstable : ∀ z : ℂ,
      (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0)
    (t : ℝ) (ht : t < p.coeff d / p.coeff (d-1)) :
    ∀ z : ℂ, ((routhPolynomialHomotopy d p t).map
      (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0 := by
  classical
  let c := p.coeff d / p.coeff (d-1)
  let T := Set.Iio c
  let : PreconnectedSpace T := Subtype.preconnectedSpace isPreconnected_Iio
  let H : T → ℝ[X] := fun u => routhPolynomialHomotopy d p u.val
  let g : T → ℝ := fun u => p.coeff d-u.val*p.coeff (d-1)
  let M : T → ℂ[X] := fun u => Polynomial.C ((g u : ℂ)⁻¹) *
    (H u).map (algebraMap ℝ ℂ)
  have hspec (u : T) : (H u).natDegree = d ∧
      (H u).leadingCoeff = g u ∧ 0 < (H u).leadingCoeff :=
    routhPolynomialHomotopy_interior_degree_and_leading
      d hd p hdegree hpivot u.val u.property
  have hgpos (u : T) : 0 < g u := by
    rw [← (hspec u).2.1]
    exact (hspec u).2.2
  have hgzero (u : T) : (g u : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (hgpos u))
  have hmonic (u : T) : (M u).Monic := by
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    have hlead : ((H u).map (algebraMap ℝ ℂ)).leadingCoeff = (g u : ℂ) := by
      rw [Polynomial.leadingCoeff_map, (hspec u).2.1]
      rfl
    rw [hlead]
    exact inv_mul_cancel₀ (hgzero u)
  have hMdegree (u : T) : (M u).natDegree = d := by
    rw [Polynomial.natDegree_C_mul_of_isUnit
      (isUnit_iff_ne_zero.mpr (inv_ne_zero (hgzero u))), Polynomial.natDegree_map]
    exact (hspec u).1
  have hgcont : Continuous g :=
    continuous_const.sub (continuous_subtype_val.mul continuous_const)
  have hinvcont : Continuous (fun u : T => (g u : ℂ)⁻¹) :=
    (Complex.continuous_ofReal.comp hgcont).inv₀ hgzero
  have hHcoeff (i : ℕ) : Continuous (fun u : T => (H u).coeff i) := by
    exact (routhPolynomialHomotopy_coeff_continuous d i p).comp continuous_subtype_val
  have hMcoeff (i : ℕ) (_hi : i ≤ d) :
      Continuous (fun u : T => (M u).coeff i) := by
    simp only [M, Polynomial.coeff_C_mul, Polynomial.coeff_map]
    exact hinvcont.mul (Complex.continuous_ofReal.comp (hHcoeff i))
  have hrootiff (u : T) (z : ℂ) :
      (M u).eval z = 0 ↔ ((H u).map (algebraMap ℝ ℂ)).eval z = 0 := by
    simp [M, Polynomial.eval_mul, hgzero u]
  have haxis (u : T) (z : ℂ) (hz : z.re = 0) : (M u).eval z ≠ 0 := by
    intro hroot
    exact routhPolynomialHomotopy_no_imaginary_axis_roots d p hstable
      u.val z hz ((hrootiff u z).mp hroot)
  have hcpos : 0 < c := div_pos hleading hpivot
  let u₀ : T := ⟨0, hcpos⟩
  have hstart (z : ℂ) (hz : (M u₀).eval z = 0) : z.re < 0 := by
    apply hstable z
    have h := (hrootiff u₀ z).mp hz
    simpa [H, u₀, routhPolynomialHomotopy] using h
  have hall := monic_fixed_degree_hurwitz_of_no_axis
    M d hmonic hMdegree hMcoeff haxis u₀ hstart
  intro z hz
  exact hall ⟨t, ht⟩ z ((hrootiff ⟨t, ht⟩ z).mpr hz)

/-- Reflection at the fixed declared degree controls the endpoint where
the original homotopy loses a degree. Its constant coefficient stays
nonzero, so every normalized reflection has degree d. The endpoint
reflection may have a zero root; only its nonzero reciprocal roots are
used to recover the roots of the reduced polynomial. -/
theorem routhReducedPolynomial_hurwitz_of_degree_bound
    (d : ℕ) (hd : 0 < d) (p : ℝ[X]) (hdegree : p.natDegree ≤ d)
    (hleading : 0 < p.coeff d) (hpivot : 0 < p.coeff (d-1))
    (hstable : ∀ z : ℂ,
      (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0) :
    ∀ z : ℂ, ((routhReducedPolynomial d p).map
      (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0 := by
  classical
  let c := p.coeff d / p.coeff (d-1)
  let b : ℂ := (p.coeff 0 : ℂ)
  let H : ℝ → ℂ[X] := fun t =>
    (routhPolynomialHomotopy d p t).map (algebraMap ℝ ℂ)
  let R : ℝ → ℂ[X] := fun t => Polynomial.C b⁻¹ * (H t).reflect d
  have hpzero : p.coeff 0 ≠ 0 := by
    intro hz
    have h := hstable 0 (by simp only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map, hz, map_zero])
    simp at h
  have hb : b ≠ 0 := by
    change (p.coeff 0 : ℂ) ≠ 0
    exact_mod_cast hpzero
  have hHdegree (t : ℝ) : (H t).natDegree ≤ d := by
    simpa only [H, Polynomial.natDegree_map] using
      routhPolynomialHomotopy_natDegree_le d p hdegree t
  have hHconstant (t : ℝ) : (H t).coeff 0 = b := by
    simp [H, b, Polynomial.coeff_map, routhPolynomialHomotopy_coeff_zero]
  have hRspec (t : ℝ) : (R t).Monic ∧ (R t).natDegree = d := by
    have h := normalized_fixed_reflection_monic_and_degree
      (H t) d (hHdegree t) (by rw [hHconstant]; exact hb)
    simpa only [hHconstant, R] using h
  have hRcoeff (i : ℕ) (_hi : i ≤ d) :
      Continuous (fun t : ℝ => (R t).coeff i) := by
    simp only [R, Polynomial.coeff_C_mul, Polynomial.coeff_reflect,
      H, Polynomial.coeff_map]
    exact continuous_const.mul (Complex.continuous_ofReal.comp
      (routhPolynomialHomotopy_coeff_continuous d (Polynomial.revAt d i) p))
  have hRrootiff (t : ℝ) (z : ℂ) :
      (R t).eval z = 0 ↔ ((H t).reflect d).eval z = 0 := by
    simp [R, Polynomial.eval_mul, hb]
  have hRleft : ∀ᶠ t in 𝓝[<] c,
      (R t).Monic ∧ (R t).natDegree = d ∧
        ∀ z ∈ (R t).roots, z.re ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    refine ⟨(hRspec t).1, (hRspec t).2, ?_⟩
    have hdeg : (H t).natDegree = d := by
      rw [Polynomial.natDegree_map]
      exact (routhPolynomialHomotopy_interior_degree_and_leading
        d hd p hdegree hpivot t ht).1
    have hstableH : ∀ z : ℂ, (H t).eval z = 0 → z.re < 0 :=
      routhPolynomialHomotopy_hurwitz_interior
        d hd p hdegree hleading hpivot hstable t ht
    intro z hz
    have hroot := (hRrootiff t z).mp (Polynomial.isRoot_of_mem_roots hz)
    exact (fixed_reflection_hurwitz_of_exact_degree
      (H t) d hdeg hstableH z hroot).le
  have hRlimit (z : ℂ) :
      Tendsto (fun t : ℝ => (R t).eval z) (𝓝[<] c) (𝓝 ((R c).eval z)) :=
    ((fixed_degree_polynomial_eval_continuous R d
      (fun t => (hRspec t).2.le) hRcoeff z).tendsto c).mono_left
      nhdsWithin_le_nhds
  have hclosed := evaluation_limit_roots_re_nonpos
    (𝓝[<] c) R (R c) d hRleft hRlimit
  have ha0 : routhDescendingCoeff d p 0 = p.coeff d := by
    simp [routhDescendingCoeff]
  have ha1 : routhDescendingCoeff d p 1 = p.coeff (d-1) := by
    simp [routhDescendingCoeff, show (1 : ℤ) ≤ (d : ℤ) by omega]
  have hpivot' : routhDescendingCoeff d p 1 ≠ 0 := by
    rw [ha1]
    exact ne_of_gt hpivot
  have hqhom : routhReducedPolynomial d p = routhPolynomialHomotopy d p c := by
    simpa only [ha0, ha1, c] using
      routhReducedPolynomial_eq_homotopy d hd p hdegree hpivot'
  intro z hroot
  have hrootH : (H c).eval z = 0 := by
    simpa only [hqhom, H] using hroot
  have hz : z ≠ 0 := by
    intro hz0
    have hzero : b = 0 := by
      simpa only [hz0, ← Polynomial.coeff_zero_eq_eval_zero, hHconstant] using hrootH
    exact hb hzero
  have hreflectroot : ((H c).reflect d).eval z⁻¹ = 0 :=
    (fixed_reflection_eval_zero_iff (H c) d (hHdegree c)
      z⁻¹ (inv_ne_zero hz)).mpr (by simpa only [inv_inv] using hrootH)
  have hleftinverse : (z⁻¹).re ≤ 0 :=
    hclosed z⁻¹ ((hRrootiff c z⁻¹).mpr hreflectroot)
  have hleft : z.re ≤ 0 := (complex_inv_re_nonpos_iff z).mp hleftinverse
  exact lt_of_le_of_ne hleft (fun heq =>
    routhReducedPolynomial_no_imaginary_axis_roots
      d hd p hdegree hpivot' hstable z heq hroot)

/-- Every positive-leading nonconstant real Hurwitz polynomial has a
Hurwitz Routh reduction. First-pivot positivity is proved from its root
sum, and endpoint preservation follows from the genuine no-crossing and
fixed-degree reflection arguments above. No Routh criterion is assumed. -/
theorem routhReducedPolynomial_hurwitz
    (p : ℝ[X]) (hdegree : 0 < p.natDegree)
    (hleading : 0 < p.leadingCoeff)
    (hstable : ∀ z : ℂ,
      (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0) :
    ∀ z : ℂ, ((routhReducedPolynomial p.natDegree p).map
      (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0 := by
  have htop : 0 < p.coeff p.natDegree := by
    simpa only [Polynomial.coeff_natDegree] using hleading
  have hpivot : 0 < p.coeff (p.natDegree-1) := by
    simpa only [Polynomial.nextCoeff_of_natDegree_pos hdegree] using
      hurwitzPolynomial_nextCoeff_pos p hdegree hleading hstable
  exact routhReducedPolynomial_hurwitz_of_degree_bound
    p.natDegree hdegree p le_rfl htop hpivot hstable

end
end PhosphorylationStableCapacity
