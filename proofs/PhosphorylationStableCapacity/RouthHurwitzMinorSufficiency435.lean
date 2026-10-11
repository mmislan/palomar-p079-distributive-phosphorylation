module
public import proofs.PhosphorylationStableCapacity.RouthHurwitzMinorNecessity435
public import proofs.PhosphorylationStableCapacity.RouthParityRealPart435

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

open Polynomial
open scoped ComplexConjugate

noncomputable section

/-- The component with the same parity as the declared leading degree. -/
def routhSameParity (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  p - routhOppositeParity d p

/-- Positive-real parity ratio in the open right half-plane. This
auxiliary induction invariant is stronger than mere root exclusion. -/
def RouthParityPositiveReal (d : ℕ) (p : ℝ[X]) : Prop :=
  ∀ z : ℂ, 0 < z.re →
    ((routhSameParity d p).map (algebraMap ℝ ℂ)).eval z ≠ 0 ∧
      0 ≤ (((routhOppositeParity d p).map (algebraMap ℝ ℂ)).eval z /
        ((routhSameParity d p).map (algebraMap ℝ ℂ)).eval z).re

theorem routhSameParity_next_homotopy
    (d : ℕ) (hd : 0 < d) (p : ℝ[X]) (t : ℝ) :
    routhSameParity (d-1) (routhPolynomialHomotopy d p t) =
      routhOppositeParity d p := by
  ext n
  simp only [routhSameParity, Polynomial.coeff_sub, routhOppositeParity_coeff]
  cases n with
  | zero =>
      rw [routhPolynomialHomotopy_coeff_zero]
      by_cases heven : d % 2 = 0 % 2
      · have hnext : ¬ ((d-1) % 2 = 0 % 2) := by omega
        simp [heven, hnext]
      · have hnext : (d-1) % 2 = 0 % 2 := by omega
        simp [heven, hnext]
  | succ n =>
      rw [routhPolynomialHomotopy_coeff_succ]
      by_cases heven : d % 2 = (n+1) % 2
      · have hnext : ¬ ((d-1) % 2 = (n+1) % 2) := by omega
        simp [heven, hnext]
      · have hnext : (d-1) % 2 = (n+1) % 2 := by omega
        have hprev : d % 2 = n % 2 := by omega
        simp only [ite_eq_left hnext, ite_eq_left hprev, ite_eq_right heven,
          mul_zero, sub_zero]

theorem routhOppositeParity_next_homotopy
    (d : ℕ) (hd : 0 < d) (p : ℝ[X]) (t : ℝ) :
    routhOppositeParity (d-1) (routhPolynomialHomotopy d p t) =
      routhSameParity d p - Polynomial.C t*Polynomial.X*routhOppositeParity d p := by
  calc
    routhOppositeParity (d-1) (routhPolynomialHomotopy d p t) =
        routhPolynomialHomotopy d p t -
          routhSameParity (d-1) (routhPolynomialHomotopy d p t) := by
      rw [routhSameParity]
      ring
    _ = routhSameParity d p - Polynomial.C t*Polynomial.X*routhOppositeParity d p := by
      rw [routhSameParity_next_homotopy d hd p t]
      simp only [routhPolynomialHomotopy, routhSameParity]
      ring

/-- An original imaginary-axis root is also a homotopy root. Together
with the earlier reverse implication this gives exact boundary-root
correspondence, without assuming stability of either polynomial. -/
theorem routhPolynomialHomotopy_imaginary_root_of_original
    (d : ℕ) (p : ℝ[X]) (t : ℝ) (z : ℂ) (hz : z.re = 0)
    (hroot : (p.map (algebraMap ℝ ℂ)).eval z = 0) :
    ((routhPolynomialHomotopy d p t).map (algebraMap ℝ ℂ)).eval z = 0 := by
  have hop : ((routhOppositeParity d p).map (algebraMap ℝ ℂ)).eval z = 0 := by
    rw [routhOppositeParity_eval_imaginary_axis d p z hz, hroot]
    simp
  rw [routhPolynomialHomotopy_eval, hroot, hop]
  simp

private theorem routhParityPositiveReal_no_right_root
    (d : ℕ) (p : ℝ[X]) (hparity : RouthParityPositiveReal d p)
    (z : ℂ) (hz : 0 < z.re) :
    (p.map (algebraMap ℝ ℂ)).eval z ≠ 0 := by
  intro hroot
  obtain ⟨he, hratio⟩ := hparity z hz
  let E := ((routhSameParity d p).map (algebraMap ℝ ℂ)).eval z
  let O := ((routhOppositeParity d p).map (algebraMap ℝ ℂ)).eval z
  have hsum : E+O = 0 := by
    simpa [E, O, routhSameParity, Polynomial.map_sub, Polynomial.eval_sub] using hroot
  change 0 ≤ (O/E).re at hratio
  exact complex_sum_ne_zero_of_ratio_re_nonneg E O he hratio hsum

private theorem routhParityPositiveReal_constant
    (a : ℝ) (ha : a ≠ 0) : RouthParityPositiveReal 0 (Polynomial.C a) := by
  have hcast : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  intro z _hz
  simp [routhSameParity, routhOppositeParity, hcast]

/-- The parity induction step is an exact positive-real continued
fraction transformation. The reduced same-parity part equals the old
opposite-parity part, with no equilibrium or spectral assumptions. -/
private theorem routhParityPositiveReal_of_reduced
    (d : ℕ) (hd : 0 < d) (p q : ℝ[X]) (c : ℝ) (hc : 0 < c)
    (hq : q = routhPolynomialHomotopy d p c)
    (hparity : RouthParityPositiveReal (d-1) q) :
    RouthParityPositiveReal d p := by
  intro z hz
  obtain ⟨hEq, hratio⟩ := hparity z hz
  let E := ((routhSameParity d p).map (algebraMap ℝ ℂ)).eval z
  let O := ((routhOppositeParity d p).map (algebraMap ℝ ℂ)).eval z
  have hO : O ≠ 0 := by
    simpa only [hq, routhSameParity_next_homotopy d hd p c, O] using hEq
  have hb : 0 ≤ ((E-(c : ℂ)*z*O)/O).re := by
    simpa only [hq, routhSameParity_next_homotopy d hd p c,
      routhOppositeParity_next_homotopy d hd p c,
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Complex.coe_algebraMap, E, O] using hratio
  have h := routh_parity_ratio_inverse_positive E O z c hc hz hO hb
  exact ⟨h.1, h.2.le⟩

/-- Positive leading coefficient and positivity of every actual Hurwitz
minor imply the actual Hurwitz root condition. The simultaneous parity
ratio induction proves right-half-plane exclusion; exact boundary-root
correspondence excludes the imaginary axis. No Routh criterion or root
counting theorem is used as an assumption. -/
theorem routhHurwitz_sufficiency_and_positiveReal
    (p : ℝ[X]) (hleading : 0 < p.leadingCoeff)
    (hminors : ∀ k : ℕ, k ≤ p.natDegree →
      0 < routhHurwitzMinor p.natDegree k p) :
    (∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0) ∧
      RouthParityPositiveReal p.natDegree p := by
  suffices h : ∀ d : ℕ, ∀ q : ℝ[X], q.natDegree = d →
      0 < q.leadingCoeff →
      (∀ k : ℕ, k ≤ d → 0 < routhHurwitzMinor d k q) →
      (∀ z : ℂ, (q.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0) ∧
        RouthParityPositiveReal d q from
    h p.natDegree p rfl hleading hminors
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
      intro p hdegree hlead hminor
      by_cases hd0 : d = 0
      · have hpdegree : p.natDegree = 0 := hdegree.trans hd0
        have hpC := Polynomial.eq_C_of_natDegree_eq_zero hpdegree
        have ha : 0 < p.coeff 0 := by
          simpa only [Polynomial.leadingCoeff, hpdegree] using hlead
        have hcast : (p.coeff 0 : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
        refine ⟨?_, ?_⟩
        · intro z hz
          exfalso
          apply hcast
          rw [hpC] at hz
          simpa only [Polynomial.map_C, Polynomial.eval_C, Complex.coe_algebraMap] using hz
        · rw [hd0, hpC]
          exact routhParityPositiveReal_constant _ ha.ne'
      · have hd : 0 < d := Nat.pos_of_ne_zero hd0
        have hpivot : 0 < routhDescendingCoeff d p 1 := by
          have hfirst := hminor 1 (by omega)
          simpa [routhHurwitzMinor, Matrix.det_fin_one, routhHurwitzMatrix] using hfirst
        let q := routhReducedPolynomial d p
        have hqdegree : q.natDegree = d-1 :=
          routhReducedPolynomial_natDegree d hd p hpivot.ne'
        have hqleading : 0 < q.leadingCoeff := by
          change 0 < (routhReducedPolynomial d p).leadingCoeff
          rw [routhReducedPolynomial_leadingCoeff d hd p hpivot.ne']
          exact hpivot
        have hqminors : ∀ k : ℕ, k ≤ d-1 →
            0 < routhHurwitzMinor (d-1) k q := by
          intro k hk
          have hparent := hminor (k+1) (by omega)
          rw [routhHurwitzMinor_reduction d hd p hpivot.ne' k] at hparent
          exact (mul_pos_iff_of_pos_left hpivot).mp hparent
        obtain ⟨hqstable, hqparity⟩ :=
          ih (d-1) (by omega) q hqdegree hqleading hqminors
        let c := routhDescendingCoeff d p 0 / routhDescendingCoeff d p 1
        have ha0 : 0 < routhDescendingCoeff d p 0 := by
          have heq : routhDescendingCoeff d p 0 = p.leadingCoeff := by
            simp [routhDescendingCoeff, Polynomial.leadingCoeff, hdegree]
          rw [heq]
          exact hlead
        have hc : 0 < c := div_pos ha0 hpivot
        have hqhom : q = routhPolynomialHomotopy d p c :=
          routhReducedPolynomial_eq_homotopy d hd p hdegree.le hpivot.ne'
        have hparity : RouthParityPositiveReal d p :=
          routhParityPositiveReal_of_reduced d hd p q c hc hqhom hqparity
        refine ⟨?_, hparity⟩
        intro z hz
        by_cases hright : 0 < z.re
        · exact False.elim (routhParityPositiveReal_no_right_root d p hparity z hright hz)
        · have hleft : z.re ≤ 0 := le_of_not_gt hright
          rcases lt_or_eq_of_le hleft with hstrict | haxis
          · exact hstrict
          · have hqroot : (q.map (algebraMap ℝ ℂ)).eval z = 0 := by
              rw [hqhom]
              exact routhPolynomialHomotopy_imaginary_root_of_original d p c z haxis hz
            have h := hqstable z hqroot
            exact False.elim ((not_lt_of_ge haxis.ge) h)

/-- Full Hurwitz-minor sufficiency for the exact existing determinant
definitions, including nonzero constant polynomials. -/
theorem hurwitzPolynomial_of_all_routh_minors_positive
    (p : ℝ[X]) (hleading : 0 < p.leadingCoeff)
    (hminors : ∀ k : ℕ, k ≤ p.natDegree →
      0 < routhHurwitzMinor p.natDegree k p) :
    ∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0 :=
  (routhHurwitz_sufficiency_and_positiveReal p hleading hminors).1

/-- The full criterion is now proved in both directions for actual
complex roots and the manuscript's actual Hurwitz determinants. -/
theorem hurwitzPolynomial_iff_all_routh_minors_positive
    (p : ℝ[X]) (hleading : 0 < p.leadingCoeff) :
    (∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0) ↔
      ∀ k : ℕ, k ≤ p.natDegree → 0 < routhHurwitzMinor p.natDegree k p := by
  exact ⟨hurwitzPolynomial_all_routh_minors_positive p hleading,
    hurwitzPolynomial_of_all_routh_minors_positive p hleading⟩

end
end PhosphorylationStableCapacity
