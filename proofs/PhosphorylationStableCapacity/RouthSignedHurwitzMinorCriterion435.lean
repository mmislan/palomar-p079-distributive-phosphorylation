module
public import proofs.PhosphorylationStableCapacity.RouthSignedTerminalFamily435

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial

private theorem signedRouth_rational_algebraMap_real (q : ℚ) :
    algebraMap ℚ ℝ q = (q : ℝ) := by
  have h : algebraMap ℚ ℝ = Rat.castHom ℝ := Subsingleton.elim _ _
  simpa only [Rat.coe_castHom] using RingHom.congr_fun h q

/-- The signed proper-minor criterion for an arbitrary actual polynomial:
one simple positive real root and every other complex root strictly left.
The proof extracts its literal Routh reconstruction, preserves the same
negative constant, proves the normalized terminal-family factorization,
and transfers back to this original polynomial. -/
theorem signed_routh_proper_minors_one_positive_root
    (p : ℝ[X]) (hleading : 0 < p.leadingCoeff)
    (hproper : ∀ k : Fin (p.natDegree-1),
      0 < routhHurwitzMinor p.natDegree (k.val+1) p)
    (hconstant : p.coeff 0 < 0) :
    ∃ u : ℝ, 0 < u ∧ (p.map (algebraMap ℝ ℂ)).eval (u : ℂ) = 0 ∧
      (p.map (algebraMap ℝ ℂ)).derivative.eval (u : ℂ) ≠ 0 ∧
      ∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).eval z = 0 → z = (u : ℂ) ∨ z.re < 0 := by
  have hdegree : 0 < p.natDegree := by
    by_contra hd
    have hzero : p.natDegree = 0 := Nat.eq_zero_of_not_pos hd
    have heq : p.leadingCoeff = p.coeff 0 := by
      simp only [Polynomial.leadingCoeff, hzero]
    rw [heq] at hleading
    linarith
  obtain ⟨a, cs, ha, hcs, hlength, hfamily⟩ :=
    routh_positive_proper_minors_terminal_decomposition p hdegree hleading hproper
  have hscalar : (a*cs.prod)⁻¹ ≠ 0 :=
    inv_ne_zero (mul_pos ha (List.prod_pos hcs)).ne'
  have hf := routhTerminalFamily_normalized_signed_factorization
    a ha cs hcs (p.coeff 0) hconstant
  have hpnormalized : PositiveRealRootHurwitzFactorization p.natDegree
      ((C ((a*cs.prod)⁻¹)*p).map (algebraMap ℝ ℂ)) := by
    simpa only [routhNormalizedTerminalFamily, hlength, hfamily] using hf
  exact signed_root_classification_of_scalar_normalization p p.natDegree
    ((a*cs.prod)⁻¹) hscalar hpnormalized

/-- Every accepted odd branch of the original finite rational local test
has exactly the actual signed root configuration. Its degree and positive
leading coefficient are matched to the actual polynomial; the signed
spectral conclusion is proved rather than supplied as a checker premise. -/
theorem rationalLocalRouthAccepts_odd_sound
    (d : ℕ) (p : ℚ[X]) (hdegree : p.natDegree = d)
    (hleading : 0 < p.leadingCoeff)
    (haccept : rationalLocalRouthAccepts d p true = true) :
    ∃ u : ℝ, 0 < u ∧
      ((p.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)).eval (u : ℂ) = 0 ∧
      ((p.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)).derivative.eval (u : ℂ) ≠ 0 ∧
      ∀ z : ℂ, ((p.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)).eval z = 0 →
        z = (u : ℂ) ∨ z.re < 0 := by
  have h := (rationalLocalRouthAccepts_iff d p true).mp haccept
  have hrealdegree : (p.map (algebraMap ℚ ℝ)).natDegree = d := by
    simpa only [Polynomial.natDegree_map] using hdegree
  have hrealhead : 0 < (p.map (algebraMap ℚ ℝ)).leadingCoeff := by
    rw [Polynomial.leadingCoeff_map, signedRouth_rational_algebraMap_real]
    exact_mod_cast hleading
  apply signed_routh_proper_minors_one_positive_root _ hrealhead
  · rw [hrealdegree]
    exact h.1
  · simpa using h.2

end
end PhosphorylationStableCapacity
