module
public import proofs.PhosphorylationStableCapacity.RouthHurwitzMinorSufficiency435
public import proofs.PhosphorylationStableCapacity.SplitAttainmentPreparation
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

open Polynomial Matrix

/-- A total finite rational Hurwitz test, including the declared degree
and positive leading coefficient. Every determinant is computed exactly. -/
def rationalFullRouthAccepts (d : ℕ) (p : ℚ[X]) : Bool :=
  decide (p.natDegree = d ∧ 0 < p.leadingCoeff ∧
    ∀ k : Fin (d+1), 0 < routhHurwitzMinor d k.val p)

/-- The coalesced deflation's literal full-minor test. Its monicity is
provided by the actual zero-constant characteristic factorization, not
retested or assumed by the validator. -/
def rationalNeutralDeflationRouthAccepts (d : ℕ) (q : ℚ[X]) : Bool :=
  decide (q.natDegree = d ∧
    ∀ k : Fin d, 0 < routhHurwitzMinor d (k.val+1) q)

/-- A closed finite validator for an actual rational matrix: characteristic
constant zero and the actual degree/cardinality-matched deflated test. -/
noncomputable def rationalNeutralMatrixRouthAccepts
    {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι ℚ) : Bool :=
  decide (J.charpoly.coeff 0 = 0) &&
    rationalNeutralDeflationRouthAccepts (Fintype.card ι-1) J.charpoly.divX

noncomputable section

private theorem rational_algebraMap_real (q : ℚ) :
    algebraMap ℚ ℝ q = (q : ℝ) := by
  have h : algebraMap ℚ ℝ = Rat.castHom ℝ := Subsingleton.elim _ _
  simpa only [Rat.coe_castHom] using RingHom.congr_fun h q

/-- The Boolean checker is exactly the corresponding real-coefficient
degree/leading/minor predicate, with a proved rational embedding. -/
theorem rationalFullRouthAccepts_iff_real_minors
    (d : ℕ) (p : ℚ[X]) :
    rationalFullRouthAccepts d p = true ↔
      (p.map (algebraMap ℚ ℝ)).natDegree = d ∧
      0 < (p.map (algebraMap ℚ ℝ)).leadingCoeff ∧
      ∀ k : Fin (d+1), 0 < routhHurwitzMinor d k.val
        (p.map (algebraMap ℚ ℝ)) := by
  rw [rationalFullRouthAccepts, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Polynomial.natDegree_map] using h.1
    · rw [Polynomial.leadingCoeff_map, rational_algebraMap_real]
      exact_mod_cast h.2.1
    · intro k
      rw [routhHurwitzMinor_map, rational_algebraMap_real]
      exact_mod_cast h.2.2 k
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Polynomial.natDegree_map] using h.1
    · have hh := h.2.1
      rw [Polynomial.leadingCoeff_map, rational_algebraMap_real] at hh
      exact_mod_cast hh
    · intro k
      have hh := h.2.2 k
      rw [routhHurwitzMinor_map, rational_algebraMap_real] at hh
      exact_mod_cast hh

/-- Every accepted rational finite test proves the actual complex-root
Hurwitz condition. The criterion is supplied by the proved source theorem,
not assumed in this validator's contract. -/
theorem rationalFullRouthAccepts_sound
    (d : ℕ) (p : ℚ[X]) (haccept : rationalFullRouthAccepts d p = true) :
    ∀ z : ℂ, ((p.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)).eval z = 0 →
      z.re < 0 := by
  have h := (rationalFullRouthAccepts_iff_real_minors d p).mp haccept
  apply hurwitzPolynomial_of_all_routh_minors_positive _ h.2.1
  intro k hk
  rw [h.1] at hk ⊢
  exact h.2.2 ⟨k, by omega⟩

/-- Full correctness of the total finite rational test for the actual
embedded polynomial, including degree zero. -/
theorem rationalFullRouthAccepts_iff_hurwitz
    (d : ℕ) (p : ℚ[X]) :
    rationalFullRouthAccepts d p = true ↔
      (p.map (algebraMap ℚ ℝ)).natDegree = d ∧
      0 < (p.map (algebraMap ℚ ℝ)).leadingCoeff ∧
      (∀ z : ℂ, ((p.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)).eval z = 0 →
        z.re < 0) := by
  constructor
  · intro h
    have hh := (rationalFullRouthAccepts_iff_real_minors d p).mp h
    exact ⟨hh.1, hh.2.1, rationalFullRouthAccepts_sound d p h⟩
  · intro h
    apply (rationalFullRouthAccepts_iff_real_minors d p).mpr
    refine ⟨h.1, h.2.1, ?_⟩
    intro k
    have hm := hurwitzPolynomial_all_routh_minors_positive
      (p.map (algebraMap ℚ ℝ)) h.2.1 h.2.2 k.val
        (by rw [h.1]; exact Nat.lt_succ_iff.mp k.isLt)
    simpa only [h.1] using hm

/-- A zero characteristic constant and accepted complementary Hurwitz
minors prove one algebraically simple neutral factor. Monicity and
nonvanishing of the complement are conclusions, not validator assumptions. -/
theorem simpleNeutralHurwitzComplement_of_divX_minors
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (hzero : J.charpoly.coeff 0 = 0)
    (hminors : ∀ k : ℕ, k ≤ J.charpoly.divX.natDegree →
      0 < routhHurwitzMinor J.charpoly.divX.natDegree k J.charpoly.divX) :
    SimpleNeutralHurwitzComplement J := by
  let q := J.charpoly.divX
  have hfactor : J.charpoly = Polynomial.X*q := by
    have h := Polynomial.X_mul_divX_add J.charpoly
    simpa only [hzero, Polynomial.C_0, add_zero, q] using h.symm
  have hmonic : q.Monic := by
    apply Polynomial.monic_X.of_mul_monic_left
    rw [← hfactor]
    exact J.charpoly_monic
  have hleading : 0 < q.leadingCoeff := by rw [hmonic.leadingCoeff]; norm_num
  have hstable : ∀ z : ℂ,
      (q.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0 :=
    hurwitzPolynomial_of_all_routh_minors_positive q hleading hminors
  refine ⟨q.map (algebraMap ℝ ℂ), ?_, ?_, hstable⟩
  · rw [Matrix.charpoly_map, hfactor, Polynomial.map_mul, Polynomial.map_X]
  · intro hz
    have h := hstable 0 hz
    simp at h

/-- The coalesced full-minor predicate has the exact finite indexing used
by the manuscript: determinants 1,...,d of the actual degree-d deflation. -/
theorem simpleNeutralHurwitzComplement_of_finite_divX_minors
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (d : ℕ) (hzero : J.charpoly.coeff 0 = 0)
    (hdegree : J.charpoly.divX.natDegree = d)
    (hminors : ∀ k : Fin d, 0 < routhHurwitzMinor d (k.val+1) J.charpoly.divX) :
    SimpleNeutralHurwitzComplement J := by
  apply simpleNeutralHurwitzComplement_of_divX_minors J hzero
  intro k hk
  by_cases hkzero : k = 0
  · subst k
    simp [routhHurwitzMinor]
  · rw [hdegree] at hk ⊢
    have h := hminors ⟨k-1, by omega⟩
    simpa only [show k-1+1 = k by omega] using h

theorem characteristic_deflation_natDegree
    {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι ℝ) :
    J.charpoly.divX.natDegree = Fintype.card ι-1 := by
  rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, Matrix.charpoly_natDegree_eq_dim]

/-- The literal matrix-size-indexed coalesced test entails the spectral
certificate; even the deflation degree is derived from the actual matrix. -/
theorem simpleNeutralHurwitzComplement_of_characteristic_size_minors
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (hzero : J.charpoly.coeff 0 = 0)
    (hminors : ∀ k : Fin (Fintype.card ι-1),
      0 < routhHurwitzMinor (Fintype.card ι-1) (k.val+1) J.charpoly.divX) :
    SimpleNeutralHurwitzComplement J :=
  simpleNeutralHurwitzComplement_of_finite_divX_minors
    J (Fintype.card ι-1) hzero (characteristic_deflation_natDegree J) hminors

/-- Exact rational full-minor data for the actual coalesced deflation
proves its neutral certificate, without an additional degree/leading or
simple-neutral premise. The actual matrix supplies those properties. -/
theorem rational_characteristic_deflation_minors_sound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (q : ℚ[X])
    (hzero : J.charpoly.coeff 0 = 0)
    (hcast : q.map (algebraMap ℚ ℝ) = J.charpoly.divX)
    (hminors : ∀ k : Fin (Fintype.card ι-1),
      0 < routhHurwitzMinor (Fintype.card ι-1) (k.val+1) q) :
    SimpleNeutralHurwitzComplement J := by
  apply simpleNeutralHurwitzComplement_of_characteristic_size_minors J hzero
  intro k
  rw [← hcast, routhHurwitzMinor_map, rational_algebraMap_real]
  exact_mod_cast hminors k

theorem rationalNeutralDeflationRouthAccepts_iff_real_minors
    (d : ℕ) (q : ℚ[X]) :
    rationalNeutralDeflationRouthAccepts d q = true ↔
      (q.map (algebraMap ℚ ℝ)).natDegree = d ∧
      ∀ k : Fin d, 0 < routhHurwitzMinor d (k.val+1)
        (q.map (algebraMap ℚ ℝ)) := by
  rw [rationalNeutralDeflationRouthAccepts, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [Polynomial.natDegree_map] using h.1
    · intro k
      rw [routhHurwitzMinor_map, rational_algebraMap_real]
      exact_mod_cast h.2 k
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [Polynomial.natDegree_map] using h.1
    · intro k
      have hh := h.2 k
      rw [routhHurwitzMinor_map, rational_algebraMap_real] at hh
      exact_mod_cast hh

/-- Acceptance of the literal coalesced full-minor test proves the
actual matrix's simple-neutral Hurwitz complement at every accepted
parameter, retaining the rational-to-real characteristic correspondence. -/
theorem rationalNeutralDeflationRouthAccepts_sound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (d : ℕ) (q : ℚ[X])
    (hzero : J.charpoly.coeff 0 = 0)
    (hcast : q.map (algebraMap ℚ ℝ) = J.charpoly.divX)
    (haccept : rationalNeutralDeflationRouthAccepts d q = true) :
    SimpleNeutralHurwitzComplement J := by
  have h := (rationalNeutralDeflationRouthAccepts_iff_real_minors d q).mp haccept
  apply simpleNeutralHurwitzComplement_of_finite_divX_minors J d hzero
  · rw [← hcast]
    exact h.1
  · rw [← hcast]
    exact h.2

/-- The actual rational matrix validator has no unchecked characteristic
correspondence premise: matrix and polynomial casts commute by proof. -/
theorem rationalNeutralMatrixRouthAccepts_sound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℚ) (haccept : rationalNeutralMatrixRouthAccepts J = true) :
    SimpleNeutralHurwitzComplement (J.map (algebraMap ℚ ℝ)) := by
  have h : J.charpoly.coeff 0 = 0 ∧
      rationalNeutralDeflationRouthAccepts (Fintype.card ι-1) J.charpoly.divX = true := by
    simpa [rationalNeutralMatrixRouthAccepts] using haccept
  apply rationalNeutralDeflationRouthAccepts_sound
    (J.map (algebraMap ℚ ℝ)) (Fintype.card ι-1) J.charpoly.divX
  · rw [Matrix.charpoly_map, Polynomial.coeff_map, h.1]
    simp
  · rw [Matrix.charpoly_map]
    ext n
    simp [Polynomial.coeff_divX, Polynomial.coeff_map]
  · exact h.2

/-- Any accepted coalesced deflation branch is spectrally sound when its
rational polynomial is the actual characteristic deflation. No favorable
existential witness or pre-existing simple-neutral certificate is needed. -/
theorem rational_neutral_deflation_accepted_sound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (d : ℕ) (q : ℚ[X])
    (hzero : J.charpoly.coeff 0 = 0)
    (hcast : q.map (algebraMap ℚ ℝ) = J.charpoly.divX)
    (haccept : rationalFullRouthAccepts d q = true) :
    SimpleNeutralHurwitzComplement J := by
  have h := (rationalFullRouthAccepts_iff_real_minors d q).mp haccept
  apply simpleNeutralHurwitzComplement_of_divX_minors J hzero
  intro k hk
  have hdegree : J.charpoly.divX.natDegree = d := by
    rw [← hcast]
    exact h.1
  rw [hdegree] at hk ⊢
  rw [← hcast]
  exact h.2.2 ⟨k, by omega⟩

/-- Positive proper minors and positive constant supply the last positive
minor by its exact determinant identity, and therefore imply Hurwitz.
This is the manuscript's even-index local test. -/
theorem hurwitzPolynomial_of_proper_minors_and_constant_positive
    (p : ℝ[X]) (hleading : 0 < p.leadingCoeff)
    (hproper : ∀ k : Fin (p.natDegree-1),
      0 < routhHurwitzMinor p.natDegree (k.val+1) p)
    (hconstant : 0 < p.coeff 0) :
    ∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0 := by
  apply hurwitzPolynomial_of_all_routh_minors_positive p hleading
  have hproperNat (k : ℕ) (hk0 : 0 < k) (hk : k < p.natDegree) :
      0 < routhHurwitzMinor p.natDegree k p := by
    have h := hproper ⟨k-1, by omega⟩
    simpa only [show k-1+1 = k by omega] using h
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp [routhHurwitzMinor]
  · by_cases hless : k < p.natDegree
    · exact hproperNat k (Nat.pos_of_ne_zero hk0) hless
    · have heq : k = p.natDegree := by omega
      cases hdegree : p.natDegree with
      | zero => omega
      | succ d =>
          have hprevious : 0 < routhHurwitzMinor (d+1) d p := by
            by_cases hd0 : d = 0
            · subst d
              simp [routhHurwitzMinor]
            · have h := hproperNat d (Nat.pos_of_ne_zero hd0) (by omega)
              simpa only [hdegree] using h
          rw [heq, hdegree, routhHurwitzMinor_last]
          exact mul_pos hconstant hprevious

/-- Acceptance of the existing even local rational checker proves actual
Hurwitz stability once the declared degree and positive leading coefficient
are matched to the actual rational polynomial. -/
theorem rationalLocalRouthAccepts_even_sound
    (d : ℕ) (p : ℚ[X]) (hdegree : p.natDegree = d)
    (hleading : 0 < p.leadingCoeff)
    (haccept : rationalLocalRouthAccepts d p false = true) :
    ∀ z : ℂ, ((p.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)).eval z = 0 →
      z.re < 0 := by
  have h := (rationalLocalRouthAccepts_iff d p false).mp haccept
  have hrealdegree : (p.map (algebraMap ℚ ℝ)).natDegree = d := by
    simpa only [Polynomial.natDegree_map] using hdegree
  have hrealhead : 0 < (p.map (algebraMap ℚ ℝ)).leadingCoeff := by
    rw [Polynomial.leadingCoeff_map, rational_algebraMap_real]
    exact_mod_cast hleading
  apply hurwitzPolynomial_of_proper_minors_and_constant_positive _ hrealhead
  · rw [hrealdegree]
    exact h.1
  · simpa only [Bool.false_eq_true, ite_false] using h.2

end
end PhosphorylationStableCapacity
