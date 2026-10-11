module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingRouthAdmission435
public import proofs.PhosphorylationStableCapacity.RouthHurwitzMinorNecessity435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingActualCurrentDesign
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingRationality
public import proofs.PhosphorylationStableCapacity.FiniteRationalJacobianAction
public import proofs.PhosphorylationStableCapacity.RouthNeutralCheckerSoundness435
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Polynomial Matrix Filter
open scoped Topology

noncomputable section

/-- The real deflation of the literal characteristic polynomial is
exactly the Hurwitz complement supplied by the simple-neutral certificate.
No new spectral or determinant premise is introduced. -/
theorem simpleNeutral_real_charpoly_divX_hurwitz
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (hspec : SimpleNeutralHurwitzComplement J) :
    J.charpoly.divX.Monic ∧
      ∀ z : ℂ, (J.charpoly.divX.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0 := by
  obtain ⟨q, hfactor, hqzero, hleft⟩ := hspec
  have hpzero : J.charpoly.coeff 0 = 0 :=
    simpleNeutral_real_charpoly_coeff_zero J ⟨q, hfactor, hqzero, hleft⟩
  have hrealFactor : Polynomial.X*J.charpoly.divX = J.charpoly := by
    simpa only [hpzero, Polynomial.C_0, add_zero] using
      Polynomial.X_mul_divX_add J.charpoly
  have hmonic : J.charpoly.divX.Monic :=
    Polynomial.monic_X.of_mul_monic_left (hrealFactor.symm ▸ Matrix.charpoly_monic J)
  have hfactor' : J.charpoly.map (algebraMap ℝ ℂ) = Polynomial.X*q := by
    simpa only [Matrix.charpoly_map] using hfactor
  have hmap : J.charpoly.map (algebraMap ℝ ℂ) =
      Polynomial.X*J.charpoly.divX.map (algebraMap ℝ ℂ) := by
    conv_lhs => rw [← hrealFactor]
    rw [Polynomial.map_mul, Polynomial.map_X]
  have hq : J.charpoly.divX.map (algebraMap ℝ ℂ) = q := by
    apply mul_left_cancel₀ Polynomial.X_ne_zero
    exact hmap.symm.trans hfactor'
  exact ⟨hmonic, fun z hz => hleft z (by rwa [← hq])⟩

/-- Every proper minor of the actual coalesced characteristic polynomial
deflation is positive, at its actual dimension minus one. -/
theorem simpleNeutral_real_charpoly_divX_routh_minors_positive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (hspec : SimpleNeutralHurwitzComplement J) :
    ∀ k : ℕ, k ≤ Fintype.card ι-1 →
      0 < routhHurwitzMinor (Fintype.card ι-1) k J.charpoly.divX := by
  obtain ⟨hmonic, hleft⟩ := simpleNeutral_real_charpoly_divX_hurwitz J hspec
  have hdegree : J.charpoly.divX.natDegree = Fintype.card ι-1 := by
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one,
      Matrix.charpoly_natDegree_eq_dim]
  intro k hk
  have hk' : k ≤ J.charpoly.divX.natDegree := by omega
  simpa only [hdegree] using
    hurwitzPolynomial_all_routh_minors_positive J.charpoly.divX
      (by rw [hmonic.leadingCoeff]; norm_num) hleft k hk'

/-- Rational rate coordinates lift to exact rational input data for the
existing finite Jacobian evaluator. Positivity is not needed for this
algebraic construction. -/
private theorem rationalRates_exists_input {n : ℕ} (k : Rates n)
    (hk : RationalRates k) : ∃ kQ : RationalSiteRates n, kQ.toReal = k := by
  classical
  choose a ha using fun i => (hk i).1
  choose b hb using fun i => (hk i).2.1
  choose c hc using fun i => (hk i).2.2.1
  choose alpha halpha using fun i => (hk i).2.2.2.1
  choose beta hbeta using fun i => (hk i).2.2.2.2.1
  choose gamma hgamma using fun i => (hk i).2.2.2.2.2
  let kQ : RationalSiteRates n := ⟨a, b, c, alpha, beta, gamma⟩
  refine ⟨kQ, ?_⟩
  cases k
  change Rates.mk (fun i => (a i : ℝ)) (fun i => (b i : ℝ))
    (fun i => (c i : ℝ)) (fun i => (alpha i : ℝ))
    (fun i => (beta i : ℝ)) (fun i => (gamma i : ℝ)) = _
  congr 1
  · exact funext ha
  · exact funext hb
  · exact funext hc
  · exact funext halpha
  · exact funext hbeta
  · exact funext hgamma

private theorem rationalState_exists_chart_input {n : ℕ} (x : State n)
    (hx : RationalState x) :
    ∃ uQ : RationalSiteCoordinate n, uQ.toReal = toCoordinateSpace (chart x) := by
  classical
  choose s hs using fun i : Fin n => hx.1 i.succ
  choose c hc using hx.2.2.2.1
  choose d hd using hx.2.2.2.2
  refine ⟨(s, c, d), ?_⟩
  change ((fun i => (s i : ℝ)), (fun i => (c i : ℝ)), (fun i => (d i : ℝ))) =
    ((fun i => x.S i.succ), x.C, x.D)
  exact Prod.ext (funext hs) (Prod.ext (funext hc) (funext hd))

/-- A rational polynomial is an exact representative of the literal
class-Jacobian characteristic polynomial, using the same rates and state.
The finite evaluator and reindexing are proved equal to that Jacobian. -/
theorem rational_actual_restricted_charpoly_exists {n : ℕ}
    (ET FT ST : ℚ) (k : Rates n) (x : State n)
    (hk : RationalRates k) (hx : RationalState x) :
    ∃ pQ : ℚ[X], pQ.map (algebraMap ℚ ℝ) =
      (restrictedJacobianMatrix (ET : ℝ) (FT : ℝ) (ST : ℝ) k
        (toCoordinateSpace (chart x))).charpoly := by
  obtain ⟨kQ, hkQ⟩ := rationalRates_exists_input k hk
  obtain ⟨uQ, huQ⟩ := rationalState_exists_chart_input x hx
  refine ⟨(rationalJacobianMatrix ET FT ST kQ uQ).charpoly, ?_⟩
  rw [← Matrix.charpoly_map, rationalJacobianMatrix_cast, hkQ, huQ,
    allSiteExplicitFinMatrix_charpoly_eq_restricted]

/-- The original literal fixed-binding halving theorem with every former
coalesced-deflation minor premise proved from the same simple-neutral
matrix witness. All physical inputs, offsets and common rates are retained. -/
theorem paperFixedBinding_routh_pattern_has_halving_index_of_simpleNeutral
    (m : ℕ) (ξ : ℕ → ℝ) (hξ : StrictMono ξ)
    (r τ ε : ℝ) (ω : Fin (m+1) → ℝ)
    (hω : ∀ i, 0 < ω i) (hr : 1 < r)
    (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : (coalescedAllScaledRates m r (Fin.lastCases τ ω)).Positive)
    (hk₀ : (relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε).Positive)
    (hx₀ : (coalescedFiniteState (m+1) r).Positive)
    (heq₀ : Equilibrium (relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
      (coalescedFiniteState (m+1) r))
    (hET₀ : totalE (coalescedFiniteState (m+1) r) = 2*r)
    (hFT₀ : totalF (coalescedFiniteState (m+1) r) = 2)
    (hspec : SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
        (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r))))) :
    ∃ b : ℕ, ∀ j : Fin (2*(m+1)+1),
      (∀ k : Fin (3*(m+2)-1),
        0 < routhHurwitzMinor (3*(m+2)) (k.val+1)
          (paperFixedBindingRouthPolynomial m ξ r τ ε ((1/2 : ℝ)^b) ω j)) ∧
      (if decide (Odd j.val) then
        (paperFixedBindingRouthPolynomial m ξ r τ ε ((1/2 : ℝ)^b) ω j).coeff 0 < 0
      else 0 < (paperFixedBindingRouthPolynomial m ξ r τ ε ((1/2 : ℝ)^b) ω j).coeff 0) := by
  apply paperFixedBinding_routh_pattern_has_halving_index
    m ξ hξ r τ ε ω hω hr hτ hε hε1 hD₀ hB₀ hbase hk₀ hx₀ heq₀ hET₀ hFT₀ hspec
  let J₀ := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
    (relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
    (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r)))
  change ∀ k : Fin (3*(m+2)-1),
    0 < routhHurwitzMinor (3*(m+2)-1) (k.val+1) J₀.charpoly.divX
  intro k
  have hcard : Fintype.card (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) =
      3*(m+2) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hk : k.val+1 ≤
      Fintype.card (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2)))-1 := by
    rw [hcard]
    omega
  simpa only [hcard] using
    simpleNeutral_real_charpoly_divX_routh_minors_positive J₀ hspec (k.val+1) hk

/-- Every rational-distance member of the same literal family has an
exact rational characteristic-polynomial representative. Rationality is
proved from its rates and state; no cast-correspondence premise is assumed. -/
theorem paperFixedBinding_rational_routh_family_exists
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (ω : Fin (m+1) → ℝ)
    (hr : RationalReal r) (hτ : RationalReal τ) (hε : RationalReal ε)
    (hξ : ∀ j, RationalReal (ξ j)) (hω : ∀ i, RationalReal (ω i)) :
    ∃ Q : Fin (2*(m+1)+1) → ℚ → ℚ[X],
      ∀ j δ, (Q j δ).map (algebraMap ℚ ℝ) =
        paperFixedBindingRouthPolynomial m ξ r τ ε (δ : ℝ) ω j := by
  classical
  obtain ⟨rQ, hrQ⟩ := hr
  have hw : ∀ i : Fin (m+2),
      RationalReal ((Fin.lastCases (motive := fun _ => ℝ) τ ω) i) := by
    intro i
    refine Fin.lastCases (motive := fun i =>
      RationalReal ((Fin.lastCases (motive := fun _ => ℝ) τ ω) i)) ?_ ?_ i
    · simpa only [Fin.lastCases_last] using hτ
    · intro i
      simpa only [Fin.lastCases_castSucc] using hω i
  have hexists (j : Fin (2*(m+1)+1)) (δ : ℚ) :
      ∃ pQ : ℚ[X], pQ.map (algebraMap ℚ ℝ) =
        paperFixedBindingRouthPolynomial m ξ r τ ε (δ : ℝ) ω j := by
    obtain ⟨hk, hx⟩ := paperFixedBindingSplit_rational_offsets
      m ξ (Fin.lastCases τ ω) ⟨rQ, hrQ⟩ ⟨δ, rfl⟩ hε hξ hw
    obtain ⟨pQ, hpQ⟩ := rational_actual_restricted_charpoly_exists
      (2*rQ) 2 (2*(rQ+1))
      (paperFixedBindingSplitRates m ξ r (δ : ℝ) ε (Fin.lastCases τ ω))
      (arbitrarySplitFiniteState (m+1) ξ r (δ : ℝ) j) hk (hx j)
    refine ⟨pQ, ?_⟩
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat, Rat.cast_one,
      hrQ, paperFixedBindingRouthPolynomial] using hpQ
  choose Q hQ using hexists
  exact ⟨Q, hQ⟩

/-- The original rational Boolean Routh test accepts the same family at
the same common finite index as its literal real minors and constant signs.
This uses the proved determinant embedding, not numerical eigenvalues. -/
theorem paperFixedBinding_rational_routh_admits_of_literal_pattern
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (ω : Fin (m+1) → ℝ)
    (Q : Fin (2*(m+1)+1) → ℚ → ℚ[X])
    (hQ : ∀ j δ, (Q j δ).map (algebraMap ℚ ℝ) =
      paperFixedBindingRouthPolynomial m ξ r τ ε (δ : ℝ) ω j)
    (hpattern : ∃ b : ℕ, ∀ j : Fin (2*(m+1)+1),
      (∀ k : Fin (3*(m+2)-1),
        0 < routhHurwitzMinor (3*(m+2)) (k.val+1)
          (paperFixedBindingRouthPolynomial m ξ r τ ε ((1/2 : ℝ)^b) ω j)) ∧
      (if decide (Odd j.val) then
        (paperFixedBindingRouthPolynomial m ξ r τ ε ((1/2 : ℝ)^b) ω j).coeff 0 < 0
      else 0 < (paperFixedBindingRouthPolynomial m ξ r τ ε ((1/2 : ℝ)^b) ω j).coeff 0)) :
    ∃ b : ℕ, ∀ j : Fin (2*(m+1)+1),
      rationalLocalRouthAccepts (3*(m+2)) (Q j ((1/2 : ℚ)^b))
        (decide (Odd j.val)) = true := by
  obtain ⟨b, hb⟩ := hpattern
  refine ⟨b, ?_⟩
  intro j
  rw [rationalLocalRouthAccepts_iff, hQ]
  simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hb j

/-- For every construction size and every strictly ordered rational offset sequence,
the actual unit-current dyadic design has a common finite index at which
the original alternating rational Routh test accepts all labelled members.
Its coalesced physical data, simple-neutral matrix, frozen current factors
and exact rational characteristic family share the same a,b,c witnesses.
This is arithmetic admission, not a signed spectral counting theorem or a
claim about every earlier first-success branch of the four nested loops. -/
theorem paperFixedBinding_all_size_rational_routh_admission (m : ℕ) (ξ : ℕ → ℚ) (hξ : StrictMono ξ) :
    ∃ a b c : ℕ,
      let r : ℝ := (2 : ℝ)^a
      let t : ℝ := (1/2 : ℝ)^b
      let ε : ℝ := (1/2 : ℝ)^c
      let x := coalescedFiniteState (m+1) r
      let τ : ℝ := t / x.D (Fin.last (m+1))
      let θ : Fin (m+1) → ℝ := fun i => 1 / x.D i.castSucc
      let k := relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r (Fin.lastCases τ θ))) ε
      1 < r ∧ (3*(m+2 : ℝ))/2 ≤ r ∧
      0 < t ∧ 0 < τ ∧ 0 < ε ∧ ε ≤ 1 ∧
      DensePositive (coalescedRawD (m+1) r) (m+1) ∧
      DensePositive (coalescedRawB (m+1) r) (m+1) ∧
      (∀ i, 0 < θ i) ∧
      (coalescedAllScaledRates m r (Fin.lastCases τ θ)).Positive ∧
      k.Positive ∧ x.Positive ∧ Equilibrium k x ∧
      totalE x = 2*r ∧ totalF x = 2 ∧
      SimpleNeutralHurwitzComplement
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k
          (fromLoadedCoord (loadedCoordOfState x))) ∧
      (∀ i : Fin (m+1), k.gamma i.castSucc * x.D i.castSucc = 1) ∧
      k.gamma (Fin.last (m+1)) * x.D (Fin.last (m+1)) = t ∧
      ∃ Q : Fin (2*(m+1)+1) → ℚ → ℚ[X],
        (∀ j δ, (Q j δ).map (algebraMap ℚ ℝ) =
          paperFixedBindingRouthPolynomial m (fun i => (ξ i : ℝ))
            r τ ε (δ : ℝ) θ j) ∧
        ∃ d : ℕ, ∀ j : Fin (2*(m+1)+1),
          rationalLocalRouthAccepts (3*(m+2)) (Q j ((1/2 : ℚ)^d))
            (decide (Odd j.val)) = true := by
  obtain ⟨a, b, c, hr, hrAdequate, ht, hτ, hε, hε1, hD, hB,
    hθ, hbase, hk, hx, heq, hET, hFT, hspec, hprefix, hfinal⟩ :=
    paperFixedBinding_actual_unit_current_design m
  let r : ℝ := (2 : ℝ)^a
  let t : ℝ := (1/2 : ℝ)^b
  let ε : ℝ := (1/2 : ℝ)^c
  let x := coalescedFiniteState (m+1) r
  let τ : ℝ := t/x.D (Fin.last (m+1))
  let θ : Fin (m+1) → ℝ := fun i => 1/x.D i.castSucc
  let ξR : ℕ → ℝ := fun i => (ξ i : ℝ)
  have hξR : StrictMono ξR := by
    intro i j hij
    change (ξ i : ℝ) < (ξ j : ℝ)
    exact_mod_cast hξ hij
  have hpattern := paperFixedBinding_routh_pattern_has_halving_index_of_simpleNeutral
    m ξR hξR r τ ε θ hθ hr hτ hε hε1 hD hB hbase hk hx heq hET hFT hspec
  have hrRat : RationalReal r := by
    refine ⟨(2 : ℚ)^a, ?_⟩
    push_cast
    rfl
  have htRat : RationalReal t := by
    refine ⟨(1/2 : ℚ)^b, ?_⟩
    push_cast
    rfl
  have hεRat : RationalReal ε := by
    refine ⟨(1/2 : ℚ)^c, ?_⟩
    push_cast
    rfl
  have hxRat := coalescedFiniteState_rational_of_rational_source m hrRat
  have hτRat : RationalReal τ := by
    obtain ⟨tQ, htQ⟩ := htRat
    obtain ⟨dQ, hdQ⟩ := hxRat.2.2.2.2 (Fin.last (m+1))
    refine ⟨tQ/dQ, ?_⟩
    change ((tQ/dQ : ℚ) : ℝ) = t/x.D (Fin.last (m+1))
    rw [Rat.cast_div, htQ, hdQ]
  have hθRat (i : Fin (m+1)) : RationalReal (θ i) := by
    obtain ⟨dQ, hdQ⟩ := hxRat.2.2.2.2 i.castSucc
    refine ⟨1/dQ, ?_⟩
    change ((1/dQ : ℚ) : ℝ) = 1/x.D i.castSucc
    rw [Rat.cast_div, Rat.cast_one, hdQ]
  obtain ⟨Q, hQ⟩ := paperFixedBinding_rational_routh_family_exists
    m ξR r τ ε θ hrRat hτRat hεRat (fun i => ⟨ξ i, rfl⟩) hθRat
  obtain ⟨d, hadmit⟩ := paperFixedBinding_rational_routh_admits_of_literal_pattern
    m ξR r τ ε θ Q hQ hpattern
  exact ⟨a, b, c, hr, hrAdequate, ht, hτ, hε, hε1, hD, hB,
    hθ, hbase, hk, hx, heq, hET, hFT, hspec, hprefix, hfinal,
    Q, hQ, d, hadmit⟩

/-- The literal odd/even Routh pattern holds at every sufficiently small
positive distance on the same fixed-binding family. Keeping the germ allows
physical admission and the spectral test to be joined before selecting d. -/
theorem paperFixedBinding_routh_pattern_eventually_of_simpleNeutral
    (m : ℕ) (ξ : ℕ → ℝ) (hξ : StrictMono ξ)
    (r τ ε : ℝ) (ω : Fin (m+1) → ℝ)
    (hω : ∀ i, 0 < ω i) (hr : 1 < r)
    (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : (coalescedAllScaledRates m r (Fin.lastCases τ ω)).Positive)
    (hk₀ : (relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε).Positive)
    (hx₀ : (coalescedFiniteState (m+1) r).Positive)
    (heq₀ : Equilibrium (relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
      (coalescedFiniteState (m+1) r))
    (hET₀ : totalE (coalescedFiniteState (m+1) r) = 2*r)
    (hFT₀ : totalF (coalescedFiniteState (m+1) r) = 2)
    (hspec : SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
        (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r))))) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), ∀ j : Fin (2*(m+1)+1),
      (∀ k : Fin (3*(m+2)-1),
        0 < routhHurwitzMinor (3*(m+2)) (k.val+1)
          (paperFixedBindingRouthPolynomial m ξ r τ ε δ ω j)) ∧
      (if decide (Odd j.val) then
        (paperFixedBindingRouthPolynomial m ξ r τ ε δ ω j).coeff 0 < 0
      else 0 < (paperFixedBindingRouthPolynomial m ξ r τ ε δ ω j).coeff 0) := by
  let J₀ := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
    (relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
    (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r)))
  let q : ℝ[X] := J₀.charpoly.divX
  have hpzero : J₀.charpoly.coeff 0 = 0 :=
    simpleNeutral_real_charpoly_coeff_zero J₀ hspec
  have hfactor : J₀.charpoly = Polynomial.X*q := by
    have h := (Polynomial.X_mul_divX_add J₀.charpoly).symm
    simpa [q, hpzero] using h
  let P : Fin (2*(m+1)+1) → ℝ → ℝ[X] :=
    fun j δ => paperFixedBindingRouthPolynomial m ξ r τ ε δ ω j
  have hzero : ∀ j, P j 0 = Polynomial.X*q := by
    intro j
    have h := congrArg Matrix.charpoly
      (paperFixedBindingSplit_restrictedJacobianMatrix_zero_eq_coalesced
        m ξ r ε (Fin.lastCases τ ω) j)
    change P j 0 = J₀.charpoly at h
    exact h.trans hfactor
  have hcoeff : ∀ j n, ContinuousAt (fun δ => (P j δ).coeff n) 0 := by
    intro j n
    exact (paperFixedBindingSplit_charpoly_coeff_differentiableAt
      m ξ r τ ε ω (ne_of_gt (lt_trans zero_lt_one hr)) hD₀ hB₀ hbase j n).continuousAt
  have hconstant := paperFixedBinding_routh_constant_alternates
    m ξ hξ r τ ε ω hω hr hτ hε hε1 hD₀ hB₀ hbase
      hk₀ hx₀ heq₀ hET₀ hFT₀
  have hsign : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j, if decide (Odd j.val) then (P j δ).coeff 0 < 0 else 0 < (P j δ).coeff 0 := by
    filter_upwards [hconstant] with δ hδ j
    by_cases hj : Odd j.val
    · simpa [hj] using (hδ j).2 hj
    · have heven : Even j.val := Nat.not_odd_iff_even.mp hj
      simpa [hj] using (hδ j).1 heven
  have hd : (3*(m+2)-1)+1 = 3*(m+2) := by omega
  have hq : ∀ k : Fin (3*(m+2)-1),
      0 < routhHurwitzMinor (3*(m+2)-1) (k.val+1) q := by
    intro k
    have hcard : Fintype.card (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) =
        3*(m+2) := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    have hk : k.val+1 ≤
        Fintype.card (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2)))-1 := by
      rw [hcard]
      omega
    simpa only [hcard, q] using
      simpleNeutral_real_charpoly_divX_routh_minors_positive J₀ hspec (k.val+1) hk
  have hminors : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j, ∀ k : Fin (3*(m+2)-1),
        0 < routhHurwitzMinor ((3*(m+2)-1)+1) (k.val+1) (P j δ) :=
    (properRouthMinors_eventually_positive
      (3*(m+2)-1) P q hzero hcoeff hq).filter_mono
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  filter_upwards [hminors, hsign] with δ hminors hsign j
  simpa only [hd, P] using And.intro (hminors j) (hsign j)

/-- The original alternating rational Routh test and the positive physical
split family are admitted at ONE common halving index. The Routh, conversion,
root and positive-distance germs are conjoined before selecting d. At this
same index the rates and whole equilibrium list are rational and positive,
the equilibrium set is exhausted with its exact count, and every literal
catalytic current is positive and obeys the same frozen edge factor.
The original coalesced a,b,c, unit prefix/final current identities and exact
Q family are retained. Signed Routh counting is a separate theorem. -/
theorem paperFixedBinding_all_size_rational_routh_physical_admission (m : ℕ) (ξ : ℕ → ℚ) (hξ : StrictMono ξ) :
    ∃ a b c : ℕ,
      let r : ℝ := (2 : ℝ)^a
      let t : ℝ := (1/2 : ℝ)^b
      let ε : ℝ := (1/2 : ℝ)^c
      let x := coalescedFiniteState (m+1) r
      let τ : ℝ := t / x.D (Fin.last (m+1))
      let θ : Fin (m+1) → ℝ := fun i => 1 / x.D i.castSucc
      let k := relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r (Fin.lastCases τ θ))) ε
      1 < r ∧ (3*(m+2 : ℝ))/2 ≤ r ∧
      0 < t ∧ 0 < τ ∧ 0 < ε ∧ ε ≤ 1 ∧
      DensePositive (coalescedRawD (m+1) r) (m+1) ∧
      DensePositive (coalescedRawB (m+1) r) (m+1) ∧
      (∀ i, 0 < θ i) ∧
      (coalescedAllScaledRates m r (Fin.lastCases τ θ)).Positive ∧
      k.Positive ∧ x.Positive ∧ Equilibrium k x ∧
      totalE x = 2*r ∧ totalF x = 2 ∧
      SimpleNeutralHurwitzComplement
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k
          (fromLoadedCoord (loadedCoordOfState x))) ∧
      (∀ i : Fin (m+1), k.gamma i.castSucc * x.D i.castSucc = 1) ∧
      k.gamma (Fin.last (m+1)) * x.D (Fin.last (m+1)) = t ∧
      ∃ Q : Fin (2*(m+1)+1) → ℚ → ℚ[X],
        (∀ j δ, (Q j δ).map (algebraMap ℚ ℝ) =
          paperFixedBindingRouthPolynomial m (fun i => (ξ i : ℝ))
            r τ ε (δ : ℝ) θ j) ∧
        ∃ d : ℕ,
          let δ : ℝ := (1/2 : ℝ)^d
          let kδ := paperFixedBindingSplitRates m (fun i => (ξ i : ℝ))
            r δ ε (Fin.lastCases τ θ)
          let f := arbitrarySplitFiniteState (m+1) (fun i => (ξ i : ℝ)) r δ
          (∀ j : Fin (2*(m+1)+1),
            rationalLocalRouthAccepts (3*(m+2)) (Q j ((1/2 : ℚ)^d))
              (decide (Odd j.val)) = true) ∧
          kδ.Positive ∧ RationalRates kδ ∧
          (∀ j : Fin (2*(m+1)+1), (f j).Positive ∧ RationalState (f j) ∧
            Equilibrium kδ (f j) ∧ InClass (2*r) 2 (2*(r+1)) (f j)) ∧
          Function.Injective f ∧
          {s : State (m+2) | s.Positive ∧ Equilibrium kδ s ∧
            InClass (2*r) 2 (2*(r+1)) s} = Set.range f ∧
          {s : State (m+2) | s.Positive ∧ Equilibrium kδ s ∧
            InClass (2*r) 2 (2*(r+1)) s}.ncard = 2*(m+1)+1 ∧
          ∀ j : Fin (2*(m+1)+1), ∀ i : Fin (m+2),
            kδ.c i*(f j).C i = kδ.gamma i*(f j).D i ∧
            0 < kδ.gamma i*(f j).D i ∧
            kδ.gamma i*(f j).D i = (Fin.lastCases τ θ i)*(f j).D i := by
  obtain ⟨a, b, c, hr, hrAdequate, ht, hτ, hε, hε1, hD, hB,
    hθ, hbase, hk, hx, heq, hET, hFT, hspec, hprefix, hfinal,
    Q, hQ, _oldRouthIndex⟩ := paperFixedBinding_all_size_rational_routh_admission m ξ hξ
  let r : ℝ := (2 : ℝ)^a
  let t : ℝ := (1/2 : ℝ)^b
  let ε : ℝ := (1/2 : ℝ)^c
  let x := coalescedFiniteState (m+1) r
  let τ : ℝ := t/x.D (Fin.last (m+1))
  let θ : Fin (m+1) → ℝ := fun i => 1/x.D i.castSucc
  let ξR : ℕ → ℝ := fun i => (ξ i : ℝ)
  let w : Fin (m+2) → ℝ := Fin.lastCases τ θ
  have hξR : StrictMono ξR := by
    intro i j hij
    change (ξ i : ℝ) < (ξ j : ℝ)
    exact_mod_cast hξ hij
  have hw (i : Fin (m+2)) : 0 < w i := by
    refine Fin.lastCases (motive := fun i => 0 < w i) ?_ ?_ i
    · simpa only [w, Fin.lastCases_last] using hτ
    · intro i
      simpa only [w, Fin.lastCases_castSucc] using hθ i
  have hrouth := paperFixedBinding_routh_pattern_eventually_of_simpleNeutral
    m ξR hξR r τ ε θ hθ hr hτ hε hε1 hD hB hbase hk hx heq hET hFT hspec
  have hconversion := arbitrarySplit_conversion_positive_near_zero
    (m+1) ξR r (ne_of_gt (lt_trans zero_lt_one hr)) hD hB
  have hroots : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j : Fin (2*(m+1)+1), 1 < offsetSplitRoot ξR δ j.val := by
    have h := (offsetSplitRoot_gt_one_eventually (m+1) ξR).filter_mono
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    filter_upwards [h] with δ hδ j
    exact hδ j.val (by omega)
  obtain ⟨d, hpattern, hconversion, hroots, hδ⟩ :=
    eventually_right_has_halving_index _
      (hrouth.and (hconversion.and (hroots.and self_mem_nhdsWithin)))
  let δ : ℝ := (1/2 : ℝ)^d
  let kδ := paperFixedBindingSplitRates m ξR r δ ε w
  let f := arbitrarySplitFiniteState (m+1) ξR r δ
  have hsource (j : Fin (2*(m+1)+1)) := paperFixedBindingSplit_source
    m ξR r δ ε w hw hε hε1 hconversion.1 hconversion.2 j (hroots j)
  have hinjective : Function.Injective f :=
    arbitrarySplitFiniteState_injective_of_positive_split
      (m+1) ξR hξR r δ hδ hroots
  have hexact : {s : State (m+2) | s.Positive ∧ Equilibrium kδ s ∧
      InClass (2*r) 2 (2*(r+1)) s} = Set.range f :=
    paperFixedBindingSplit_positive_equilibria_exact_family
      m ξR hξR r τ δ ε θ (lt_trans zero_lt_one hr) hτ hθ hδ hε hε1
        hconversion.1 hconversion.2 hroots
  have hcount : {s : State (m+2) | s.Positive ∧ Equilibrium kδ s ∧
      InClass (2*r) 2 (2*(r+1)) s}.ncard = 2*(m+1)+1 := by
    rw [hexact]
    simpa [f] using Set.ncard_range_of_injective hinjective
  have hrRat : RationalReal r := by
    refine ⟨(2 : ℚ)^a, ?_⟩
    push_cast
    rfl
  have htRat : RationalReal t := by
    refine ⟨(1/2 : ℚ)^b, ?_⟩
    push_cast
    rfl
  have hεRat : RationalReal ε := by
    refine ⟨(1/2 : ℚ)^c, ?_⟩
    push_cast
    rfl
  have hδRat : RationalReal δ := by
    refine ⟨(1/2 : ℚ)^d, ?_⟩
    push_cast
    rfl
  have hxRat := coalescedFiniteState_rational_of_rational_source m hrRat
  have hτRat : RationalReal τ := by
    obtain ⟨tQ, htQ⟩ := htRat
    obtain ⟨dQ, hdQ⟩ := hxRat.2.2.2.2 (Fin.last (m+1))
    refine ⟨tQ/dQ, ?_⟩
    change ((tQ/dQ : ℚ) : ℝ) = t/x.D (Fin.last (m+1))
    rw [Rat.cast_div, htQ, hdQ]
  have hθRat (i : Fin (m+1)) : RationalReal (θ i) := by
    obtain ⟨dQ, hdQ⟩ := hxRat.2.2.2.2 i.castSucc
    refine ⟨1/dQ, ?_⟩
    change ((1/dQ : ℚ) : ℝ) = 1/x.D i.castSucc
    rw [Rat.cast_div, Rat.cast_one, hdQ]
  have hwRat (i : Fin (m+2)) : RationalReal (w i) := by
    refine Fin.lastCases (motive := fun i => RationalReal (w i)) ?_ ?_ i
    · simpa only [w, Fin.lastCases_last] using hτRat
    · intro i
      simpa only [w, Fin.lastCases_castSucc] using hθRat i
  obtain ⟨hkRat, hfRat⟩ := paperFixedBindingSplit_rational_offsets
    m ξR w hrRat hδRat hεRat (fun i => ⟨ξ i, rfl⟩) hwRat
  refine ⟨a, b, c, hr, hrAdequate, ht, hτ, hε, hε1, hD, hB,
    hθ, hbase, hk, hx, heq, hET, hFT, hspec, hprefix, hfinal,
    Q, hQ, d, ?_, (hsource 0).1, hkRat, ?_, hinjective, hexact, hcount, ?_⟩
  · intro j
    rw [rationalLocalRouthAccepts_iff, hQ]
    simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hpattern j
  · intro j
    exact ⟨(hsource j).2.1, hfRat j, (hsource j).2.2.1, (hsource j).2.2.2⟩
  · intro j i
    have hgamma : kδ.gamma i = w i := by
      change (paperFixedBindingRates
        (edgeScaledRates w (arbitrarySplitFiniteRates (m+1) ξR r δ))).gamma i = w i
      exact (paperFixedBindingSplit_unrelaxed_frozen_scales m ξR r δ w i).2.2
    refine ⟨equilibrium_catalytic_balance kδ (f j) (hsource j).2.2.1 i,
      mul_pos (((hsource 0).1 i).2.2.2.2.2) (((hsource j).2.1).2.2.2.2 i), ?_⟩
    exact congrArg (fun z : ℝ => z*(f j).D i) hgamma

/-- The common coalesced characteristic polynomial has its neutral factor
because the actual physical root-gap identity vanishes at zero splitting.
This proof requires no spectral certificate or deflation hypothesis. -/
theorem paperFixedBinding_coalesced_charpoly_coeff_zero
    (m : ℕ) (ξ : ℕ → ℝ) (r ε : ℝ) (w : Fin (m+2) → ℝ)
    (hw : ∀ i, 0 < w i) (hr : 1 < r) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1)) :
    (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (relaxRates (paperFixedBindingRates (coalescedAllScaledRates m r w)) ε)
      (fromLoadedCoord (loadedCoordOfState
        (coalescedFiniteState (m+1) r)))).charpoly.coeff 0 = 0 := by
  have hD : DensePositive (arbitrarySplitRawD (m+1) ξ r 0) (m+1) := by
    simpa [arbitrarySplitRawD, coalescedRawD,
      arbitrarySplitPair_zero_eq_coalesced] using hD₀
  have hB : DensePositive (arbitrarySplitRawB (m+1) ξ r 0) (m+1) := by
    simpa [arbitrarySplitRawB, coalescedRawB,
      arbitrarySplitPair_zero_eq_coalesced] using hB₀
  let j : Fin (2*(m+1)+1) := 0
  have hy : 1 < offsetSplitRoot ξ 0 j.val := by norm_num [offsetSplitRoot]
  have hv : 0 < r-ratio (offsetSplitRoot ξ 0 j.val) := by
    norm_num [offsetSplitRoot, ratio]
    linarith
  obtain ⟨hk, hx, heq, hclass⟩ := paperFixedBindingSplit_source
    m ξ r 0 ε w hw hε hε1 hD hB j hy
  have hconstant := arbitrarySplitGeneric_charpoly_constant_root_gap
    m ξ r 0 (paperFixedBindingSplitRates m ξ r 0 ε w) hk hD hB j hy hv
      heq hclass.1 hclass.2.1 hclass.2.2
  rw [paperFixedBindingSplit_restrictedJacobianMatrix_zero_eq_coalesced] at hconstant
  simpa [show 2*(m+1) ≠ 0 by omega] using hconstant

set_option maxHeartbeats 800000 in
/-- Every accepted coalesced deflation branch of this same rational family
is spectrally sound. The zero factor and the polynomial cast are both
derived from the literal physical family, rather than assumed certificates. -/
theorem paperFixedBinding_coalesced_rational_routh_acceptance_sound
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (ω : Fin (m+1) → ℝ)
    (hω : ∀ i, 0 < ω i) (hr : 1 < r) (hτ : 0 < τ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (Q : Fin (2*(m+1)+1) → ℚ → ℚ[X])
    (hQ : ∀ j δ, (Q j δ).map (algebraMap ℚ ℝ) =
      paperFixedBindingRouthPolynomial m ξ r τ ε (δ : ℝ) ω j)
    (haccept : rationalNeutralDeflationRouthAccepts
      (3*(m+2)-1) (Q 0 0).divX = true) :
    SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
        (fromLoadedCoord (loadedCoordOfState
          (coalescedFiniteState (m+1) r)))) := by
  let w : Fin (m+2) → ℝ := Fin.lastCases (motive := fun _ => ℝ) τ ω
  let J₀ : Matrix (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2)))
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) ℝ :=
    restrictedJacobianMatrix (2*r) 2 (2*(r+1))
    (relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r w)) ε)
    (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r)))
  change SimpleNeutralHurwitzComplement J₀
  have hw (i : Fin (m+2)) : 0 < w i := by
    refine Fin.lastCases (motive := fun i => 0 < w i) ?_ ?_ i
    · simpa only [w, Fin.lastCases_last] using hτ
    · intro i
      simpa only [w, Fin.lastCases_castSucc] using hω i
  have hzero : J₀.charpoly.coeff 0 = 0 :=
    paperFixedBinding_coalesced_charpoly_coeff_zero
      m ξ r ε w hw hr hε hε1 hD₀ hB₀
  have hpolyzero := congrArg
    (fun A : Matrix (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2)))
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) ℝ => A.charpoly)
    (paperFixedBindingSplit_restrictedJacobianMatrix_zero_eq_coalesced
      m ξ r ε w (0 : Fin (2*(m+1)+1)))
  change paperFixedBindingRouthPolynomial m ξ r τ ε 0 ω 0 = J₀.charpoly at hpolyzero
  have hcastAtZero : (Q 0 0).map (algebraMap ℚ ℝ) =
      paperFixedBindingRouthPolynomial m ξ r τ ε 0 ω 0 := by
    simpa only [Rat.cast_zero] using hQ 0 0
  have hcast : (Q 0 0).map (algebraMap ℚ ℝ) = J₀.charpoly :=
    hcastAtZero.trans hpolyzero
  have hcastDiv : (Q 0 0).divX.map (algebraMap ℚ ℝ) = J₀.charpoly.divX := by
    have hmapDiv : (Q 0 0).divX.map (algebraMap ℚ ℝ) =
        ((Q 0 0).map (algebraMap ℚ ℝ)).divX := by
      ext n
      simp only [Polynomial.coeff_divX, Polynomial.coeff_map]
    exact hmapDiv.trans (congrArg Polynomial.divX hcast)
  exact rationalNeutralDeflationRouthAccepts_sound
    (ι := Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) J₀ (3*(m+2)-1) (Q 0 0).divX hzero hcastDiv haccept

/-- The original coalesced rational full-minor test accepts the same Q
whenever its actual coalesced matrix has the proved spectral certificate.
This supplies the original finite checker data for the existential design. -/
theorem paperFixedBinding_coalesced_rational_routh_accepts_of_simpleNeutral
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (ω : Fin (m+1) → ℝ)
    (Q : Fin (2*(m+1)+1) → ℚ → ℚ[X])
    (hQ : ∀ j δ, (Q j δ).map (algebraMap ℚ ℝ) =
      paperFixedBindingRouthPolynomial m ξ r τ ε (δ : ℝ) ω j)
    (hspec : SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
        (fromLoadedCoord (loadedCoordOfState
          (coalescedFiniteState (m+1) r))))) :
    rationalNeutralDeflationRouthAccepts
      (3*(m+2)-1) (Q 0 0).divX = true := by
  let J₀ := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
    (relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
    (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r)))
  have hpolyzero := congrArg Matrix.charpoly
    (paperFixedBindingSplit_restrictedJacobianMatrix_zero_eq_coalesced
      m ξ r ε (Fin.lastCases τ ω) (0 : Fin (2*(m+1)+1)))
  change paperFixedBindingRouthPolynomial m ξ r τ ε 0 ω 0 = J₀.charpoly at hpolyzero
  have hcastAtZero : (Q 0 0).map (algebraMap ℚ ℝ) =
      paperFixedBindingRouthPolynomial m ξ r τ ε 0 ω 0 := by
    simpa only [Rat.cast_zero] using hQ 0 0
  have hcast : (Q 0 0).map (algebraMap ℚ ℝ) = J₀.charpoly :=
    hcastAtZero.trans hpolyzero
  have hcastDiv : (Q 0 0).divX.map (algebraMap ℚ ℝ) = J₀.charpoly.divX := by
    rw [← hcast]
    ext n
    simp [Polynomial.coeff_divX, Polynomial.coeff_map]
  have hcard : Fintype.card (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) =
      3*(m+2) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  rw [rationalNeutralDeflationRouthAccepts_iff_real_minors, hcastDiv]
  refine ⟨?_, ?_⟩
  · rw [characteristic_deflation_natDegree, hcard]
  · intro k
    have hk : k.val+1 ≤
        Fintype.card (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2)))-1 := by
      rw [hcard]
      omega
    simpa only [hcard] using
      simpleNeutral_real_charpoly_divX_routh_minors_positive J₀ hspec (k.val+1) hk

end
end PhosphorylationStableCapacity

