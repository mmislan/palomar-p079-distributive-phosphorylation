module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingRouthMinorAdmission435
public import proofs.PhosphorylationStableCapacity.SelectedTransverseStability435
public import proofs.PhosphorylationStableCapacity.RouthSignedHurwitzMinorCriterion435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Matrix

/-- Exact casts to an actual matrix characteristic polynomial supply all
the degree and leading-coefficient inputs of the original rational checker.
These properties are derived for every parameter, without spectral premises. -/
theorem rational_actual_charpoly_degree_monic_leading
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (p : ℚ[X])
    (hcast : p.map (algebraMap ℚ ℝ) = J.charpoly) :
    p.natDegree = Fintype.card ι ∧ p.Monic ∧ p.leadingCoeff = 1 := by
  have hdegree : (p.map (algebraMap ℚ ℝ)).natDegree = Fintype.card ι := by
    rw [hcast, Matrix.charpoly_natDegree_eq_dim]
  have hmonic : p.Monic := by
    apply Polynomial.monic_of_injective (show Function.Injective (algebraMap ℚ ℝ) from
      Rat.cast_injective)
    rw [hcast]
    exact J.charpoly_monic
  exact ⟨by simpa only [Polynomial.natDegree_map] using hdegree,
    hmonic, hmonic.leadingCoeff⟩

/-- In the literal fixed-binding rational family, the declared degree is
exactly 3n and the leading coefficient is exactly one, at EVERY rational
distance and EVERY labelled equilibrium. -/
theorem paperFixedBinding_rational_routh_polynomial_data
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (ω : Fin (m+1) → ℝ)
    (Q : Fin (2*(m+1)+1) → ℚ → ℚ[X])
    (hQ : ∀ j δ, (Q j δ).map (algebraMap ℚ ℝ) =
      paperFixedBindingRouthPolynomial m ξ r τ ε (δ : ℝ) ω j)
    (j : Fin (2*(m+1)+1)) (δ : ℚ) :
    (Q j δ).natDegree = 3*(m+2) ∧ (Q j δ).Monic ∧ (Q j δ).leadingCoeff = 1 := by
  have h := rational_actual_charpoly_degree_monic_leading
    (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (paperFixedBindingSplitRates m ξ r (δ : ℝ) ε (Fin.lastCases τ ω))
      (toCoordinateSpace (chart (arbitrarySplitFiniteState (m+1) ξ r (δ : ℝ) j))))
    (Q j δ) (hQ j δ)
  have hcard : Fintype.card (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) =
      3*(m+2) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  simpa only [hcard] using h

/-- The actual coalesced matrix is certified by every accepted rational
coalesced branch under its physical positivity guards. There is no assumed
neutral-spectrum, zero-factor, or deflation-cast certificate. -/
theorem paperFixedBinding_accepted_coalesced_branch_simpleNeutral
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
          (coalescedFiniteState (m+1) r)))) :=
  paperFixedBinding_coalesced_rational_routh_acceptance_sound
    m ξ r τ ε ω hω hr hτ hε hε1 hD₀ hB₀ Q hQ haccept

/-- Every accepted even Boolean branch proves Hurwitz stability of the
ACTUAL restricted matrix. Degree and positive leading coefficient are
derived from the characteristic correspondence, not passed as assumptions. -/
theorem paperFixedBinding_accepted_even_branch_linearlyStable
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (ω : Fin (m+1) → ℝ)
    (Q : Fin (2*(m+1)+1) → ℚ → ℚ[X])
    (hQ : ∀ j δ, (Q j δ).map (algebraMap ℚ ℝ) =
      paperFixedBindingRouthPolynomial m ξ r τ ε (δ : ℝ) ω j)
    (j : Fin (2*(m+1)+1)) (δ : ℚ) (heven : Even j.val)
    (haccept : rationalLocalRouthAccepts (3*(m+2)) (Q j δ)
      (decide (Odd j.val)) = true) :
    IsLinearlyStable (2*r) 2 (2*(r+1))
      (paperFixedBindingSplitRates m ξ r (δ : ℝ) ε (Fin.lastCases τ ω))
      (toCoordinateSpace (chart (arbitrarySplitFiniteState (m+1) ξ r (δ : ℝ) j))) := by
  obtain ⟨hdegree, _hmonic, hleading⟩ :=
    paperFixedBinding_rational_routh_polynomial_data m ξ r τ ε ω Q hQ j δ
  have hleadingpos : 0 < (Q j δ).leadingCoeff := by rw [hleading]; norm_num
  have hnotodd : ¬Odd j.val := Nat.not_odd_iff_even.mpr heven
  have hfalse : rationalLocalRouthAccepts (3*(m+2)) (Q j δ) false = true := by
    simpa only [hnotodd, decide_false] using haccept
  have hstable := rationalLocalRouthAccepts_even_sound
    (3*(m+2)) (Q j δ) hdegree hleadingpos hfalse
  change IsHurwitz _
  simpa only [IsHurwitz, Matrix.charpoly_map, hQ, paperFixedBindingRouthPolynomial]
    using hstable

/-- Every accepted even branch with the actual physical guards is a
nonlinear locally asymptotically stable class equilibrium. All rate, state,
equilibrium and class hypotheses are supplied by the literal family source. -/
theorem paperFixedBinding_accepted_even_branch_nonlinearSink
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (ω : Fin (m+1) → ℝ)
    (hr : 0 < r) (hτ : 0 < τ) (hω : ∀ i, 0 < ω i)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (Q : Fin (2*(m+1)+1) → ℚ → ℚ[X])
    (hQ : ∀ j δ, (Q j δ).map (algebraMap ℚ ℝ) =
      paperFixedBindingRouthPolynomial m ξ r τ ε (δ : ℝ) ω j)
    (j : Fin (2*(m+1)+1)) (δ : ℚ)
    (hD : DensePositive (arbitrarySplitRawD (m+1) ξ r (δ : ℝ)) (m+1))
    (hB : DensePositive (arbitrarySplitRawB (m+1) ξ r (δ : ℝ)) (m+1))
    (hy : 1 < offsetSplitRoot ξ (δ : ℝ) j.val) (heven : Even j.val)
    (haccept : rationalLocalRouthAccepts (3*(m+2)) (Q j δ)
      (decide (Odd j.val)) = true) :
    IsLinearlyStable (2*r) 2 (2*(r+1))
      (paperFixedBindingSplitRates m ξ r (δ : ℝ) ε (Fin.lastCases τ ω))
      (toCoordinateSpace (chart (arbitrarySplitFiniteState (m+1) ξ r (δ : ℝ) j))) ∧
    IsLocallyAsymptoticallyStableClass (2*r) 2 (2*(r+1))
      (paperFixedBindingSplitRates m ξ r (δ : ℝ) ε (Fin.lastCases τ ω))
      (toCoordinateSpace (chart (arbitrarySplitFiniteState (m+1) ξ r (δ : ℝ) j))) := by
  have hw (i : Fin (m+2)) :
      (0 : ℝ) < Fin.lastCases (motive := fun _ => ℝ) τ ω i := by
    refine Fin.lastCases (motive := fun i =>
      (0 : ℝ) < Fin.lastCases (motive := fun _ => ℝ) τ ω i) ?_ ?_ i
    · simpa only [Fin.lastCases_last] using hτ
    · intro i
      simpa only [Fin.lastCases_castSucc] using hω i
  obtain ⟨hk, hs, heq, hclass⟩ := paperFixedBindingSplit_source
    m ξ r (δ : ℝ) ε (Fin.lastCases τ ω) hw hε hε1 hD hB j hy
  have hstable := paperFixedBinding_accepted_even_branch_linearlyStable
    m ξ r τ ε ω Q hQ j δ heven haccept
  exact ⟨hstable, positiveClassEquilibrium_nonlinear_sink
    (by omega : 1 ≤ m+2) (2*r) 2 (2*(r+1))
    (mul_pos (by norm_num : (0 : ℝ) < 2) hr) _ hk _ hs heq hclass hstable⟩

/-- Every accepted odd branch has exactly one simple positive real
eigenvalue and a strictly Hurwitz complement in the ACTUAL class Jacobian.
The same literal Q and characteristic degree are retained throughout. -/
theorem paperFixedBinding_accepted_odd_branch_oneUnstableSaddle
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (ω : Fin (m+1) → ℝ)
    (Q : Fin (2*(m+1)+1) → ℚ → ℚ[X])
    (hQ : ∀ j δ, (Q j δ).map (algebraMap ℚ ℝ) =
      paperFixedBindingRouthPolynomial m ξ r τ ε (δ : ℝ) ω j)
    (j : Fin (2*(m+1)+1)) (δ : ℚ) (hodd : Odd j.val)
    (haccept : rationalLocalRouthAccepts (3*(m+2)) (Q j δ)
      (decide (Odd j.val)) = true) :
    IsOneUnstableSaddle (2*r) 2 (2*(r+1))
      (paperFixedBindingSplitRates m ξ r (δ : ℝ) ε (Fin.lastCases τ ω))
      (toCoordinateSpace (chart (arbitrarySplitFiniteState (m+1) ξ r (δ : ℝ) j))) := by
  obtain ⟨hdegree, _hmonic, hleading⟩ :=
    paperFixedBinding_rational_routh_polynomial_data m ξ r τ ε ω Q hQ j δ
  have hleadingpos : 0 < (Q j δ).leadingCoeff := by rw [hleading]; norm_num
  have htrue : rationalLocalRouthAccepts (3*(m+2)) (Q j δ) true = true := by
    simpa only [hodd, decide_true] using haccept
  have hsigned := rationalLocalRouthAccepts_odd_sound
    (3*(m+2)) (Q j δ) hdegree hleadingpos htrue
  let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
    (paperFixedBindingSplitRates m ξ r (δ : ℝ) ε (Fin.lastCases τ ω))
    (toCoordinateSpace (chart (arbitrarySplitFiniteState (m+1) ξ r (δ : ℝ) j)))
  have hactual : ∃ u : ℝ, 0 < u ∧
      ((J.map (algebraMap ℝ ℂ)).charpoly).eval (u : ℂ) = 0 ∧
      ((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (u : ℂ) ≠ 0 ∧
      ∀ z : ℂ, ((J.map (algebraMap ℝ ℂ)).charpoly).eval z = 0 →
        z = (u : ℂ) ∨ z.re < 0 := by
    simpa only [J, Matrix.charpoly_map, hQ, paperFixedBindingRouthPolynomial] using hsigned
  obtain ⟨u, hu, hroot, hsimple, hclass⟩ := hactual
  have hrealroot : J.charpoly.IsRoot u := by
    change J.charpoly.eval u = 0
    have hmap : (J.charpoly.map (algebraMap ℝ ℂ)).eval (u : ℂ) =
        ((J.charpoly.eval u : ℝ) : ℂ) := by
      simpa only [Complex.coe_algebraMap] using Polynomial.eval_map_apply
        (p := J.charpoly) (f := algebraMap ℝ ℂ) u
    have hcast : ((J.charpoly.eval u : ℝ) : ℂ) = 0 := by
      have hc := hroot
      rw [Matrix.charpoly_map, hmap] at hc
      exact hc
    exact_mod_cast hcast
  change ∃ u : ℝ, 0 < u ∧ J.charpoly.IsRoot u ∧
    ((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (u : ℂ) ≠ 0 ∧
    ∀ z : ℂ, z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) → z.re < 0 ∨ z = (u : ℂ)
  refine ⟨u, hu, hrealroot, hsimple, ?_⟩
  intro z hz
  exact (hclass z (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz)).symm

/-- Every accepted branch of the original odd/even rational checker has
the intended actual class-Jacobian classification, with no spectral premise. -/
theorem paperFixedBinding_accepted_branch_sink_or_saddle
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (ω : Fin (m+1) → ℝ)
    (Q : Fin (2*(m+1)+1) → ℚ → ℚ[X])
    (hQ : ∀ j δ, (Q j δ).map (algebraMap ℚ ℝ) =
      paperFixedBindingRouthPolynomial m ξ r τ ε (δ : ℝ) ω j)
    (j : Fin (2*(m+1)+1)) (δ : ℚ)
    (haccept : rationalLocalRouthAccepts (3*(m+2)) (Q j δ)
      (decide (Odd j.val)) = true) :
    (Even j.val → IsLinearlyStable (2*r) 2 (2*(r+1))
      (paperFixedBindingSplitRates m ξ r (δ : ℝ) ε (Fin.lastCases τ ω))
      (toCoordinateSpace (chart (arbitrarySplitFiniteState (m+1) ξ r (δ : ℝ) j)))) ∧
    (Odd j.val → IsOneUnstableSaddle (2*r) 2 (2*(r+1))
      (paperFixedBindingSplitRates m ξ r (δ : ℝ) ε (Fin.lastCases τ ω))
      (toCoordinateSpace (chart (arbitrarySplitFiniteState (m+1) ξ r (δ : ℝ) j)))) :=
  ⟨fun heven => paperFixedBinding_accepted_even_branch_linearlyStable
      m ξ r τ ε ω Q hQ j δ heven haccept,
    fun hodd => paperFixedBinding_accepted_odd_branch_oneUnstableSaddle
      m ξ r τ ε ω Q hQ j δ hodd haccept⟩

end
end PhosphorylationStableCapacity
