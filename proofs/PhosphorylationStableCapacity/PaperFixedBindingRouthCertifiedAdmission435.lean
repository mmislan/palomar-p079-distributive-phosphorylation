module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingRouthAcceptedBranch435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingOrderedAdmissibility435

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Polynomial Matrix

/-- The same a,b,c,Q,d, physical rational system and COMPLETE common
equilibrium list now carry the actual sink/saddle classification as well.
Even members are both linearly and nonlinearly class stable; odd members
have one simple unstable direction. No spectral condition is passed to the
checker: the original accepted minor data imply the actual spectra. -/
theorem paperFixedBinding_all_size_rational_routh_certified_admission (m : ℕ) (ξ : ℕ → ℚ) (hξ : StrictMono ξ) :
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
          (∀ j : Fin (2*(m+1)+1), ∀ i : Fin (m+2),
            kδ.c i*(f j).C i = kδ.gamma i*(f j).D i ∧
            0 < kδ.gamma i*(f j).D i ∧
            kδ.gamma i*(f j).D i = (Fin.lastCases τ θ i)*(f j).D i ) ∧
          ∀ j : Fin (2*(m+1)+1),
            (Even j.val →
              IsLinearlyStable (2*r) 2 (2*(r+1)) kδ (toCoordinateSpace (chart (f j))) ∧
              IsLocallyAsymptoticallyStableClass (2*r) 2 (2*(r+1)) kδ
                (toCoordinateSpace (chart (f j)))) ∧
            (Odd j.val →
              IsOneUnstableSaddle (2*r) 2 (2*(r+1)) kδ (toCoordinateSpace (chart (f j)))) := by
  obtain ⟨a, b, c, hr, hrAdequate, ht, hτ, hε, hε1, hD, hB,
    hθ, hbase, hk, hx, heq, hET, hFT, hspec, hprefix, hfinal,
    Q, hQ, d, haccept, hkδ, hkRat, hstates, hinjective, hexact, hcount, hcurrents⟩ :=
    paperFixedBinding_all_size_rational_routh_physical_admission m ξ hξ
  let r : ℝ := (2 : ℝ)^a
  let t : ℝ := (1/2 : ℝ)^b
  let ε : ℝ := (1/2 : ℝ)^c
  let x := coalescedFiniteState (m+1) r
  let τ : ℝ := t/x.D (Fin.last (m+1))
  let θ : Fin (m+1) → ℝ := fun i => 1/x.D i.castSucc
  let δ : ℝ := (1/2 : ℝ)^d
  let kδ := paperFixedBindingSplitRates m (fun i => (ξ i : ℝ)) r δ ε (Fin.lastCases τ θ)
  let f := arbitrarySplitFiniteState (m+1) (fun i => (ξ i : ℝ)) r δ
  refine ⟨a, b, c, hr, hrAdequate, ht, hτ, hε, hε1, hD, hB,
    hθ, hbase, hk, hx, heq, hET, hFT, hspec, hprefix, hfinal,
    Q, hQ, d, haccept, hkδ, hkRat, hstates, hinjective, hexact, hcount, hcurrents, ?_⟩
  intro j
  have hclassification := paperFixedBinding_accepted_branch_sink_or_saddle
    m (fun i => (ξ i : ℝ)) r τ ε θ Q hQ j ((1/2 : ℚ)^d) (haccept j)
  constructor
  · intro heven
    have hstable : IsLinearlyStable (2*r) 2 (2*(r+1)) kδ
        (toCoordinateSpace (chart (f j))) := by
      simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
        (hclassification.1 heven)
    exact ⟨hstable, positiveClassEquilibrium_nonlinear_sink
      (by omega : 1 ≤ m+2) (2*r) 2 (2*(r+1))
      (mul_pos (by norm_num : (0 : ℝ) < 2) (lt_trans zero_lt_one hr))
      kδ hkδ (f j) (hstates j).1 (hstates j).2.2.1 (hstates j).2.2.2 hstable⟩
  · intro hodd
    simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (hclassification.2 hodd)

/-- Exact coalesced checker for an indexed rational characteristic family.
The rational producer can be instantiated by the computable paper producer. -/
def rationalRouthFamilyCoalescedAccepts (m : ℕ)
    (Q : ℕ → ℕ → ℕ → Fin (2*(m+1)+1) → ℚ → ℚ[X]) (a b c : ℕ) : Bool :=
  rationalNeutralDeflationRouthAccepts (3*(m+2)-1) (Q a b c 0 0).divX

/-- The original simultaneous odd/even test at the SAME halving index. -/
def rationalRouthFamilySplitAccepts (m : ℕ)
    (Q : ℕ → ℕ → ℕ → Fin (2*(m+1)+1) → ℚ → ℚ[X]) (a b c d : ℕ) : Bool :=
  decide (∀ j : Fin (2*(m+1)+1),
    rationalLocalRouthAccepts (3*(m+2)) (Q a b c j ((1/2 : ℚ)^d))
      (decide (Odd j.val)) = true)

/-- EVERY first-success output of the four ordered physical/spectral loops
has the actual rational equilibrium list and sink/saddle classification.
The inputs are the original arithmetic tests and exact characteristic cast;
no simple-neutral, Hurwitz or signed-spectrum premise is supplied. The same
a,b,c,d and frozen coalesced current factors are retained in the conclusion. -/
theorem orderedRationalRouthDesign_certified_same_family
    (m : ℕ) (ξ : ℕ → ℚ) (hξ : StrictMono ξ)
    (prefixTest : ℕ → Bool) (slow : ℕ → ℕ → Bool)
    (Q : ℕ → ℕ → ℕ → Fin (2*(m+1)+1) → ℚ → ℚ[X])
    (hQ : ∀ a b c j δ,
      let r : ℝ := (((2 : ℚ)^a : ℚ) : ℝ)
      let t : ℝ := (((1/2 : ℚ)^b : ℚ) : ℝ)
      let ε : ℝ := (((1/2 : ℚ)^c : ℚ) : ℝ)
      let x := coalescedFiniteState (m+1) r
      (Q a b c j δ).map (algebraMap ℚ ℝ) =
        paperFixedBindingRouthPolynomial m (fun i => (ξ i : ℝ))
          r (t/x.D (Fin.last (m+1))) ε (δ : ℝ)
          (fun i => 1/x.D i.castSucc) j)
    (a b c d : ℕ)
    (haccepted : OrderedDesignAccepted
      (orderedRationalPhysicalPrefixTest m prefixTest) slow
      (rationalRouthFamilyCoalescedAccepts m Q)
      (orderedRationalPhysicalSplitTest m ξ (rationalRouthFamilySplitAccepts m Q))
      a b c d) :
    let r : ℝ := (((2 : ℚ)^a : ℚ) : ℝ)
    let t : ℝ := (((1/2 : ℚ)^b : ℚ) : ℝ)
    let ε : ℝ := (((1/2 : ℚ)^c : ℚ) : ℝ)
    let δ : ℝ := (((1/2 : ℚ)^d : ℚ) : ℝ)
    let x := coalescedFiniteState (m+1) r
    let τ : ℝ := t/x.D (Fin.last (m+1))
    let θ : Fin (m+1) → ℝ := fun i => 1/x.D i.castSucc
    let w := Fin.lastCases τ θ
    let k₀ := relaxRates (paperFixedBindingRates (coalescedAllScaledRates m r w)) ε
    let k := paperFixedBindingSplitRates m (fun i => (ξ i : ℝ)) r δ ε w
    let f := arbitrarySplitFiniteState (m+1) (fun i => (ξ i : ℝ)) r δ
    (3*(m+2 : ℝ))/2 ≤ r ∧
      SimpleNeutralHurwitzComplement
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k₀
          (fromLoadedCoord (loadedCoordOfState x))) ∧
      (∀ i : Fin (m+1), k₀.gamma i.castSucc*x.D i.castSucc = 1) ∧
      k₀.gamma (Fin.last (m+1))*x.D (Fin.last (m+1)) = t ∧
      k.Positive ∧ RationalRates k ∧
      (∀ j : Fin (2*(m+1)+1), (f j).Positive ∧ RationalState (f j) ∧
        Equilibrium k (f j) ∧ InClass (2*r) 2 (2*(r+1)) (f j)) ∧
      Function.Injective f ∧
      {s : State (m+2) | s.Positive ∧ Equilibrium k s ∧ InClass (2*r) 2 (2*(r+1)) s} =
        Set.range f ∧
      {s : State (m+2) | s.Positive ∧ Equilibrium k s ∧ InClass (2*r) 2 (2*(r+1)) s}.ncard =
        2*(m+1)+1 ∧
      (∀ j : Fin (2*(m+1)+1), ∀ i : Fin (m+2),
        k.c i*(f j).C i = k.gamma i*(f j).D i ∧
        0 < k.gamma i*(f j).D i ∧ k.gamma i*(f j).D i = w i*(f j).D i) ∧
      ∀ j : Fin (2*(m+1)+1),
        (Even j.val →
          IsLinearlyStable (2*r) 2 (2*(r+1)) k (toCoordinateSpace (chart (f j))) ∧
          IsLocallyAsymptoticallyStableClass (2*r) 2 (2*(r+1)) k
            (toCoordinateSpace (chart (f j)))) ∧
        (Odd j.val → IsOneUnstableSaddle (2*r) 2 (2*(r+1)) k
          (toCoordinateSpace (chart (f j)))) := by
  let r : ℝ := (((2 : ℚ)^a : ℚ) : ℝ)
  let t : ℝ := (((1/2 : ℚ)^b : ℚ) : ℝ)
  let ε : ℝ := (((1/2 : ℚ)^c : ℚ) : ℝ)
  let δ : ℝ := (((1/2 : ℚ)^d : ℚ) : ℝ)
  let ξR : ℕ → ℝ := fun i => (ξ i : ℝ)
  let x := coalescedFiniteState (m+1) r
  let τ : ℝ := t/x.D (Fin.last (m+1))
  let θ : Fin (m+1) → ℝ := fun i => 1/x.D i.castSucc
  let w : Fin (m+2) → ℝ := Fin.lastCases (motive := fun _ => ℝ) τ θ
  let k₀ := relaxRates (paperFixedBindingRates (coalescedAllScaledRates m r w)) ε
  let k := paperFixedBindingSplitRates m ξR r δ ε w
  let f := arbitrarySplitFiniteState (m+1) ξR r δ
  have hp : orderedRationalPrefixAdmits m ((2 : ℚ)^a) = true :=
    (Bool.and_eq_true_iff.mp haccepted.1.1).1
  obtain ⟨hr, hrAdequate, hD₀, hB₀⟩ := (orderedRationalPrefixAdmits_iff m ((2 : ℚ)^a)).mp hp
  have hx := orderedRationalPrefixAdmits_coalesced_positive m ((2 : ℚ)^a) hp
  have hxLocal : x.Positive := by
    simpa only [x, r, Rat.cast_pow, Rat.cast_ofNat] using hx
  have hDx (i : Fin (m+2)) : 0 < x.D i := hxLocal.2.2.2.2 i
  have ht : 0 < t := by
    change (0 : ℝ) < (((1/2 : ℚ)^b : ℚ) : ℝ)
    exact_mod_cast (pow_pos (by norm_num : (0 : ℚ) < 1/2) b)
  have hτ : 0 < τ := div_pos ht (hDx (Fin.last (m+1)))
  have hθ (i : Fin (m+1)) : 0 < θ i :=
    div_pos (by norm_num) (hDx i.castSucc)
  have hsplitPhysical : orderedRationalSplitAdmits m ξ
      ((2 : ℚ)^a) ((1/2 : ℚ)^d) ((1/2 : ℚ)^c) = true :=
    (Bool.and_eq_true_iff.mp haccepted.2.2.2.1).1
  obtain ⟨hrpos, hδ, hε, hε1, hroots, _hD, _hB⟩ :=
    (orderedRationalSplitAdmits_iff m ξ ((2 : ℚ)^a) ((1/2 : ℚ)^d) ((1/2 : ℚ)^c)).mp
      hsplitPhysical
  have hcoalesced : rationalNeutralDeflationRouthAccepts
      (3*(m+2)-1) (Q a b c 0 0).divX = true := haccepted.2.2.1.1
  have hlocal : ∀ j : Fin (2*(m+1)+1),
      rationalLocalRouthAccepts (3*(m+2)) (Q a b c j ((1/2 : ℚ)^d))
        (decide (Odd j.val)) = true := by
    have h := (Bool.and_eq_true_iff.mp haccepted.2.2.2.1).2
    simpa only [rationalRouthFamilySplitAccepts, decide_eq_true_eq] using h
  have hneutral := paperFixedBinding_accepted_coalesced_branch_simpleNeutral
    m ξR r τ ε θ hθ hr hτ hε hε1 hD₀ hB₀ (Q a b c) (hQ a b c) hcoalesced
  obtain ⟨_hrAdequate, hk, hkRat, hstates, hexact⟩ :=
    orderedRationalPhysicalDesign_rational_exact_family m ξ hξ prefixTest slow
      (rationalRouthFamilyCoalescedAccepts m Q) (rationalRouthFamilySplitAccepts m Q)
      a b c d haccepted
  have hξR : StrictMono ξR := by
    intro i j hij
    change (ξ i : ℝ) < (ξ j : ℝ)
    exact_mod_cast hξ hij
  have hinjective : Function.Injective f :=
    arbitrarySplitFiniteState_injective_of_positive_split (m+1) ξR hξR r δ hδ hroots
  have hcount : {s : State (m+2) | s.Positive ∧ Equilibrium k s ∧
      InClass (2*r) 2 (2*(r+1)) s}.ncard = 2*(m+1)+1 := by
    rw [hexact]
    simpa [f, ξR, r, δ] using Set.ncard_range_of_injective hinjective
  have hgamma₀ (i : Fin (m+2)) : k₀.gamma i = w i := by
    simp [k₀, relaxRates, paperFixedBindingRates, coalescedAllScaledRates,
      edgeScaledRates, coalescedFiniteRates, realize]
  have hprefix : ∀ i : Fin (m+1), k₀.gamma i.castSucc*x.D i.castSucc = 1 := by
    intro i
    rw [hgamma₀]
    simp only [w, Fin.lastCases_castSucc, θ]
    exact one_div_mul_cancel (hDx i.castSucc).ne'
  have hfinal : k₀.gamma (Fin.last (m+1))*x.D (Fin.last (m+1)) = t := by
    rw [hgamma₀]
    simp only [w, Fin.lastCases_last, τ]
    exact div_mul_cancel₀ t (hDx (Fin.last (m+1))).ne'
  refine ⟨hrAdequate, hneutral, hprefix, hfinal, hk, hkRat, hstates,
    hinjective, hexact, hcount, ?_, ?_⟩
  · intro j i
    have hgamma : k.gamma i = w i := by
      change (paperFixedBindingRates
        (edgeScaledRates w (arbitrarySplitFiniteRates (m+1) ξR r δ))).gamma i = w i
      exact (paperFixedBindingSplit_unrelaxed_frozen_scales m ξR r δ w i).2.2
    exact ⟨equilibrium_catalytic_balance k (f j) (hstates j).2.2.1 i,
      mul_pos ((hk i).2.2.2.2.2) ((hstates j).1.2.2.2.2 i),
      congrArg (fun z : ℝ => z*(f j).D i) hgamma⟩
  · intro j
    have hclassification := paperFixedBinding_accepted_branch_sink_or_saddle
      m ξR r τ ε θ (Q a b c) (hQ a b c) j ((1/2 : ℚ)^d) (hlocal j)
    constructor
    · intro heven
      have hstable := hclassification.1 heven
      exact ⟨hstable, positiveClassEquilibrium_nonlinear_sink
        (by omega : 1 ≤ m+2) (2*r) 2 (2*(r+1))
        (mul_pos (by norm_num : (0 : ℝ) < 2) hrpos)
        k hk (f j) (hstates j).1 (hstates j).2.2.1 (hstates j).2.2.2 hstable⟩
    · exact hclassification.2

end
end PhosphorylationStableCapacity
