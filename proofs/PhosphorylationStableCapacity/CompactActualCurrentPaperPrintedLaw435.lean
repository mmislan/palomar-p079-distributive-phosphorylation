module
public import proofs.PhosphorylationStableCapacity.CompactActualCurrentPaperSpectrum435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCompactAllRootsLaw435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingSourcePositiveTube435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingSplitCount435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitUniformReadout435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitReadoutOrder435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCompactSelectedAnalytic435
public import proofs.PhosphorylationStableCapacity.SplitReciprocalSlowLaw
public import proofs.PhosphorylationStableCapacity.SelectedTransverseStability435
public import proofs.PhosphorylationStableCapacity.LiteralPhosphorylationFlux435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingPrintedCoefficient

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Matrix Polynomial
open scoped Topology


set_option maxHeartbeats 400000 in
/-- The printed split law and exact positive equilibrium family use
one fixed-binding system for every actual prefix-current vector in
an arbitrary compact positive set. The final actual current, binding
scale, split interval, transverse margin, relative-error constant,
and quadratic readout constant are all common. -/
theorem compactActualCurrent_paperFixedBinding_printed_family
    (m : ℕ) (ξ : ℕ → ℝ) (hξ : StrictMono ξ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (K : Set (PositivePrefixCurrents m)), IsCompact K →
        ∃ t ε α Q Cread : ℝ,
          0 < t ∧ 0 < ε ∧ ε ≤ 1 ∧ 0 < α ∧ 0 < Q ∧ 0 < Cread ∧
          (∀ ω ∈ K, ∀ j : Fin (2*(m+1)+1),
            let w := Fin.lastCases
              (t/(coalescedFiniteState (m+1) r).D (Fin.last (m+1)))
              (fun i => ω.val i /
                (coalescedFiniteState (m+1) r).D i.castSucc)
            let selected := selectedTransverseRoot
              (fun (p : Fin (m+2) → ℝ) (s : ℝ) =>
                restrictedJacobianMatrix (2*r) 2 (2*(r+1))
                  (paperFixedBindingSplitRates m ξ r s ε p)
                  (toCoordinateSpace (chart
                    (arbitrarySplitFiniteState (m+1) ξ r s j))))
              α w
            AnalyticAt ℝ selected 0 ∧ selected 0 = 0) ∧
          ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
            (∀ j k : Fin (2*(m+1)+1),
              |(fullyPhosphorylatedReadout (m+1)
                  (arbitrarySplitFiniteState (m+1) ξ r δ j) -
                fullyPhosphorylatedReadout (m+1)
                  (arbitrarySplitFiniteState (m+1) ξ r δ k)) -
                (ξ j.val-ξ k.val) *
                  deriv (splitReadoutScalar (m+1)
                    (coalescedRawD (m+1) r)) 3 * δ| ≤
                Cread*δ^2) ∧
            StrictMono (fun j : Fin (2*(m+1)+1) =>
              fullyPhosphorylatedReadout (m+1)
                (arbitrarySplitFiniteState (m+1) ξ r δ j)) ∧
            ∀ ω ∈ K,
              let w := Fin.lastCases
                (t/(coalescedFiniteState (m+1) r).D (Fin.last (m+1)))
                (fun i => ω.val i /
                  (coalescedFiniteState (m+1) r).D i.castSucc)
              let k₀ := relaxRates (paperFixedBindingRates
                (coalescedAllScaledRates m r w)) ε
              let k := paperFixedBindingSplitRates m ξ r δ ε w
              (∀ i : Fin (m+1),
                k₀.gamma i.castSucc *
                  (coalescedFiniteState (m+1) r).D i.castSucc = ω.val i) ∧
              k₀.gamma (Fin.last (m+1)) *
                (coalescedFiniteState (m+1) r).D (Fin.last (m+1)) = t ∧
              k.Positive ∧
              Function.Injective
                (arbitrarySplitFiniteState (m+1) ξ r δ) ∧
              {x : State (m+2) |
                x.Positive ∧ Equilibrium k x ∧
                  InClass (2*r) 2 (2*(r+1)) x} =
                Set.range (arbitrarySplitFiniteState (m+1) ξ r δ) ∧
              {x : State (m+2) |
                x.Positive ∧ Equilibrium k x ∧
                  InClass (2*r) 2 (2*(r+1)) x}.ncard =
                2*(m+1)+1 ∧
              StrictMono (fun j : Fin (2*(m+1)+1) =>
                fullyPhosphorylatedReadout (m+1)
                  (arbitrarySplitFiniteState (m+1) ξ r δ j)) ∧
              0 < paperFixedBindingPrintedCoefficient m r
                (t/(coalescedFiniteState (m+1) r).D
                  (Fin.last (m+1))) ε
                (fun i => ω.val i /
                  (coalescedFiniteState (m+1) r).D i.castSucc) ∧
              (paperFixedBindingPrintedCoefficient m r
                (t/(coalescedFiniteState (m+1) r).D
                  (Fin.last (m+1))) ε
                (fun i => ω.val i /
                  (coalescedFiniteState (m+1) r).D i.castSucc) =
                let J₀ := restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k₀
                  (toCoordinateSpace (chart
                    (coalescedFiniteState (m+1) r)))
                let Θ₀ : ℂ :=
                  ((J₀.map (algebraMap ℝ ℂ)).charpoly.roots.erase 0).prod
                let P := coalescedPair (m+1)
                let D := coalescedRawD (m+1) r
                let B := coalescedRawB (m+1) r
                let C := 2*r*P.1.eval r+P.2.eval r
                let M := (B.eval 1-D.eval 1)/D.coeff 0
                (4*C*M/((r-1)*D.eval 1*‖Θ₀‖)) *
                  (∏ i : Fin (m+2),
                    (k₀.b i+k₀.c i)*k₀.alpha i*k₀.gamma i)) ∧
              ∀ j : Fin (2*(m+1)+1), ∃ lam : ℝ,
                let s := arbitrarySplitFiniteState (m+1) ξ r δ j
                let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k
                  (toCoordinateSpace (chart s))
                let selected := selectedTransverseRoot
                  (fun (p : Fin (m+2) → ℝ) (s : ℝ) =>
                    restrictedJacobianMatrix (2*r) 2 (2*(r+1))
                      (paperFixedBindingSplitRates m ξ r s ε p)
                      (toCoordinateSpace (chart
                        (arbitrarySplitFiniteState (m+1) ξ r s j))))
                  α w
                s.Positive ∧
                  0 < ∑ i : Fin (m+2), k.gamma i * s.D i ∧
                  Equilibrium k s ∧
                  InClass (2*r) 2 (2*(r+1)) s ∧
                  Real.sqrt (1+8*s.E/s.F) = 3+δ*ξ j.val ∧
                  AnalyticAt ℝ selected 0 ∧ selected 0 = 0 ∧
                  lam = selected δ ∧ J.charpoly.IsRoot lam ∧
                  ((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
                    (lam : ℂ) ≠ 0 ∧
                  (∀ z : ℂ, z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
                    z = (lam : ℂ) ∨ z.re ≤ -α) ∧
                  |lam / (-paperFixedBindingPrintedCoefficient m r
                      (t/(coalescedFiniteState (m+1) r).D
                        (Fin.last (m+1))) ε
                      (fun i => ω.val i /
                        (coalescedFiniteState (m+1) r).D i.castSucc) *
                      δ^(2*(m+1)) *
                        (∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
                          (ξ j.val-ξ i)))-1| ≤ Q*|δ| ∧
                  ∃ err : ℝ, |err| ≤ 2*Q*|δ| ∧
                    1/|lam| = (1+err)/
                      (paperFixedBindingPrintedCoefficient m r
                        (t/(coalescedFiniteState (m+1) r).D
                          (Fin.last (m+1))) ε
                        (fun i => ω.val i /
                          (coalescedFiniteState (m+1) r).D i.castSucc) *
                        |∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
                          (ξ j.val-ξ i)| * δ^(2*(m+1))) ∧
                  (Even j.val → lam < 0) ∧
                  (Odd j.val → 0 < lam) ∧
                  (Even j.val →
                    IsLinearlyStable (2*r) 2 (2*(r+1)) k
                      (toCoordinateSpace (chart
                        (arbitrarySplitFiniteState (m+1) ξ r δ j))) ∧
                    IsLocallyAsymptoticallyStableClass
                      (2*r) 2 (2*(r+1)) k
                      (toCoordinateSpace (chart
                        (arbitrarySplitFiniteState (m+1) ξ r δ j)))) ∧
                  (Odd j.val →
                    IsOneUnstableSaddle (2*r) 2 (2*(r+1)) k
                      (toCoordinateSpace (chart
                        (arbitrarySplitFiniteState (m+1) ξ r δ j)))) := by
  obtain ⟨hp, hq⟩ := coalescedPair_dense (m+1)
  filter_upwards [compactActualCurrent_paperFixedBinding_coalesced_exists m,
    coalescedFiniteState_eventually_equilibrium (m+1),
    coalescedAllScaledRates_eventually_source m,
    conversion_eventually_positive hp hq,
    eventually_gt_atTop 1]
    with r hactual hstate hscaled hconv hr
  intro K hK
  obtain ⟨_, hx₀, _, hET₀, hFT₀, _⟩ := hstate
  let Φ := edgePrefixFactorsOfActualCurrent m r hx₀
  let K' : Set (PositivePrefixCurrents m) := Φ '' K
  have hK' : IsCompact K' :=
    isCompact_edgePrefixFactorsOfActualCurrent_image m r hx₀ K hK
  obtain ⟨t, ε, ht, hε, hε1, hfamily⟩ := hactual K hK
  let τ := t/(coalescedFiniteState (m+1) r).D (Fin.last (m+1))
  have hτ : 0 < τ := div_pos ht (hx₀.2.2.2.2 (Fin.last (m+1)))
  have hw (a : PositivePrefixCurrents m) :
      ∀ i : Fin (m+2), 0 < Fin.lastCases (motive := fun _ => ℝ) τ a.val i := by
    intro i
    cases i using Fin.lastCases with
    | last => simpa [τ] using hτ
    | cast i => simpa using a.property i
  have hbase : ∀ a ∈ K',
      (coalescedAllScaledRates m r
        (Fin.lastCases τ a.val)).Positive := by
    intro a ha
    exact (hscaled _ (hw a)).1
  have heq₀ : ∀ a ∈ K',
      Equilibrium (relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r (Fin.lastCases τ a.val))) ε)
        (coalescedFiniteState (m+1) r) := by
    intro a ha
    obtain ⟨hk, heq⟩ := hscaled _ (hw a)
    exact relaxRates_preserves_equilibrium _ _ (ne_of_gt hε)
      (paperFixedBindingRates_preserves_equilibrium _ _ hk heq)
  have hspec : ∀ a ∈ K', SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r
            (Fin.lastCases τ a.val))) ε)
        (fromLoadedCoord (loadedCoordOfState
          (coalescedFiniteState (m+1) r)))) := by
    intro a ha
    rcases ha with ⟨ω, hω, rfl⟩
    simpa only [Φ, τ, edgePrefixFactorsOfActualCurrent]
      using (hfamily ω hω).2.2
  have hbase0 : (coalescedFiniteRates (m+1) r).Positive := by
    have h := (hscaled (fun _ => 1) (by intro i; norm_num)).1
    simpa [coalescedAllScaledRates, edgeScaledRates] using h
  have hsigned : ∀ᶠ δ : ℝ in 𝓝 0,
      (arbitrarySplitFiniteRates (m+1) ξ r δ).Positive :=
    arbitrarySplitFiniteRates_positive_signed_near_zero
      m ξ r (by linarith : r ≠ 0) hconv.1 hconv.2 hbase0
  obtain ⟨α, hα, hgap⟩ :=
    compact_paperFixedBinding_all_split_slowMode_uniform_gap
      m ξ r τ ε K' hK' (by linarith : r ≠ 0)
      hconv.1 hconv.2 hbase hspec
  have hanalytic :=
    (paperFixedBinding_compact_selected_root_analyticAt
      m ξ r τ ε K' hK' (by linarith : r ≠ 0)
      hconv.1 hconv.2 hbase hspec α hα hgap).2
  obtain ⟨Q, hQ, hlaw⟩ :=
    paperFixedBinding_compact_all_roots_relative_law
      m ξ hξ r τ ε K' hK' hr hτ hε hε1
      hconv.1 hconv.2 hx₀ hbase0 hsigned
      hbase heq₀ hET₀ hFT₀ hspec α hα hgap
  obtain ⟨Cread, hCread, hreadout⟩ :=
    arbitrarySplitReadout_uniform_quadratic_remainder
      (m+1) ξ r (by linarith : r ≠ 0) hconv.1 hconv.2
  have hconversion := arbitrarySplit_conversion_positive_near_zero
    (m+1) ξ r (by linarith : r ≠ 0) hconv.1 hconv.2
  have hroot : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ i, i ≤ 2*(m+1) → 1 < offsetSplitRoot ξ δ i := by
    have h := offsetSplitRoot_gt_one_eventually (m+1) ξ
    exact h.filter_mono nhdsWithin_le_nhds
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      Q*|δ| ≤ 1/2 := by
    have hεQ : 0 < (1/2 : ℝ)/Q := div_pos (by norm_num) hQ
    have htube : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ),
        δ < (1/2 : ℝ)/Q := Iio_mem_nhds hεQ
    filter_upwards [htube.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with δ hδQ hδ
    rw [abs_of_pos hδ]
    have hmul : Q*δ ≤ Q*((1/2 : ℝ)/Q) :=
      mul_le_mul_of_nonneg_left hδQ.le hQ.le
    have hcancel : Q*((1/2 : ℝ)/Q) = 1/2 := by
      field_simp [ne_of_gt hQ]
    exact hmul.trans_eq hcancel
  have hanactual :
      ∀ ω ∈ K, ∀ j : Fin (2*(m+1)+1),
        let w := Fin.lastCases
          (t/(coalescedFiniteState (m+1) r).D (Fin.last (m+1)))
          (fun i => ω.val i /
            (coalescedFiniteState (m+1) r).D i.castSucc)
        let selected := selectedTransverseRoot
          (fun (p : Fin (m+2) → ℝ) (s : ℝ) =>
            restrictedJacobianMatrix (2*r) 2 (2*(r+1))
              (paperFixedBindingSplitRates m ξ r s ε p)
              (toCoordinateSpace (chart
                (arbitrarySplitFiniteState (m+1) ξ r s j))))
          α w
        AnalyticAt ℝ selected 0 ∧ selected 0 = 0 := by
    intro ω hω j
    have hΦ : Φ ω ∈ K' := ⟨ω, hω, rfl⟩
    let ι := Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))
    let Jsub : PositivePrefixCurrents m → ℝ → Matrix ι ι ℝ :=
      fun (p : PositivePrefixCurrents m) (s : ℝ) =>
      restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (paperFixedBindingSplitRates m ξ r s ε
          (Fin.lastCases τ p.val))
        (toCoordinateSpace (chart
          (arbitrarySplitFiniteState (m+1) ξ r s j)))
    let Jfull : (Fin (m+2) → ℝ) → ℝ → Matrix ι ι ℝ :=
      fun (p : Fin (m+2) → ℝ) (s : ℝ) =>
      restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (paperFixedBindingSplitRates m ξ r s ε p)
        (toCoordinateSpace (chart
          (arbitrarySplitFiniteState (m+1) ξ r s j)))
    have hmatrix (s : ℝ) :
        Jsub (Φ ω) s = Jfull (Fin.lastCases τ (Φ ω).val) s := rfl
    have hselected :
        selectedTransverseRoot Jsub α (Φ ω) =
          selectedTransverseRoot Jfull α
            (Fin.lastCases τ (Φ ω).val) := by
      classical
      funext s
      unfold selectedTransverseRoot
      exact congrArg (fun M : Matrix ι ι ℝ =>
        if h : ∃ x : ℝ, SimpleTransverseRoot M α x then
          Classical.choose h else 0) (hmatrix s)
    have h := hanalytic j (Φ ω) hΦ
    change AnalyticAt ℝ (selectedTransverseRoot Jsub α (Φ ω)) 0 ∧
      selectedTransverseRoot Jsub α (Φ ω) 0 = 0 at h
    rw [hselected] at h
    simpa only [Jfull, τ, Φ, edgePrefixFactorsOfActualCurrent]
      using h
  refine ⟨t, ε, α, Q, Cread, ht, hε, hε1, hα, hQ, hCread, hanactual, ?_⟩
  filter_upwards [hlaw, hreadout, hconversion, hroot, hsmall,
    self_mem_nhdsWithin]
    with δ hlawδ hreadδ hconvδ hrootδ hsmallδ hδ
  have horderGlobal := arbitrarySplitReadout_strictMono_all_roots
    (m+1) ξ r δ hξ hδ hrootδ hconvδ.1
  refine ⟨hreadδ, horderGlobal, ?_⟩
  intro ω hω
  have hΦ : Φ ω ∈ K' := ⟨ω, hω, rfl⟩
  have hcurrent := hfamily ω hω
  have hcount := paperFixedBindingSplit_positive_equilibria_exact_family
    m ξ hξ r τ δ ε (Φ ω).val (by linarith) hτ
      (Φ ω).property hδ hε hε1 hconvδ.1 hconvδ.2
      (fun j => hrootδ j.val (by omega))
  have hinj : Function.Injective
      (arbitrarySplitFiniteState (m+1) ξ r δ) :=
    arbitrarySplitFiniteState_injective_of_positive_split
      (m+1) ξ hξ r δ hδ
      (fun j => hrootδ j.val (by omega))
  have hcard :
      {x : State (m+2) |
        x.Positive ∧ Equilibrium
          (paperFixedBindingSplitRates m ξ r δ ε
            (Fin.lastCases τ (Φ ω).val)) x ∧
          InClass (2*r) 2 (2*(r+1)) x}.ncard =
        2*(m+1)+1 := by
    rw [hcount]
    simpa using Set.ncard_range_of_injective hinj
  have horder := arbitrarySplitReadout_strictMono_all_roots
    (m+1) ξ r δ hξ hδ hrootδ hconvδ.1
  have hk₀ :
      (relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r
          (Fin.lastCases τ (Φ ω).val))) ε).Positive :=
    relaxRates_positive _
      (paperFixedBindingRates_positive _ (hbase (Φ ω) hΦ)) hε hε1
  have hcoefPos := paperFixedBindingPrintedCoefficient_pos
    m ξ r τ ε (Φ ω).val ⟨0, by omega⟩
      hr hconv.1 hk₀ hx₀ (heq₀ (Φ ω) hΦ)
      hET₀ hFT₀ (hspec (Φ ω) hΦ)
  have hprinted := paperFixedBindingPrintedCoefficient_eq_published_aconst
    m r τ ε (Φ ω).val hr hconv.1 hk₀ hx₀
      (heq₀ (Φ ω) hΦ) hET₀ hFT₀ (hspec (Φ ω) hΦ)
  simp only [loadedCoordOfState, from_toLoadedCoord] at hprinted
  have hksplit :
      (paperFixedBindingSplitRates m ξ r δ ε
        (Fin.lastCases τ (Φ ω).val)).Positive :=
    (paperFixedBindingSplit_source
      m ξ r δ ε (Fin.lastCases τ (Φ ω).val)
        (hw (Φ ω)) hε hε1 hconvδ.1 hconvδ.2
        ⟨0, by omega⟩ (hrootδ 0 (by omega))).1
  dsimp only
  refine ⟨?_, ?_, ?_, hinj, ?_, ?_, horder, ?_, ?_, ?_⟩
  · intro i
    simpa only [τ, Φ, edgePrefixFactorsOfActualCurrent]
      using (hcurrent.1 i)
  · simpa only [τ, Φ, edgePrefixFactorsOfActualCurrent]
      using hcurrent.2.1
  · simpa only [τ, Φ, edgePrefixFactorsOfActualCurrent]
      using hksplit
  · simpa only [τ, Φ, edgePrefixFactorsOfActualCurrent]
      using hcount
  · simpa only [τ, Φ, edgePrefixFactorsOfActualCurrent]
      using hcard
  · simpa only [τ, Φ, edgePrefixFactorsOfActualCurrent]
      using hcoefPos
  · simpa only [τ, Φ, edgePrefixFactorsOfActualCurrent]
      using hprinted
  · intro j
    obtain ⟨lam, hroot, hsimple, hmargin, hselected, hrelative⟩ :=
      hlawδ j (Φ ω) hΦ
    obtain ⟨han, hzero⟩ := hanactual ω hω j
    have hsource := paperFixedBindingSplit_source
      m ξ r δ ε (Fin.lastCases τ (Φ ω).val)
        (hw (Φ ω)) hε hε1 hconvδ.1 hconvδ.2
        j (hrootδ j.val (by omega))
    obtain ⟨hk, hs, heq, hclass⟩ := hsource
    have hobs := arbitrarySplitFiniteState_sqrt_observable_eq_offset
      (m+1) ξ r δ j (hrootδ j.val (by omega))
    have hselectedRoot : SimpleTransverseRoot
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (paperFixedBindingSplitRates m ξ r δ ε
            (Fin.lastCases τ (Φ ω).val))
          (toCoordinateSpace (chart
            (arbitrarySplitFiniteState (m+1) ξ r δ j))))
        α lam := ⟨hroot, hsimple, hmargin⟩
    have hparity := arbitrary_offset_root_gap_alternates
      (m+1) ξ hξ j
    have hsign := slow_root_sign_of_relative_error
      (2*(m+1))
      (paperFixedBindingPrintedCoefficient m r τ ε (Φ ω).val)
      Q δ
      (∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
        (ξ j.val-ξ i)) lam
      hcoefPos hδ (by linarith : Q*|δ| < 1) hrelative
    have hneg : Even j.val → lam < 0 :=
      fun heven => hsign.1 (hparity.1 heven)
    have hpos : Odd j.val → 0 < lam :=
      fun hodd => hsign.2 (hparity.2 hodd)
    refine ⟨lam, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hs
    · exact positive_total_phosphorylation_flux (m+1) _ _ hk hs
    · simpa only [τ, Φ, edgePrefixFactorsOfActualCurrent] using heq
    · exact hclass
    · exact hobs
    · simpa only [τ, Φ, edgePrefixFactorsOfActualCurrent] using han
    · simpa only [τ, Φ, edgePrefixFactorsOfActualCurrent] using hzero
    · simpa only [τ, Φ, edgePrefixFactorsOfActualCurrent] using hselected
    · simpa only [τ, Φ, edgePrefixFactorsOfActualCurrent] using hroot
    · simpa only [τ, Φ, edgePrefixFactorsOfActualCurrent] using hsimple
    · simpa only [τ, Φ, edgePrefixFactorsOfActualCurrent] using hmargin
    · simpa only [τ, Φ, edgePrefixFactorsOfActualCurrent] using hrelative
    · have hgapne := arbitrarySplit_root_gap_ne_zero
        (m+1) ξ hξ j
      have hreciprocalExists : ∃ err : ℝ,
          |err| ≤ 2*Q*|δ| ∧
          1/|lam| = (1+err) /
            (paperFixedBindingPrintedCoefficient m r τ ε (Φ ω).val *
              |∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
                (ξ j.val-ξ i)| * δ^(2*(m+1))) :=
        slow_mode_reciprocal_first_order_law
          (2*(m+1))
          (paperFixedBindingPrintedCoefficient m r τ ε (Φ ω).val)
          Q δ
          (∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
            (ξ j.val-ξ i)) lam
          hcoefPos hδ hgapne hQ.le hsmallδ hrelative
      rcases hreciprocalExists with ⟨err, herr, hreciprocal⟩
      refine ⟨err, ?_, ?_, hneg, hpos, ?_, ?_⟩
      · simpa only [τ, Φ, edgePrefixFactorsOfActualCurrent]
          using herr
      · simpa only [τ, Φ, edgePrefixFactorsOfActualCurrent]
          using hreciprocal
      · intro heven
        have hstable : IsLinearlyStable (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r δ ε
              (Fin.lastCases τ (Φ ω).val))
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r δ j))) :=
          simpleTransverseRoot_hurwitz_of_negative _ α lam
            hα (hneg heven) hselectedRoot
        have hnonlinear : IsLocallyAsymptoticallyStableClass
            (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r δ ε
              (Fin.lastCases τ (Φ ω).val))
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r δ j))) :=
          positiveClassEquilibrium_nonlinear_sink (n := m+2)
          (by omega : 1 ≤ m+2) (2*r) 2 (2*(r+1))
          (by linarith : 0 < 2*r)
          (paperFixedBindingSplitRates m ξ r δ ε
            (Fin.lastCases τ (Φ ω).val)) hk
          (arbitrarySplitFiniteState (m+1) ξ r δ j)
          hs heq hclass hstable
        simpa only [τ, Φ, edgePrefixFactorsOfActualCurrent]
          using And.intro hstable hnonlinear
      · intro hodd
        have hsaddle := simpleTransverseRoot_oneUnstable_of_positive
          (2*r) 2 (2*(r+1))
          (paperFixedBindingSplitRates m ξ r δ ε
            (Fin.lastCases τ (Φ ω).val))
          (toCoordinateSpace (chart
            (arbitrarySplitFiniteState (m+1) ξ r δ j)))
          α lam hα (hpos hodd) hselectedRoot
        simpa only [τ, Φ, edgePrefixFactorsOfActualCurrent]
          using hsaddle

end

end PhosphorylationStableCapacity
