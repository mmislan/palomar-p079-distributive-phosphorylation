module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCommonAnalyticLaw
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingSplitCount435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitObservable
public import proofs.PhosphorylationStableCapacity.SplitReciprocalSlowLaw
public import proofs.PhosphorylationStableCapacity.SplitSlowSignFromRelativeError
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitRootGapParity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Polynomial
open scoped Topology

/-- The complete pointwise paper configuration. The same fixed-binding
rates and the same selected analytic slow branch support the exact
equilibrium set, signs, transverse gap, relative splitting law, and
reciprocal conditioning law. -/
def PaperFixedBindingCompletePoint
    (m : ℕ) (ξ : ℕ → ℝ)
    (r τ ε α K δ : ℝ) (ω : Fin (m+1) → ℝ)
    (lam : Fin (2*(m+1)+1) → ℝ → ℝ) : Prop :=
  let k := paperFixedBindingSplitRates m ξ r δ ε (Fin.lastCases τ ω)
  k.Positive ∧
    Function.Injective (arbitrarySplitFiniteState (m+1) ξ r δ) ∧
    {s : State (m+2) |
      s.Positive ∧ Equilibrium k s ∧ InClass (2*r) 2 (2*(r+1)) s} =
      Set.range (arbitrarySplitFiniteState (m+1) ξ r δ) ∧
    {s : State (m+2) |
      s.Positive ∧ Equilibrium k s ∧ InClass (2*r) 2 (2*(r+1)) s}.ncard =
      2*(m+1)+1 ∧
    ∀ j : Fin (2*(m+1)+1),
      let s := arbitrarySplitFiniteState (m+1) ξ r δ j
      let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k
        (toCoordinateSpace (chart s))
      s.Positive ∧ Equilibrium k s ∧
      totalE s = 2*r ∧ totalF s = 2 ∧ totalS s = 2*(r+1) ∧
      Real.sqrt (1+8*s.E/s.F) = 3+δ*ξ j.val ∧
      J.charpoly.IsRoot (lam j δ) ∧
      ((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
        ((lam j δ) : ℂ) ≠ 0 ∧
      (∀ z : ℂ, z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
        z = ((lam j δ) : ℂ) ∨ z.re ≤ -α) ∧
      |lam j δ / (-paperFixedBindingPrintedCoefficient m r τ ε ω *
        δ^(2*(m+1)) *
        (∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
          (ξ j.val-ξ i))) - 1| ≤ K*|δ| ∧
      (∃ err : ℝ, |err| ≤ 2*K*|δ| ∧
        1/|lam j δ| = (1+err)/
          (paperFixedBindingPrintedCoefficient m r τ ε ω *
            |∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
              (ξ j.val-ξ i)| * δ^(2*(m+1)))) ∧
      (Even j.val → lam j δ < 0) ∧
      (Odd j.val → 0 < lam j δ)

/-- All-small-positive-δ completion for the genuine fixed-binding rate
family, conditional only on one coalesced construction. The selected
analytic functions precede the eventual neighborhood quantifier. -/
theorem paperFixedBinding_complete_analytic_law
    (m : ℕ) (ξ : ℕ → ℝ) (hξ : StrictMono ξ)
    (r τ ε : ℝ) (ω : Fin (m+1) → ℝ)
    (hω : ∀ i, 0 < ω i)
    (hr : 1 < r) (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : (coalescedAllScaledRates m r
      (Fin.lastCases τ ω)).Positive)
    (hk₀ : (relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε).Positive)
    (hx₀ : (coalescedFiniteState (m+1) r).Positive)
    (heq₀ : Equilibrium
      (relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
      (coalescedFiniteState (m+1) r))
    (hET₀ : totalE (coalescedFiniteState (m+1) r) = 2*r)
    (hFT₀ : totalF (coalescedFiniteState (m+1) r) = 2)
    (hspec : SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
        (fromLoadedCoord (loadedCoordOfState
          (coalescedFiniteState (m+1) r))))) :
    ∃ lam : Fin (2*(m+1)+1) → ℝ → ℝ,
      (∀ j, AnalyticAt ℝ (lam j) 0 ∧ lam j 0 = 0) ∧
      0 < paperFixedBindingPrintedCoefficient m r τ ε ω ∧
      ∃ α K : ℝ, 0 < α ∧ 0 < K ∧
        ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
          PaperFixedBindingCompletePoint m ξ r τ ε α K δ ω lam := by
  obtain ⟨lam, hlam, ha, α, K, hα, hK, hslow⟩ :=
    paperFixedBinding_all_indices_common_analytic_printed_law
      m ξ hξ r τ ε ω hω hr hτ hε hε1 hD₀ hB₀
      hbase hk₀ hx₀ heq₀ hET₀ hFT₀ hspec
  have hconv := arbitrarySplit_conversion_positive_near_zero
    (m+1) ξ r (ne_of_gt (lt_trans zero_lt_one hr)) hD₀ hB₀
  have hy : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j : Fin (2*(m+1)+1),
        1 < offsetSplitRoot ξ δ j.val := by
    have h := offsetSplitRoot_gt_one_eventually (m+1) ξ
    filter_upwards [h.filter_mono nhdsWithin_le_nhds] with δ hd j
    exact hd j.val (by omega)
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      K*|δ| ≤ 1/2 := by
    have hcont : ContinuousAt (fun δ : ℝ => K*|δ|) 0 := by fun_prop
    have hzero : K*|(0 : ℝ)| < 1/2 := by norm_num
    exact ((hcont.eventually (Iio_mem_nhds hzero)).filter_mono
      nhdsWithin_le_nhds).mono (fun _ h => h.le)
  refine ⟨lam, hlam, ha, α, K, hα, hK, ?_⟩
  filter_upwards [hslow, hconv, hy, hsmall, self_mem_nhdsWithin]
    with δ hslow hconv hy hsmall hδ
  let w : Fin (m+2) → ℝ := Fin.lastCases τ ω
  have hw : ∀ i : Fin (m+2), 0 < w i := by
    intro i
    cases i using Fin.lastCases with
    | last => simpa [w] using hτ
    | cast i => simpa [w] using hω i
  let k := paperFixedBindingSplitRates m ξ r δ ε w
  let f : Fin (2*(m+1)+1) → State (m+2) :=
    arbitrarySplitFiniteState (m+1) ξ r δ
  have hsource (j : Fin (2*(m+1)+1)) :=
    paperFixedBindingSplit_source m ξ r δ ε w hw hε hε1
      hconv.1 hconv.2 j (hy j)
  have hinj : Function.Injective f :=
    arbitrarySplitFiniteState_injective_of_positive_split
      (m+1) ξ hξ r δ hδ hy
  have hexact :
      {s : State (m+2) |
        s.Positive ∧ Equilibrium k s ∧ InClass (2*r) 2 (2*(r+1)) s} =
      Set.range f :=
    paperFixedBindingSplit_positive_equilibria_exact_family
      m ξ hξ r τ δ ε ω (lt_trans zero_lt_one hr) hτ hω hδ hε hε1
      hconv.1 hconv.2 hy
  have hcount :
      {s : State (m+2) |
        s.Positive ∧ Equilibrium k s ∧ InClass (2*r) 2 (2*(r+1)) s}.ncard =
      2*(m+1)+1 := by
    rw [hexact]
    simpa [f] using Set.ncard_range_of_injective hinj
  refine ⟨(hsource 0).1, hinj, hexact, hcount, ?_⟩
  intro j
  obtain ⟨hroot, hsimple, hmargin, hbound⟩ := hslow j
  obtain ⟨_, hs, heq, hclass⟩ := hsource j
  have hobs := arbitrarySplitFiniteState_sqrt_observable_eq_offset
    (m+1) ξ r δ j (hy j)
  have hgap := arbitrarySplit_root_gap_ne_zero (m+1) ξ hξ j
  obtain ⟨err, herr, hreciprocal⟩ :=
    slow_mode_reciprocal_first_order_law
      (2*(m+1)) (paperFixedBindingPrintedCoefficient m r τ ε ω)
      K δ
      (∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
        (ξ j.val-ξ i)) (lam j δ)
      ha hδ hgap hK.le hsmall hbound
  have hparity := arbitrary_offset_root_gap_alternates
    (m+1) ξ hξ j
  have hsign := slow_root_sign_of_relative_error
    (2*(m+1)) (paperFixedBindingPrintedCoefficient m r τ ε ω)
    K δ
    (∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
      (ξ j.val-ξ i)) (lam j δ)
    ha hδ (by linarith : K*|δ| < 1) hbound
  exact ⟨hs, heq, hclass.1, hclass.2.1, hclass.2.2,
    hobs, hroot, hsimple, hmargin, hbound,
    ⟨err, herr, hreciprocal⟩,
    fun heven => hsign.1 (hparity.1 heven),
    fun hodd => hsign.2 (hparity.2 hodd)⟩

end
end PhosphorylationStableCapacity
