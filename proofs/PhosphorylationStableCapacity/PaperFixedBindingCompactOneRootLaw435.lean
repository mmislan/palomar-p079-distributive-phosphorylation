module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCompactRelativeFromCore435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCompactSelectedRoot435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCompactTransverseLower435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingUniformConstantTerm435
public import proofs.PhosphorylationStableCapacity.ActualPrefixCurrentReparam435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitRootGapNonzero
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitGenericPrefactorZero435
public import proofs.PhosphorylationStableCapacity.SelectedTransverseRootChoice435
public import proofs.PhosphorylationStableCapacity.CoalescedArbitraryPrefactorPositive

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Matrix Polynomial
open scoped Topology

/-- One fixed ordered split state satisfies the paper's printed
relative eigenvalue law with a constant common to every member of a
compact prefix-current family. The rates, coalesced coefficient,
selected simple eigenvalue, and transverse margin are all from the
same literal fixed-binding construction. -/
theorem paperFixedBinding_compact_one_root_relative_law
    (m : ℕ) (ξ : ℕ → ℝ) (hξ : StrictMono ξ)
    (r τ ε : ℝ)
    (K : Set (PositivePrefixCurrents m)) (hK : IsCompact K)
    (hr : 1 < r) (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hx₀ : (coalescedFiniteState (m+1) r).Positive)
    (hbase0 : (coalescedFiniteRates (m+1) r).Positive)
    (hsource : ∀ᶠ δ : ℝ in 𝓝 0,
      (arbitrarySplitFiniteRates (m+1) ξ r δ).Positive)
    (hbase : ∀ a ∈ K,
      (coalescedAllScaledRates m r
        (Fin.lastCases τ a.val)).Positive)
    (heq₀ : ∀ a ∈ K,
      Equilibrium (relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r (Fin.lastCases τ a.val))) ε)
          (coalescedFiniteState (m+1) r))
    (hET₀ : totalE (coalescedFiniteState (m+1) r) = 2*r)
    (hFT₀ : totalF (coalescedFiniteState (m+1) r) = 2)
    (hspec : ∀ a ∈ K, SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r
            (Fin.lastCases τ a.val))) ε)
        (fromLoadedCoord (loadedCoordOfState
          (coalescedFiniteState (m+1) r)))))
    (α : ℝ) (hα : 0 < α)
    (hgap : ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ (i : Fin (2*(m+1)+1)) (a : PositivePrefixCurrents m),
        a ∈ K → ∃ lam : ℝ,
          let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r δ ε
              (Fin.lastCases τ a.val))
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r δ i)))
          J.charpoly.IsRoot lam ∧
            ((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
              (lam : ℂ) ≠ 0 ∧
            ∀ z : ℂ, z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
              z = (lam : ℂ) ∨ z.re ≤ -α)
    (j : Fin (2*(m+1)+1)) :
    ∃ Q : ℝ, 0 < Q ∧
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        ∀ a ∈ K, ∃ lam : ℝ,
          let w := Fin.lastCases τ a.val
          let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r δ ε w)
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r δ j)))
          let J₀ := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r 0 ε w)
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r 0 j)))
          J.charpoly.IsRoot lam ∧
          ((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
            (lam : ℂ) ≠ 0 ∧
          (∀ z : ℂ, z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
            z = (lam : ℂ) ∨ z.re ≤ -α) ∧
          lam = selectedTransverseRoot
            (fun (p : Fin (m+2) → ℝ) (s : ℝ) =>
              restrictedJacobianMatrix (2*r) 2 (2*(r+1))
                (paperFixedBindingSplitRates m ξ r s ε p)
                (toCoordinateSpace (chart
                  (arbitrarySplitFiniteState (m+1) ξ r s j))))
            α w δ ∧
          |lam / (-(arbitrarySplitGenericPhysicalPrefactor m ξ r 0
              (paperFixedBindingSplitRates m ξ r 0 ε w) j /
                J₀.charpoly.derivative.eval 0) *
              δ^(2*(m+1)) *
                (∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
                  (ξ j.val-ξ i)))-1| ≤ Q*|δ| := by
  let W (a : PositivePrefixCurrents m) : Fin (m+2) → ℝ :=
    Fin.lastCases τ a.val
  let KF : Set (Fin (m+2) → ℝ) := W '' K
  have hKF : IsCompact KF :=
    hK.image (continuous_fullEdgeFactors_from_positivePrefix m τ)
  have hWpos (a : PositivePrefixCurrents m) :
      ∀ i : Fin (m+2), 0 < W a i := by
    intro i
    cases i using Fin.lastCases with
    | last => simpa [W] using hτ
    | cast i => simpa [W] using a.property i
  have hKFpos : ∀ w ∈ KF, ∀ i, 0 < w i := by
    rintro w ⟨a, ha, rfl⟩ i
    exact hWpos a i
  let J (w : Fin (m+2) → ℝ) (δ : ℝ) :=
    restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (paperFixedBindingSplitRates m ξ r δ ε w)
      (toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j)))
  let S (w : Fin (m+2) → ℝ) (δ lam : ℝ) : Prop :=
    ((J w δ).map (algebraMap ℝ ℂ)).charpoly.derivative.eval
      (lam : ℂ) ≠ 0 ∧
      (∀ z : ℂ, z ∈ spectrum ℂ ((J w δ).map (algebraMap ℝ ℂ)) →
        z = (lam : ℂ) ∨ z.re ≤ -α) ∧
      lam = selectedTransverseRoot J α w δ
  have hslow (ρ : ℝ) (hρ : 0 < ρ) :
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        ∀ w ∈ KF, ∃ lam : ℝ,
          |lam| < ρ ∧
          (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r δ ε w)
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r δ j)))).charpoly.IsRoot lam ∧
          S w δ lam := by
    let σ := min ρ (α/2)
    have hσ : 0 < σ := lt_min hρ (by positivity)
    have hsigned := paperFixedBinding_compact_selected_root_small
      m ξ r τ ε K hK (by linarith : r ≠ 0)
      hD₀ hB₀ hbase hspec α hα hgap σ hσ
    filter_upwards [hsigned.filter_mono nhdsWithin_le_nhds,
      hgap.filter_mono nhdsWithin_le_nhds]
      with δ hd hgapδ w hw
    rcases hw with ⟨a, ha, rfl⟩
    obtain ⟨lam, hlam, hroot, hsimple, hmargin⟩ := hd j a ha
    have hcert : ∃ x : ℝ, SimpleTransverseRoot
        (J (W a) δ) α x := by
      simpa only [J, W, SimpleTransverseRoot] using hgapδ j a ha
    have hnear : -α < lam := by
      have hsmall : |lam| < α/2 :=
        lt_of_lt_of_le hlam (min_le_right ..)
      linarith [neg_abs_le lam]
    have heq := near_root_eq_selectedTransverseRoot
      J α (W a) δ lam hcert
      (by simpa only [J, W] using hroot) hnear
    refine ⟨lam, lt_of_lt_of_le hlam (min_le_left ..), hroot,
      hsimple, hmargin, heq⟩
  have hconst := paperFixedBinding_uniform_constantTerm_root_gap
    m ξ r ε hr hε hε1 hD₀ hB₀ j
  let gap : ℝ := ∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
    (ξ j.val-ξ i)
  have hgapne : gap ≠ 0 :=
    arbitrarySplit_root_gap_ne_zero (m+1) ξ hξ j
  have hconstKF : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ w ∈ KF,
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (paperFixedBindingSplitRates m ξ r δ ε w)
          (toCoordinateSpace (chart
            (arbitrarySplitFiniteState (m+1) ξ r δ j)))).charpoly.eval 0 =
        arbitrarySplitGenericPhysicalPrefactor m ξ r δ
          (paperFixedBindingSplitRates m ξ r δ ε w) j *
          δ^(2*(m+1))*gap := by
    filter_upwards [hconst] with δ hd w hw
    simpa only [gap, mul_assoc] using hd w (hKFpos w hw)
  obtain ⟨pmin, hpmin, hpbound⟩ :=
    paperFixedBinding_compact_coalesced_coeff_one_lower
      m ξ r τ ε K hK (by linarith : r ≠ 0)
      hD₀ hB₀ hbase hspec j
  have hpKF : ∀ w ∈ KF, pmin ≤
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (paperFixedBindingSplitRates m ξ r 0 ε w)
        (toCoordinateSpace (chart
          (arbitrarySplitFiniteState (m+1) ξ r 0 j)))).charpoly.derivative.eval 0 := by
    rintro w ⟨a, ha, rfl⟩
    exact hpbound a ha
  have hcpos : ∀ w ∈ KF,
      0 < arbitrarySplitGenericPhysicalPrefactor m ξ r 0
        (paperFixedBindingSplitRates m ξ r 0 ε w) j := by
    rintro w ⟨a, ha, rfl⟩
    have hk₀ :
        (paperFixedBindingSplitRates m ξ r 0 ε (W a)).Positive := by
      have hka := hbase a ha
      simpa only [paperFixedBindingSplitRates,
        arbitrarySplitFiniteRates_zero_eq_coalesced,
        coalescedAllScaledRates, W] using
        relaxRates_positive _
          (paperFixedBindingRates_positive _ hka) hε hε1
    have heq : Equilibrium
        (paperFixedBindingSplitRates m ξ r 0 ε (W a))
        (coalescedFiniteState (m+1) r) := by
      simpa only [paperFixedBindingSplitRates,
        arbitrarySplitFiniteRates_zero_eq_coalesced,
        coalescedAllScaledRates, W] using heq₀ a ha
    exact arbitrarySplitGenericPhysicalPrefactor_zero_pos
      m ξ r _ j hr hD₀ hk₀ hx₀ heq hET₀ hFT₀
  have hstate0 := arbitrarySplitFiniteState_zero_mass_den_ne_zero
    m ξ r hD₀ hB₀ j
  obtain ⟨Q, hQ, hrelative⟩ :=
    paperFixedBinding_compact_relative_from_actual_core
      m ξ r ε KF hKF hKFpos hr hε hD₀ hB₀
      hbase0 hsource j hstate0 S gap pmin hgapne hpmin
      hpKF hcpos hconstKF hslow
  refine ⟨Q, hQ, ?_⟩
  filter_upwards [hrelative] with δ hd a ha
  have hWa : W a ∈ KF := ⟨a, ha, rfl⟩
  obtain ⟨lam, hroot, hproperties, herror⟩ := hd (W a) hWa
  rcases hproperties with ⟨hsimple, htransverse, hselected⟩
  refine ⟨lam, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [W, J] using hroot
  · simpa only [W, J] using hsimple
  · simpa only [W, J] using htransverse
  · simpa only [W, J] using hselected
  · simpa only [W, J, gap] using herror

end

end PhosphorylationStableCapacity
