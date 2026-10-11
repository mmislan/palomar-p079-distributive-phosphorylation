module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCompactOneRootLaw435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingPrintedRatio435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Matrix Polynomial
open scoped Topology

/-- Finiteness of the ordered split family makes the transverse margin,
the relative-error constant and the split neighborhood common to all
states and all currents in the same literal fixed-binding system. -/
theorem paperFixedBinding_compact_all_roots_relative_law
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
              z = (lam : ℂ) ∨ z.re ≤ -α) :
    ∃ Q : ℝ, 0 < Q ∧
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        ∀ (j : Fin (2*(m+1)+1)) (a : PositivePrefixCurrents m),
          a ∈ K → ∃ lam : ℝ,
            let w := Fin.lastCases τ a.val
            let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
              (paperFixedBindingSplitRates m ξ r δ ε w)
              (toCoordinateSpace (chart
                (arbitrarySplitFiniteState (m+1) ξ r δ j)))
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
            |lam / (-paperFixedBindingPrintedCoefficient m r τ ε a.val *
                δ^(2*(m+1)) *
                  (∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
                    (ξ j.val-ξ i)))-1| ≤ Q*|δ| := by
  classical
  have hper (j : Fin (2*(m+1)+1)) :=
    paperFixedBinding_compact_one_root_relative_law
      m ξ hξ r τ ε K hK hr hτ hε hε1 hD₀ hB₀
      hx₀ hbase0 hsource hbase heq₀ hET₀ hFT₀ hspec
      α hα hgap j
  choose Q hQ hEv using hper
  let Qall := (∑ j : Fin (2*(m+1)+1), Q j)+1
  have hQall : 0 < Qall := by
    dsimp [Qall]
    have hsum : 0 ≤ ∑ j : Fin (2*(m+1)+1), Q j :=
      Finset.sum_nonneg (fun j hj => (hQ j).le)
    linarith
  have hQle (j : Fin (2*(m+1)+1)) : Q j ≤ Qall := by
    have hsle : Q j ≤ ∑ i : Fin (2*(m+1)+1), Q i :=
      Finset.single_le_sum (fun i hi => (hQ i).le)
        (Finset.mem_univ j)
    dsimp [Qall]
    linarith
  refine ⟨Qall, hQall, ?_⟩
  have hAll : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j : Fin (2*(m+1)+1), ∀ a ∈ K,
        ∃ lam : ℝ,
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
                  (ξ j.val-ξ i)))-1| ≤ Q j*|δ| :=
    Filter.eventually_all.mpr hEv
  filter_upwards [hAll] with δ hd j a ha
  obtain ⟨lam, hroot, hsimple, hmargin, hselected, hrelative⟩ :=
    hd j a ha
  have hk₀ :
      (relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r (Fin.lastCases τ a.val))) ε).Positive :=
    relaxRates_positive _
      (paperFixedBindingRates_positive _ (hbase a ha)) hε hε1
  have hratio := paperFixedBindingSplit_zero_physical_ratio_eq_printed
    m ξ r τ ε a.val j hr hD₀ hk₀ hx₀
      (heq₀ a ha) hET₀ hFT₀
  refine ⟨lam, hroot, hsimple, hmargin, hselected, ?_⟩
  · have hrelative' :
        |lam / (-paperFixedBindingPrintedCoefficient m r τ ε a.val *
          δ^(2*(m+1)) *
            (∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
              (ξ j.val-ξ i)))-1| ≤ Q j*|δ| := by
        simpa only [hratio] using hrelative
    exact hrelative'.trans
      (mul_le_mul_of_nonneg_right (hQle j) (abs_nonneg δ))

end

end PhosphorylationStableCapacity
