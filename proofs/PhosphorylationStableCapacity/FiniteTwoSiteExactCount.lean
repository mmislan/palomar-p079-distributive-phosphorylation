module
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteManuscriptWitness
public import proofs.PhosphorylationStableCapacity.UniversalEquilibriumCount

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The printed two-site system has exactly the three printed positive
equilibria in its `(4,2,6)` compatibility class. -/
theorem manuscriptTwoSite_exact_equilibrium_count :
    {x : State 2 | x.Positive ∧ Equilibrium manuscriptTwoSiteRates x ∧
      InClass 4 2 6 x}.ncard = 3 := by
  let E : Set (State 2) :=
    {x | x.Positive ∧ Equilibrium manuscriptTwoSiteRates x ∧
      InClass 4 2 6 x}
  have hsource : (Set.range manuscriptTwoSiteStates) ⊆ E := by
    rintro x ⟨j, rfl⟩
    exact ⟨manuscriptTwoSiteStates_positive j,
      manuscriptTwoSiteStates_equilibrium j,
      manuscriptTwoSiteStates_inClass j⟩
  obtain ⟨hfinite, hbudget⟩ :=
    positive_equilibria_finite_and_ncard_le_two_n_sub_one
      (n := 2) (by norm_num) manuscriptTwoSiteRates
      manuscriptTwoSiteRates_positive 4 2 6
      (by norm_num) (by norm_num) (by norm_num)
  have hcount : (Set.range manuscriptTwoSiteStates).ncard = 3 := by
    simpa using Set.ncard_range_of_injective manuscriptTwoSiteStates_injective
  have hlower : 3 ≤ E.ncard := by
    rw [← hcount]
    exact Set.ncard_le_ncard hsource hfinite
  change E.ncard ≤ 3 at hbudget
  change E.ncard = 3
  omega

theorem manuscriptTwoSite_exact_equilibrium_family :
    {x : State 2 | x.Positive ∧ Equilibrium manuscriptTwoSiteRates x ∧
      InClass 4 2 6 x} = Set.range manuscriptTwoSiteStates := by
  let E : Set (State 2) :=
    {x | x.Positive ∧ Equilibrium manuscriptTwoSiteRates x ∧
      InClass 4 2 6 x}
  have hsource : (Set.range manuscriptTwoSiteStates) ⊆ E := by
    rintro x ⟨j, rfl⟩
    exact ⟨manuscriptTwoSiteStates_positive j,
      manuscriptTwoSiteStates_equilibrium j,
      manuscriptTwoSiteStates_inClass j⟩
  have hfinite :=
    (positive_equilibria_finite_and_ncard_le_two_n_sub_one
      (n := 2) (by norm_num) manuscriptTwoSiteRates
      manuscriptTwoSiteRates_positive 4 2 6
      (by norm_num) (by norm_num) (by norm_num)).1
  change E.Finite at hfinite
  change E = Set.range manuscriptTwoSiteStates
  apply (Set.eq_of_subset_of_ncard_le hsource ?_ hfinite).symm
  rw [Set.ncard_range_of_injective manuscriptTwoSiteStates_injective]
  simpa [E] using le_of_eq manuscriptTwoSite_exact_equilibrium_count

end
end PhosphorylationStableCapacity
