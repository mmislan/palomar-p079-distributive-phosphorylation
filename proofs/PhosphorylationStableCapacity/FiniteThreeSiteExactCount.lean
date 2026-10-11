module
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteBenchmarkEquilibria
public import proofs.PhosphorylationStableCapacity.UniversalEquilibriumCount

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The reviewed three-site benchmark has exactly its five printed positive
equilibria in the class with totals `(18,2,20)`. -/
theorem benchmarkThreeSite_exact_equilibrium_count :
    {x : State 3 | x.Positive ∧ Equilibrium benchmarkThreeSiteRates x ∧
      InClass 18 2 20 x}.ncard = 5 := by
  let E : Set (State 3) :=
    {x | x.Positive ∧ Equilibrium benchmarkThreeSiteRates x ∧
      InClass 18 2 20 x}
  have hsource : (Set.range benchmarkThreeSiteStates) ⊆ E := by
    rintro x ⟨j, rfl⟩
    exact ⟨benchmarkThreeSiteStates_positive j,
      benchmarkThreeSiteStates_equilibrium j,
      benchmarkThreeSiteStates_inClass j⟩
  obtain ⟨hfinite, hbudget⟩ :=
    positive_equilibria_finite_and_ncard_le_two_n_sub_one
      (n := 3) (by norm_num) benchmarkThreeSiteRates
      benchmarkThreeSiteRates_positive 18 2 20
      (by norm_num) (by norm_num) (by norm_num)
  have hcount : (Set.range benchmarkThreeSiteStates).ncard = 5 := by
    simpa using Set.ncard_range_of_injective benchmarkThreeSiteStates_injective
  have hlower : 5 ≤ E.ncard := by
    rw [← hcount]
    exact Set.ncard_le_ncard hsource hfinite
  change E.ncard ≤ 5 at hbudget
  change E.ncard = 5
  omega

theorem benchmarkThreeSite_exact_equilibrium_family :
    {x : State 3 | x.Positive ∧ Equilibrium benchmarkThreeSiteRates x ∧
      InClass 18 2 20 x} = Set.range benchmarkThreeSiteStates := by
  let E : Set (State 3) :=
    {x | x.Positive ∧ Equilibrium benchmarkThreeSiteRates x ∧
      InClass 18 2 20 x}
  have hsource : (Set.range benchmarkThreeSiteStates) ⊆ E := by
    rintro x ⟨j, rfl⟩
    exact ⟨benchmarkThreeSiteStates_positive j,
      benchmarkThreeSiteStates_equilibrium j,
      benchmarkThreeSiteStates_inClass j⟩
  have hfinite :=
    (positive_equilibria_finite_and_ncard_le_two_n_sub_one
      (n := 3) (by norm_num) benchmarkThreeSiteRates
      benchmarkThreeSiteRates_positive 18 2 20
      (by norm_num) (by norm_num) (by norm_num)).1
  change E.Finite at hfinite
  change E = Set.range benchmarkThreeSiteStates
  apply (Set.eq_of_subset_of_ncard_le hsource ?_ hfinite).symm
  rw [Set.ncard_range_of_injective benchmarkThreeSiteStates_injective]
  simpa [E] using le_of_eq benchmarkThreeSite_exact_equilibrium_count

end
end PhosphorylationStableCapacity
