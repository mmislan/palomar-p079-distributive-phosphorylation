module
public import proofs.PhosphorylationStableCapacity.RationalConfiguration435
public import proofs.PhosphorylationStableCapacity.UniversalEquilibriumCount
public import proofs.PhosphorylationStableCapacity.OneSiteNonlinearStability

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The explicit one-site rational system has its unique positive class
equilibrium as a Hurwitz and nonlinear sink. The odd-index saddle clause
is empty for a one-element family. -/
theorem one_site_rational_full_family_with_sinks_and_saddles :
    RationalFullFamilyWithSinksAndSaddles 1 := by
  let E : Set (State 1) :=
    {x | x.Positive ∧ Equilibrium oneRates x ∧
      InClass (3/2) (3/2) 3 x}
  have hcard : E.ncard = 1 :=
    one_site_positive_equilibria_exactly_one
  have hmem : oneState ∈ E :=
    ⟨oneState_positive, oneState_equilibrium, oneState_inClass⟩
  have hEeq : E = {oneState} := by
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hcard
    have heq : a = oneState := by
      have hm : oneState ∈ ({a} : Set (State 1)) := ha ▸ hmem
      simpa using hm.symm
    simpa [heq] using ha
  have hratOne : RationalReal (1 : ℝ) := ⟨1, by norm_num⟩
  have hratHalf : RationalReal (1/2 : ℝ) :=
    ⟨(1/2 : ℚ), by norm_num⟩
  have hratRates : RationalRates oneRates := by
    intro i
    exact ⟨hratOne, hratOne, hratOne,
      hratOne, hratOne, hratOne⟩
  have hratState : RationalState oneState := by
    exact ⟨(fun _ => hratOne), hratOne, hratOne,
      (fun _ => hratHalf), (fun _ => hratHalf)⟩
  unfold RationalFullFamilyWithSinksAndSaddles
  refine ⟨oneRates, 3/2, 3/2, 3,
    (fun _ : Fin (2*1-1) => oneCoord),
    hratRates, ⟨(3/2 : ℚ), by norm_num⟩,
    ⟨(3/2 : ℚ), by norm_num⟩,
    ⟨(3 : ℚ), by norm_num⟩,
    oneRates_positive, by norm_num, by norm_num, by norm_num,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j _
    exact Fin.ext (by omega)
  · intro j
    rw [oneState_eq_unChart]
    exact ⟨hratState, oneState_positive, oneCoord_equilibrium⟩
  · intro i
    exact ⟨⟨0, by omega⟩, by omega,
      oneCoord_linearly_stable, oneSite_locally_asymptotically_stable⟩
  · intro j hj
    simp at hj
  · change E = Set.range (fun _ : Fin (2*1-1) =>
      unChart (3/2) (3/2) 3 (ofCoordinateSpace oneCoord))
    rw [hEeq]
    ext x
    constructor
    · intro hx
      refine ⟨⟨0, by omega⟩, ?_⟩
      simpa [oneState_eq_unChart] using hx.symm
    · rintro ⟨j, rfl⟩
      simp [oneState_eq_unChart]
  · simpa only [show 2*1-1 = 1 by omega] using hcard

/-- Rational exact full-family attainment, hyperbolic sinks, and
one-unstable saddles hold for every positive chain length. -/
theorem all_positive_sizes_rational_full_family_with_sinks_and_saddles
    (n : ℕ) (hn : 1 ≤ n) :
    RationalFullFamilyWithSinksAndSaddles n := by
  by_cases h1 : n = 1
  · simpa [h1] using one_site_rational_full_family_with_sinks_and_saddles
  · exact all_size_rational_full_family_with_sinks_and_saddles
      n (by omega)

end
end PhosphorylationStableCapacity
