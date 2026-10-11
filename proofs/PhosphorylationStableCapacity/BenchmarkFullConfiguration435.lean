module
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteExactCount
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteSinkNonlinear
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteSaddleSpectra
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The complete printed three-site benchmark: the five literal states
exhaust one class, with three nonlinear sinks and two simple hyperbolic
saddles on the same exact rate vector. -/
def PaperBenchmarkFullConfiguration : Prop :=
    benchmarkThreeSiteRates.Positive ∧
    Function.Injective benchmarkThreeSiteStates ∧
    {s : State 3 | s.Positive ∧ Equilibrium benchmarkThreeSiteRates s ∧
      InClass 18 2 20 s} = Set.range benchmarkThreeSiteStates ∧
    {s : State 3 | s.Positive ∧ Equilibrium benchmarkThreeSiteRates s ∧
      InClass 18 2 20 s}.ncard = 5 ∧
    ∀ j : Fin 5,
      (benchmarkThreeSiteStates j).Positive ∧
      Equilibrium benchmarkThreeSiteRates (benchmarkThreeSiteStates j) ∧
      InClass 18 2 20 (benchmarkThreeSiteStates j) ∧
      (Even j.val →
        IsLinearlyStable 18 2 20 benchmarkThreeSiteRates
          (benchmarkThreeSiteCoord j) ∧
        IsLocallyAsymptoticallyStableClass 18 2 20 benchmarkThreeSiteRates
          (benchmarkThreeSiteCoord j)) ∧
      (Odd j.val →
        IsOneUnstableSaddle 18 2 20 benchmarkThreeSiteRates
          (benchmarkThreeSiteCoord j))

theorem three_site_benchmark_full_configuration :
    PaperBenchmarkFullConfiguration := by
  refine ⟨benchmarkThreeSiteRates_positive,
    benchmarkThreeSiteStates_injective,
    benchmarkThreeSite_exact_equilibrium_family,
    benchmarkThreeSite_exact_equilibrium_count, ?_⟩
  intro j
  refine ⟨benchmarkThreeSiteStates_positive j,
    benchmarkThreeSiteStates_equilibrium j,
    benchmarkThreeSiteStates_inClass j, ?_, ?_⟩
  · intro heven
    fin_cases j
    · exact ⟨benchmarkThreeSite_zero_linearly_stable,
        benchmarkThreeSite_zero_nonlinear_sink⟩
    · rcases heven with ⟨a, ha⟩
      change (1 : ℕ) = a + a at ha
      omega
    · exact ⟨benchmarkThreeSite_two_linearly_stable,
        benchmarkThreeSite_two_nonlinear_sink⟩
    · rcases heven with ⟨a, ha⟩
      change (3 : ℕ) = a + a at ha
      omega
    · exact ⟨benchmarkThreeSite_four_linearly_stable,
        benchmarkThreeSite_four_nonlinear_sink⟩
  · intro hodd
    fin_cases j
    · rcases hodd with ⟨a, ha⟩
      change (0 : ℕ) = 2 * a + 1 at ha
      omega
    · exact benchmarkThreeSite_one_is_one_unstable_saddle
    · rcases hodd with ⟨a, ha⟩
      change (2 : ℕ) = 2 * a + 1 at ha
      omega
    · exact benchmarkThreeSite_three_is_one_unstable_saddle
    · rcases hodd with ⟨a, ha⟩
      change (4 : ℕ) = 2 * a + 1 at ha
      omega

end
end PhosphorylationStableCapacity
