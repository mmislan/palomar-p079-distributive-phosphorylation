module
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteBenchmarkData
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

set_option maxHeartbeats 2000000

theorem benchmarkThreeSiteRates_positive : benchmarkThreeSiteRates.Positive := by
  intro i
  fin_cases i <;> norm_num [benchmarkThreeSiteRates]

theorem benchmarkThreeSiteStates_positive (j : Fin 5) :
    (benchmarkThreeSiteStates j).Positive := by
  fin_cases j
  all_goals
    refine ⟨?_, by norm_num [benchmarkThreeSiteStates],
      by norm_num [benchmarkThreeSiteStates], ?_, ?_⟩
    all_goals intro i
    all_goals fin_cases i <;> norm_num [benchmarkThreeSiteStates]

theorem benchmarkThreeSiteStates_equilibrium (j : Fin 5) :
    Equilibrium benchmarkThreeSiteRates (benchmarkThreeSiteStates j) := by
  apply equilibrium_of_currents
  · intro i
    fin_cases j <;> fin_cases i <;>
      norm_num [benchmarkThreeSiteRates, benchmarkThreeSiteStates, kinaseNet]
  · intro i
    fin_cases j <;> fin_cases i <;>
      norm_num [benchmarkThreeSiteRates, benchmarkThreeSiteStates, phosphataseNet]
  · intro i
    fin_cases j <;> fin_cases i <;>
      norm_num [benchmarkThreeSiteRates, benchmarkThreeSiteStates]

theorem benchmarkThreeSiteStates_inClass (j : Fin 5) :
    InClass 18 2 20 (benchmarkThreeSiteStates j) := by
  fin_cases j <;>
    norm_num [InClass, totalE, totalF, totalS,
      benchmarkThreeSiteStates, Fin.sum_univ_succ]

theorem benchmarkThreeSiteStates_injective :
    Function.Injective benchmarkThreeSiteStates := by
  intro i j hij
  have hE := congrArg State.E hij
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals norm_num [benchmarkThreeSiteStates] at hE

end
end PhosphorylationStableCapacity
