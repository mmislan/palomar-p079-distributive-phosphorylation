module
public import proofs.PhosphorylationStableCapacity.Compatibility
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The exact rate table printed in Example 9.2 of the P079 manuscript. -/
def manuscriptTwoSiteRates : Rates 2 where
  a := ![(19782 : ℝ)/1375, (311808 : ℝ)/192049]
  b := ![1, 1]
  c := ![(625 : ℝ)/1573, (4065 : ℝ)/2431]
  alpha := ![(147000 : ℝ)/124267, (79 : ℝ)/34]
  beta := ![1, 1]
  gamma := ![(45 : ℝ)/11, (45 : ℝ)/34]

/-- The three complete species vectors printed in Example 9.2. -/
def manuscriptTwoSiteStates : Fin 3 → State 2 := ![
  { S := ![(250 : ℝ)/693, (1027 : ℝ)/1008, (271 : ℝ)/528],
    E := 3/4, F := 8/7,
    C := ![(39 : ℝ)/14, (13 : ℝ)/28],
    D := ![(125 : ℝ)/462, (271 : ℝ)/462] },
  { S := ![(2625 : ℝ)/11297, 1, (8672 : ℝ)/11297],
    E := 1, F := 1,
    C := ![(189 : ℝ)/79, (48 : ℝ)/79],
    D := ![(2625 : ℝ)/11297, (8672 : ℝ)/11297] },
  { S := ![(350 : ℝ)/2223, (869 : ℝ)/912, (4065 : ℝ)/3952],
    E := 5/4, F := 8/9,
    C := ![(77 : ℝ)/38, (55 : ℝ)/76],
    D := ![(875 : ℝ)/4446, (1355 : ℝ)/1482] }
]

theorem manuscriptTwoSiteRates_positive : manuscriptTwoSiteRates.Positive := by
  intro i
  fin_cases i <;> norm_num [manuscriptTwoSiteRates]

theorem manuscriptTwoSiteStates_positive (j : Fin 3) :
    (manuscriptTwoSiteStates j).Positive := by
  fin_cases j
  all_goals
    refine ⟨?_, by norm_num [manuscriptTwoSiteStates],
      by norm_num [manuscriptTwoSiteStates], ?_, ?_⟩
    all_goals intro i
    all_goals fin_cases i <;> norm_num [manuscriptTwoSiteStates]

theorem manuscriptTwoSiteStates_equilibrium (j : Fin 3) :
    Equilibrium manuscriptTwoSiteRates (manuscriptTwoSiteStates j) := by
  apply equilibrium_of_currents
  · intro i
    fin_cases j <;> fin_cases i <;>
      norm_num [manuscriptTwoSiteRates, manuscriptTwoSiteStates, kinaseNet]
  · intro i
    fin_cases j <;> fin_cases i <;>
      norm_num [manuscriptTwoSiteRates, manuscriptTwoSiteStates, phosphataseNet]
  · intro i
    fin_cases j <;> fin_cases i <;>
      norm_num [manuscriptTwoSiteRates, manuscriptTwoSiteStates]

theorem manuscriptTwoSiteStates_inClass (j : Fin 3) :
    InClass 4 2 6 (manuscriptTwoSiteStates j) := by
  fin_cases j <;>
    norm_num [InClass, totalE, totalF, totalS, manuscriptTwoSiteStates,
      Fin.sum_univ_succ]

theorem manuscriptTwoSiteStates_injective :
    Function.Injective manuscriptTwoSiteStates := by
  intro i j hij
  have hE := congrArg State.E hij
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals norm_num [manuscriptTwoSiteStates] at hE

end
end PhosphorylationStableCapacity
