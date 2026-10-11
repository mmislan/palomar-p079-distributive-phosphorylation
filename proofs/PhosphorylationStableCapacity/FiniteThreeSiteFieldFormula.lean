module
public import proofs.PhosphorylationStableCapacity.Jacobian
public import Mathlib.Tactic.FinCases

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

def threeSiteFreeS0 (ST : ℝ) (u : CoordinateSpace 3) : ℝ :=
  ST - u.1 0 - u.1 1 - u.1 2 -
    u.2.1 0 - u.2.1 1 - u.2.1 2 -
    u.2.2 0 - u.2.2 1 - u.2.2 2

def threeSiteFreeE (ET : ℝ) (u : CoordinateSpace 3) : ℝ :=
  ET - u.2.1 0 - u.2.1 1 - u.2.1 2

def threeSiteFreeF (FT : ℝ) (u : CoordinateSpace 3) : ℝ :=
  FT - u.2.2 0 - u.2.2 1 - u.2.2 2

/-- Exact nine-coordinate class field for the three-site system. -/
def threeSiteField (ET FT ST : ℝ) (k : Rates 3)
    (u : CoordinateSpace 3) : CoordinateSpace 3 :=
  (![k.c 0 * u.2.1 0 - k.alpha 0 * u.1 0 * threeSiteFreeF FT u +
      k.beta 0 * u.2.2 0 - k.a 1 * u.1 0 * threeSiteFreeE ET u +
      k.b 1 * u.2.1 1 + k.gamma 1 * u.2.2 1,
     k.c 1 * u.2.1 1 - k.alpha 1 * u.1 1 * threeSiteFreeF FT u +
      k.beta 1 * u.2.2 1 - k.a 2 * u.1 1 * threeSiteFreeE ET u +
      k.b 2 * u.2.1 2 + k.gamma 2 * u.2.2 2,
     k.c 2 * u.2.1 2 - k.alpha 2 * u.1 2 * threeSiteFreeF FT u +
      k.beta 2 * u.2.2 2],
   (![k.a 0 * threeSiteFreeS0 ST u * threeSiteFreeE ET u -
      (k.b 0 + k.c 0) * u.2.1 0,
     k.a 1 * u.1 0 * threeSiteFreeE ET u -
      (k.b 1 + k.c 1) * u.2.1 1,
     k.a 2 * u.1 1 * threeSiteFreeE ET u -
      (k.b 2 + k.c 2) * u.2.1 2],
    ![k.alpha 0 * u.1 0 * threeSiteFreeF FT u -
        (k.beta 0 + k.gamma 0) * u.2.2 0,
      k.alpha 1 * u.1 1 * threeSiteFreeF FT u -
        (k.beta 1 + k.gamma 1) * u.2.2 1,
      k.alpha 2 * u.1 2 * threeSiteFreeF FT u -
        (k.beta 2 + k.gamma 2) * u.2.2 2]))

private theorem fin4_cases_one (a : ℝ) (f : Fin 3 → ℝ) :
    Fin.cases a f (1 : Fin 4) = f 0 := by rfl

private theorem fin4_cases_two (a : ℝ) (f : Fin 3 → ℝ) :
    Fin.cases a f (2 : Fin 4) = f 1 := by rfl

theorem restrictedFieldEuclid_threeSite
    (ET FT ST : ℝ) (k : Rates 3) (u : CoordinateSpace 3) :
    restrictedFieldEuclid ET FT ST k u = threeSiteField ET FT ST k u := by
  ext i <;> fin_cases i <;>
    simp [restrictedFieldEuclid, restrictedField, chart, field, unChart,
      ofCoordinateSpace, toCoordinateSpace, kinaseNet, phosphataseNet,
      threeSiteField, threeSiteFreeS0, threeSiteFreeE, threeSiteFreeF,
      Fin.sum_univ_succ, fin4_cases_one, fin4_cases_two] <;> ring

end
end PhosphorylationStableCapacity
