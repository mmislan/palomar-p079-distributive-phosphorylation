module
public import proofs.PhosphorylationStableCapacity.OperationalAffineExpressions

@[expose] public section

namespace PhosphorylationStableCapacity

def operationalReactionFirst : Fin 18 → Fin 12 :=
  ![0,6,6,1,9,9,1,7,7,2,10,10,2,8,8,3,11,11]

def operationalReactionSecond : Fin 18 → Option (Fin 12) :=
  ![some 4,none,none,some 5,none,none,
    some 4,none,none,some 5,none,none,
    some 4,none,none,some 5,none,none]

def operationalFluxExpression (species : Fin 12 → RationalExpression (Fin 30))
    (a : Fin 18) : RationalExpression (Fin 30) :=
  match operationalReactionSecond a with
  | none => .mul (.var (Fin.castAdd 12 a)) (species (operationalReactionFirst a))
  | some b => .mul (.mul (.var (Fin.castAdd 12 a))
      (species (operationalReactionFirst a))) (species b)

def operationalNominalFlux (rates : Fin 18 → ℚ) (species : Fin 12 → ℚ)
    (a : Fin 18) : ℚ :=
  match operationalReactionSecond a with
  | none => rates a * species (operationalReactionFirst a)
  | some b => rates a * species (operationalReactionFirst a) * species b

def operationalFluxDifferenceExpression (q : Fin 9 → ℚ)
    (rates : Fin 18 → ℚ) (nominalSpecies : Fin 12 → ℚ) (a : Fin 18) :
    RationalExpression (Fin 30) :=
  .add (operationalFluxExpression (operationalCentreExpression q) a)
    (.neg (.const (operationalNominalFlux rates nominalSpecies a)))

/-- The exact perturbation of an elementary reaction derivative. All state
variables are reconstructed from the same totals and weighted coordinates. -/
def operationalDerivativeDifferenceExpression (q s : Fin 9 → ℚ)
    (rates : Fin 18 → ℚ) (nominalSpecies : Fin 12 → ℚ) (a : Fin 18) (j : Fin 9) :
    RationalExpression (Fin 30) :=
  let first := operationalReactionFirst a
  let rate : RationalExpression (Fin 30) := .var (Fin.castAdd 12 a)
  match operationalReactionSecond a with
  | none => .mul (.const (operationalSpeciesLinear s first j))
      (.add rate (.neg (.const (rates a))))
  | some b => .add
      (.mul (.const (operationalSpeciesLinear s b j))
        (.add (.mul rate (operationalSpeciesExpression q s first))
          (.neg (.const (rates a*nominalSpecies first)))))
      (.mul (.const (operationalSpeciesLinear s first j))
        (.add (.mul rate (operationalSpeciesExpression q s b))
          (.neg (.const (rates a*nominalSpecies b)))))

end PhosphorylationStableCapacity
