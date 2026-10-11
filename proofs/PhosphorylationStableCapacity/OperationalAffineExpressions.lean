module
public import proofs.PhosphorylationStableCapacity.RationalExpressionLinearCombination
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fin.VecNotation

@[expose] public section
namespace PhosphorylationStableCapacity
open scoped BigOperators
def operationalInput (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) : Fin 30 → ℝ :=
  fun i => Fin.addCases (m := 21) (n := 9) θ w i

/-- Exact affine derivative of physical species with respect to the weighted
class coordinates, including the three species reconstructed from totals. -/
def operationalSpeciesLinear (s : Fin 9 → ℚ) : Matrix (Fin 12) (Fin 9) ℚ := Matrix.of
  ![![-s 0,-s 1,-s 2,-s 3,-s 4,-s 5,-s 6,-s 7,-s 8],
    ![s 0,0,0,0,0,0,0,0,0], ![0,s 1,0,0,0,0,0,0,0],
    ![0,0,s 2,0,0,0,0,0,0],
    ![0,0,0,-s 3,-s 4,-s 5,0,0,0],
    ![0,0,0,0,0,0,-s 6,-s 7,-s 8],
    ![0,0,0,s 3,0,0,0,0,0], ![0,0,0,0,s 4,0,0,0,0],
    ![0,0,0,0,0,s 5,0,0,0], ![0,0,0,0,0,0,s 6,0,0],
    ![0,0,0,0,0,0,0,s 7,0], ![0,0,0,0,0,0,0,0,s 8]]

def operationalCentreExpression (q : Fin 9 → ℚ) :
    Fin 12 → RationalExpression (Fin 30) :=
  ![.add (.const (-∑ j, q j)) (.var 20),
    .const (q 0),.const (q 1),.const (q 2),
    .add (.const (-q 3-q 4-q 5)) (.var 18),
    .add (.const (-q 6-q 7-q 8)) (.var 19),
    .const (q 3),.const (q 4),.const (q 5),
    .const (q 6),.const (q 7),.const (q 8)]

def operationalSpeciesExpression (q s : Fin 9 → ℚ) (i : Fin 12) :
    RationalExpression (Fin 30) :=
  .add (operationalCentreExpression q i)
    (RationalExpression.linearCombination 9 (operationalSpeciesLinear s i)
      (fun j => .var (Fin.natAdd 21 j)))

end PhosphorylationStableCapacity
