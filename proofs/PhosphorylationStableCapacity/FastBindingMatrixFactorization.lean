module
public import proofs.PhosphorylationStableCapacity.FastBindingFactorization
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness
open Module

/-- Standard kinase-then-phosphatase complex-coordinate basis. -/
def fastBasis (n : ℕ) : Basis (Fin n ⊕ Fin n) ℝ (FastSpace n) :=
  (Pi.basisFun ℝ (Fin n)).prod (Pi.basisFun ℝ (Fin n))

def fastAffinityMatrix (n : ℕ) (x : State n) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  LinearMap.toMatrix (fastBasis n) (fastBasis n) (fastAffinityLinear n x)

def fastRateMatrix (n : ℕ) (rho sigma : Fin n → ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  LinearMap.toMatrix (fastBasis n) (fastBasis n)
    (fastRateLinear n rho sigma)

def fastBindingMatrix (n : ℕ) (x : State n)
    (rho sigma : Fin n → ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  LinearMap.toMatrix (fastBasis n) (fastBasis n)
    (fastBindingEnd n x rho sigma)

/-- Matrix form of the exact fast-block factorization `L = -R H`. -/
theorem fastBindingMatrix_factorization {n : ℕ} (x : State n)
    (rho sigma : Fin n → ℝ) :
    fastBindingMatrix n x rho sigma =
      -(fastRateMatrix n rho sigma * fastAffinityMatrix n x) := by
  unfold fastBindingMatrix fastRateMatrix fastAffinityMatrix
  rw [fastBindingEnd_factorization]
  rw [map_neg]
  rw [LinearMap.toMatrix_comp (fastBasis n) (fastBasis n) (fastBasis n)
    (fastRateLinear n rho sigma) (fastAffinityLinear n x)]

end
end PhosphorylationStableCapacity
