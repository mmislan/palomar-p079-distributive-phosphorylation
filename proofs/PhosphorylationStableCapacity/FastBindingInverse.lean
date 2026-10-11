module
public import proofs.PhosphorylationStableCapacity.FastBindingLinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Positive binding weights make the abstract fast block a linear
equivalence, so its inverse is available for exact Schur elimination. -/
def fastBindingEquiv {n : ℕ} (x : State n) (hx : x.Positive)
    (rho sigma : Fin n → ℝ) (hrho : ∀ i, 0 < rho i)
    (hsigma : ∀ i, 0 < sigma i) : FastSpace n ≃ₗ[ℝ] FastSpace n :=
  LinearEquiv.ofInjectiveEndo (fastBindingEnd n x rho sigma)
    (fastBindingEnd_injective x hx rho sigma hrho hsigma)

@[simp] theorem fastBindingEquiv_apply {n : ℕ} (x : State n)
    (hx : x.Positive) (rho sigma : Fin n → ℝ)
    (hrho : ∀ i, 0 < rho i) (hsigma : ∀ i, 0 < sigma i)
    (v : FastSpace n) :
    fastBindingEquiv x hx rho sigma hrho hsigma v =
      fastBindingLinear x rho sigma v := rfl

end
end PhosphorylationStableCapacity
