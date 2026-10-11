module
public import proofs.PhosphorylationStableCapacity.FastBindingInverse

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Positive flux weights act diagonally on kinase and phosphatase complex
coordinates. -/
def fastRateLinear (n : ℕ) (rho sigma : Fin n → ℝ) :
    FastSpace n →ₗ[ℝ] FastSpace n where
  toFun v := (fun i => rho i * v.1 i, fun i => sigma i * v.2 i)
  map_add' := by
    intro v w
    apply Prod.ext
    · funext i
      change rho i * (v.1 i + w.1 i) =
        rho i * v.1 i + rho i * w.1 i
      ring
    · funext i
      change sigma i * (v.2 i + w.2 i) =
        sigma i * v.2 i + sigma i * w.2 i
      ring
  map_smul' := by
    intro c v
    apply Prod.ext
    · funext i
      change rho i * (c * v.1 i) = c * (rho i * v.1 i)
      ring
    · funext i
      change sigma i * (c * v.2 i) = c * (sigma i * v.2 i)
      ring

/-- The fast binding operator is minus the positive diagonal flux map
composed with the symmetric affinity map. -/
theorem fastBindingEnd_factorization {n : ℕ} (x : State n)
    (rho sigma : Fin n → ℝ) :
    fastBindingEnd n x rho sigma =
      -(fastRateLinear n rho sigma).comp (fastAffinityLinear n x) := by
  apply LinearMap.ext
  intro v
  apply Prod.ext
  · funext i
    change -rho i * fastAffinityC x v i =
      -(rho i * fastAffinityC x v i)
    ring
  · funext i
    change -sigma i * fastAffinityD x v i =
      -(sigma i * fastAffinityD x v i)
    ring

end
end PhosphorylationStableCapacity
