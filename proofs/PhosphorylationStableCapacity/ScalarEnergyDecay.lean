module
public import proofs.PhosphorylationStableCapacity.OneSiteLyapunovCertificate
public import Mathlib.Analysis.ODE.Gronwall

@[expose] public section

namespace PhosphorylationStableCapacity

open Set Filter

noncomputable section

/-- A scalar energy whose right derivative is at most `-α` times
itself decays exponentially on every compact forward interval.
The decay rate may be obtained from a quadratic Lyapunov inequality. -/
theorem scalar_energy_decay_on_Icc
    (g g' : ℝ → ℝ) (α T : ℝ)
    (hcont : ContinuousOn g (Icc (0 : ℝ) T))
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt g (g' t) (Ici t) t)
    (hineq : ∀ t ∈ Ico (0 : ℝ) T,
      g' t ≤ -α * g t) :
    ∀ t ∈ Icc (0 : ℝ) T,
      g t ≤ g 0 * Real.exp (-α * t) := by
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (δ := g 0) (K := -α) (ε := 0)
    (a := 0) (b := T) (f := g) (f' := g')
    hcont
    (fun t ht r hr => (hderiv t ht).liminf_right_slope_le hr)
    (le_refl (g 0))
    (by
      intro t ht
      simpa [neg_mul] using hineq t ht)
  intro t ht
  have hbound := h t ht
  simpa [gronwallBound_ε0, sub_zero] using hbound

end
end PhosphorylationStableCapacity
