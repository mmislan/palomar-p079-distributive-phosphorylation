module
public import proofs.PhosphorylationStableCapacity.NonlinearAttainmentTarget
public import proofs.PhosphorylationStableCapacity.LocalStableEquilibriumBudget

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- The remaining universal ceiling includes all locally
asymptotically stable positive equilibria, whether hyperbolic or not. -/
def UniversalNonlinearStableCeiling : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ (ET FT ST : ℝ), 0 < ET → 0 < FT → 0 < ST →
    ∀ (k : Rates n), k.Positive →
      (locallyStablePositiveStates ET FT ST k).ncard ≤ n

/-- The exact common-class nonlinear capacity contract at each size. -/
def ExactNonlinearStableCapacity (n : ℕ) : Prop :=
  NonlinearlyStableClassAttains n n ∧
    ∀ (ET FT ST : ℝ), 0 < ET → 0 < FT → 0 < ST →
      ∀ (k : Rates n), k.Positive →
        (locallyStablePositiveStates ET FT ST k).ncard ≤ n

/-- The lower-bound half is strict; a proof of the exact remaining
ceiling immediately gives the advertised all-size endpoint. -/
theorem all_size_exact_nonlinear_capacity_of_universal_ceiling
    (hceiling : UniversalNonlinearStableCeiling)
    (n : ℕ) (hn : 1 ≤ n) :
    ExactNonlinearStableCapacity n := by
  exact ⟨all_size_nonlinearly_stable_attainment n hn,
    hceiling n hn⟩

end
end PhosphorylationStableCapacity
