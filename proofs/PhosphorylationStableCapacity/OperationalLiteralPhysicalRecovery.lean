module
public import proofs.PhosphorylationStableCapacity.OperationalSinkOutcome

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open Matrix Set PhosphorylationSharpness
open scoped BigOperators

/-- A solution of the literal physical mass-action equation, expressed in
the printed physical weighted class coordinates and measured in seconds. -/
def IsOperationalLiteralPhysicalCurve (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ)
    (initial : Fin 9 → ℝ) (γ : ℝ → Fin 9 → ℝ) : Prop :=
  γ 0 = initial ∧ ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt γ
      (operationalWeightedField (fun i => q i/10) (fun i => s i/10)
        (operationalPhysicalParameters θ) (γ t)) (Ici (0 : ℝ)) t

theorem operational_literal_physical_curve_iff
    (q s : Fin 9 → ℝ) (hs : ∀ i, s i ≠ 0) (θ : Fin 21 → ℝ)
    (initial : Fin 9 → ℝ) (γ : ℝ → Fin 9 → ℝ) :
    IsOperationalLiteralPhysicalCurve q s θ initial γ ↔
      IsOperationalPhysicalCurve q s θ initial γ := by
  unfold IsOperationalLiteralPhysicalCurve IsOperationalPhysicalCurve
  simp_rw [operational_physical_weighted_field q s hs θ]

/-- Both recovery regions quantify over solutions of the actual physical
field, retaining the same rates, totals, shifted equilibrium and fixed P. -/
def OperationalLiteralPhysicalRecovery (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ)
    (P : Matrix (Fin 9) (Fin 9) ℝ)
    (ρ ρin p c M recoveryTime : ℝ) (equilibrium : Fin 9 → ℝ) : Prop :=
  (∀ initial : Fin 9 → ℝ, (∑ i, (initial i-equilibrium i)^2) ≤ ρin^2 →
    (∃ γ : ℝ → Fin 9 → ℝ, IsOperationalLiteralPhysicalCurve q s θ initial γ) ∧
    ∀ γ : ℝ → Fin 9 → ℝ, IsOperationalLiteralPhysicalCurve q s θ initial γ →
      OperationalRecoveryConclusion equilibrium ρ c M recoveryTime γ) ∧
  (∀ initial : Fin 9 → ℝ,
    (initial-equilibrium) ⬝ᵥ (P *ᵥ (initial-equilibrium)) ≤ p*(ρ/2)^2 →
    (∃ γ : ℝ → Fin 9 → ℝ, IsOperationalLiteralPhysicalCurve q s θ initial γ) ∧
    ∀ γ : ℝ → Fin 9 → ℝ, IsOperationalLiteralPhysicalCurve q s θ initial γ →
      (∀ t : ℝ, 0 ≤ t → (γ t-equilibrium) ⬝ᵥ
        (P *ᵥ (γ t-equilibrium)) ≤ p*(ρ/2)^2) ∧
      OperationalRecoveryConclusion equilibrium ρ c M recoveryTime γ)

theorem OperationalSinkOutcome.literal_physical_recovery
    {q s : Fin 9 → ℝ} {θ : Fin 21 → ℝ}
    {P : Matrix (Fin 9) (Fin 9) ℝ}
    {ρ ρin p c M recoveryTime lower upper : ℝ} {equilibrium : Fin 9 → ℝ}
    (h : OperationalSinkOutcome q s θ P ρ ρin p c M recoveryTime lower upper equilibrium)
    (hs : ∀ i, s i ≠ 0) :
    OperationalLiteralPhysicalRecovery q s θ P ρ ρin p c M recoveryTime equilibrium := by
  constructor
  · intro initial hinit
    obtain ⟨⟨γ, hγ⟩, hall⟩ := h.inner_recovery initial hinit
    refine ⟨⟨γ, (operational_literal_physical_curve_iff q s hs θ initial γ).mpr hγ⟩, ?_⟩
    intro γ hγ
    exact hall γ ((operational_literal_physical_curve_iff q s hs θ initial γ).mp hγ)
  · intro initial hinit
    obtain ⟨⟨γ, hγ⟩, hall⟩ := h.closed_ellipsoid_recovery initial hinit
    refine ⟨⟨γ, (operational_literal_physical_curve_iff q s hs θ initial γ).mpr hγ⟩, ?_⟩
    intro γ hγ
    exact hall γ ((operational_literal_physical_curve_iff q s hs θ initial γ).mp hγ)

end
end PhosphorylationStableCapacity
