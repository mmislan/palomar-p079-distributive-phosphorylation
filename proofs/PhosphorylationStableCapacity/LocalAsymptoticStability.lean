module
public import proofs.PhosphorylationStableCapacity.RateRegularBudget
public import Mathlib.Analysis.ODE.Basic

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Filter
open scoped Topology

noncomputable section

/-- A global forward solution of an autonomous class-coordinate ODE.
Only the nonnegative-time derivative is prescribed. -/
def IsForwardClassCurve {n : ℕ} (f : CoordinateSpace n → CoordinateSpace n)
    (y : CoordinateSpace n) (γ : ℝ → CoordinateSpace n) : Prop :=
  γ 0 = y ∧
    ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt γ (f (γ t)) (Set.Ici (0 : ℝ)) t

/-- Lyapunov stability, local attraction, and forward existence for an
equilibrium of the exact `3n` compatibility-class ODE. Quantification
over every forward solution avoids vacuous attraction if uniqueness is
not yet docked. -/
def IsLocallyAsymptoticallyStableClassField {n : ℕ}
    (f : CoordinateSpace n → CoordinateSpace n)
    (x : CoordinateSpace n) : Prop :=
  f x = 0 ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y : CoordinateSpace n, dist y x < δ →
        ∀ γ, IsForwardClassCurve f y γ →
          ∀ t : ℝ, 0 ≤ t → dist (γ t) x < ε) ∧
    (∃ δ : ℝ, 0 < δ ∧
      ∀ y : CoordinateSpace n, dist y x < δ →
        ∀ γ, IsForwardClassCurve f y γ →
          Tendsto γ atTop (𝓝 x)) ∧
    (∃ δ : ℝ, 0 < δ ∧
      ∀ y : CoordinateSpace n, dist y x < δ →
        ∃ γ, IsForwardClassCurve f y γ)

/-- The nonlinear stability predicate for the literal positive
mass-action dynamics in its fixed-total class chart. -/
def IsLocallyAsymptoticallyStableClass {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (x : CoordinateSpace n) : Prop :=
  IsLocallyAsymptoticallyStableClassField
    (restrictedFieldEuclid ET FT ST k) x

/-- A genuine local attractor is isolated among zeros of its class
field, including when its Jacobian is singular. -/
theorem local_attractor_isolated_zero {n : ℕ}
    {f : CoordinateSpace n → CoordinateSpace n}
    {x : CoordinateSpace n}
    (hx : IsLocallyAsymptoticallyStableClassField f x) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y : CoordinateSpace n, dist y x < δ → f y = 0 → y = x := by
  obtain ⟨δ, hδ, hattract⟩ := hx.2.2.1
  refine ⟨δ, hδ, ?_⟩
  intro y hyclose hyzero
  have hcurve : IsForwardClassCurve f y (fun _ : ℝ => y) := by
    constructor
    · rfl
    · intro t ht
      simpa [hyzero] using
        (hasDerivWithinAt_const t (Set.Ici (0 : ℝ)) y)
  have hlim := hattract y hyclose (fun _ : ℝ => y) hcurve
  exact (tendsto_const_nhds_iff.mp hlim)

/-- Isolation for the literal class-coordinate mass-action field. -/
theorem locally_asymptotically_stable_class_isolated {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (x : CoordinateSpace n)
    (hx : IsLocallyAsymptoticallyStableClass ET FT ST k x) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y : CoordinateSpace n, dist y x < δ →
        restrictedFieldEuclid ET FT ST k y = 0 → y = x :=
  local_attractor_isolated_zero hx

end
end PhosphorylationStableCapacity
