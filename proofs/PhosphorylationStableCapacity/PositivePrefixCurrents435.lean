module
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace PhosphorylationStableCapacity

/-- Positive independent catalytic-current coordinates on every
prefix edge of an `(m+2)`-site chain. -/
abbrev PositivePrefixCurrents (m : ℕ) :=
  {ω : Fin (m+1) → ℝ // ∀ i, 0 < ω i}

end PhosphorylationStableCapacity
