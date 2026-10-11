module
public import proofs.PhosphorylationStableCapacity.FastBindingFieldDifference

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- An equilibrium binding balance rewrites the linearized mass-action term
as minus the positive binding flux times its concentration affinity. -/
theorem bindingLinearTerm_eq_affinity
    (a out S E C dS dE vc : ℝ)
    (hS : S ≠ 0) (hE : E ≠ 0) (hC : C ≠ 0)
    (hbal : a * S * E = out * C) :
    a * (S * dE + E * dS) - out * vc =
      -(a * S * E) * (vc / C - dS / S - dE / E) := by
  have h1 : a * S * dE = (a * S * E) * (dE / E) := by
    field_simp [hE]
  have h2 : a * E * dS = (a * S * E) * (dS / S) := by
    field_simp [hS]
  have h3 : out * vc = (a * S * E) * (vc / C) := by
    rw [hbal]
    field_simp [hC]
  calc
    a * (S * dE + E * dS) - out * vc =
        a * S * dE + a * E * dS - out * vc := by ring
    _ = (a * S * E) * (dE / E) + (a * S * E) * (dS / S) -
        (a * S * E) * (vc / C) := by rw [h1, h2, h3]
    _ = -(a * S * E) * (vc / C - dS / S - dE / E) := by ring

theorem bindingFieldDifference_eq_affinity
    (a out S E C dS dE vc : ℝ)
    (hS : S ≠ 0) (hE : E ≠ 0) (hC : C ≠ 0)
    (hbal : a * S * E = out * C) :
    a * (S * dE + E * dS + dS * dE) - out * vc =
      -(a * S * E) * (vc / C - dS / S - dE / E) +
        a * dS * dE := by
  calc
    a * (S * dE + E * dS + dS * dE) - out * vc =
        (a * (S * dE + E * dS) - out * vc) + a * dS * dE := by ring
    _ = -(a * S * E) * (vc / C - dS / S - dE / E) +
        a * dS * dE := by
      rw [bindingLinearTerm_eq_affinity a out S E C dS dE vc
        hS hE hC hbal]

end
end PhosphorylationStableCapacity
