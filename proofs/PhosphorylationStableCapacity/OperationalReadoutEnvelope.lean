module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace PhosphorylationStableCapacity

/-- The measured fully phosphorylated readout at a perturbed equilibrium
is controlled by its two coordinate shifts and the measurement error. -/
theorem two_coordinate_readout_error_bound
    (a b C s err u v measurement : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hu : |u| ≤ s) (hv : |v| ≤ s) (hmeas : |measurement| ≤ err) :
    |C*(a*u+b*v)+measurement| ≤ C*(a+b)*s+err := by
  calc
    _ ≤ |C*(a*u+b*v)|+|measurement| := abs_add_le _ _
    _ = C*|a*u+b*v|+|measurement| := by rw [abs_mul, abs_of_nonneg hC]
    _ ≤ C*(|a*u|+|b*v|)+err :=
      add_le_add (mul_le_mul_of_nonneg_left (abs_add_le _ _) hC) hmeas
    _ = C*(a*|u|+b*|v|)+err := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ C*(a*s+b*s)+err := by
      exact add_le_add (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hu ha)
          (mul_le_mul_of_nonneg_left hv hb)) hC) le_rfl
    _ = _ := by ring

theorem measured_readout_mem_certified_interval
    (nominal value radius lo hi : ℝ)
    (herror : |value-nominal| ≤ radius)
    (hlo : lo ≤ nominal-radius) (hhi : nominal+radius ≤ hi) :
    lo ≤ value ∧ value ≤ hi := by
  rw [abs_le] at herror
  constructor <;> linarith

end PhosphorylationStableCapacity
