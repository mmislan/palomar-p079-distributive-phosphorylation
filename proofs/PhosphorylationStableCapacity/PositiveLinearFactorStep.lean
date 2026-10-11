module
public import proofs.PhosphorylationStableCapacity.PositiveRootLogConcavity

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial PhosphorylationSharpness

noncomputable section

/-- Multiplication by a positive linear factor, in a form with direct
coefficient recurrence. -/
def positiveLinearStep (r : ℝ) (p : ℝ[X]) : ℝ[X] :=
  C r * p + X * p

theorem positiveLinearStep_eq_mul (r : ℝ) (p : ℝ[X]) :
    positiveLinearStep r p = (X + C r) * p := by
  unfold positiveLinearStep
  ring

theorem positiveLinearStep_coeff_zero (r : ℝ) (p : ℝ[X]) :
    (positiveLinearStep r p).coeff 0 = r * p.coeff 0 := by
  simp [positiveLinearStep]

theorem positiveLinearStep_coeff_succ (r : ℝ) (p : ℝ[X]) (i : ℕ) :
    (positiveLinearStep r p).coeff (i + 1) =
      r * p.coeff (i + 1) + p.coeff i := by
  simp [positiveLinearStep, coeff_add, coeff_C_mul, coeff_X_mul]

theorem positiveLinearStep_dense {p : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) {r : ℝ} (hr : 0 < r) :
    DensePositive (positiveLinearStep r p) (m + 1) := by
  simpa [positiveLinearStep] using
    dense_step hp hp r 1 0 0 hr (by norm_num) (by norm_num) (by norm_num)

end
end PhosphorylationStableCapacity
