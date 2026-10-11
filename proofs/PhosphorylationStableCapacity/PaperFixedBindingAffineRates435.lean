module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingRealization435
public import proofs.PhosphorylationStableCapacity.SplitJacobianContinuity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Current-independent intercept of the literal frozen-binding relaxed
rate vector. These are algebraic coefficients, not a kinetic witness. -/
def paperFixedBindingRateIntercept {n : ℕ} (k : Rates n) (ε : ℝ) :
    Fin 6 → Fin n → ℝ :=
  ![(fun i => sourceBindingP k i.castSucc / ε),
    (fun _ => 1 / ε), (fun _ => 0),
    (fun i => sourceBindingQ k i.succ / ε),
    (fun _ => 1 / ε), (fun _ => 0)]

/-- Each edge current has an affine coefficient in the actual rates.
The coefficients vary with the source and the fixed relaxation scale. -/
def paperFixedBindingRateSlope {n : ℕ} (k : Rates n) (ε : ℝ) :
    Fin 6 → Fin n → ℝ :=
  ![(fun i => k.c i * sourceBindingP k i.castSucc / ε),
    (fun i => k.c i * (1 / ε - 1)), k.c,
    (fun i => k.gamma i * sourceBindingQ k i.succ / ε),
    (fun i => k.gamma i * (1 / ε - 1)), k.gamma]

/-- Exact affine dependence of the paper's actual kinetic vector on
the positive edge currents. This avoids inverse-current estimates
when transferring first-order bounds over compact current sets. -/
theorem paperFixedBinding_relaxed_rateVector_affine
    {n : ℕ} (k : Rates n) (w : Fin n → ℝ) (ε : ℝ)
    (hk : k.Positive) (hw : ∀ i, 0 < w i)
    (j : Fin 6) (i : Fin n) :
    rateVector (relaxRates
      (paperFixedBindingRates (edgeScaledRates w k)) ε) j i =
      paperFixedBindingRateIntercept k ε j i +
        w i * paperFixedBindingRateSlope k ε j i := by
  obtain ⟨hP, hQ⟩ := sourceBindingRatios_edgeScaledRates w k hw hk
  fin_cases j <;>
    simp [rateVector, paperFixedBindingRateIntercept,
      paperFixedBindingRateSlope, relaxRates, paperFixedBindingRates,
      hP, hQ] <;> simp only [edgeScaledRates] <;> ring

end
end PhosphorylationStableCapacity
