module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingPositiveProbes435
public import proofs.PhosphorylationStableCapacity.LoadedJacobianRateLinearity435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix

/-- For every positive current vector and every source parameter where
the base rate list is positive, the actual full loaded Jacobian is an
affine combination of finitely many strictly positive current probes.
The state and compatibility class remain fixed throughout this identity. -/
theorem paperFixedBinding_loadedJacobian_all_positive_probes
    {n : ℕ} (ET FT ST : ℝ) (k : Rates n) (ε : ℝ)
    (hk : k.Positive) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (u : CoordinateSpace n) :
    loadedJacobianMatrix ET FT ST
      (relaxRates (paperFixedBindingRates (edgeScaledRates w k)) ε) u =
      loadedJacobianMatrix ET FT ST
        (relaxRates (paperFixedBindingRates
          (edgeScaledRates (fun _ => 1) k)) ε) u +
      ∑ p : Fin n, (w p - 1) •
        (loadedJacobianMatrix ET FT ST
          (relaxRates (paperFixedBindingRates
            (edgeScaledRates (paperPositiveCurrentProbe p) k)) ε) u -
         loadedJacobianMatrix ET FT ST
           (relaxRates (paperFixedBindingRates
             (edgeScaledRates (fun _ => 1) k)) ε) u) := by
  let K : (Fin n → ℝ) → Rates n := fun z =>
    relaxRates (paperFixedBindingRates (edgeScaledRates z k)) ε
  have hrate := paperFixedBinding_rateVector_all_positive_probes
    k ε hk w hw
  change loadedJacobianMatrix ET FT ST (K w) u = _
  calc
    loadedJacobianMatrix ET FT ST (K w) u =
        loadedJacobianMatrix ET FT ST
          (ratesFromVector (rateVector (K w))) u := by
            rw [ratesFromVector_rateVector]
    _ = loadedJacobianMatrix ET FT ST
          (ratesFromVector
            (rateVector (K (fun _ => 1)) +
              ∑ p : Fin n, (w p - 1) •
                (rateVector (K (paperPositiveCurrentProbe p)) -
                  rateVector (K (fun _ => 1))))) u := by
            rw [hrate]
    _ = _ := by
      rw [loadedJacobianMatrix_rateVector_add,
        loadedJacobianMatrix_rateVector_sum]
      simp_rw [loadedJacobianMatrix_rateVector_smul,
        loadedJacobianMatrix_rateVector_sub,
        ratesFromVector_rateVector]
      rfl

end

end PhosphorylationStableCapacity
