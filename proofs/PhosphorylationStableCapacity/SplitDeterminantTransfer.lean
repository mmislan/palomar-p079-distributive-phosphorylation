module
public import proofs.PhosphorylationStableCapacity.EdgeScaledDeterminantPreparation
public import proofs.PhosphorylationStableCapacity.SplitRetunedSource

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix

/-- The exact determinant multiplier from the source kinetics to the
equilibrium-preserving edge-scaled, fast-binding split kinetics. -/
theorem splitRetunedJacobian_det_factor (m : ℕ)
    (r τ δ ε : ℝ) (j : Fin (2*(m+1)+1)) (hε : 0 < ε) :
    (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (splitRetunedRates m r τ δ ε)
      (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).det =
    (ε⁻¹) ^ (2*(m+2)) *
      (∏ i : Fin (m+2), coalescedFinalCurrentWeights m τ i) ^ 3 *
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (splitFiniteRates (m+1) r δ)
          (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).det := by
  let u := toLoadedCoord
    (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))
  have hu : fromLoadedCoord u =
      toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)) :=
    from_toLoadedCoord _
  rw [← hu]
  change (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
    (relaxRates (edgeScaledRates (coalescedFinalCurrentWeights m τ)
      (splitFiniteRates (m+1) r δ)) ε)
    (fromLoadedCoord u)).det = _
  rw [restrictedJacobianMatrix_relax_det (2*r) 2 (2*(r+1))
    (edgeScaledRates (coalescedFinalCurrentWeights m τ)
      (splitFiniteRates (m+1) r δ)) u hε]
  rw [restrictedJacobianMatrix_edgeScaled_det]
  ring

theorem splitRetunedJacobian_det_sign (m : ℕ)
    (r τ δ ε : ℝ) (j : Fin (2*(m+1)+1))
    (hτ : 0 < τ) (hε : 0 < ε) :
    ((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (splitRetunedRates m r τ δ ε)
        (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).det < 0 ↔
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (splitFiniteRates (m+1) r δ)
        (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).det < 0) ∧
    (0 < (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (splitRetunedRates m r τ δ ε)
        (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).det ↔
      0 < (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (splitFiniteRates (m+1) r δ)
        (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).det) := by
  rw [splitRetunedJacobian_det_factor m r τ δ ε j hε]
  have hw : ∀ i : Fin (m+2), 0 < coalescedFinalCurrentWeights m τ i := by
    intro i
    by_cases hi : i = Fin.last (m+1)
    · simp [coalescedFinalCurrentWeights, hi, hτ]
    · simp [coalescedFinalCurrentWeights, hi]
  have hweight : 0 <
      (∏ i : Fin (m+2), coalescedFinalCurrentWeights m τ i) ^ 3 :=
    pow_pos (Finset.prod_pos (fun i _ => hw i)) _
  have hfactor : 0 < (ε⁻¹) ^ (2*(m+2)) *
      (∏ i : Fin (m+2), coalescedFinalCurrentWeights m τ i) ^ 3 :=
    mul_pos (pow_pos (inv_pos.mpr hε) _) hweight
  constructor
  · simpa only [mul_assoc, mul_zero] using
      (mul_lt_mul_iff_of_pos_left hfactor (b :=
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (splitFiniteRates (m+1) r δ)
          (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).det)
        (c := 0))
  · simpa only [mul_assoc] using mul_pos_iff_of_pos_left hfactor

end
end PhosphorylationStableCapacity
