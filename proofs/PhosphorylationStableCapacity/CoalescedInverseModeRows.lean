module
public import proofs.PhosphorylationStableCapacity.CoalescedMassModeRows
public import proofs.PhosphorylationStableCapacity.CoalescedFullMassPositive

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- The finite-parameter response whose limit is equation (5) of the
ordinary spectral argument. -/
def coalescedInverseResponse (m : ℕ) (r : ℝ)
    (q : Fin (m + 3) → ℝ) : Fin (m + 3) → ℝ :=
  r • (coalescedFullMass m r)⁻¹.mulVec q

/-- Finite nonsingularity makes the scaled inverse response solve the exact
loaded-mass equation. -/
theorem coalescedInverseResponse_mass_equation
    (m : ℕ) (r : ℝ) (q : Fin (m + 3) → ℝ)
    (hdet : (coalescedFullMass m r).det ≠ 0) :
    (coalescedFullMass m r).mulVec (coalescedInverseResponse m r q) =
      r • q := by
  have hunit : IsUnit (coalescedFullMass m r).det :=
    isUnit_iff_ne_zero.mpr hdet
  unfold coalescedInverseResponse
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]

/-- A zero-sum direction supported away from the final substrate level
forces exact total and final constraints on the finite inverse response.
No convergence assertion is used. -/
theorem coalescedInverseResponse_mode_rows
    (m : ℕ) (r : ℝ) (q : Fin (m + 3) → ℝ)
    (hqsum : (∑ i : Fin (m + 3), q i) = 0)
    (hqlast : q (Fin.last (m + 2)) = 0)
    (hdet : (coalescedFullMass m r).det ≠ 0)
    (hpos : (coalescedFiniteState (m + 1) r).Positive)
    (hC : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).C i) = 2 * r - 1)
    (hD : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).D i) = 1)
    (hr : r ≠ 0) :
    (let σ := coalescedInverseResponse m r q;
      (∑ i : Fin (m + 3),
        (coalescedFiniteState (m + 1) r).S i * σ i) +
        (∑ i : Fin (m + 3), coalescedFiniteCLevel m r i * σ i) /
          (2 * r) +
          (∑ i : Fin (m + 3), coalescedFiniteYLevel m r i * σ i) / 2 = 0) ∧
    (let σ := coalescedInverseResponse m r q;
      (∑ i : Fin (m + 3), coalescedFiniteYLevel m r i * σ i) =
        4 * σ (Fin.last (m + 2))) := by
  let σ := coalescedInverseResponse m r q
  have hmx := coalescedInverseResponse_mass_equation m r q hdet
  have hsum : (∑ i : Fin (m + 3),
      (coalescedFullMass m r).mulVec σ i) = 0 := by
    calc
      (∑ i : Fin (m + 3),
        (coalescedFullMass m r).mulVec σ i) =
          ∑ i : Fin (m + 3), (r • q) i := by rw [hmx]
      _ = r * (∑ i : Fin (m + 3), q i) := by
        simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      _ = 0 := by rw [hqsum, mul_zero]
  have hfinal : (coalescedFullMass m r).mulVec σ
      (Fin.last (m + 2)) = 0 := by
    rw [hmx]
    simp [Pi.smul_apply, hqlast]
  constructor
  · dsimp
    rw [← coalescedFullMass_total_action m r σ hr hC hD]
    exact hsum
  · dsimp
    exact coalescedFullMass_final_zero_equation m r σ hpos hfinal

/-- The exact finite inverse mode constraints hold at every sufficiently
large literal source parameter for any zero-sum direction with zero final
entry. The singular inverse limit remains a separate theorem. -/
theorem coalescedInverseResponse_eventually_mode_rows
    (m : ℕ) (q : Fin (m + 3) → ℝ)
    (hqsum : (∑ i : Fin (m + 3), q i) = 0)
    (hqlast : q (Fin.last (m + 2)) = 0) :
    ∀ᶠ r : ℝ in atTop,
      (let σ := coalescedInverseResponse m r q;
        (∑ i : Fin (m + 3),
          (coalescedFiniteState (m + 1) r).S i * σ i) +
          (∑ i : Fin (m + 3), coalescedFiniteCLevel m r i * σ i) /
            (2 * r) +
            (∑ i : Fin (m + 3), coalescedFiniteYLevel m r i * σ i) / 2 = 0) ∧
      (let σ := coalescedInverseResponse m r q;
        (∑ i : Fin (m + 3), coalescedFiniteYLevel m r i * σ i) =
          4 * σ (Fin.last (m + 2))) := by
  filter_upwards [coalescedFullMass_eventually_det_ne_zero m,
    coalescedFiniteState_eventually_equilibrium (m + 1),
    coalescedFiniteState_eventually_component_totals (m + 1),
    eventually_gt_atTop (0 : ℝ)] with r hdet hstate htot hr
  exact coalescedInverseResponse_mode_rows m r q hqsum hqlast hdet
    hstate.2.1 htot.1 htot.2.1 (ne_of_gt hr)

end
end PhosphorylationStableCapacity
