module
public import proofs.PhosphorylationStableCapacity.CoalescedPathGreen435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Symmetry transfers the two Poisson equations into the feedback
identity `∑w=∑f z`. -/
theorem symmetric_poisson_mass_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) (f z w : ι → ℝ)
    (hSymm : ∀ i j, H i j = H j i)
    (hHz : ∀ i, (∑ j, H i j * z j) = 1)
    (hHw : ∀ i, (∑ j, H i j * w j) = f i) :
    (∑ i, w i) = ∑ i, f i * z i := by
  calc
    (∑ i, w i) = ∑ i, (∑ j, H i j * z j) * w i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hHz i]
      ring
    _ = ∑ j, (∑ i, H j i * w i) * z j := by
      calc
        (∑ i, (∑ j, H i j * z j) * w i) =
            ∑ i, ∑ j, H i j * z j * w i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
        _ = ∑ j, ∑ i, H j i * w i * z j := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro i _
          rw [hSymm i j]
          ring
        _ = ∑ j, (∑ i, H j i * w i) * z j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
    _ = ∑ j, f j * z j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hHw j]

/-- Explicit diagonal Lyapunov certificate for the manuscript's
coalesced limiting prefix `B_*=-H+1φᵀ`, with exactly
`P=diag((H⁻¹φ)_i/(H⁻¹1)_i)`. -/
theorem coalescedPathBlock_explicit_diagonal_lyapunov (m : ℕ) :
    let d := coalescedPathWeights m
    let f := coalescedPathEdgeFeedback m
    let z := pathVectorFin d
    let w := (pathH d)⁻¹.mulVec f
    let P := Matrix.diagonal (fun i : Fin (m+1) => w i / z i)
    P.PosDef ∧
      (-((coalescedPathBlock m).transpose * P +
        P * coalescedPathBlock m)).PosDef ∧
      ∀ i, (∑ j,
        ((coalescedPathBlock m).transpose * P +
          P * coalescedPathBlock m) i j * z j) < 0 := by
  intro d f z w P
  have hd : ∀ k, 0 < d k := coalescedPathWeights_pos m
  have hf : ∀ i, 0 < f i := coalescedPathEdgeFeedback_pos m
  obtain ⟨w', hwEq, hwpos, hHw⟩ :=
    pathH_inverse_positive_forcing (by omega : 0 < m+1) d hd f hf
  have hw : ∀ i, 0 < w i := by
    simpa only [w, hwEq] using hwpos
  have hHw' : ∀ i, (∑ j, pathH d i j * w j) = f i := by
    simpa only [w, hwEq] using hHw
  have hz : ∀ i, 0 < z i := pathVectorFin_pos d hd
  have hHz : ∀ i, (∑ j, pathH d i j * z j) = 1 := by
    intro i
    simpa only [Matrix.mulVec, dotProduct] using
      pathVectorFin_action (by omega : 0 < m+1) d hd i
  have hmass : (∑ i, w i) = ∑ i, f i * z i :=
    symmetric_poisson_mass_identity (pathH d) f z w
      (pathH_symmetric d) hHz hHw'
  have hG : (∑ j, f j * z j) < 1 := by
    let i : Fin (m+1) := ⟨0, by omega⟩
    have hb := coalescedPathBlock_negative_vector m i
    have hbEq : (∑ j, coalescedPathBlock m i j * z j) =
        -1 + ∑ j, f j * z j := by
      simp only [coalescedPathBlock, z, d, f,
        add_mul, neg_mul, Finset.sum_add_distrib,
        Finset.sum_neg_distrib]
      rw [hHz i]
    rw [hbEq] at hb
    linarith
  have hleft : ∀ i,
      (∑ j, coalescedPathBlock m j i * w j) < 0 := by
    intro i
    have heq : (∑ j, coalescedPathBlock m j i * w j) =
        -(f i) + f i * (∑ j, w j) := by
      simp only [coalescedPathBlock, f, add_mul, neg_mul,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
      have hsym : (∑ j, pathH d j i * w j) = f i := by
        calc
          (∑ j, pathH d j i * w j) =
              ∑ j, pathH d i j * w j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [pathH_symmetric d j i]
          _ = f i := hHw' i
      rw [hsym, ← Finset.mul_sum]
    rw [heq, hmass]
    have hprod := mul_lt_mul_of_pos_left hG (hf i)
    nlinarith
  have hcert := explicit_diagonal_lyapunov_of_two_metzler_certificates
    (coalescedPathBlock m) z w hz hw
    (fun i j hij =>
      le_of_lt (coalescedPath_block_offdiag_pos m i j hij))
    (coalescedPathBlock_negative_vector m) hleft
  exact hcert

end

end PhosphorylationStableCapacity
