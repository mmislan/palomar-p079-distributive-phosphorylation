module
public import proofs.PhosphorylationStableCapacity.CoalescedExplicitDiagonalLyapunov435
public import proofs.PhosphorylationStableCapacity.CoalescedPrefixEdgeBlockLimit

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter
open scoped Topology

noncomputable section

/-- The manuscript's fixed diagonal `P` for the coalesced limit remains a
strict Lyapunov matrix for the actual normalized finite-rate prefix `A_r`
once the source parameter is sufficiently large. -/
theorem coalescedPrefixEdgeActionMatrix_eventually_fixed_diagonal_lyapunov
    (m : ℕ) :
    let d := coalescedPathWeights m
    let f := coalescedPathEdgeFeedback m
    let z := pathVectorFin d
    let w := (pathH d)⁻¹.mulVec f
    let P := Matrix.diagonal (fun i : Fin (m+1) => w i / z i)
    ∀ᶠ r : ℝ in atTop,
      P.PosDef ∧
        (-((coalescedPrefixEdgeActionMatrix m r).transpose * P +
          P * coalescedPrefixEdgeActionMatrix m r)).PosDef := by
  intro d f z w P
  let B := coalescedPathBlock m
  let A := coalescedPrefixEdgeActionMatrix m
  let Q : ℝ → Matrix (Fin (m+1)) (Fin (m+1)) ℝ :=
    fun r => (A r).transpose * P + P * A r
  let Q₀ : Matrix (Fin (m+1)) (Fin (m+1)) ℝ :=
    B.transpose * P + P * B
  have hlim := coalescedPathBlock_explicit_diagonal_lyapunov m
  have hP : P.PosDef := hlim.1
  have hz : ∀ i, 0 < z i :=
    pathVectorFin_pos d (coalescedPathWeights_pos m)
  have hp : ∀ i, 0 < w i / z i := by
    intro i
    have hdiag := Matrix.posDef_diagonal_iff.mp hP i
    exact hdiag
  have hQentry : ∀ i j,
      Tendsto (fun r : ℝ => Q r i j) atTop (𝓝 (Q₀ i j)) := by
    intro i j
    have h1 := coalescedPrefixEdgeActionMatrix_tendsto m j i
    have h2 := coalescedPrefixEdgeActionMatrix_tendsto m i j
    have h := (h1.mul (tendsto_const_nhds (x := w j / z j))).add
      ((tendsto_const_nhds (x := w i / z i)).mul h2)
    simpa only [Q, Q₀, A, B, P, Matrix.add_apply,
      Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.transpose_apply] using h
  have hQoff : ∀ i j, i ≠ j → 0 < Q₀ i j := by
    intro i j hij
    simp only [Q₀, P, Matrix.add_apply, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Matrix.transpose_apply]
    exact add_pos
      (mul_pos (coalescedPath_block_offdiag_pos m j i (Ne.symm hij))
        (hp j))
      (mul_pos (hp i) (coalescedPath_block_offdiag_pos m i j hij))
  have hQneg : ∀ i, (∑ j, Q₀ i j * z j) < 0 := hlim.2.2
  have hOffEventually : ∀ᶠ r : ℝ in atTop,
      ∀ i j, i ≠ j → 0 ≤ Q r i j := by
    suffices h : ∀ᶠ r : ℝ in atTop,
        ∀ i ∈ (Finset.univ : Finset (Fin (m+1))),
          ∀ j ∈ (Finset.univ : Finset (Fin (m+1))),
            i ≠ j → 0 ≤ Q r i j by
      simpa using h
    apply (Filter.eventually_all_finset (Finset.univ :
      Finset (Fin (m+1)))).2
    intro i _
    apply (Filter.eventually_all_finset (Finset.univ :
      Finset (Fin (m+1)))).2
    intro j _
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hij))
    · exact ((hQentry i j).eventually
        (isOpen_Ioi.mem_nhds (hQoff i j hij))).mono
          (fun _ hp _ => hp.le)
  have hNegEventually : ∀ᶠ r : ℝ in atTop,
      ∀ i, (∑ j, Q r i j * z j) < 0 := by
    suffices h : ∀ᶠ r : ℝ in atTop,
        ∀ i ∈ (Finset.univ : Finset (Fin (m+1))),
          (∑ j, Q r i j * z j) < 0 by
      simpa using h
    apply (Filter.eventually_all_finset (Finset.univ :
      Finset (Fin (m+1)))).2
    intro i _
    have hrow : Tendsto (fun r : ℝ => ∑ j, Q r i j * z j) atTop
        (𝓝 (∑ j, Q₀ i j * z j)) := by
      apply tendsto_finsetSum
      intro j _
      exact (hQentry i j).mul tendsto_const_nhds
    exact hrow.eventually (isOpen_Iio.mem_nhds (hQneg i))
  filter_upwards [hOffEventually, hNegEventually] with r hOff hNeg
  refine ⟨hP, ?_⟩
  refine symmetric_metzler_neg_posDef (Q r) ?_ hOff z hz hNeg
  intro i j
  simp only [Q, Matrix.add_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.transpose_apply, P]
  ring

end

end PhosphorylationStableCapacity
