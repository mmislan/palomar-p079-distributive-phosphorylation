module
public import proofs.PhosphorylationStableCapacity.FinitePrefixDiagonalCurrentLyapunov435
public import proofs.PhosphorylationStableCapacity.CoalescedPrefixLoadedMatrix
public import proofs.PhosphorylationStableCapacity.CoalescedPrefixCurrentBlockLimit

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix Filter

/-- A strict diagonal Lyapunov certificate survives independent positive
row and column scalings. The new diagonal certificate is `ωᵢpᵢ/ℓᵢ`. -/
theorem two_sided_diagonal_scaling_lyapunov
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (p ℓ ω : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hℓ : ∀ i, 0 < ℓ i)
    (hω : ∀ i, 0 < ω i)
    (hQ : (-((A.transpose * Matrix.diagonal p) +
      Matrix.diagonal p * A)).PosDef) :
    let L := Matrix.diagonal ℓ
    let Ω := Matrix.diagonal ω
    let W := Matrix.diagonal (fun i => ω i * p i / ℓ i)
    W.PosDef ∧
      (-(((L * A * Ω).transpose * W) + W * (L * A * Ω))).PosDef ∧
      IsHurwitz (L * A * Ω) := by
  intro L Ω W
  let Q := -((A.transpose * Matrix.diagonal p) + Matrix.diagonal p * A)
  have hW : W.PosDef := by
    change (Matrix.diagonal (fun i => ω i * p i / ℓ i)).PosDef
    exact Matrix.posDef_diagonal_iff.mpr
      (fun i => div_pos (mul_pos (hω i) (hp i)) (hℓ i))
  have hΩpos : Ω.PosDef := Matrix.posDef_diagonal_iff.mpr hω
  have hQω : (Ω * Q * Ω).PosDef := by
    have h := hQ.conjTranspose_mul_mul_same hΩpos.mulVec_injective
    change (Ω.conjTranspose * Q * Ω).PosDef at h
    rw [hΩpos.isHermitian] at h
    exact h
  have hEq :
      -(((L * A * Ω).transpose * W) + W * (L * A * Ω)) =
        Ω * Q * Ω := by
    ext i j
    simp only [Matrix.neg_apply, Matrix.add_apply,
      Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.transpose_apply, L, Ω, W, Q]
    field_simp [ne_of_gt (hℓ i), ne_of_gt (hℓ j)]
  refine ⟨hW, ?_, ?_⟩
  · rw [hEq]
    exact hQω
  · apply hurwitz_of_posDef_lyapunov (L * A * Ω) W (Ω * Q * Ω)
      hW hQω
    rw [← hEq]
    simp

/-- Exact finite source identity: the loaded slow prefix is the
normalized edge-action matrix with a positive row scaling. -/
theorem coalescedPrefixLoadedMatrix_eq_row_scaled_edge_action
    (m : ℕ) (r : ℝ) (hr : r ≠ 0) :
    coalescedPrefixLoadedMatrix m r =
      Matrix.diagonal (fun i : Fin (m+1) =>
        (coalescedFiniteState (m+1) r).D i.castSucc / r) *
        coalescedPrefixEdgeActionMatrix m r := by
  ext i j
  have h := coalescedPrefixCurrentMatrix_eq_r_mul_loaded m r i j
  change (coalescedFiniteState (m+1) r).D i.castSucc *
      coalescedPrefixEdgeActionMatrix m r i j =
        r * coalescedPrefixLoadedMatrix m r i j at h
  simp only [Matrix.diagonal_mul]
  calc
    coalescedPrefixLoadedMatrix m r i j =
        ((coalescedFiniteState (m+1) r).D i.castSucc *
          coalescedPrefixEdgeActionMatrix m r i j) / r := by
      apply (eq_div_iff hr).2
      calc
        coalescedPrefixLoadedMatrix m r i j * r =
            r * coalescedPrefixLoadedMatrix m r i j := mul_comm _ _
        _ = _ := h.symm
    _ = _ := by ring

/-- One sufficiently large finite source parameter makes the actual
loaded slow prefix Hurwitz for every positive independent current vector.
The diagonal Lyapunov matrix is explicit and depends on the currents. -/
theorem coalescedPrefixLoadedMatrix_eventually_diagonal_all_currents
    (m : ℕ) :
    let d := coalescedPathWeights m
    let f := coalescedPathEdgeFeedback m
    let z := pathVectorFin d
    let w := (pathH d)⁻¹.mulVec f
    let p : Fin (m+1) → ℝ := fun i => w i / z i
    ∀ᶠ r : ℝ in atTop,
      ∀ (ω : Fin (m+1) → ℝ), (∀ i, 0 < ω i) →
        let ℓ : Fin (m+1) → ℝ := fun i =>
          (coalescedFiniteState (m+1) r).D i.castSucc / r
        let W := Matrix.diagonal (fun i => ω i * p i / ℓ i)
        W.PosDef ∧
          (-(((coalescedPrefixLoadedMatrix m r * Matrix.diagonal ω).transpose * W) +
            W * (coalescedPrefixLoadedMatrix m r * Matrix.diagonal ω))).PosDef ∧
          IsHurwitz (coalescedPrefixLoadedMatrix m r * Matrix.diagonal ω) := by
  intro d f z w p
  filter_upwards [coalescedPrefixEdgeActionMatrix_eventually_fixed_diagonal_lyapunov m,
    coalescedFiniteState_eventually_equilibrium (m+1),
    eventually_gt_atTop (0 : ℝ)] with r hlyap hsource hr
  intro ω hω ℓ W
  have hℓ : ∀ i : Fin (m+1), 0 < ℓ i := by
    intro i
    exact div_pos (hsource.2.1.2.2.2.2 i.castSucc) hr
  have hp : ∀ i : Fin (m+1), 0 < p i :=
    Matrix.posDef_diagonal_iff.mp hlyap.1
  have h := two_sided_diagonal_scaling_lyapunov
    (coalescedPrefixEdgeActionMatrix m r) p ℓ ω hp hℓ hω hlyap.2
  dsimp only at h
  have hL : Matrix.diagonal ℓ * coalescedPrefixEdgeActionMatrix m r =
      coalescedPrefixLoadedMatrix m r :=
    (coalescedPrefixLoadedMatrix_eq_row_scaled_edge_action m r hr.ne').symm
  rw [hL] at h
  exact h

end

end PhosphorylationStableCapacity
