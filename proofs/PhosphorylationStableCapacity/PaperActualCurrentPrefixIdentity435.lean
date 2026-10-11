module
public import proofs.PhosphorylationStableCapacity.LoadedPrefixIndependentCurrents435
public import proofs.PhosphorylationStableCapacity.FinitePrefixDiagonalCurrentLyapunov435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix Filter

/-- The paper's actual coalesced prefix currents are `ωᵢ=γᵢYᵢ(0)`.
With edge factors `γᵢ=ωᵢ/Yᵢ(0)`, the literal loaded slow prefix
is a positive diagonal conjugate of the printed finite `A_r Ω`, with
one positive time factor `1/r`. This identifies the matrix in the
diagonal Lyapunov proposition without changing its fixed `P`. -/
theorem coalescedPrefixLoadedMatrix_actualCurrent_factor
    (m : ℕ) (r : ℝ) (hr : r ≠ 0)
    (hstate : (coalescedFiniteState (m+1) r).Positive)
    (ω : Fin (m+1) → ℝ) :
    let D : Fin (m+1) → ℝ := fun i =>
      (coalescedFiniteState (m+1) r).D i.castSucc
    coalescedPrefixLoadedMatrix m r *
      Matrix.diagonal (fun i => ω i / D i) =
        Matrix.diagonal D *
          (coalescedPrefixEdgeActionMatrix m r * Matrix.diagonal ω) *
            Matrix.diagonal (fun i => 1/(r*D i)) := by
  intro D
  rw [coalescedPrefixLoadedMatrix_eq_row_scaled_edge_action m r hr]
  ext i j
  have hDi : D i ≠ 0 := ne_of_gt (hstate.2.2.2.2 i.castSucc)
  have hDj : D j ≠ 0 := ne_of_gt (hstate.2.2.2.2 j.castSucc)
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, D]
  field_simp [hr, hDi, hDj]

/-- For the literal actual-current normalization, the diagonal
certificate induced on loaded coordinates is explicit. The fixed
`p_i=(H⁻¹φ)_i/(H⁻¹1)_i` remains the same one in the manuscript. -/
theorem coalescedPrefixLoadedMatrix_actualCurrent_lyapunov
    (m : ℕ) :
    let d := coalescedPathWeights m
    let f := coalescedPathEdgeFeedback m
    let z := pathVectorFin d
    let w := (pathH d)⁻¹.mulVec f
    let p : Fin (m+1) → ℝ := fun i => w i / z i
    ∀ᶠ r : ℝ in atTop,
      ∀ (ω : Fin (m+1) → ℝ), (∀ i, 0 < ω i) →
        let D : Fin (m+1) → ℝ := fun i =>
          (coalescedFiniteState (m+1) r).D i.castSucc
        let θ : Fin (m+1) → ℝ := fun i => ω i / D i
        let W := Matrix.diagonal (fun i => r*ω i*p i/(D i)^2)
        W.PosDef ∧
          (-(((coalescedPrefixLoadedMatrix m r * Matrix.diagonal θ).transpose * W) +
            W * (coalescedPrefixLoadedMatrix m r * Matrix.diagonal θ))).PosDef ∧
          IsHurwitz (coalescedPrefixLoadedMatrix m r * Matrix.diagonal θ) := by
  intro d f z w p
  filter_upwards [coalescedPrefixLoadedMatrix_eventually_diagonal_all_currents m,
    coalescedFiniteState_eventually_equilibrium (m+1),
    eventually_gt_atTop (0 : ℝ)] with r hlyap hsource hr
  intro ω hω D θ W
  have hD : ∀ i : Fin (m+1), 0 < D i := by
    intro i
    exact hsource.2.1.2.2.2.2 i.castSucc
  have hθ : ∀ i : Fin (m+1), 0 < θ i := by
    intro i
    exact div_pos (hω i) (hD i)
  have h := hlyap θ hθ
  have hW : Matrix.diagonal (fun i : Fin (m+1) =>
      θ i * p i / (D i/r)) = W := by
    ext i j
    dsimp only [W]
    simp only [Matrix.diagonal_apply]
    split_ifs with hij
    · subst j
      change (ω i / D i) * p i / (D i / r) =
        r * ω i * p i / (D i)^2
      have hDi : D i ≠ 0 := ne_of_gt (hD i)
      have hr0 : r ≠ 0 := ne_of_gt hr
      field_simp [hDi, hr0]
    · rfl
  dsimp only at h
  rw [hW] at h
  exact h

end

end PhosphorylationStableCapacity
