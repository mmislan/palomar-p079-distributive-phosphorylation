module
public import proofs.PhosphorylationStableCapacity.FinitePrefixDiagonalLyapunov435
public import proofs.PhosphorylationStableCapacity.PositiveDefiniteLyapunovHurwitz

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- A fixed diagonal Lyapunov matrix remains a certificate after arbitrary
independent positive column scaling, with the scaled Lyapunov matrix
`Ω P`. -/
theorem diagonal_lyapunov_all_positive_currents
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (p ω : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hω : ∀ i, 0 < ω i)
    (hQ : (-((A.transpose * Matrix.diagonal p) +
      Matrix.diagonal p * A)).PosDef) :
    let Ω := Matrix.diagonal ω
    let Pω := Ω * Matrix.diagonal p
    Pω.PosDef ∧
      (-((A * Ω).transpose * Pω + Pω * (A * Ω))).PosDef ∧
      IsHurwitz (A * Ω) := by
  intro Ω Pω
  let Q := -(A.transpose * Matrix.diagonal p + Matrix.diagonal p * A)
  have hPωEq : Pω = Matrix.diagonal (fun i => ω i * p i) := by
    ext i j
    simp [Pω, Ω, Matrix.diagonal_mul_diagonal]
  have hPω : Pω.PosDef := by
    rw [hPωEq]
    exact Matrix.posDef_diagonal_iff.mpr (fun i => mul_pos (hω i) (hp i))
  have hΩpos : Ω.PosDef := Matrix.posDef_diagonal_iff.mpr hω
  have hQω : (Ω * Q * Ω).PosDef := by
    have h := hQ.conjTranspose_mul_mul_same hΩpos.mulVec_injective
    change (Ω.conjTranspose * Q * Ω).PosDef at h
    rw [hΩpos.isHermitian] at h
    exact h
  have hEq :
      -((A * Ω).transpose * Pω + Pω * (A * Ω)) = Ω * Q * Ω := by
    ext i j
    rw [hPωEq]
    simp only [Matrix.neg_apply, Matrix.add_apply,
      Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.transpose_apply, Ω, Q]
    ring
  refine ⟨hPω, ?_, ?_⟩
  · rw [hEq]
    exact hQω
  · apply hurwitz_of_posDef_lyapunov
      (A * Ω) Pω (Ω * Q * Ω) hPω hQω
    rw [← hEq]
    simp

/-- For the actual finite-rate coalesced prefix, the manuscript's
single fixed `P` certifies every positive current vector after one
large-`r` threshold. -/
theorem coalescedPrefixEdgeActionMatrix_eventually_diagonal_all_currents
    (m : ℕ) :
    let d := coalescedPathWeights m
    let f := coalescedPathEdgeFeedback m
    let z := pathVectorFin d
    let w := (pathH d)⁻¹.mulVec f
    let p : Fin (m+1) → ℝ := fun i => w i / z i
    ∀ᶠ r : ℝ in Filter.atTop,
      ∀ (ω : Fin (m+1) → ℝ), (∀ i, 0 < ω i) →
        let Ω := Matrix.diagonal ω
        let Pω := Ω * Matrix.diagonal p
        Pω.PosDef ∧
          (-((coalescedPrefixEdgeActionMatrix m r * Ω).transpose * Pω +
            Pω * (coalescedPrefixEdgeActionMatrix m r * Ω))).PosDef ∧
          IsHurwitz (coalescedPrefixEdgeActionMatrix m r * Ω) := by
  intro d f z w p
  filter_upwards [coalescedPrefixEdgeActionMatrix_eventually_fixed_diagonal_lyapunov m]
    with r hr
  intro ω hω
  have hp : ∀ i, 0 < p i :=
    Matrix.posDef_diagonal_iff.mp hr.1
  exact diagonal_lyapunov_all_positive_currents
    (coalescedPrefixEdgeActionMatrix m r) p ω hp hω hr.2

end

end PhosphorylationStableCapacity
