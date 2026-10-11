module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCompactJacobianFirstOrder435
public import proofs.PhosphorylationStableCapacity.MatrixCharpolyUniformFirstOrder435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Matrix Polynomial
open scoped Topology Matrix.Norms.Elementwise

/-- The coalesced full loaded Jacobian is continuous in positive edge
currents because its positive-probe formula is affine. -/
theorem paperFixedBinding_center_loadedJacobian_continuousOn
    {n : ℕ} (ET FT ST ε : ℝ) (k : Rates n)
    (u : CoordinateSpace n)
    (K : Set (Fin n → ℝ))
    (hKpos : ∀ w ∈ K, ∀ i, 0 < w i)
    (hk : k.Positive) :
    ContinuousOn (fun w => loadedJacobianMatrix ET FT ST
      (relaxRates (paperFixedBindingRates (edgeScaledRates w k)) ε) u) K := by
  classical
  let F : (Fin n → ℝ) →
      Matrix (Fin n ⊕ (Fin n ⊕ Fin n))
        (Fin n ⊕ (Fin n ⊕ Fin n)) ℝ := fun w =>
    loadedJacobianMatrix ET FT ST
      (relaxRates (paperFixedBindingRates (edgeScaledRates w k)) ε) u
  have hcontinuous : Continuous (fun w : Fin n → ℝ =>
      F (fun _ => 1) +
        ∑ i : Fin n, (w i - 1) •
          (F (paperPositiveCurrentProbe i) - F (fun _ => 1))) := by
    have hsum : Continuous (fun w : Fin n → ℝ =>
        ∑ i : Fin n, (w i - 1) •
          (F (paperPositiveCurrentProbe i) - F (fun _ => 1))) := by
      apply continuous_finsetSum
      intro i hi
      exact ((continuous_apply i).sub continuous_const).smul
        continuous_const
    exact continuous_const.add hsum
  apply hcontinuous.continuousOn.congr
  intro w hw
  exact (paperFixedBinding_loadedJacobian_all_positive_probes
    ET FT ST k ε hk w (hKpos w hw) u)

/-- Every characteristic coefficient of the *actual fixed-binding*
loaded class Jacobian has one compact-current first-order bound. The
probe theorem supplies full-matrix control; compact continuity at the
coalesced slice supplies the common matrix ball. -/
theorem paperFixedBinding_compact_charpoly_coeff_first_order
    {n : ℕ} (ET FT ST ε : ℝ)
    (k : ℝ → Rates n) (u : ℝ → CoordinateSpace n)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    (hKpos : ∀ w ∈ K, ∀ i, 0 < w i)
    (hpos0 : (k 0).Positive)
    (hposev : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), (k δ).Positive)
    (hdiff : ∀ w : Fin n → ℝ, (∀ i, 0 < w i) →
      DifferentiableAt ℝ (fun δ =>
        loadedJacobianMatrix ET FT ST
          (relaxRates (paperFixedBindingRates (edgeScaledRates w (k δ))) ε)
          (u δ)) 0)
    (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), ∀ w ∈ K,
        |(loadedJacobianMatrix ET FT ST
          (relaxRates (paperFixedBindingRates (edgeScaledRates w (k δ))) ε)
          (u δ)).charpoly.coeff q -
         (loadedJacobianMatrix ET FT ST
          (relaxRates (paperFixedBindingRates (edgeScaledRates w (k 0))) ε)
          (u 0)).charpoly.coeff q| ≤ C * |δ| := by
  classical
  let F : (Fin n → ℝ) → ℝ →
      Matrix (Fin n ⊕ (Fin n ⊕ Fin n))
        (Fin n ⊕ (Fin n ⊕ Fin n)) ℝ := fun w δ =>
    loadedJacobianMatrix ET FT ST
      (relaxRates (paperFixedBindingRates (edgeScaledRates w (k δ))) ε)
      (u δ)
  obtain ⟨D, hD, hfirst⟩ :=
    paperFixedBinding_compact_loadedJacobian_first_order
      ET FT ST ε k u K hK hKpos hpos0 hposev hdiff
  have hcenter : ContinuousOn (fun w => F w 0) K := by
    exact paperFixedBinding_center_loadedJacobian_continuousOn
      ET FT ST ε (k 0) (u 0) K hKpos hpos0
  obtain ⟨R, hR, hRbound⟩ :=
    compact_matrix_norm_upper K hK (fun w => F w 0) hcenter
  exact matrix_charpoly_coeff_uniform_of_matrix_first_order
    K F R D hR hD.le hRbound hfirst q

end

end PhosphorylationStableCapacity
