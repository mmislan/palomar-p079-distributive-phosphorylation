module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingJacobianPositiveProbes435
public import proofs.PhosphorylationStableCapacity.FiniteMatrixProbeFirstOrder435
public import proofs.PhosphorylationStableCapacity.CompactAffineProbeFirstOrder435
public import proofs.PhosphorylationStableCapacity.CompactFiniteScalarBound435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Matrix
open scoped Topology Matrix.Norms.Elementwise

/-- The literal frozen-binding full Jacobian has a first-order bound
uniform over a compact positive edge-current family. The only analytic
input is first-order regularity at finitely many positive probes;
source-parameter positivity is required only on one signed tube. -/
theorem paperFixedBinding_compact_loadedJacobian_first_order
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
          (u δ)) 0) :
    ∃ D : ℝ, 0 < D ∧
      ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), ∀ w ∈ K,
        ‖loadedJacobianMatrix ET FT ST
          (relaxRates (paperFixedBindingRates (edgeScaledRates w (k δ))) ε)
          (u δ) -
         loadedJacobianMatrix ET FT ST
          (relaxRates (paperFixedBindingRates (edgeScaledRates w (k 0))) ε)
          (u 0)‖ ≤ D * |δ| := by
  classical
  let F : (Fin n → ℝ) → ℝ →
      Matrix (Fin n ⊕ (Fin n ⊕ Fin n))
        (Fin n ⊕ (Fin n ⊕ Fin n)) ℝ := fun w δ =>
    loadedJacobianMatrix ET FT ST
      (relaxRates (paperFixedBindingRates (edgeScaledRates w (k δ))) ε)
      (u δ)
  let probe : Option (Fin n) → Fin n → ℝ :=
    fun p => match p with
      | none => fun _ => 1
      | some i => paperPositiveCurrentProbe i
  have hprobePos (p : Option (Fin n)) : ∀ i, 0 < probe p i := by
    cases p with
    | none => intro i; norm_num [probe]
    | some j => exact paperPositiveCurrentProbe_pos j
  obtain ⟨C, hC, hprobeRaw⟩ := finite_matrix_probe_uniform_first_order
    (fun p δ => F (probe p) δ)
    (fun p => hdiff (probe p) (hprobePos p))
  have hprobe : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ),
      ‖F (fun _ => 1) δ - F (fun _ => 1) 0‖ ≤ C * |δ| ∧
      ∀ i : Fin n,
        ‖F (fun j => if j = i then 2 else 1) δ -
          F (fun j => if j = i then 2 else 1) 0‖ ≤ C * |δ| := by
    filter_upwards [hprobeRaw] with δ hδ
    exact ⟨hδ none, fun i => hδ (some i)⟩
  obtain ⟨M, hM, hMbound⟩ := compact_finite_scalar_abs_upper
    K hK (fun i w => w i - 1)
      (fun i => ((continuous_apply i).sub continuous_const).continuousOn)
  have haffine : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), ∀ w ∈ K,
      F w δ = F (fun _ => 1) δ +
        ∑ i : Fin n, (w i - 1) •
          (F (fun j => if j = i then 2 else 1) δ -
            F (fun _ => 1) δ) := by
    filter_upwards [hposev] with δ hδ w hw
    exact paperFixedBinding_loadedJacobian_all_positive_probes
      ET FT ST (k δ) ε hδ w (hKpos w hw) (u δ)
  have haffine0 : ∀ w ∈ K,
      F w 0 = F (fun _ => 1) 0 +
        ∑ i : Fin n, (w i - 1) •
          (F (fun j => if j = i then 2 else 1) 0 -
            F (fun _ => 1) 0) := by
    intro w hw
    exact paperFixedBinding_loadedJacobian_all_positive_probes
      ET FT ST (k 0) ε hpos0 w (hKpos w hw) (u 0)
  let D := C + (Fintype.card (Fin n) : ℝ) * M * (2 * C)
  have hD : 0 < D := by
    dsimp [D]
    positivity
  refine ⟨D, hD, ?_⟩
  simpa only [F, D] using
    affine_positive_probe_uniform_first_order
      K F C M hC.le hM.le hMbound
      haffine haffine0 hprobe

end

end PhosphorylationStableCapacity
