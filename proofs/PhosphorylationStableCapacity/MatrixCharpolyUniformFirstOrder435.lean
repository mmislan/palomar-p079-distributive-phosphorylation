module
public import proofs.PhosphorylationStableCapacity.MatrixCharpolyCompactLipschitz435
public import proofs.PhosphorylationStableCapacity.FiniteMatrixCurrentBound435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter Matrix
open scoped Topology Matrix.Norms.Elementwise

/-- A continuous finite matrix family has one norm bound on a compact
parameter set, including the empty-set case. -/
theorem compact_matrix_norm_upper
    {α ι : Type*} [TopologicalSpace α]
    [Fintype ι] [DecidableEq ι]
    (K : Set α) (hK : IsCompact K)
    (F : α → Matrix ι ι ℝ) (hF : ContinuousOn F K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ a ∈ K, ‖F a‖ ≤ R := by
  by_cases hnon : K.Nonempty
  · have hnorm : ContinuousOn (fun a => ‖F a‖) K :=
      continuous_norm.comp_continuousOn hF
    obtain ⟨a₀, ha₀, hmax⟩ :=
      hK.exists_isMaxOn hnon hnorm
    refine ⟨‖F a₀‖, norm_nonneg _, ?_⟩
    intro a ha
    exact hmax ha
  · refine ⟨0, le_refl _, ?_⟩
    intro a ha
    exact (hnon ⟨a, ha⟩).elim

/-- Upgrade the entrywise current-factor estimate to the finite matrix
norm used by the compact characteristic-coefficient argument. -/
theorem finite_matrix_left_factor_norm_first_order_bound
    {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Set α) (W : α → Matrix ι ι ℝ)
    (B : ℝ → Matrix ι ι ℝ)
    (M C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hW : ∀ a ∈ K, ∀ i j, |W a i j| ≤ M)
    (hB : ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ i j, |B δ i j-B 0 i j| ≤ C*|δ|) :
    ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ a ∈ K,
        ‖W a * B δ-W a * B 0‖ ≤
          (Fintype.card ι : ℝ)*M*C*|δ| := by
  have hentry := finite_matrix_left_factor_first_order_bound
    K W B M C hM hC hW hB
  filter_upwards [hentry] with δ hδ a ha
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  simpa only [Real.norm_eq_abs, Matrix.sub_apply] using hδ a ha i j

/-- A uniform first-order bound on a compact family of actual finite
matrices transfers to every characteristic-polynomial coefficient.
The bound uses a common matrix ball, so its constant is independent
of the current parameter. -/
theorem matrix_charpoly_coeff_uniform_of_matrix_first_order
    {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Set α) (F : α → ℝ → Matrix ι ι ℝ)
    (R₀ D : ℝ) (hR₀ : 0 ≤ R₀) (hD : 0 ≤ D)
    (hcenter : ∀ a ∈ K, ‖F a 0‖ ≤ R₀)
    (hfirst : ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ a ∈ K, ‖F a δ - F a 0‖ ≤ D*|δ|)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ δ : ℝ in 𝓝 0,
        ∀ a ∈ K,
          |(F a δ).charpoly.coeff k -
            (F a 0).charpoly.coeff k| ≤ C*|δ| := by
  let R := R₀ + D + 1
  have hR : 0 ≤ R := by dsimp [R]; linarith
  obtain ⟨L, hLip⟩ :=
    matrix_charpoly_coeff_lipschitzOn_closedBall (ι := ι) k R
  let C : ℝ := (L : ℝ)*D + 1
  have hC : 0 < C := by
    dsimp [C]
    have hL : 0 ≤ (L : ℝ) := L.coe_nonneg
    positivity
  refine ⟨C, hC, ?_⟩
  have hsmall : ∀ᶠ δ : ℝ in 𝓝 0, |δ| ≤ 1 := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1)] with δ hδ
    exact (abs_lt.mpr hδ).le
  filter_upwards [hfirst, hsmall] with δ hδ hδsmall a ha
  have hnormδ : ‖F a δ‖ ≤ R := by
    have ht : ‖F a δ‖ ≤ ‖F a 0‖ + ‖F a δ-F a 0‖ := by
      calc
        _ = ‖(F a δ-F a 0) + F a 0‖ := by rw [sub_add_cancel]
        _ ≤ ‖F a δ-F a 0‖ + ‖F a 0‖ := norm_add_le _ _
        _ = _ := add_comm _ _
    have hvar := hδ a ha
    have hmul : D*|δ| ≤ D := by nlinarith [mul_le_mul_of_nonneg_left hδsmall hD]
    dsimp [R]
    linarith [hcenter a ha]
  have hnorm0 : ‖F a 0‖ ≤ R := by
    dsimp [R]
    linarith [hcenter a ha]
  have hmemδ : F a δ ∈ Metric.closedBall (0 : Matrix ι ι ℝ) R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hnormδ
  have hmem0 : F a 0 ∈ Metric.closedBall (0 : Matrix ι ι ℝ) R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm0
  have hlip := hLip.dist_le_mul (F a δ) hmemδ (F a 0) hmem0
  have hcoef : |(F a δ).charpoly.coeff k -
      (F a 0).charpoly.coeff k| ≤ (L : ℝ)*‖F a δ-F a 0‖ := by
    simpa [Real.dist_eq, dist_eq_norm] using hlip
  calc
    _ ≤ (L : ℝ)*‖F a δ-F a 0‖ := hcoef
    _ ≤ (L : ℝ)*(D*|δ|) :=
      mul_le_mul_of_nonneg_left (hδ a ha) L.coe_nonneg
    _ ≤ C*|δ| := by
      dsimp [C]
      nlinarith [abs_nonneg δ]

/-- Compact current parameters, a continuous current factor, and a
first-order fixed-current matrix family give one coefficient bound
throughout the compact family. -/
theorem compact_left_factor_charpoly_coeff_first_order
    {α ι : Type*} [TopologicalSpace α]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (K : Set α) (hK : IsCompact K)
    (W : α → Matrix ι ι ℝ)
    (B : ℝ → Matrix ι ι ℝ)
    (hW : ContinuousOn W K)
    (hcenter : ContinuousOn (fun a => W a * B 0) K)
    (hB : DifferentiableAt ℝ B 0)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ δ : ℝ in 𝓝 0,
        ∀ a ∈ K,
          |(W a * B δ).charpoly.coeff k -
            (W a * B 0).charpoly.coeff k| ≤ C*|δ| := by
  obtain ⟨M, hM, hMbound⟩ :=
    compact_matrix_entry_abs_upper K hK W hW
  obtain ⟨C₀, hC₀, hC₀bound⟩ :=
    finite_matrix_entry_first_order_bound B hB
  obtain ⟨R₀, hR₀, hR₀bound⟩ :=
    compact_matrix_norm_upper K hK (fun a => W a * B 0) hcenter
  have hvar := finite_matrix_left_factor_norm_first_order_bound
    K W B M C₀ hM.le hC₀.le hMbound hC₀bound
  exact matrix_charpoly_coeff_uniform_of_matrix_first_order
    K (fun a δ => W a * B δ) R₀
    ((Fintype.card ι : ℝ)*M*C₀) hR₀ (by positivity)
    hR₀bound hvar k

end

end PhosphorylationStableCapacity
