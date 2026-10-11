module
public import proofs.PhosphorylationStableCapacity.FastSlowSpectralLimit

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter Topology
open Matrix
open scoped Matrix.Norms.L2Operator

/-- The spectral Schur matrix depends continuously on the product `εz`
near zero, with the ordinary Schur matrix as its limit. -/
theorem fastSlowSpectralSchur_mu_tendsto_zero
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0) :
    Tendsto (fun μ : ℂ => A + B * (fastSlowResolventMatrix D μ 1)⁻¹ * C)
      (nhds 0) (nhds (A - B * D⁻¹ * C)) := by
  have hR : Continuous (fun μ : ℂ => fastSlowResolventMatrix D μ 1) := by
    apply continuous_matrix
    intro i j
    simp only [fastSlowResolventMatrix, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul]
    fun_prop
  have hunit : IsUnit (-D).det := by
    simpa [fastSlowResolventMatrix] using
      (fastSlowResolventMatrix_isUnit_det_of_hurwitz D hD
        (show (0 : ℝ) < 1 by norm_num) 0 (le_refl 0))
  have hInv : ContinuousAt (Inv.inv : Matrix f f ℂ → Matrix f f ℂ) (-D) :=
    continuousAt_matrix_inv (-D) (by
      simpa using (continuousAt_inv₀ hunit.ne_zero))
  have hRlim : Tendsto (fun μ : ℂ => fastSlowResolventMatrix D μ 1)
      (nhds 0) (nhds (-D)) := by
    simpa [fastSlowResolventMatrix] using (hR.tendsto 0)
  have hInvlim : Tendsto (fun μ : ℂ => (fastSlowResolventMatrix D μ 1)⁻¹)
      (nhds 0) (nhds (-D)⁻¹) := hInv.tendsto.comp hRlim
  have hA : Continuous (fun _ : Matrix f f ℂ => A) := continuous_const
  have hB : Continuous (fun _ : Matrix f f ℂ => B) := continuous_const
  have hM : Continuous (fun M : Matrix f f ℂ => M) := continuous_id
  have hC : Continuous (fun _ : Matrix f f ℂ => C) := continuous_const
  have hMap : Continuous (fun M : Matrix f f ℂ => A + B * M * C) :=
    hA.add ((hB.matrix_mul hM).matrix_mul hC)
  rw [← fastSlowSchur_limit_eq A B C D]
  exact hMap.continuousAt.tendsto.comp hInvlim

/-- The spectral Schur matrices are uniformly norm bounded whenever
the product `εz` lies sufficiently near zero. -/
theorem fastSlowSpectralSchur_mu_eventually_norm_lt
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0) :
    ∀ᶠ μ : ℂ in nhds 0,
      ‖A + B * (fastSlowResolventMatrix D μ 1)⁻¹ * C‖ <
        ‖A - B * D⁻¹ * C‖ + 1 := by
  let S := A - B * D⁻¹ * C
  let M := fun μ : ℂ => A + B * (fastSlowResolventMatrix D μ 1)⁻¹ * C
  have hM : Tendsto M (nhds 0) (nhds S) :=
    fastSlowSpectralSchur_mu_tendsto_zero A B C D hD
  have hball : ∀ᶠ μ : ℂ in nhds 0, M μ ∈ Metric.ball S 1 :=
    hM.eventually (Metric.ball_mem_nhds S (by norm_num))
  filter_upwards [hball] with μ hμ
  have hdist : ‖M μ - S‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hμ
  calc
    ‖M μ‖ = ‖(M μ - S) + S‖ := by simp
    _ ≤ ‖M μ - S‖ + ‖S‖ := norm_add_le _ _
    _ < ‖S‖ + 1 := by linarith

theorem matrix_spectrum_norm_le_norm
    {s : Type*} [Fintype s] [DecidableEq s] [Nonempty s]
    (M : Matrix s s ℂ) (z : ℂ) (hz : z ∈ spectrum ℂ M) :
    ‖z‖ ≤ ‖M‖ :=
  spectrum.norm_le_norm_of_mem hz

set_option maxHeartbeats 500000

/-- Every full fast/slow eigenvalue in the closed right half-plane is
uniformly bounded as the positive time scale tends to zero. -/
theorem fastSlow_nonnegative_eigen_eventually_bounded
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f] [Nonempty s]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0) :
    ∀ᶠ ε : ℝ in nhds 0, ∀ z : ℂ, ∀ v : s ⊕ f → ℂ,
      0 < ε → 0 ≤ z.re → v ≠ 0 →
      fastSlowMatrix A B C D (ε : ℂ) *ᵥ v = z • v →
      ‖z‖ < ‖A - B * D⁻¹ * C‖ + 1 := by
  have hU : {μ : ℂ |
      ‖A + B * (fastSlowResolventMatrix D μ 1)⁻¹ * C‖ <
        ‖A - B * D⁻¹ * C‖ + 1} ∈ 𝓝 (0 : ℂ) :=
    fastSlowSpectralSchur_mu_eventually_norm_lt A B C D hD
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hscaled :=
    fastSlowScaledMatrix_eventually_spectrum_near_zero_or_left A B C D hD hδ
  have hreal : Tendsto (fun ε : ℝ => (ε : ℂ)) (nhds 0) (nhds 0) := by
    simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
  filter_upwards [hreal.eventually hscaled] with ε hε z v hεpos hzre hv0 hv
  have hεc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hεpos)
  have hscaledEig : fastSlowScaledMatrix A B C D (ε : ℂ) *ᵥ v =
      ((ε : ℂ) * z) • v := by
    rw [fastSlowScaledMatrix_eq_smul_fastSlowMatrix A B C D hεc,
      Matrix.smul_mulVec, hv, smul_smul]
  have hscaledMem : (ε : ℂ) * z ∈
      spectrum ℂ (fastSlowScaledMatrix A B C D (ε : ℂ)) :=
    matrix_mem_spectrum_of_mulVec_eq_smul _ _ _ hv0 hscaledEig
  have hμre : 0 ≤ ((ε : ℂ) * z).re := by
    simpa using mul_nonneg (le_of_lt hεpos) hzre
  have hμball : (ε : ℂ) * z ∈ Metric.ball 0 δ :=
    (hε _ hscaledMem).resolve_left (not_lt_of_ge hμre)
  have hschurMem := fastSlowMatrix_nonnegative_eigen_schur_spectrum
    A B C D hD hεpos z hzre v hv0 hv
  have hEq : fastSlowResolventMatrix D (ε : ℂ) z =
      fastSlowResolventMatrix D ((ε : ℂ) * z) 1 := by
    simp [fastSlowResolventMatrix]
  have hschurNorm :
      ‖A + B * (fastSlowResolventMatrix D (ε : ℂ) z)⁻¹ * C‖ <
        ‖A - B * D⁻¹ * C‖ + 1 := by
    rw [hEq]
    exact hball hμball
  have hnorm : ‖z‖ ≤
      ‖A + B * (fastSlowResolventMatrix D (ε : ℂ) z)⁻¹ * C‖ :=
    matrix_spectrum_norm_le_norm _ z hschurMem
  exact hnorm.trans_lt hschurNorm

end
end PhosphorylationStableCapacity
