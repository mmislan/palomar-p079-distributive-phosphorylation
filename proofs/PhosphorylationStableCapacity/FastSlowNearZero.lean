module
public import proofs.PhosphorylationStableCapacity.FastSlowBoundedness

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter Topology
open Matrix
open scoped Matrix.Norms.L2Operator

/-- Near zero product `μ=εz`, the spectral Schur equation has no
right-half-plane roots away from zero when its ordinary Schur limit has
no such roots. -/
theorem fastSlowSpectralSchur_mu_eventually_spectrum_near_zero_or_left
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0)
    (hS : ∀ w : ℂ, w ∈ spectrum ℂ (A - B * D⁻¹ * C) →
      w.re < 0 ∨ w = 0)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ μ : ℂ in nhds 0, ∀ z : ℂ,
      z ∈ spectrum ℂ
        (A + B * (fastSlowResolventMatrix D μ 1)⁻¹ * C) →
      z.re < 0 ∨ z ∈ Metric.ball 0 η := by
  let U : Set ℂ := {z | z.re < 0} ∪ Metric.ball 0 η
  have hUopen : IsOpen U :=
    (isOpen_Iio.preimage Complex.continuous_re).union Metric.isOpen_ball
  have hUlimit : U ∈ 𝓝ˢ (spectrum ℂ (A - B * D⁻¹ * C)) := by
    apply hUopen.mem_nhdsSet.mpr
    intro z hz
    rcases hS z hz with hleft | hzero
    · exact Or.inl hleft
    · subst z
      exact Or.inr (Metric.mem_ball_self hη)
  have hnear : ∀ᶠ M : Matrix s s ℂ in nhds (A - B * D⁻¹ * C),
      U ∈ 𝓝ˢ (spectrum ℂ M) :=
    (upperHemicontinuous_spectrum ℂ (Matrix s s ℂ)).upperHemicontinuousAt
      (A - B * D⁻¹ * C) U hUlimit
  filter_upwards
      [(fastSlowSpectralSchur_mu_tendsto_zero A B C D hD).eventually hnear]
    with μ hμ z hz
  exact (subset_of_mem_nhdsSet hμ) hz

/-- At sufficiently small positive binding time scale, every full
eigenvalue in the closed right half-plane lies in any prescribed ball
about zero. The conclusion is uniform over all eigenvalues. -/
theorem fastSlow_nonnegative_eigen_eventually_near_zero
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0)
    (hS : ∀ w : ℂ, w ∈ spectrum ℂ (A - B * D⁻¹ * C) →
      w.re < 0 ∨ w = 0)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε : ℝ in nhds 0, ∀ z : ℂ, ∀ v : s ⊕ f → ℂ,
      0 < ε → 0 ≤ z.re → v ≠ 0 →
      fastSlowMatrix A B C D (ε : ℂ) *ᵥ v = z • v →
      z ∈ Metric.ball 0 η := by
  have hU : {μ : ℂ | ∀ z : ℂ,
      z ∈ spectrum ℂ
        (A + B * (fastSlowResolventMatrix D μ 1)⁻¹ * C) →
      z.re < 0 ∨ z ∈ Metric.ball 0 η} ∈ 𝓝 (0 : ℂ) :=
    fastSlowSpectralSchur_mu_eventually_spectrum_near_zero_or_left
      A B C D hD hS hη
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
  have hnear := hball hμball z
  rw [← hEq] at hnear
  exact (hnear hschurMem).resolve_left (not_lt_of_ge hzre)

end
end PhosphorylationStableCapacity
