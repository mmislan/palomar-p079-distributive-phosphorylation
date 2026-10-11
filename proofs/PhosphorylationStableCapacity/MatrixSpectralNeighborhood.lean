module
public import proofs.PhosphorylationStableCapacity.FastSlowSpectralTransfer

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter Matrix
open scoped Topology Matrix.Norms.L2Operator

/-- A finite complex matrix whose spectrum is left of the imaginary axis
apart from zero keeps every perturbed spectral point either left or in any
prescribed neighborhood of zero. This is the first spectral-continuity
interface needed by the split-source attainment argument. -/
theorem matrix_spectrum_eventually_left_or_near_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ)
    (hA : ∀ z : ℂ, z ∈ spectrum ℂ A → z.re < 0 ∨ z = 0)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ M : Matrix ι ι ℂ in 𝓝 A,
      ∀ z : ℂ, z ∈ spectrum ℂ M → z.re < 0 ∨ ‖z‖ < η := by
  let U : Set ℂ := {z | z.re < 0} ∪ Metric.ball 0 η
  have hU : IsOpen U :=
    (isOpen_Iio.preimage Complex.continuous_re).union Metric.isOpen_ball
  have hsubset : spectrum ℂ A ⊆ U := by
    intro z hz
    rcases hA z hz with hzleft | rfl
    · exact Or.inl hzleft
    · exact Or.inr (Metric.mem_ball.mpr (by simpa using hη))
  have hnear := (upperHemicontinuous_spectrum ℂ (Matrix ι ι ℂ)).forall_isOpen
    A U hU hsubset
  filter_upwards [hnear] with M hM z hz
  rcases hM hz with hzleft | hzball
  · exact Or.inl hzleft
  · exact Or.inr (by simpa [Metric.mem_ball, dist_eq_norm] using hzball)

/-- Pull the spectral neighborhood result back along a matrix family
continuous at the coalesced parameter. -/
theorem matrix_family_spectrum_eventually_left_or_near_zero
    {α ι : Type*} [TopologicalSpace α]
    [Fintype ι] [DecidableEq ι]
    (J : α → Matrix ι ι ℂ) (a : α)
    (hJ : ContinuousAt J a)
    (hA : ∀ z : ℂ, z ∈ spectrum ℂ (J a) → z.re < 0 ∨ z = 0)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ b : α in 𝓝 a,
      ∀ z : ℂ, z ∈ spectrum ℂ (J b) → z.re < 0 ∨ ‖z‖ < η := by
  exact hJ.tendsto.eventually
    (matrix_spectrum_eventually_left_or_near_zero (J a) hA η hη)

end
end PhosphorylationStableCapacity
