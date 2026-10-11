module
public import proofs.PhosphorylationStableCapacity.FastSlowEigenElimination

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter Topology
open Matrix
open scoped Matrix.Norms.L2Operator

/-- Eigenvalues of a convergent finite complex-matrix family have only
spectral limit points. -/
theorem matrix_spectral_limit_of_tendsto
    {ι n : Type*} [Fintype n] [DecidableEq n]
    {l : Filter ι} [NeBot l]
    (M : ι → Matrix n n ℂ) (M₀ : Matrix n n ℂ)
    (z : ι → ℂ) (z₀ : ℂ)
    (hM : Tendsto M l (nhds M₀))
    (hz : Tendsto z l (nhds z₀))
    (hmem : ∀ᶠ i in l, z i ∈ spectrum ℂ (M i)) :
    z₀ ∈ spectrum ℂ M₀ := by
  exact ((upperHemicontinuous_spectrum ℂ (Matrix n n ℂ)).upperHemicontinuousAt M₀)
    |>.mem_of_tendsto (spectrum.isClosed M₀) hM hmem.frequently hz

/-- Every bounded spectral-parameter limit of roots of the fast/slow
spectral Schur equation lies in the spectrum of its ordinary Schur limit. -/
theorem fastSlowSpectralSchur_limit_mem_spectrum
    {ι s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    {l : Filter ι} [NeBot l]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0)
    (ε z : ι → ℂ) (z₀ : ℂ)
    (hpair : Tendsto (fun i => (ε i, z i)) l (nhds (0, z₀)))
    (hmem : ∀ᶠ i in l, z i ∈ spectrum ℂ
      (A + B * (fastSlowResolventMatrix D (ε i) (z i))⁻¹ * C)) :
    z₀ ∈ spectrum ℂ (A - B * D⁻¹ * C) := by
  have hM := (fastSlowSpectralSchur_tendsto_schur A B C D hD z₀).comp hpair
  have hz : Tendsto z l (nhds z₀) :=
    (continuous_snd.tendsto (0, z₀)).comp hpair
  exact matrix_spectral_limit_of_tendsto _ _ z z₀ hM hz hmem

/-- If a family of nonstable full eigenvalues has a finite limit as the
binding time scale vanishes, that limit must be zero whenever the ordinary
Schur matrix has no other eigenvalues in the closed right half-plane. -/
theorem fastSlow_nonnegative_eigen_limit_eq_zero
    {ι s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    {l : Filter ι} [NeBot l]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0)
    (hS : ∀ w : ℂ, w ∈ spectrum ℂ (A - B * D⁻¹ * C) →
      0 ≤ w.re → w = 0)
    (ε : ι → ℝ) (z : ι → ℂ) (v : ι → (s ⊕ f → ℂ)) (z₀ : ℂ)
    (hpair : Tendsto (fun i => ((ε i : ℂ), z i)) l (nhds (0, z₀)))
    (hε : ∀ᶠ i in l, 0 < ε i)
    (hzre : ∀ᶠ i in l, 0 ≤ (z i).re)
    (hv0 : ∀ᶠ i in l, v i ≠ 0)
    (hv : ∀ᶠ i in l,
      fastSlowMatrix A B C D (ε i : ℂ) *ᵥ v i = z i • v i) :
    z₀ = 0 := by
  have hmem : ∀ᶠ i in l, z i ∈ spectrum ℂ
      (A + B * (fastSlowResolventMatrix D (ε i : ℂ) (z i))⁻¹ * C) := by
    filter_upwards [hε, hzre, hv0, hv] with i hei hzi hvi hi
    exact fastSlowMatrix_nonnegative_eigen_schur_spectrum
      A B C D hD hei (z i) hzi (v i) hvi hi
  have hlim := fastSlowSpectralSchur_limit_mem_spectrum A B C D hD
    (fun i => (ε i : ℂ)) z z₀ hpair hmem
  have hz : Tendsto z l (nhds z₀) :=
    (continuous_snd.tendsto (0, z₀)).comp hpair
  have hzre₀ : 0 ≤ z₀.re := by
    have hreal : Tendsto (fun i => (z i).re) l (nhds z₀.re) :=
      (Complex.continuous_re.tendsto z₀).comp hz
    exact isClosed_Ici.mem_of_tendsto hreal hzre
  exact hS z₀ hlim hzre₀

end
end PhosphorylationStableCapacity
