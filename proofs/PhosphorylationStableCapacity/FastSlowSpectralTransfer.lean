module
public import proofs.PhosphorylationStableCapacity.PolynomialCoefficientContinuity

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix Polynomial Filter
open scoped Topology

/-- Convert a finite-matrix spectral point into a nonzero eigenvector in
the coordinates used by the fast/slow estimates. -/
private theorem spectral_point_has_mulVec_eigenvector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (z : ℂ)
    (hz : z ∈ spectrum ℂ M) :
    ∃ v : ι → ℂ, v ≠ 0 ∧ M *ᵥ v = z • v := by
  have hscalar : (Matrix.scalar ι z : Matrix ι ι ℂ) = z • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  have hdet : (z • (1 : Matrix ι ι ℂ) - M).det = 0 := by
    simpa [Matrix.mem_spectrum_iff_isRoot_charpoly,
      Polynomial.IsRoot, Matrix.eval_charpoly, hscalar] using hz
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv0, ?_⟩
  have hv' : z • v - M *ᵥ v = 0 := by
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec] using hv
  exact (sub_eq_zero.mp hv').symm

/-- For all sufficiently small positive binding scales, zero is the
only full-matrix spectral point in the closed right half-plane. -/
theorem fastSlow_nonnegative_spectrum_eventually_eq_zero
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0)
    (q : ℂ[X])
    (hS : (A - B * D⁻¹ * C).charpoly = q * Polynomial.X)
    (hq : q.eval 0 ≠ 0)
    (hSleft : ∀ w : ℂ, w ∈ spectrum ℂ (A - B * D⁻¹ * C) →
      w.re < 0 ∨ w = 0) :
    ∀ᶠ ε : ℝ in 𝓝 0,
      ∀ z : ℂ, 0 < ε → z ∈ spectrum ℂ (fastSlowMatrix A B C D (ε : ℂ)) →
        0 ≤ z.re → z = 0 := by
  obtain ⟨δ, η, hδ, hη, hisolate⟩ :=
    fastSlowPencilPolynomial_uniform_zero_isolation A B C D hD q hS hq
  have hreal : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
  have hsmall : ∀ᶠ ε : ℝ in 𝓝 0, (ε : ℂ) ∈ Metric.ball 0 δ :=
    hreal.eventually (Metric.ball_mem_nhds (0 : ℂ) hδ)
  have hnear := fastSlow_nonnegative_eigen_eventually_near_zero
    A B C D hD hSleft hη
  filter_upwards [hsmall, hnear] with ε hε hnear z hεpos hz hzre
  obtain ⟨v, hv0, heig⟩ := spectral_point_has_mulVec_eigenvector
    (fastSlowMatrix A B C D (ε : ℂ)) z hz
  have hzball : z ∈ Metric.ball 0 η :=
    hnear z v hεpos hzre hv0 heig
  by_contra hz0
  have hεc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hεpos)
  have hpencil : (fastSlowPencilPolynomial A B C D (ε : ℂ)).eval z = 0 := by
    rw [fastSlowPencilPolynomial_eval,
      fastSlowCharacteristicBlock_det_eq_charpoly A B C D (ε : ℂ) z hεc]
    have hroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
    simp [Polynomial.IsRoot] at hroot
    simp [hroot]
  exact (hisolate (ε : ℂ) z hε hzball hz0) hpencil

/-- At sufficiently small positive binding scale the full Jacobian has
an algebraically simple exact zero characteristic factor. -/
theorem fastSlow_zero_eventually_algebraically_simple
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0)
    (q : ℂ[X])
    (hS : (A - B * D⁻¹ * C).charpoly = q * Polynomial.X)
    (hq : q.eval 0 ≠ 0) :
    ∀ᶠ ε : ℝ in 𝓝 0,
      0 < ε →
        let J := fastSlowMatrix A B C D (ε : ℂ)
        J.charpoly = Polynomial.X * J.charpoly.divX ∧
          J.charpoly.divX.eval 0 ≠ 0 := by
  have hreal : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
  have hcoeff := hreal.eventually
    (fastSlowPencilPolynomial_coeff_one_eventually_ne_zero A B C D hD q hS hq)
  filter_upwards [hcoeff] with ε hcoeff hεpos
  let J := fastSlowMatrix A B C D (ε : ℂ)
  have hεc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hεpos)
  have hpoly : fastSlowPencilPolynomial A B C D (ε : ℂ) =
      Polynomial.C ((ε : ℂ) ^ Fintype.card f) * J.charpoly := by
    apply Polynomial.funext
    intro z
    rw [fastSlowPencilPolynomial_eval,
      fastSlowCharacteristicBlock_det_eq_charpoly A B C D (ε : ℂ) z hεc,
      Polynomial.eval_mul, Polynomial.eval_C]
  have hcoeffJ : J.charpoly.coeff 1 ≠ 0 := by
    rw [hpoly, Polynomial.coeff_C_mul] at hcoeff
    exact (mul_ne_zero_iff.mp hcoeff).2
  have hSzero : (0 : ℂ) ∈ spectrum ℂ (A - B * D⁻¹ * C) := by
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (by
      rw [hS]
      simp [Polynomial.IsRoot])
  have hJzero : (0 : ℂ) ∈ spectrum ℂ J :=
    fastSlowMatrix_zero_mem_spectrum_of_schur A B C D hD hSzero (ε : ℂ) hεc
  have hcoeff0 : J.charpoly.coeff 0 = 0 := by
    have hroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hJzero
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simpa [Polynomial.IsRoot] using hroot
  constructor
  · simpa [hcoeff0] using (Polynomial.X_mul_divX_add J.charpoly).symm
  · simpa [← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_divX] using hcoeffJ

/-- Generic fast/slow spectral transfer: the full Jacobian has one
algebraically simple neutral factor, and every complementary root has
strictly negative real part at sufficiently small positive binding scale. -/
theorem fastSlow_eventually_simple_zero_hurwitz_complement
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0)
    (q : ℂ[X])
    (hS : (A - B * D⁻¹ * C).charpoly = q * Polynomial.X)
    (hq : q.eval 0 ≠ 0)
    (hSleft : ∀ w : ℂ, w ∈ spectrum ℂ (A - B * D⁻¹ * C) →
      w.re < 0 ∨ w = 0) :
    ∀ᶠ ε : ℝ in 𝓝 0,
      0 < ε →
        let J := fastSlowMatrix A B C D (ε : ℂ)
        ∃ r : ℂ[X], J.charpoly = Polynomial.X * r ∧
          r.eval 0 ≠ 0 ∧
          ∀ z : ℂ, r.eval z = 0 → z.re < 0 := by
  have hspec := fastSlow_nonnegative_spectrum_eventually_eq_zero
    A B C D hD q hS hq hSleft
  have hsimple := fastSlow_zero_eventually_algebraically_simple
    A B C D hD q hS hq
  filter_upwards [hspec, hsimple] with ε hspec hsimple hεpos
  let J := fastSlowMatrix A B C D (ε : ℂ)
  obtain ⟨hfactor, hzero⟩ := hsimple hεpos
  refine ⟨J.charpoly.divX, hfactor, hzero, ?_⟩
  intro z hz
  by_contra hn
  have hzre : 0 ≤ z.re := le_of_not_gt hn
  have hchar : J.charpoly.eval z = 0 := by
    rw [hfactor, Polynomial.eval_mul, Polynomial.eval_X, hz, mul_zero]
  have hzspec : z ∈ spectrum ℂ J :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (by
      simpa [Polynomial.IsRoot] using hchar)
  have hz0 := hspec z hεpos hzspec hzre
  subst z
  exact hzero hz

end
end PhosphorylationStableCapacity
