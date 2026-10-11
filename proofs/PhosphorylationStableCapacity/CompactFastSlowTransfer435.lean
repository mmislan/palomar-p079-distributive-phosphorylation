module
public import proofs.PhosphorylationStableCapacity.CompactFastSlowScaled435

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix Polynomial Filter
open scoped Topology Matrix.Norms.L2Operator

private theorem compact_spectral_point_has_mulVec_eigenvector
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

/-- Uniformly over a compact continuous family of fast/slow blocks, zero
is the only full spectral point in the closed right half-plane for every
sufficiently small positive binding scale. -/
theorem compact_fastSlow_nonnegative_spectrum_eventually_eq_zero
    {α s f : Type*} [TopologicalSpace α]
    [Fintype s] [Fintype f] [DecidableEq s] [DecidableEq f]
    (K : Set α) (hK : IsCompact K)
    (A : α → Matrix s s ℂ) (B : α → Matrix s f ℂ)
    (C : α → Matrix f s ℂ) (D : α → Matrix f f ℂ)
    (q : α → ℂ[X])
    (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hDcont : Continuous D)
    (hD : ∀ a ∈ K, ∀ w : ℂ,
      w ∈ spectrum ℂ (D a) → w.re < 0)
    (hS : ∀ a ∈ K,
      (A a - B a * (D a)⁻¹ * C a).charpoly = q a * Polynomial.X)
    (hq : ∀ a ∈ K, (q a).eval 0 ≠ 0)
    (hSleft : ∀ a ∈ K, ∀ w : ℂ,
      w ∈ spectrum ℂ (A a - B a * (D a)⁻¹ * C a) →
        w.re < 0 ∨ w = 0) :
    ∀ᶠ ε : ℝ in 𝓝 0,
      ∀ a ∈ K, ∀ z : ℂ,
        0 < ε →
        z ∈ spectrum ℂ
          (fastSlowMatrix (A a) (B a) (C a) (D a) (ε : ℂ)) →
        0 ≤ z.re → z = 0 := by
  obtain ⟨δ, η, hδ, hη, hisolate⟩ :=
    compact_fastSlowPencil_uniform_zero_isolation
      K hK A B C D q hA hB hC hDcont hD hS hq
  have hreal : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
  have hsmall : ∀ᶠ ε : ℝ in 𝓝 0, (ε : ℂ) ∈ Metric.ball 0 δ :=
    hreal.eventually (Metric.ball_mem_nhds (0 : ℂ) hδ)
  have hnear := compact_fastSlow_nonnegative_eigen_eventually_near_zero
    K hK A B C D hA hB hC hDcont hD hSleft η hη
  filter_upwards [hsmall, hnear] with ε hε hnear a ha z hεpos hz hzre
  obtain ⟨v, hv0, heig⟩ := compact_spectral_point_has_mulVec_eigenvector
    (fastSlowMatrix (A a) (B a) (C a) (D a) (ε : ℂ)) z hz
  have hzball : z ∈ Metric.ball 0 η :=
    hnear a ha z v hεpos hzre hv0 heig
  by_contra hz0
  have hεc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hεpos)
  have hpencil :
      (fastSlowPencilPolynomial (A a) (B a) (C a) (D a) (ε : ℂ)).eval z = 0 := by
    rw [fastSlowPencilPolynomial_eval,
      fastSlowCharacteristicBlock_det_eq_charpoly
        (A a) (B a) (C a) (D a) (ε : ℂ) z hεc]
    have hroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
    simp [Polynomial.IsRoot] at hroot
    simp [hroot]
  exact (hisolate a ha (ε : ℂ) z hε hzball hz0) hpencil

/-- The neutral full-Jacobian root is algebraically simple with one
binding-scale threshold shared by a compact continuous block family. -/
theorem compact_fastSlow_zero_eventually_algebraically_simple
    {α s f : Type*} [TopologicalSpace α]
    [Fintype s] [Fintype f] [DecidableEq s] [DecidableEq f]
    (K : Set α) (hK : IsCompact K)
    (A : α → Matrix s s ℂ) (B : α → Matrix s f ℂ)
    (C : α → Matrix f s ℂ) (D : α → Matrix f f ℂ)
    (q : α → ℂ[X])
    (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hDcont : Continuous D)
    (hD : ∀ a ∈ K, ∀ w : ℂ,
      w ∈ spectrum ℂ (D a) → w.re < 0)
    (hS : ∀ a ∈ K,
      (A a - B a * (D a)⁻¹ * C a).charpoly = q a * Polynomial.X)
    (hq : ∀ a ∈ K, (q a).eval 0 ≠ 0) :
    ∀ᶠ ε : ℝ in 𝓝 0,
      ∀ a ∈ K, 0 < ε →
        let J := fastSlowMatrix (A a) (B a) (C a) (D a) (ε : ℂ)
        J.charpoly = Polynomial.X * J.charpoly.divX ∧
          J.charpoly.divX.eval 0 ≠ 0 := by
  have hreal : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
  have hcoeff := hreal.eventually
    (compact_fastSlowPencil_coeff_one_eventually_of_continuous_blocks
      K hK A B C D q hA hB hC hDcont hD hS hq)
  filter_upwards [hcoeff] with ε hcoeff a ha hεpos
  let J := fastSlowMatrix (A a) (B a) (C a) (D a) (ε : ℂ)
  have hεc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hεpos)
  have hpoly : fastSlowPencilPolynomial
      (A a) (B a) (C a) (D a) (ε : ℂ) =
      Polynomial.C ((ε : ℂ) ^ Fintype.card f) * J.charpoly := by
    apply Polynomial.funext
    intro z
    rw [fastSlowPencilPolynomial_eval,
      fastSlowCharacteristicBlock_det_eq_charpoly
        (A a) (B a) (C a) (D a) (ε : ℂ) z hεc,
      Polynomial.eval_mul, Polynomial.eval_C]
  have hcoeffJ : J.charpoly.coeff 1 ≠ 0 := by
    have hcoeffa := hcoeff a ha
    rw [hpoly, Polynomial.coeff_C_mul] at hcoeffa
    exact (mul_ne_zero_iff.mp hcoeffa).2
  have hSzero : (0 : ℂ) ∈ spectrum ℂ
      (A a - B a * (D a)⁻¹ * C a) := by
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (by
      rw [hS a ha]
      simp [Polynomial.IsRoot])
  have hJzero : (0 : ℂ) ∈ spectrum ℂ J :=
    fastSlowMatrix_zero_mem_spectrum_of_schur
      (A a) (B a) (C a) (D a) (hD a ha) hSzero (ε : ℂ) hεc
  have hcoeff0 : J.charpoly.coeff 0 = 0 := by
    have hroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hJzero
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simpa [Polynomial.IsRoot] using hroot
  constructor
  · simpa [hcoeff0] using (Polynomial.X_mul_divX_add J.charpoly).symm
  · simpa [← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_divX] using hcoeffJ

/-- The entire fast/slow simple-neutral Hurwitz-complement result holds
with one sufficiently small binding-scale threshold over compact
continuous families of admissible matrix blocks. -/
theorem compact_fastSlow_eventually_simple_zero_hurwitz_complement
    {α s f : Type*} [TopologicalSpace α]
    [Fintype s] [Fintype f] [DecidableEq s] [DecidableEq f]
    (K : Set α) (hK : IsCompact K)
    (A : α → Matrix s s ℂ) (B : α → Matrix s f ℂ)
    (C : α → Matrix f s ℂ) (D : α → Matrix f f ℂ)
    (q : α → ℂ[X])
    (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hDcont : Continuous D)
    (hD : ∀ a ∈ K, ∀ w : ℂ,
      w ∈ spectrum ℂ (D a) → w.re < 0)
    (hS : ∀ a ∈ K,
      (A a - B a * (D a)⁻¹ * C a).charpoly = q a * Polynomial.X)
    (hq : ∀ a ∈ K, (q a).eval 0 ≠ 0)
    (hSleft : ∀ a ∈ K, ∀ w : ℂ,
      w ∈ spectrum ℂ (A a - B a * (D a)⁻¹ * C a) →
        w.re < 0 ∨ w = 0) :
    ∀ᶠ ε : ℝ in 𝓝 0,
      ∀ a ∈ K, 0 < ε →
        let J := fastSlowMatrix (A a) (B a) (C a) (D a) (ε : ℂ)
        ∃ r : ℂ[X], J.charpoly = Polynomial.X * r ∧
          r.eval 0 ≠ 0 ∧
          ∀ z : ℂ, r.eval z = 0 → z.re < 0 := by
  have hspec := compact_fastSlow_nonnegative_spectrum_eventually_eq_zero
    K hK A B C D q hA hB hC hDcont hD hS hq hSleft
  have hsimple := compact_fastSlow_zero_eventually_algebraically_simple
    K hK A B C D q hA hB hC hDcont hD hS hq
  filter_upwards [hspec, hsimple] with ε hspec hsimple a ha hεpos
  let J := fastSlowMatrix (A a) (B a) (C a) (D a) (ε : ℂ)
  obtain ⟨hfactor, hzero⟩ := hsimple a ha hεpos
  refine ⟨J.charpoly.divX, hfactor, hzero, ?_⟩
  intro z hz
  by_contra hn
  have hzre : 0 ≤ z.re := le_of_not_gt hn
  have hchar : J.charpoly.eval z = 0 := by
    rw [hfactor, Polynomial.eval_mul, Polynomial.eval_X, hz, mul_zero]
  have hzspec : z ∈ spectrum ℂ J :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (by
      simpa [Polynomial.IsRoot] using hchar)
  have hz0 := hspec a ha z hεpos hzspec hzre
  subst z
  exact hzero hz

end

end PhosphorylationStableCapacity
