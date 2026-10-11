module
public import proofs.PhosphorylationStableCapacity.FastSlowScaledLimit
public import proofs.PhosphorylationStableCapacity.FastSlowEigenElimination
public import proofs.PhosphorylationStableCapacity.FastSlowPencilPolynomial
public import proofs.PhosphorylationStableCapacity.JointPolynomialCoefficientContinuity435
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter Matrix
open scoped Topology Matrix.Norms.L2Operator Polynomial
set_option maxHeartbeats 800000

theorem continuous_fastSlowScaledMatrix_parameter_family
    {α s f : Type*} [TopologicalSpace α]
    [Fintype s] [Fintype f]
    (A : α → Matrix s s ℂ) (B : α → Matrix s f ℂ)
    (C : α → Matrix f s ℂ) (D : α → Matrix f f ℂ)
    (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hD : Continuous D) :
    Continuous (fun p : α × ℂ =>
      fastSlowScaledMatrix (A p.1) (B p.1) (C p.1) (D p.1) p.2) := by
  apply continuous_matrix
  intro i j
  cases i <;> cases j <;>
    simp only [fastSlowScaledMatrix, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul] <;>
    fun_prop

/-- Compact uniform upper semicontinuity for a continuous matrix pencil.
All roots above a compact parameter set lie in the stable half-plane or
one fixed small ball when the pencil parameter is sufficiently small. -/
theorem compact_spectral_near_left_of_zero_family
    {α ι : Type*} [TopologicalSpace α]
    [Fintype ι] [DecidableEq ι]
    (K : Set α) (hK : IsCompact K)
    (F : α × ℂ → Matrix ι ι ℂ)
    (hF : ∀ a ∈ K, ContinuousAt F (a, 0))
    (hzero : ∀ a ∈ K, ∀ z : ℂ,
      z ∈ spectrum ℂ (F (a, 0)) → z.re < 0 ∨ z = 0)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ ε : ℂ in 𝓝 0,
      ∀ a ∈ K, ∀ z : ℂ,
        z ∈ spectrum ℂ (F (a, ε)) →
          z.re < 0 ∨ z ∈ Metric.ball 0 η := by
  let U : Set ℂ := {z | z.re < 0} ∪ Metric.ball 0 η
  have hU : IsOpen U :=
    (isOpen_Iio.preimage Complex.continuous_re).union Metric.isOpen_ball
  let S : Set (α × ℂ) := {p | spectrum ℂ (F p) ⊆ U}
  have hSnear : S ∈ 𝓝ˢ (K ×ˢ ({0} : Set ℂ)) := by
    apply mem_nhdsSet_iff_forall.mpr
    rintro ⟨a, ε⟩ ⟨ha, hε⟩
    have hε0 : ε = 0 := Set.mem_singleton_iff.mp hε
    subst ε
    have hspec : spectrum ℂ (F (a, 0)) ⊆ U := by
      intro z hz
      rcases hzero a ha z hz with hleft | hz0
      · exact Or.inl hleft
      · subst z
        exact Or.inr (Metric.mem_ball_self hη)
    have hnear :=
      (upperHemicontinuous_spectrum ℂ (Matrix ι ι ℂ)).forall_isOpen
        (F (a, 0)) U hU hspec
    exact (hF a ha).tendsto.eventually hnear
  obtain ⟨T, hTopen, hK0T, hTS⟩ :=
    mem_nhdsSet_iff_exists.mp hSnear
  obtain ⟨V, W, _, hWopen, hKV, h0W, hVW⟩ :=
    generalized_tube_lemma hK isCompact_singleton hTopen hK0T
  have hW : W ∈ 𝓝 (0 : ℂ) := hWopen.mem_nhds (h0W (by simp))
  filter_upwards [hW] with ε hε a ha z hz
  exact (hTS (hVW ⟨hKV ha, hε⟩)) hz

/-- The scaled fast/slow pencil has a compact-uniform spectral confinement
step once its parameter-dependent matrix family is jointly continuous. -/
theorem compact_fastSlowScaledMatrix_eventually_spectrum_near_zero_or_left
    {α s f : Type*} [TopologicalSpace α]
    [Fintype s] [Fintype f] [DecidableEq s] [DecidableEq f]
    (K : Set α) (hK : IsCompact K)
    (A : α → Matrix s s ℂ) (B : α → Matrix s f ℂ)
    (C : α → Matrix f s ℂ) (D : α → Matrix f f ℂ)
    (hF : Continuous (fun p : α × ℂ =>
      fastSlowScaledMatrix (A p.1) (B p.1) (C p.1) (D p.1) p.2))
    (hD : ∀ a ∈ K, ∀ z : ℂ, z ∈ spectrum ℂ (D a) → z.re < 0)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ ε : ℂ in 𝓝 0,
      ∀ a ∈ K, ∀ z : ℂ,
        z ∈ spectrum ℂ
          (fastSlowScaledMatrix (A a) (B a) (C a) (D a) ε) →
          z.re < 0 ∨ z ∈ Metric.ball 0 η := by
  apply compact_spectral_near_left_of_zero_family K hK
    (fun p => fastSlowScaledMatrix (A p.1) (B p.1) (C p.1) (D p.1) p.2)
    (fun a ha => hF.continuousAt) ?_ η hη
  intro a ha z hz
  rcases fastSlowScaledMatrix_zero_spectrum_subset
      (A a) (B a) (C a) (D a) hz with hzero | hfast
  · exact Or.inr (Set.mem_singleton_iff.mp hzero)
  · exact Or.inl (hD a ha z hfast)

theorem compact_fastSlowScaledMatrix_eventually_of_continuous_blocks
    {α s f : Type*} [TopologicalSpace α]
    [Fintype s] [Fintype f] [DecidableEq s] [DecidableEq f]
    (K : Set α) (hK : IsCompact K)
    (A : α → Matrix s s ℂ) (B : α → Matrix s f ℂ)
    (C : α → Matrix f s ℂ) (D : α → Matrix f f ℂ)
    (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hDcont : Continuous D)
    (hD : ∀ a ∈ K, ∀ z : ℂ, z ∈ spectrum ℂ (D a) → z.re < 0)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ ε : ℂ in 𝓝 0,
      ∀ a ∈ K, ∀ z : ℂ,
        z ∈ spectrum ℂ
          (fastSlowScaledMatrix (A a) (B a) (C a) (D a) ε) →
          z.re < 0 ∨ z ∈ Metric.ball 0 η :=
  compact_fastSlowScaledMatrix_eventually_spectrum_near_zero_or_left
    K hK A B C D
      (continuous_fastSlowScaledMatrix_parameter_family
        A B C D hA hB hC hDcont) hD η hη

theorem continuousAt_fastSlowSpectralSchur_parameter_family
    {α s f : Type*} [TopologicalSpace α]
    [Fintype s] [Fintype f] [DecidableEq s] [DecidableEq f]
    (A : α → Matrix s s ℂ) (B : α → Matrix s f ℂ)
    (C : α → Matrix f s ℂ) (D : α → Matrix f f ℂ)
    (a : α)
    (hA : ContinuousAt A a) (hB : ContinuousAt B a)
    (hC : ContinuousAt C a) (hD : ContinuousAt D a)
    (hDspec : ∀ z : ℂ, z ∈ spectrum ℂ (D a) → z.re < 0) :
    ContinuousAt
      (fun p : α × ℂ => A p.1 + B p.1 *
        (fastSlowResolventMatrix (D p.1) p.2 1)⁻¹ * C p.1)
      (a, 0) := by
  have hA' : ContinuousAt (fun p : α × ℂ => A p.1) (a, 0) :=
    hA.comp continuousAt_fst
  have hB' : ContinuousAt (fun p : α × ℂ => B p.1) (a, 0) :=
    hB.comp continuousAt_fst
  have hC' : ContinuousAt (fun p : α × ℂ => C p.1) (a, 0) :=
    hC.comp continuousAt_fst
  have hD' : ContinuousAt (fun p : α × ℂ => D p.1) (a, 0) :=
    hD.comp continuousAt_fst
  have hμ : ContinuousAt (fun p : α × ℂ => p.2) (a, 0) :=
    continuousAt_snd
  let R : α × ℂ → Matrix f f ℂ := fun p =>
    fastSlowResolventMatrix (D p.1) p.2 1
  have hR : ContinuousAt R (a, 0) := by
    dsimp [R, fastSlowResolventMatrix]
    exact ((hμ.mul continuousAt_const).smul continuousAt_const).sub hD'
  have hunit : IsUnit (-D a).det := by
    simpa [fastSlowResolventMatrix] using
      (fastSlowResolventMatrix_isUnit_det_of_hurwitz
        (D a) hDspec (show (0 : ℝ) < 1 by norm_num) 0 (le_refl 0))
  have hInv0 : ContinuousAt
      (Inv.inv : Matrix f f ℂ → Matrix f f ℂ) (-D a) :=
    continuousAt_matrix_inv (-D a) (by
      simpa using (continuousAt_inv₀ hunit.ne_zero))
  have hR0 : R (a, 0) = -D a := by
    simp [R, fastSlowResolventMatrix]
  have hInv : ContinuousAt (fun p : α × ℂ => (R p)⁻¹) (a, 0) := by
    exact hInv0.comp_of_eq hR hR0
  have hmul₁ : Continuous
      (fun p : Matrix s f ℂ × Matrix f f ℂ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  have hprod : ContinuousAt
      (fun p : α × ℂ => B p.1 * (R p)⁻¹) (a, 0) :=
    hmul₁.continuousAt.comp (hB'.prodMk hInv)
  have hmul₂ : Continuous
      (fun p : Matrix s f ℂ × Matrix f s ℂ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  exact hA'.add (hmul₂.continuousAt.comp (hprod.prodMk hC'))

/-- The spectral Schur operator has one compact-uniform near-zero
confinement step when its resolvent is continuous along the compact
parameter family at μ=0. -/
theorem compact_fastSlowSpectralSchur_mu_eventually_spectrum_near_zero_or_left
    {α s f : Type*} [TopologicalSpace α]
    [Fintype s] [Fintype f] [DecidableEq s] [DecidableEq f]
    (K : Set α) (hK : IsCompact K)
    (A : α → Matrix s s ℂ) (B : α → Matrix s f ℂ)
    (C : α → Matrix f s ℂ) (D : α → Matrix f f ℂ)
    (hF : ∀ a ∈ K, ContinuousAt
      (fun p : α × ℂ =>
        A p.1 + B p.1 *
          (fastSlowResolventMatrix (D p.1) p.2 1)⁻¹ * C p.1)
      (a, 0))
    (hS : ∀ a ∈ K, ∀ z : ℂ,
      z ∈ spectrum ℂ (A a - B a * (D a)⁻¹ * C a) →
        z.re < 0 ∨ z = 0)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ μ : ℂ in 𝓝 0,
      ∀ a ∈ K, ∀ z : ℂ,
        z ∈ spectrum ℂ
          (A a + B a * (fastSlowResolventMatrix (D a) μ 1)⁻¹ * C a) →
          z.re < 0 ∨ z ∈ Metric.ball 0 η := by
  apply compact_spectral_near_left_of_zero_family K hK
    (fun p => A p.1 + B p.1 *
      (fastSlowResolventMatrix (D p.1) p.2 1)⁻¹ * C p.1)
    hF ?_ η hη
  intro a ha z hz
  have hzeroF :
      A a + B a * (fastSlowResolventMatrix (D a) 0 1)⁻¹ * C a =
        A a - B a * (D a)⁻¹ * C a := by
    simpa [fastSlowResolventMatrix] using
      fastSlowSchur_limit_eq (A a) (B a) (C a) (D a)
  exact hS a ha z (hzeroF ▸ hz)

theorem compact_fastSlowSpectralSchur_mu_eventually_of_continuous_blocks
    {α s f : Type*} [TopologicalSpace α]
    [Fintype s] [Fintype f] [DecidableEq s] [DecidableEq f]
    (K : Set α) (hK : IsCompact K)
    (A : α → Matrix s s ℂ) (B : α → Matrix s f ℂ)
    (C : α → Matrix f s ℂ) (D : α → Matrix f f ℂ)
    (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hDcont : Continuous D)
    (hD : ∀ a ∈ K, ∀ z : ℂ,
      z ∈ spectrum ℂ (D a) → z.re < 0)
    (hS : ∀ a ∈ K, ∀ z : ℂ,
      z ∈ spectrum ℂ (A a - B a * (D a)⁻¹ * C a) →
        z.re < 0 ∨ z = 0)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ μ : ℂ in 𝓝 0,
      ∀ a ∈ K, ∀ z : ℂ,
        z ∈ spectrum ℂ
          (A a + B a * (fastSlowResolventMatrix (D a) μ 1)⁻¹ * C a) →
          z.re < 0 ∨ z ∈ Metric.ball 0 η := by
  apply compact_fastSlowSpectralSchur_mu_eventually_spectrum_near_zero_or_left
    K hK A B C D ?_ hS η hη
  intro a ha
  exact continuousAt_fastSlowSpectralSchur_parameter_family A B C D a
    hA.continuousAt hB.continuousAt hC.continuousAt hDcont.continuousAt
    (hD a ha)

/-- Compact-uniform version of the finite slow-eigenvalue confinement:
every nonstable full eigenvalue lies in one prescribed ball around zero
for all matrices in the compact family and all sufficiently small positive
binding scales. -/
theorem compact_fastSlow_nonnegative_eigen_eventually_near_zero
    {α s f : Type*} [TopologicalSpace α]
    [Fintype s] [Fintype f] [DecidableEq s] [DecidableEq f]
    (K : Set α) (hK : IsCompact K)
    (A : α → Matrix s s ℂ) (B : α → Matrix s f ℂ)
    (C : α → Matrix f s ℂ) (D : α → Matrix f f ℂ)
    (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hDcont : Continuous D)
    (hD : ∀ a ∈ K, ∀ w : ℂ,
      w ∈ spectrum ℂ (D a) → w.re < 0)
    (hSleft : ∀ a ∈ K, ∀ w : ℂ,
      w ∈ spectrum ℂ (A a - B a * (D a)⁻¹ * C a) →
        w.re < 0 ∨ w = 0)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ ε : ℝ in 𝓝 0,
      ∀ a ∈ K, ∀ z : ℂ, ∀ v : s ⊕ f → ℂ,
        0 < ε → 0 ≤ z.re → v ≠ 0 →
        fastSlowMatrix (A a) (B a) (C a) (D a) (ε : ℂ) *ᵥ v = z • v →
          z ∈ Metric.ball 0 η := by
  have hU : {μ : ℂ | ∀ a ∈ K, ∀ z : ℂ,
      z ∈ spectrum ℂ
        (A a + B a * (fastSlowResolventMatrix (D a) μ 1)⁻¹ * C a) →
        z.re < 0 ∨ z ∈ Metric.ball 0 η} ∈ 𝓝 (0 : ℂ) :=
    compact_fastSlowSpectralSchur_mu_eventually_of_continuous_blocks
      K hK A B C D hA hB hC hDcont hD hSleft η hη
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hscaled :=
    compact_fastSlowScaledMatrix_eventually_of_continuous_blocks
      K hK A B C D hA hB hC hDcont hD δ hδ
  have hreal : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
  filter_upwards [hreal.eventually hscaled] with ε hε a ha z v hεpos hzre hv0 hv
  have hεc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hεpos)
  have hscaledEig :
      fastSlowScaledMatrix (A a) (B a) (C a) (D a) (ε : ℂ) *ᵥ v =
        ((ε : ℂ) * z) • v := by
    rw [fastSlowScaledMatrix_eq_smul_fastSlowMatrix
      (A a) (B a) (C a) (D a) hεc,
      Matrix.smul_mulVec, hv, smul_smul]
  have hscaledMem : (ε : ℂ) * z ∈
      spectrum ℂ (fastSlowScaledMatrix
        (A a) (B a) (C a) (D a) (ε : ℂ)) :=
    matrix_mem_spectrum_of_mulVec_eq_smul _ _ _ hv0 hscaledEig
  have hμre : 0 ≤ ((ε : ℂ) * z).re := by
    simpa using mul_nonneg (le_of_lt hεpos) hzre
  have hμball : (ε : ℂ) * z ∈ Metric.ball 0 δ :=
    (hε a ha _ hscaledMem).resolve_left (not_lt_of_ge hμre)
  have hschurMem := fastSlowMatrix_nonnegative_eigen_schur_spectrum
    (A a) (B a) (C a) (D a) (hD a ha) hεpos z hzre v hv0 hv
  have hEq : fastSlowResolventMatrix (D a) (ε : ℂ) z =
      fastSlowResolventMatrix (D a) ((ε : ℂ) * z) 1 := by
    simp [fastSlowResolventMatrix]
  have hnear := hball hμball a ha z
  rw [← hEq] at hnear
  exact (hnear hschurMem).resolve_left (not_lt_of_ge hzre)

/-- A continuous scalar coefficient that is nonzero at zero for every
member of a compact parameter family stays nonzero for one common small
perturbation. This is the compact step needed for the simple-zero factor
of the fast/slow characteristic pencil. -/
theorem compact_continuous_coefficient_eventually_ne_zero
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (K : Set α) (hK : IsCompact K)
    (b₀ : β) (c : α × β → ℂ)
    (hc : ∀ a ∈ K, ContinuousAt c (a, b₀))
    (h0 : ∀ a ∈ K, c (a, b₀) ≠ 0) :
    ∀ᶠ b : β in 𝓝 b₀, ∀ a ∈ K, c (a, b) ≠ 0 := by
  let S : Set (α × β) := {p | c p ≠ 0}
  have hSnear : S ∈ 𝓝ˢ (K ×ˢ ({b₀} : Set β)) := by
    apply mem_nhdsSet_iff_forall.mpr
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    have hb0 : b = b₀ := Set.mem_singleton_iff.mp hb
    subst b
    exact (hc a ha).tendsto.eventually (isOpen_ne.mem_nhds (h0 a ha))
  obtain ⟨T, hTopen, hK0T, hTS⟩ :=
    mem_nhdsSet_iff_exists.mp hSnear
  obtain ⟨V, W, _, hWopen, hKV, h0W, hVW⟩ :=
    generalized_tube_lemma hK isCompact_singleton hTopen hK0T
  have hW : W ∈ 𝓝 b₀ := hWopen.mem_nhds (h0W (by simp))
  filter_upwards [hW] with b hb a ha
  exact hTS (hVW ⟨hKV ha, hb⟩)

/-- A compact-uniform version of the nonzero linear coefficient in the
fast/slow characteristic pencil, conditional on its joint coefficient
continuity. -/
theorem compact_fastSlowPencil_coeff_one_eventually_ne_zero
    {α s f : Type*} [TopologicalSpace α]
    [Fintype s] [Fintype f] [DecidableEq s] [DecidableEq f]
    (K : Set α) (hK : IsCompact K)
    (A : α → Matrix s s ℂ) (B : α → Matrix s f ℂ)
    (C : α → Matrix f s ℂ) (D : α → Matrix f f ℂ)
    (q : α → ℂ[X])
    (hc : ∀ a ∈ K, ContinuousAt
      (fun p : α × ℂ =>
        (fastSlowPencilPolynomial
          (A p.1) (B p.1) (C p.1) (D p.1) p.2).coeff 1)
      (a, 0))
    (hD : ∀ a ∈ K, ∀ z : ℂ,
      z ∈ spectrum ℂ (D a) → z.re < 0)
    (hS : ∀ a ∈ K,
      (A a - B a * (D a)⁻¹ * C a).charpoly =
        q a * Polynomial.X)
    (hq : ∀ a ∈ K, (q a).eval 0 ≠ 0) :
    ∀ᶠ ε : ℂ in 𝓝 0,
      ∀ a ∈ K,
        (fastSlowPencilPolynomial
          (A a) (B a) (C a) (D a) ε).coeff 1 ≠ 0 := by
  apply compact_continuous_coefficient_eventually_ne_zero K hK
    (0 : ℂ)
    (fun p => (fastSlowPencilPolynomial
      (A p.1) (B p.1) (C p.1) (D p.1) p.2).coeff 1)
    hc
  intro a ha
  exact fastSlowPencilPolynomial_zero_coeff_one_ne_zero
    (A a) (B a) (C a) (D a) (hD a ha) (q a) (hS a ha) (hq a ha)

theorem compact_fastSlowPencil_coeff_one_eventually_of_continuous_blocks
    {α s f : Type*} [TopologicalSpace α]
    [Fintype s] [Fintype f] [DecidableEq s] [DecidableEq f]
    (K : Set α) (hK : IsCompact K)
    (A : α → Matrix s s ℂ) (B : α → Matrix s f ℂ)
    (C : α → Matrix f s ℂ) (D : α → Matrix f f ℂ)
    (q : α → ℂ[X])
    (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hDcont : Continuous D)
    (hD : ∀ a ∈ K, ∀ z : ℂ,
      z ∈ spectrum ℂ (D a) → z.re < 0)
    (hS : ∀ a ∈ K,
      (A a - B a * (D a)⁻¹ * C a).charpoly =
        q a * Polynomial.X)
    (hq : ∀ a ∈ K, (q a).eval 0 ≠ 0) :
    ∀ᶠ ε : ℂ in 𝓝 0,
      ∀ a ∈ K,
        (fastSlowPencilPolynomial
          (A a) (B a) (C a) (D a) ε).coeff 1 ≠ 0 := by
  apply compact_fastSlowPencil_coeff_one_eventually_ne_zero
    K hK A B C D q ?_ hD hS hq
  intro a ha
  exact (continuous_fastSlowPencilPolynomial_coeff_parameter_family
    A B C D hA hB hC hDcont 1).continuousAt

/-- One pair of binding-scale and spectral radii excludes every nonzero
root near the neutral mode for all matrices in a compact parameter family. -/
theorem compact_fastSlowPencil_uniform_zero_isolation
    {α s f : Type*} [TopologicalSpace α]
    [Fintype s] [Fintype f] [DecidableEq s] [DecidableEq f]
    (K : Set α) (hK : IsCompact K)
    (A : α → Matrix s s ℂ) (B : α → Matrix s f ℂ)
    (C : α → Matrix f s ℂ) (D : α → Matrix f f ℂ)
    (q : α → ℂ[X])
    (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hDcont : Continuous D)
    (hD : ∀ a ∈ K, ∀ z : ℂ,
      z ∈ spectrum ℂ (D a) → z.re < 0)
    (hS : ∀ a ∈ K,
      (A a - B a * (D a)⁻¹ * C a).charpoly =
        q a * Polynomial.X)
    (hq : ∀ a ∈ K, (q a).eval 0 ≠ 0) :
    ∃ δ η : ℝ, 0 < δ ∧ 0 < η ∧
      ∀ a ∈ K, ∀ ε z : ℂ,
        ε ∈ Metric.ball 0 δ → z ∈ Metric.ball 0 η → z ≠ 0 →
          (fastSlowPencilPolynomial (A a) (B a) (C a) (D a) ε).eval z ≠ 0 := by
  let c : α × (ℂ × ℂ) → ℂ := fun p =>
    (fastSlowPencilPolynomial
      (A p.1) (B p.1) (C p.1) (D p.1) p.2.1).divX.eval p.2.2
  have hreshape : Continuous
      (fun p : α × (ℂ × ℂ) => ((p.1, p.2.1), p.2.2)) :=
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd)
  have hc : Continuous c := by
    exact (continuous_fastSlowPencilPolynomial_divX_eval_parameter_family
      A B C D hA hB hC hDcont).comp hreshape
  have hzero (a : α) (ha : a ∈ K) : c (a, (0, 0)) ≠ 0 := by
    dsimp [c]
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_divX]
    exact fastSlowPencilPolynomial_zero_coeff_one_ne_zero
      (A a) (B a) (C a) (D a) (hD a ha)
      (q a) (hS a ha) (hq a ha)
  have hnear : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0),
      ∀ a ∈ K, c (a, p) ≠ 0 :=
    compact_continuous_coefficient_eventually_ne_zero
      K hK (0, 0) c (fun a ha => hc.continuousAt) hzero
  obtain ⟨u, hu, v, hv, hsub⟩ := mem_nhds_prod_iff.mp hnear
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hu
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp hv
  refine ⟨δ, η, hδ, hη, ?_⟩
  intro a ha ε z hε hz hz0
  have hquot : c (a, (ε, z)) ≠ 0 :=
    hsub ⟨hδsub hε, hηsub hz⟩ a ha
  have hSchurZero : (0 : ℂ) ∈
      spectrum ℂ (A a - B a * (D a)⁻¹ * C a) := by
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (by
      rw [hS a ha]
      simp [Polynomial.IsRoot])
  have hfactor := fastSlowPencilPolynomial_X_factor
    (A a) (B a) (C a) (D a) (hD a ha) hSchurZero ε
  rw [hfactor, Polynomial.eval_mul, Polynomial.eval_X]
  exact mul_ne_zero hz0 hquot

end

end PhosphorylationStableCapacity
