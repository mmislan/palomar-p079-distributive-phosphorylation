module
public import proofs.PhosphorylationStableCapacity.ContinuousNeutralMatrixFamily435
public import proofs.PhosphorylationStableCapacity.SplitUniformTransverseGap
public import proofs.PhosphorylationStableCapacity.CompactUniformMargin435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial Filter
open scoped Topology Matrix.Norms.L2Operator

/-- A simple-neutral Hurwitz-complement matrix has a local positive
transverse spectral margin under perturbation in any pseudometric
parameter space. The selected real root remains simple and is the only
root outside the common negative half-plane. -/
theorem continuousNeutralMatrix_local_uniform_gap
    {β ι : Type*} [PseudoMetricSpace β]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (J : β → Matrix ι ι ℝ) (b₀ : β)
    (hJ : ContinuousAt J b₀)
    (hspec : SimpleNeutralHurwitzComplement (J b₀)) :
    ∃ α : ℝ, 0 < α ∧
      {b : β | ∃ x : ℝ,
        (J b).charpoly.IsRoot x ∧
          (((J b).map (algebraMap ℝ ℂ)).charpoly).derivative.eval
            (x : ℂ) ≠ 0 ∧
          ∀ z : ℂ,
            z ∈ spectrum ℂ ((J b).map (algebraMap ℝ ℂ)) →
              z = (x : ℂ) ∨ z.re ≤ -α} ∈ 𝓝 b₀ := by
  let P : β → ℂ[X] :=
    fun b => ((J b).map (algebraMap ℝ ℂ)).charpoly
  have hN : 1 < Fintype.card ι + 1 := by
    have hc : 0 < Fintype.card ι :=
      Fintype.card_pos_iff.mpr ‹Nonempty ι›
    omega
  have hdegree (b : β) : (P b).natDegree < Fintype.card ι + 1 := by
    simp [P]
  have hcoeffR (n : ℕ) :
      ContinuousAt (fun b => (J b).charpoly.coeff n) b₀ :=
    (continuousAt_matrix_charpoly_coeff (J b₀) n).comp hJ
  have hcoeff (n : ℕ) :
      ContinuousAt (fun b => (P b).coeff n) b₀ := by
    have hc : ContinuousAt
        (fun b => ((J b).charpoly.coeff n : ℂ)) b₀ :=
      Complex.continuous_ofReal.continuousAt.comp (hcoeffR n)
    simpa only [P, Matrix.charpoly_map, Polynomial.coeff_map,
      ← Complex.coe_algebraMap] using hc
  have hcoeff0 : (J b₀).charpoly.coeff 0 = 0 :=
    simpleNeutral_real_charpoly_coeff_zero _ hspec
  have hcoeff1 : (J b₀).charpoly.coeff 1 ≠ 0 :=
    simpleNeutral_real_charpoly_coeff_one_ne_zero _ hspec
  have hcoeff1C : (P b₀).coeff 1 ≠ 0 := by
    simpa only [P, Matrix.charpoly_map, Polynomial.coeff_map,
      ← Complex.coe_algebraMap] using
      (Complex.ofReal_ne_zero.mpr hcoeff1)
  obtain ⟨ρu, hρu, huniq⟩ :=
    complex_polynomial_family_unique_root_near_zero_at
      P (Fintype.card ι + 1) b₀ hN hdegree hcoeff hcoeff1C
  obtain ⟨ρd, hρd, hderiv⟩ :=
    complex_polynomial_derivative_near_nonzero_at
      P (Fintype.card ι + 1) b₀ hdegree hcoeff hcoeff1C
  let ρ := min ρu ρd
  have hρ : 0 < ρ := lt_min hρu hρd
  have hcont (x : ℝ) :
      ContinuousAt (fun b => (J b).charpoly.eval x) b₀ :=
    (continuousAt_matrix_charpoly_eval (J b₀) x).comp hJ
  have hexists := polynomial_simple_zero_real_root_eventually_at
    (fun b => (J b).charpoly) b₀ hcoeff0 hcoeff1 hcont ρ hρ
  let JC : β → Matrix ι ι ℂ :=
    fun b => (J b).map (algebraMap ℝ ℂ)
  have hJC : ContinuousAt JC b₀ := by
    have hmap : Continuous (fun M : Matrix ι ι ℝ =>
        M.map (algebraMap ℝ ℂ)) := by fun_prop
    exact hmap.continuousAt.comp hJ
  obtain ⟨q, hfactor, hq0, hleft⟩ := hspec
  have hq : q ≠ 0 := by
    intro hzero
    simp [hzero] at hq0
  obtain ⟨γ, hγ, hγgap⟩ :=
    polynomial_left_roots_uniform_gap q hq hleft
  let α := γ/2
  have hα : 0 < α := by dsimp [α]; linarith
  let U : Set ℂ := {z | z.re < -α} ∪ Metric.ball 0 ρ
  have hU : IsOpen U :=
    (isOpen_Iio.preimage Complex.continuous_re).union Metric.isOpen_ball
  have hsource : spectrum ℂ (JC b₀) ⊆ U := by
    intro z hz
    have hzroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
    rw [hfactor] at hzroot
    have heval : z * q.eval z = 0 := by
      simpa [JC] using hzroot.eq_zero
    rcases mul_eq_zero.mp heval with hzero | hqroot
    · exact Or.inr (by
        rw [hzero]
        simpa [Metric.mem_ball, dist_eq_norm] using hρ)
    · exact Or.inl (by
        change z.re < -α
        have h := hγgap z hqroot
        dsimp [α]
        linarith)
  have hnear := hJC.tendsto.eventually
    ((upperHemicontinuous_spectrum ℂ (Matrix ι ι ℂ)).forall_isOpen
      (JC b₀) U hU hsource)
  refine ⟨α, hα, ?_⟩
  filter_upwards [huniq, hderiv, hexists, hnear] with
    b huniq hderiv hexists hnear
  obtain ⟨x, hx, hroot⟩ := hexists
  have hxC : ‖(x : ℂ)‖ < ρ := by simpa using hx
  have hrootC : (x : ℂ) ∈ spectrum ℂ (JC b) := by
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    simpa only [JC, Matrix.charpoly_map, ← Complex.coe_algebraMap]
      using (Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) hroot)
  refine ⟨x, hroot,
    hderiv (x : ℂ) (lt_of_lt_of_le hxC (min_le_right ..)), ?_⟩
  intro z hz
  rcases (show z ∈ U from hnear hz) with hzleft | hznear
  · exact Or.inr (le_of_lt hzleft)
  · have hznorm : ‖z‖ < ρ := by
      simpa only [Metric.mem_ball, dist_zero_right] using hznear
    exact Or.inl (huniq z (x : ℂ)
      (lt_of_lt_of_le hznorm (min_le_left ρu ρd))
      (lt_of_lt_of_le hxC (min_le_left ρu ρd))
      (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz)
      (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hrootC))

/-- The compact family has one negative transverse margin, one split
interval, and one selected simple real root at every current. -/
theorem compact_jointNeutralMatrix_slowMode_uniform_gap
    {β ι : Type*} [PseudoMetricSpace β]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (K : Set β) (hK : IsCompact K)
    (J : β × ℝ → Matrix ι ι ℝ)
    (hJ : ∀ b ∈ K, ContinuousAt J (b, 0))
    (hspec : ∀ b ∈ K, SimpleNeutralHurwitzComplement (J (b, 0))) :
    ∃ α : ℝ, 0 < α ∧
      ∀ᶠ δ : ℝ in 𝓝 0, ∀ b ∈ K,
        ∃ x : ℝ, (J (b, δ)).charpoly.IsRoot x ∧
          (((J (b, δ)).map (algebraMap ℝ ℂ)).charpoly).derivative.eval
            (x : ℂ) ≠ 0 ∧
          ∀ z : ℂ,
            z ∈ spectrum ℂ ((J (b, δ)).map (algebraMap ℝ ℂ)) →
              z = (x : ℂ) ∨ z.re ≤ -α := by
  let P : ℝ → β × ℝ → Prop := fun α p =>
    ∃ x : ℝ, (J p).charpoly.IsRoot x ∧
      (((J p).map (algebraMap ℝ ℂ)).charpoly).derivative.eval
        (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ, z ∈ spectrum ℂ ((J p).map (algebraMap ℝ ℂ)) →
        z = (x : ℂ) ∨ z.re ≤ -α
  have hmono : ∀ {c d : ℝ}, 0 < d → d ≤ c →
      ∀ p, P c p → P d p := by
    intro c d hd hdc p hp
    obtain ⟨x, hx, hs, hrest⟩ := hp
    refine ⟨x, hx, hs, ?_⟩
    intro z hz
    rcases hrest z hz with hsame | hleft
    · exact Or.inl hsame
    · exact Or.inr (by linarith)
  have hloc : ∀ b ∈ K, ∃ α : ℝ, 0 < α ∧
      {p : β × ℝ | P α p} ∈ 𝓝 (b, 0) := by
    intro b hb
    exact continuousNeutralMatrix_local_uniform_gap J (b, 0)
      (hJ b hb) (hspec b hb)
  exact compact_uniform_margin_of_local K hK P hmono hloc

end

end PhosphorylationStableCapacity
