module
public import proofs.PhosphorylationStableCapacity.SplitSlowModeRadius
public import proofs.PhosphorylationStableCapacity.HurwitzSpectralGap

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter Matrix Polynomial
open scoped Topology Matrix.Norms.L2Operator

/-- A nonzero complex polynomial with all roots strictly left has a
    single positive margin for all of its finitely many roots. -/
theorem polynomial_left_roots_uniform_gap
    (q : ℂ[X]) (hq : q ≠ 0)
    (hleft : ∀ z : ℂ, q.eval z = 0 → z.re < 0) :
    ∃ α : ℝ, 0 < α ∧
      ∀ z : ℂ, q.eval z = 0 → z.re ≤ -α := by
  classical
  let S : Set ℂ := {z | q.eval z = 0}
  have hfinite : S.Finite := by
    have heq : S = (q.roots.toFinset : Set ℂ) := by
      ext z
      simp [S, Polynomial.IsRoot, Polynomial.mem_roots hq]
    rw [heq]
    exact q.roots.toFinset.finite_toSet
  rcases S.eq_empty_or_nonempty with hempty | hnonempty
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz
    have hzS : z ∈ S := hz
    rw [hempty] at hzS
    exact hzS.elim
  · obtain ⟨z₀, hz₀, hmin⟩ :=
      Set.exists_min_image S (fun z : ℂ => -z.re) hfinite hnonempty
    have hpos : 0 < -z₀.re := by
      have h := hleft z₀ hz₀
      linarith
    refine ⟨-z₀.re, hpos, ?_⟩
    intro z hz
    have hle := hmin z hz
    linarith

/-- For a simple neutral source with a Hurwitz complement, nearby
    spectra have one common negative margin outside an arbitrary small
    neutral disk. -/
theorem continuousNeutralMatrix_uniform_transverse_gap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ℝ → Matrix ι ι ℝ) (hJ : ContinuousAt J 0)
    (hspec : SimpleNeutralHurwitzComplement (J 0))
    (η : ℝ) (hη : 0 < η) :
    ∃ α : ℝ, 0 < α ∧
      ∀ᶠ δ : ℝ in 𝓝 0,
        ∀ z : ℂ,
          z ∈ spectrum ℂ ((J δ).map (algebraMap ℝ ℂ)) →
            z.re ≤ -α ∨ ‖z‖ < η := by
  obtain ⟨q, hfactor, hq0, hleft⟩ := hspec
  have hq : q ≠ 0 := by
    intro hzero
    simp [hzero] at hq0
  obtain ⟨β, hβ, hβgap⟩ :=
    polynomial_left_roots_uniform_gap q hq hleft
  let α := β/2
  have hα : 0 < α := by dsimp [α]; linarith
  let U : Set ℂ := {z | z.re < -α} ∪ Metric.ball 0 η
  have hU : IsOpen U :=
    (isOpen_Iio.preimage Complex.continuous_re).union Metric.isOpen_ball
  have hsubset : spectrum ℂ ((J 0).map (algebraMap ℝ ℂ)) ⊆ U := by
    intro z hz
    have hzroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
    rw [hfactor] at hzroot
    have heval : z*q.eval z=0 := by
      simpa using hzroot.eq_zero
    rcases mul_eq_zero.mp heval with hzero | hqroot
    · exact Or.inr (by
        rw [hzero]
        simpa [Metric.mem_ball, dist_eq_norm] using hη)
    · exact Or.inl (by
        change z.re < -α
        have h := hβgap z hqroot
        dsimp [α]
        linarith)
  have hJC : ContinuousAt
      (fun δ => (J δ).map (algebraMap ℝ ℂ)) 0 := by
    have hmap : Continuous (fun M : Matrix ι ι ℝ =>
        M.map (algebraMap ℝ ℂ)) := by fun_prop
    exact hmap.continuousAt.comp hJ
  have hnear := hJC.tendsto.eventually
    ((upperHemicontinuous_spectrum ℂ (Matrix ι ι ℂ)).forall_isOpen
      ((J 0).map (algebraMap ℝ ℂ)) U hU hsubset)
  refine ⟨α, hα, ?_⟩
  filter_upwards [hnear] with δ hδ z hz
  rcases hδ hz with hzleft | hzball
  · exact Or.inl (le_of_lt hzleft)
  · exact Or.inr (by
      simpa [Metric.mem_ball, dist_eq_norm] using hzball)

/-- The same selected simple slow root has all other eigenvalues to
    the left of a fixed negative margin for sufficiently small δ. -/
theorem continuousNeutralMatrix_slowMode_with_uniform_gap
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (J : ℝ → Matrix ι ι ℝ) (hJ : ContinuousAt J 0)
    (hspec : SimpleNeutralHurwitzComplement (J 0))
    (η : ℝ) (hη : 0 < η) :
    ∃ ρ α : ℝ, 0 < ρ ∧ ρ ≤ η ∧ 0 < α ∧
      ∀ᶠ δ : ℝ in 𝓝 0,
        ∃ x : ℝ,
          |x| < ρ ∧ (J δ).charpoly.IsRoot x ∧
          (((J δ).map (algebraMap ℝ ℂ)).charpoly).derivative.eval
            (x : ℂ) ≠ 0 ∧
          ∀ z : ℂ,
            z ∈ spectrum ℂ ((J δ).map (algebraMap ℝ ℂ)) →
              z = (x : ℂ) ∨ z.re ≤ -α := by
  obtain ⟨ρu, hρu, huniq⟩ :=
    matrix_complex_slow_root_unique_eventually J hJ hspec
  let η' := min η ρu
  have hη' : 0 < η' := lt_min hη hρu
  obtain ⟨ρ, hρ, hρη', hslow⟩ :=
    continuousNeutralMatrix_slowMode_with_radius J hJ hspec η' hη'
  have hρη : ρ ≤ η := le_trans hρη' (min_le_left ..)
  have hρu : ρ ≤ ρu := le_trans hρη' (min_le_right ..)
  obtain ⟨α, hα, hgap⟩ :=
    continuousNeutralMatrix_uniform_transverse_gap J hJ hspec ρ hρ
  refine ⟨ρ, α, hρ, hρη, hα, ?_⟩
  filter_upwards [hslow, hgap, huniq] with δ hslow hgap huniq
  obtain ⟨x, hx, hroot, hsimple, _⟩ := hslow
  have hxC : ‖(x : ℂ)‖ < ρu := by
    have hnorm : ‖(x : ℂ)‖ = |x| := by simp
    rw [hnorm]
    exact lt_of_lt_of_le hx hρu
  have hxspec : (x : ℂ) ∈ spectrum ℂ
      ((J δ).map (algebraMap ℝ ℂ)) := by
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    simpa only [Matrix.charpoly_map, ← Complex.coe_algebraMap] using
      (Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) hroot)
  refine ⟨x, hx, hroot, hsimple, ?_⟩
  intro z hz
  rcases hgap z hz with hzleft | hznear
  · exact Or.inr hzleft
  · exact Or.inl (huniq z (x : ℂ)
      (lt_of_lt_of_le hznear hρu) hxC hz hxspec)

/-- A single transverse margin works for every requested radius of the
    selected slow root. This is the form needed by the quantitative
    first-order quotient estimate. -/
theorem continuousNeutralMatrix_slowMode_uniform_gap_any_radius
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (J : ℝ → Matrix ι ι ℝ) (hJ : ContinuousAt J 0)
    (hspec : SimpleNeutralHurwitzComplement (J 0)) :
    ∃ α : ℝ, 0 < α ∧
      ∀ η : ℝ, 0 < η →
        ∀ᶠ δ : ℝ in 𝓝 0,
          ∃ x : ℝ,
            |x| < η ∧ (J δ).charpoly.IsRoot x ∧
            (((J δ).map (algebraMap ℝ ℂ)).charpoly).derivative.eval
              (x : ℂ) ≠ 0 ∧
            ∀ z : ℂ,
              z ∈ spectrum ℂ ((J δ).map (algebraMap ℝ ℂ)) →
                z = (x : ℂ) ∨ z.re ≤ -α := by
  obtain ⟨ρu, hρu, huniq⟩ :=
    matrix_complex_slow_root_unique_eventually J hJ hspec
  obtain ⟨α, hα, hgap⟩ :=
    continuousNeutralMatrix_uniform_transverse_gap J hJ hspec ρu hρu
  refine ⟨α, hα, ?_⟩
  intro η hη
  let η' := min η ρu
  have hη' : 0 < η' := lt_min hη hρu
  obtain ⟨ρ, hρ, hρη', hslow⟩ :=
    continuousNeutralMatrix_slowMode_with_radius J hJ hspec η' hη'
  have hρη : ρ ≤ η := le_trans hρη' (min_le_left ..)
  have hρu' : ρ ≤ ρu := le_trans hρη' (min_le_right ..)
  filter_upwards [hslow, hgap, huniq] with δ hslow hgap huniq
  obtain ⟨x, hx, hroot, hsimple, _⟩ := hslow
  have hxC : ‖(x : ℂ)‖ < ρu := by
    have hnorm : ‖(x : ℂ)‖ = |x| := by simp
    rw [hnorm]
    exact lt_of_lt_of_le hx hρu'
  have hxspec : (x : ℂ) ∈ spectrum ℂ
      ((J δ).map (algebraMap ℝ ℂ)) := by
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    simpa only [Matrix.charpoly_map, ← Complex.coe_algebraMap] using
      (Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) hroot)
  refine ⟨x, lt_of_lt_of_le hx hρη, hroot, hsimple, ?_⟩
  intro z hz
  rcases hgap z hz with hzleft | hznear
  · exact Or.inr hzleft
  · exact Or.inl (huniq z (x : ℂ) hznear hxC hz hxspec)

end
end PhosphorylationStableCapacity
