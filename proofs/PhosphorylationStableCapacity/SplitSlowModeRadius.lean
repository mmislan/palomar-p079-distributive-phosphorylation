module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitSpectrum

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Filter
open scoped Topology

/-- Spectral isolation with an arbitrarily prescribed small neighborhood
    of the neutral eigenvalue. This allows a secant quotient estimate to
    use the same real root that carries the stable transverse spectrum. -/
theorem continuousNeutralMatrix_slowMode_with_radius
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (J : ℝ → Matrix ι ι ℝ) (hJ : ContinuousAt J 0)
    (hspec : SimpleNeutralHurwitzComplement (J 0))
    (η : ℝ) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ η ∧
      ∀ᶠ δ : ℝ in 𝓝 0,
        ∃ x : ℝ,
          |x| < ρ ∧ (J δ).charpoly.IsRoot x ∧
          (((J δ).map (algebraMap ℝ ℂ)).charpoly).derivative.eval
            (x : ℂ) ≠ 0 ∧
          ∀ z : ℂ,
            z ∈ spectrum ℂ ((J δ).map (algebraMap ℝ ℂ)) →
            z.re < 0 ∨ z = (x : ℂ) := by
  obtain ⟨ρu, hρu, huniq⟩ :=
    matrix_complex_slow_root_unique_eventually J hJ hspec
  obtain ⟨ρd, hρd, hderiv⟩ :=
    matrix_complex_slow_root_derivative_near_nonzero_eventually J hJ hspec
  let ρ := min (min ρu ρd) η
  have hρ : 0 < ρ := lt_min (lt_min hρu hρd) hη
  have hρu' : ρ ≤ ρu :=
    le_trans (min_le_left ..) (min_le_left ..)
  have hρd' : ρ ≤ ρd :=
    le_trans (min_le_left ..) (min_le_right ..)
  have hρη : ρ ≤ η := min_le_right ..
  have hcoeff0 : (J 0).charpoly.coeff 0 = 0 :=
    simpleNeutral_real_charpoly_coeff_zero _ hspec
  have hcoeff1 : (J 0).charpoly.coeff 1 ≠ 0 :=
    simpleNeutral_real_charpoly_coeff_one_ne_zero _ hspec
  have hexists := polynomial_simple_zero_real_root_eventually
    (fun δ => (J δ).charpoly) hcoeff0 hcoeff1
    (matrix_real_charpoly_eval_continuousAt J hJ) ρ hρ
  let JC : ℝ → Matrix ι ι ℂ :=
    fun δ => (J δ).map (algebraMap ℝ ℂ)
  have hJC : ContinuousAt JC 0 := by
    have hmap : Continuous (fun M : Matrix ι ι ℝ =>
        M.map (algebraMap ℝ ℂ)) := by fun_prop
    exact hmap.continuousAt.comp hJ
  obtain ⟨p, hfactor, _, hleft⟩ := hspec
  have hsource : ∀ z : ℂ,
      z ∈ spectrum ℂ (JC 0) → z.re < 0 ∨ z = 0 := by
    intro z hz
    have hzroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
    rw [hfactor] at hzroot
    have heval : z * p.eval z = 0 := by
      simpa [JC] using hzroot.eq_zero
    rcases mul_eq_zero.mp heval with hzero | hp
    · exact Or.inr hzero
    · exact Or.inl (hleft z hp)
  have hnear := matrix_family_spectrum_eventually_left_or_near_zero
    JC 0 hJC hsource ρ hρ
  refine ⟨ρ, hρ, hρη, ?_⟩
  filter_upwards [huniq, hderiv, hexists, hnear] with
    δ huniq hderiv hexists hnear
  obtain ⟨x, hx, hroot⟩ := hexists
  have hxC : ‖(x : ℂ)‖ < ρ := by simpa using hx
  have hrootC : (x : ℂ) ∈ spectrum ℂ (JC δ) := by
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    simpa only [JC, Matrix.charpoly_map, ← Complex.coe_algebraMap] using
      (Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) hroot)
  refine ⟨x, hx, hroot,
    hderiv (x : ℂ) (lt_of_lt_of_le hxC hρd'), ?_⟩
  intro z hz
  rcases hnear z hz with hzleft | hznear
  · exact Or.inl hzleft
  · exact Or.inr (huniq z (x : ℂ)
      (lt_of_lt_of_le hznear hρu')
      (lt_of_lt_of_le hxC hρu') hz hrootC)

/-- The actual arbitrary-root network family admits the same slow mode
    and stable transverse spectrum inside any requested small radius. -/
theorem arbitrarySplit_slowMode_with_radius
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hspec : SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (coalescedFinalScaledRates m r τ) ε)
        (fromLoadedCoord (loadedCoordOfState
          (coalescedFiniteState (m+1) r)))))
    (j : Fin (2*(m+1)+1)) (η : ℝ) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ η ∧
      ∀ᶠ δ : ℝ in 𝓝 0,
        ∃ x : ℝ,
          |x| < ρ ∧
          (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (arbitrarySplitRetunedRates m ξ r τ δ ε)
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r δ j)))).charpoly.IsRoot x ∧
          (((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (arbitrarySplitRetunedRates m ξ r τ δ ε)
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r δ j)))).map
                (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
          ∀ z : ℂ,
            z ∈ spectrum ℂ
              ((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
                (arbitrarySplitRetunedRates m ξ r τ δ ε)
                (toCoordinateSpace (chart
                  (arbitrarySplitFiniteState (m+1) ξ r δ j)))).map
                    (algebraMap ℝ ℂ)) →
              z.re < 0 ∨ z = (x : ℂ) := by
  let J : ℝ → Matrix (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2)))
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) ℝ := fun δ =>
    restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (arbitrarySplitRetunedRates m ξ r τ δ ε)
      (toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j)))
  have hJ : ContinuousAt J 0 :=
    arbitrarySplit_restrictedJacobianMatrix_continuousAt
      m ξ r τ ε hr hD₀ hB₀ j
  have hzero : J 0 =
      restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (coalescedFinalScaledRates m r τ) ε)
        (fromLoadedCoord (loadedCoordOfState
          (coalescedFiniteState (m+1) r))) :=
    arbitrarySplit_restrictedJacobianMatrix_zero_eq_coalesced
      m ξ r τ ε j
  have hsource : SimpleNeutralHurwitzComplement (J 0) := by
    rw [hzero]
    exact hspec
  exact continuousNeutralMatrix_slowMode_with_radius J hJ hsource η hη

end
end PhosphorylationStableCapacity
