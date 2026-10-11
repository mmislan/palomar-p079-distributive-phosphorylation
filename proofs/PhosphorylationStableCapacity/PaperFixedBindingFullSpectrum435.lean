module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingSchur435
public import proofs.PhosphorylationStableCapacity.LoadedFastSlowSpectralDock

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter PhosphorylationSharpness Matrix Polynomial
open scoped Topology

/-- The exact `bᵢ=βᵢ=1` lift printed in the manuscript has one simple
zero class-Jacobian mode and a strictly left-half-plane complement,
for every positive independent prefix catalytic-current choice after
the prescribed large-source/small-final-current/small-binding order. -/
theorem paperFixedBindingRestrictedJacobian_spectrum_eventually
    (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (ω : Fin (m+1) → ℝ), (∀ i, 0 < ω i) →
        ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
          ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
            0 < ε →
              let w : Fin (m+2) → ℝ := Fin.lastCases τ ω
              let u := loadedCoordOfState (coalescedFiniteState (m+1) r)
              let k := paperFixedBindingRates (coalescedAllScaledRates m r w)
              let J := (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
                (relaxRates k ε) (fromLoadedCoord u)).map
                  (algebraMap ℝ ℂ)
              ∃ q : ℂ[X], J.charpoly = Polynomial.X * q ∧
                q.eval 0 ≠ 0 ∧
                  ∀ z : ℂ, q.eval z = 0 → z.re < 0 := by
  filter_upwards [coalescedAllCurrentFiniteSlowSpectrum_eventually m,
    paperFixedBindingSchur_charpoly_eventually m,
    coalescedAllSchurPremises_eventually m,
    coalescedAllScaledRates_eventually_source m]
    with r hslow hschur hprem hsource
  intro ω hω
  filter_upwards [hslow ω hω, self_mem_nhdsWithin]
    with τ hτ hτpos
  let w : Fin (m+2) → ℝ := Fin.lastCases τ ω
  have hw : ∀ i : Fin (m+2), 0 < w i := by
    intro i
    cases i using Fin.lastCases with
    | last => simpa [w] using hτpos
    | cast i => simpa [w] using hω i
  let u := loadedCoordOfState (coalescedFiniteState (m+1) r)
  let k₀ := coalescedAllScaledRates m r w
  let k := paperFixedBindingRates k₀
  let x := stateFromLoaded (2*r) 2 (2*(r+1)) u
  obtain ⟨hpos, heq₀, _, _⟩ := hprem w hw
  obtain ⟨hk₀, _⟩ := hsource w hw
  have hk : k.Positive := paperFixedBindingRates_positive k₀ hk₀
  have heq : Equilibrium k x :=
    paperFixedBindingRates_preserves_equilibrium k₀ x hk₀ heq₀
  have hρ : ∀ j : Fin (m+2), 0 < k.a j*x.S j.castSucc*x.E := by
    intro j
    exact mul_pos (mul_pos (hk j).1 (hpos.1 j.castSucc)) hpos.2.1
  have hσ : ∀ j : Fin (m+2), 0 < k.alpha j*x.S j.succ*x.F := by
    intro j
    exact mul_pos (mul_pos (hk j).2.2.2.1 (hpos.1 j.succ)) hpos.2.2.1
  obtain ⟨q, hchar, hq0, hqleft⟩ := hτ
  have hSchur :
      (schurLinear
        (loadedBlockA (2*r) 2 (2*(r+1)) k u).toLinearMap
        (loadedBlockB (2*r) 2 (2*(r+1)) k u).toLinearMap
        (loadedBlockC (2*r) 2 (2*(r+1)) k u).toLinearMap
        (fastBindingEquiv x hpos
          (fun j => k.a j*x.S j.castSucc*x.E)
          (fun j => k.alpha j*x.S j.succ*x.F) hρ hσ)).charpoly =
        q * Polynomial.X := by
    calc
      _ = (coalescedFullLoadedMatrix m r * Matrix.diagonal w).charpoly :=
        hschur w hw hpos heq hρ hσ
      _ = (coalescedPrefixWeightedLoadedMatrix m r ω *
        Matrix.diagonal (coalescedFinalCurrentWeights m τ)).charpoly := by
        rw [coalescedAllCurrentMatrix_eq_prefix_then_final]
      _ = q * Polynomial.X := hchar
  exact loadedRestrictedJacobian_eventually_simple_zero_hurwitz_complement
    (2*r) 2 (2*(r+1)) k u hpos heq hρ hσ q hSchur hq0 hqleft

end

end PhosphorylationStableCapacity
