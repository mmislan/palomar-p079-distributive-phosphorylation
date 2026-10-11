module
public import proofs.PhosphorylationStableCapacity.LoadedFastSlowSpectralDock

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter PhosphorylationSharpness Matrix Polynomial
open scoped Topology

/-- The literal coalesced spectral source is an admissible positive mass-action
equilibrium in one positive-total class.  The conclusion is deliberately
neutral in its one slow direction; splitting it is a separate obligation. -/
theorem coalescedAdmissibleSpectralSource_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        ∀ᶠ ε : ℝ in 𝓝 0,
          0 < ε → ε ≤ 1 →
            let x := coalescedFiniteState (m + 1) r
            let k := relaxRates (coalescedFinalScaledRates m r τ) ε
            let u := fromLoadedCoord (loadedCoordOfState x)
            let J := (restrictedJacobianMatrix (2 * r) 2 (2 * (r + 1))
              k u).map (algebraMap ℝ ℂ)
            0 < 2 * r ∧ 0 < (2 : ℝ) ∧ 0 < 2 * (r + 1) ∧
              k.Positive ∧ x.Positive ∧
              Equilibrium k x ∧
              restrictedFieldEuclid (2 * r) 2 (2 * (r + 1)) k u = 0 ∧
              ∃ p : ℂ[X], J.charpoly = Polynomial.X * p ∧
                p.eval 0 ≠ 0 ∧
                ∀ z : ℂ, p.eval z = 0 → z.re < 0 := by
  have hrpos : ∀ᶠ r : ℝ in atTop, 0 < r := eventually_gt_atTop 0
  filter_upwards [hrpos,
    coalescedFiniteState_eventually_equilibrium (m + 1),
    coalescedFinalScaledRates_eventually_source m,
    coalescedWeightedRestrictedJacobian_spectrum_eventually m]
    with r hr hsource hscaled hspec
  have hτpos : ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), 0 < τ := self_mem_nhdsWithin
  filter_upwards [hτpos, hspec] with τ hτ hspecε
  filter_upwards [hspecε] with ε hspec hε hε1
  let x := coalescedFiniteState (m + 1) r
  let k₀ := coalescedFinalScaledRates m r τ
  let k := relaxRates k₀ ε
  let u := fromLoadedCoord (loadedCoordOfState x)
  obtain ⟨_, hxpos, _, hET, hFT, hST⟩ := hsource
  obtain ⟨hk₀, heq₀⟩ := hscaled τ hτ
  have hclass : InClass (2 * r) 2 (2 * (r + 1)) x :=
    ⟨hET, hFT, hST⟩
  have hback : unChart (2 * r) 2 (2 * (r + 1))
      (ofCoordinateSpace u) = x := by
    change stateFromLoaded (2 * r) 2 (2 * (r + 1))
      (loadedCoordOfState x) = x
    exact stateFromLoaded_loadedCoordOfState _ _ _ x hclass
  have hkeq : Equilibrium k x :=
    relaxRates_preserves_equilibrium k₀ x (ne_of_gt hε) heq₀
  have hfield : restrictedFieldEuclid (2 * r) 2 (2 * (r + 1)) k u = 0 :=
    (restrictedFieldEuclid_eq_zero_iff _ _ _ k u).2 (by simpa [hback] using hkeq)
  refine ⟨by positivity, by norm_num, by positivity,
    relaxRates_positive k₀ hk₀ hε hε1, hxpos, hkeq, hfield, ?_⟩
  exact hspec hε

end
end PhosphorylationStableCapacity
