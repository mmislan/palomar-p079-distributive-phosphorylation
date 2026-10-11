module
public import proofs.PhosphorylationStableCapacity.LoadedSchurMatrixBridge
public import proofs.PhosphorylationStableCapacity.LoadedFastBlockHurwitz
public import proofs.PhosphorylationStableCapacity.CoalescedWeightedSchurSpectrum

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix Polynomial Filter
open scoped Topology

/-- The proved Schur and fast-block premises imply a simple neutral mode
and a Hurwitz complement for the literal class-restricted Jacobian after
sufficient binding relaxation. -/
theorem loadedRestrictedJacobian_eventually_simple_zero_hurwitz_complement
    {n : ℕ} (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u))
    (hρ : ∀ j : Fin n,
      0 < k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
        (stateFromLoaded ET FT ST u).E)
    (hσ : ∀ j : Fin n,
      0 < k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
        (stateFromLoaded ET FT ST u).F)
    (q : ℝ[X])
    (hSchur :
      (schurLinear
        (loadedBlockA ET FT ST k u).toLinearMap
        (loadedBlockB ET FT ST k u).toLinearMap
        (loadedBlockC ET FT ST k u).toLinearMap
        (fastBindingEquiv (stateFromLoaded ET FT ST u) hpos
          (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
            (stateFromLoaded ET FT ST u).E)
          (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
            (stateFromLoaded ET FT ST u).F)
          hρ hσ)).charpoly = q * Polynomial.X)
    (hq : q.eval 0 ≠ 0)
    (hqleft : ∀ z : ℂ,
      (q.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0) :
    ∀ᶠ ε : ℝ in 𝓝 0,
      0 < ε →
        let J := (restrictedJacobianMatrix ET FT ST (relaxRates k ε)
          (fromLoadedCoord u)).map (algebraMap ℝ ℂ)
        ∃ r : ℂ[X], J.charpoly = Polynomial.X * r ∧
          r.eval 0 ≠ 0 ∧
          ∀ z : ℂ, r.eval z = 0 → z.re < 0 := by
  let x := stateFromLoaded ET FT ST u
  let ρ : Fin n → ℝ := fun j => k.a j * x.S j.castSucc * x.E
  let σ : Fin n → ℝ := fun j => k.alpha j * x.S j.succ * x.F
  let A := LinearMap.toMatrix (Pi.basisFun ℝ (Fin n))
    (Pi.basisFun ℝ (Fin n))
    (loadedBlockA ET FT ST k u).toLinearMap
  let B := LinearMap.toMatrix (fastBasis n)
    (Pi.basisFun ℝ (Fin n))
    (loadedBlockB ET FT ST k u).toLinearMap
  let C := LinearMap.toMatrix (Pi.basisFun ℝ (Fin n))
    (fastBasis n)
    (loadedBlockC ET FT ST k u).toLinearMap
  let D := fastBindingMatrix n x ρ σ
  have hD : IsHurwitz D := fastBindingMatrix_hurwitz x hpos ρ σ hρ hσ
  have hS : (A - B * D⁻¹ * C).charpoly = q * Polynomial.X := by
    rw [← loadedSchur_charpoly_eq_matrix ET FT ST k u hpos heq hρ hσ]
    exact hSchur
  have htransfer := realFastSlow_eventually_simple_zero_hurwitz_complement
    A B C D hD q hS hq hqleft
  filter_upwards [htransfer] with ε hε hεpos
  have hεne : ε ≠ 0 := ne_of_gt hεpos
  have hblock : loadedJacobianMatrix ET FT ST (relaxRates k ε) u =
      realFastSlowMatrix A B C D ε := by
    rw [loadedJacobianMatrix_relax_eq_realFastSlow ET FT ST k u hεne]
    congr 1
    exact loadedBlockD_toMatrix_eq_fastBinding ET FT ST k u hpos heq
  have hchart := loadedJacobianMatrix_charpoly_eq_restricted
    ET FT ST (relaxRates k ε) u
  have hchar :
      ((realFastSlowMatrix A B C D ε).map (algebraMap ℝ ℂ)).charpoly =
        ((restrictedJacobianMatrix ET FT ST (relaxRates k ε)
          (fromLoadedCoord u)).map (algebraMap ℝ ℂ)).charpoly := by
    rw [← hblock]
    simpa only [Matrix.charpoly_map] using
      congrArg (fun p : ℝ[X] => p.map (algebraMap ℝ ℂ)) hchart
  simpa only [hchar] using hε hεpos

/-- The actual retuned coalesced source has a simple neutral mode and a
Hurwitz complementary class-Jacobian factor after sufficiently fast
binding, for large source parameter and small positive final weight. -/
theorem coalescedWeightedRestrictedJacobian_spectrum_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        ∀ᶠ ε : ℝ in 𝓝 0,
          0 < ε →
            let u := loadedCoordOfState (coalescedFiniteState (m + 1) r)
            let k := coalescedFinalScaledRates m r τ
            let J := (restrictedJacobianMatrix (2 * r) 2 (2 * (r + 1))
              (relaxRates k ε) (fromLoadedCoord u)).map (algebraMap ℝ ℂ)
            ∃ p : ℂ[X], J.charpoly = Polynomial.X * p ∧
              p.eval 0 ≠ 0 ∧
              ∀ z : ℂ, p.eval z = 0 → z.re < 0 := by
  filter_upwards [coalescedWeightedSchur_spectrum_eventually m,
    coalescedWeightedSchurPremises_eventually m] with r hspec hprem
  obtain ⟨z₀, _, _, hspecτ⟩ := hspec
  have hτpositive : ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), 0 < τ :=
    self_mem_nhdsWithin
  filter_upwards [hspecτ, hτpositive] with τ hτ hτpos
  let u := loadedCoordOfState (coalescedFiniteState (m + 1) r)
  let k := coalescedFinalScaledRates m r τ
  let x := stateFromLoaded (2 * r) 2 (2 * (r + 1)) u
  obtain ⟨hpos, heq, hρ, hσ⟩ := hprem τ hτpos
  obtain ⟨_, hhurwitz, hzero, hSchur⟩ := hτ hpos heq hρ hσ
  have hqleft : ∀ z : ℂ,
      ((coalescedFinalShearComplement m r τ z₀).charpoly.map
        (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0 := by
    intro z hz
    apply hhurwitz z
    rw [Matrix.charpoly_map]
    exact hz
  exact loadedRestrictedJacobian_eventually_simple_zero_hurwitz_complement
    (2 * r) 2 (2 * (r + 1)) k u hpos heq hρ hσ
    (coalescedFinalShearComplement m r τ z₀).charpoly
    hSchur hzero hqleft

end
end PhosphorylationStableCapacity
