module
public import proofs.PhosphorylationStableCapacity.IntertwinedCharpoly
public import proofs.PhosphorylationStableCapacity.CoalescedWeightedSlowSpectrumBridge

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness
open scoped Topology

noncomputable section

/-- The literal weighted Schur operator has exactly the characteristic
polynomial of the previously analyzed final-column-weighted finite slow
matrix. The actual source supplies all positivity premises eventually. -/
theorem coalescedWeightedSchur_charpoly_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ τ : ℝ,
        let u := loadedCoordOfState (coalescedFiniteState (m + 1) r)
        let k := coalescedFinalScaledRates m r τ
        let x := stateFromLoaded (2 * r) 2 (2 * (r + 1)) u
        ∀ (hpos : x.Positive) (_heq : Equilibrium k x)
          (hρ : ∀ j : Fin (m + 2),
            0 < k.a j * x.S j.castSucc * x.E)
          (hσ : ∀ j : Fin (m + 2),
            0 < k.alpha j * x.S j.succ * x.F),
          (schurLinear
            (loadedBlockA (2 * r) 2 (2 * (r + 1)) k u).toLinearMap
            (loadedBlockB (2 * r) 2 (2 * (r + 1)) k u).toLinearMap
            (loadedBlockC (2 * r) 2 (2 * (r + 1)) k u).toLinearMap
            (fastBindingEquiv x hpos
              (fun j => k.a j * x.S j.castSucc * x.E)
              (fun j => k.alpha j * x.S j.succ * x.F)
              hρ hσ)).charpoly =
                (coalescedFinalWeightedMatrix m r τ).charpoly := by
  filter_upwards [coalescedWeightedSchur_intertwining_eventually m]
    with r hinter
  intro τ u k x hpos heq hρ hσ
  have hchar := charpoly_of_matrix_intertwining
    (schurLinear
      (loadedBlockA (2 * r) 2 (2 * (r + 1)) k u).toLinearMap
      (loadedBlockB (2 * r) 2 (2 * (r + 1)) k u).toLinearMap
      (loadedBlockC (2 * r) 2 (2 * (r + 1)) k u).toLinearMap
      (fastBindingEquiv x hpos
        (fun j => k.a j * x.S j.castSucc * x.E)
        (fun j => k.alpha j * x.S j.succ * x.F)
        hρ hσ))
    (projectedPathIncidence (m + 2))
    ((Matrix.diagonal (coalescedFinalCurrentWeights m τ)) *
      coalescedFullLoadedMatrix m r)
    (projectedPathIncidence_isUnit (m + 2))
    (hinter τ hpos heq hρ hσ)
  exact hchar.trans (coalescedWeightedCurrentMatrix_charpoly m r τ)

/-- For small positive final weight, the literal weighted Schur operator
has a simple zero characteristic factor and a Hurwitz complementary
factor. The positivity witnesses are proved separately for the same
source and rate list. -/
theorem coalescedWeightedSchur_spectrum_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∃ z₀ : Fin (m + 2) → ℝ,
        z₀ (Fin.last (m + 1)) = 1 ∧
        (coalescedFullLoadedMatrix m r).mulVec z₀ = 0 ∧
        ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
          let u := loadedCoordOfState (coalescedFiniteState (m + 1) r)
          let k := coalescedFinalScaledRates m r τ
          let x := stateFromLoaded (2 * r) 2 (2 * (r + 1)) u
          ∀ (hpos : x.Positive) (_heq : Equilibrium k x)
            (hρ : ∀ j : Fin (m + 2),
              0 < k.a j * x.S j.castSucc * x.E)
            (hσ : ∀ j : Fin (m + 2),
              0 < k.alpha j * x.S j.succ * x.F),
            0 < τ ∧
            IsHurwitz (coalescedFinalShearComplement m r τ z₀) ∧
            (coalescedFinalShearComplement m r τ z₀).charpoly.eval 0 ≠ 0 ∧
            (schurLinear
              (loadedBlockA (2 * r) 2 (2 * (r + 1)) k u).toLinearMap
              (loadedBlockB (2 * r) 2 (2 * (r + 1)) k u).toLinearMap
              (loadedBlockC (2 * r) 2 (2 * (r + 1)) k u).toLinearMap
              (fastBindingEquiv x hpos
                (fun j => k.a j * x.S j.castSucc * x.E)
                (fun j => k.alpha j * x.S j.succ * x.F)
                hρ hσ)).charpoly =
                  (coalescedFinalShearComplement m r τ z₀).charpoly *
                    Polynomial.X := by
  filter_upwards [coalescedWeightedCurrentSpectrum_eventually m,
    coalescedWeightedSchur_charpoly_eventually m]
    with r hspec hchar
  obtain ⟨z₀, hzlast, hkernel, hnear⟩ := hspec
  refine ⟨z₀, hzlast, hkernel, ?_⟩
  filter_upwards [hnear] with τ hτ
  intro u k x hpos heq hρ hσ
  obtain ⟨hτpos, hhurwitz, hzero, hrow⟩ := hτ
  rw [coalescedWeightedCurrentMatrix_charpoly] at hrow
  exact ⟨hτpos, hhurwitz, hzero,
    (hchar τ hpos heq hρ hσ).trans hrow⟩

end
end PhosphorylationStableCapacity
