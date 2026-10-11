module
public import proofs.PhosphorylationStableCapacity.AllCurrentSchurSpectrum435
public import proofs.PhosphorylationStableCapacity.LoadedFastSlowSpectralDock

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter PhosphorylationSharpness Matrix Polynomial
open scoped Topology

/-- A prefix vector followed by a final current `τ` is exactly one
all-edge diagonal scaling of the complete finite source matrix. -/
theorem coalescedAllCurrentMatrix_eq_prefix_then_final
    (m : ℕ) (r τ : ℝ) (ω : Fin (m+1) → ℝ) :
    coalescedFullLoadedMatrix m r *
        Matrix.diagonal (Fin.lastCases τ ω) =
      coalescedPrefixWeightedLoadedMatrix m r ω *
        Matrix.diagonal (coalescedFinalCurrentWeights m τ) := by
  have hw (i : Fin (m+2)) :
      (Fin.lastCases 1 ω i) * coalescedFinalCurrentWeights m τ i =
        Fin.lastCases τ ω i := by
    cases i using Fin.lastCases with
    | last => simp [coalescedFinalCurrentWeights]
    | cast i => simp [coalescedFinalCurrentWeights]
  rw [coalescedPrefixWeightedLoadedMatrix, Matrix.mul_assoc,
    Matrix.diagonal_mul_diagonal]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [hw]
  · simp [hij]

/-- For each positive independent prefix-current vector, a sufficiently
small final current gives the literal slow Schur operator exactly one
simple zero eigenvalue and a Hurwitz complementary factor. -/
theorem coalescedAllCurrentSchurSpectrum_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (ω : Fin (m+1) → ℝ), (∀ i, 0 < ω i) →
        ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
          let w : Fin (m+2) → ℝ := Fin.lastCases τ ω
          let u := loadedCoordOfState (coalescedFiniteState (m+1) r)
          let k := coalescedAllScaledRates m r w
          let x := stateFromLoaded (2*r) 2 (2*(r+1)) u
          ∀ (hpos : x.Positive) (_heq : Equilibrium k x)
            (hρ : ∀ j : Fin (m+2), 0 < k.a j * x.S j.castSucc * x.E)
            (hσ : ∀ j : Fin (m+2), 0 < k.alpha j * x.S j.succ * x.F),
            ∃ q : ℝ[X],
              (schurLinear
                (loadedBlockA (2*r) 2 (2*(r+1)) k u).toLinearMap
                (loadedBlockB (2*r) 2 (2*(r+1)) k u).toLinearMap
                (loadedBlockC (2*r) 2 (2*(r+1)) k u).toLinearMap
                (fastBindingEquiv x hpos
                  (fun j => k.a j * x.S j.castSucc * x.E)
                  (fun j => k.alpha j * x.S j.succ * x.F)
                  hρ hσ)).charpoly = q * Polynomial.X ∧
              q.eval 0 ≠ 0 ∧
                ∀ z : ℂ, (q.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0 := by
  filter_upwards [coalescedAllCurrentFiniteSlowSpectrum_eventually m,
    coalescedAllSchur_charpoly_eventually m] with r hslow hschur
  intro ω hω
  filter_upwards [hslow ω hω] with τ hτ
  intro w u k x hpos heq hρ hσ
  obtain ⟨q, hchar, hq0, hqleft⟩ := hτ
  refine ⟨q, ?_, hq0, hqleft⟩
  calc
    _ = (coalescedFullLoadedMatrix m r * Matrix.diagonal w).charpoly :=
      hschur w hpos heq hρ hσ
    _ = (coalescedPrefixWeightedLoadedMatrix m r ω *
        Matrix.diagonal (coalescedFinalCurrentWeights m τ)).charpoly := by
      rw [coalescedAllCurrentMatrix_eq_prefix_then_final]
    _ = q * Polynomial.X := hchar

end

end PhosphorylationStableCapacity
