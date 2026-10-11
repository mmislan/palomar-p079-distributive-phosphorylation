module
public import proofs.PhosphorylationStableCapacity.AllCurrentSchurMatrixAction435
public import proofs.PhosphorylationStableCapacity.AllCurrentFiniteSlowSpectrum435
public import proofs.PhosphorylationStableCapacity.IntertwinedCharpoly
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter PhosphorylationSharpness Matrix Polynomial
open scoped Topology

/-- The slow Schur operator of the literal network with an arbitrary
edge-current vector has exactly the characteristic polynomial of the
finite source current matrix with the same vector. -/
theorem coalescedAllSchur_charpoly_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ w : Fin (m+2) → ℝ,
        let u := loadedCoordOfState (coalescedFiniteState (m+1) r)
        let k := coalescedAllScaledRates m r w
        let x := stateFromLoaded (2*r) 2 (2*(r+1)) u
        ∀ (hpos : x.Positive) (_heq : Equilibrium k x)
          (hρ : ∀ j : Fin (m+2), 0 < k.a j * x.S j.castSucc * x.E)
          (hσ : ∀ j : Fin (m+2), 0 < k.alpha j * x.S j.succ * x.F),
          (schurLinear
            (loadedBlockA (2*r) 2 (2*(r+1)) k u).toLinearMap
            (loadedBlockB (2*r) 2 (2*(r+1)) k u).toLinearMap
            (loadedBlockC (2*r) 2 (2*(r+1)) k u).toLinearMap
            (fastBindingEquiv x hpos
              (fun j => k.a j * x.S j.castSucc * x.E)
              (fun j => k.alpha j * x.S j.succ * x.F)
              hρ hσ)).charpoly =
            (coalescedFullLoadedMatrix m r * Matrix.diagonal w).charpoly := by
  filter_upwards [coalescedAllSchur_intertwining_eventually m]
    with r hinter
  intro w u k x hpos heq hρ hσ
  have hchar := charpoly_of_matrix_intertwining
    (schurLinear
      (loadedBlockA (2*r) 2 (2*(r+1)) k u).toLinearMap
      (loadedBlockB (2*r) 2 (2*(r+1)) k u).toLinearMap
      (loadedBlockC (2*r) 2 (2*(r+1)) k u).toLinearMap
      (fastBindingEquiv x hpos
        (fun j => k.a j * x.S j.castSucc * x.E)
        (fun j => k.alpha j * x.S j.succ * x.F)
        hρ hσ))
    (projectedPathIncidence (m+2))
    (Matrix.diagonal w * coalescedFullLoadedMatrix m r)
    (projectedPathIncidence_isUnit (m+2))
    (hinter w hpos heq hρ hσ)
  calc
    _ = (Matrix.diagonal w * coalescedFullLoadedMatrix m r).charpoly := hchar
    _ = (coalescedFullLoadedMatrix m r * Matrix.diagonal w).charpoly :=
      Matrix.charpoly_mul_comm (Matrix.diagonal w) (coalescedFullLoadedMatrix m r)

end

end PhosphorylationStableCapacity
