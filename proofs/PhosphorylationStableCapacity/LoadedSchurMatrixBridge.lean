module
public import proofs.PhosphorylationStableCapacity.LoadedJacobianCharpolyBridge
public import proofs.PhosphorylationStableCapacity.SchurMatrixToMatrix
public import proofs.PhosphorylationStableCapacity.FastBindingInverse

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix Module

/-- The literal loaded-coordinate Schur operator has the characteristic
polynomial of the explicit four-block matrix Schur complement. -/
theorem loadedSchur_charpoly_eq_matrix {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u))
    (hρ : ∀ j : Fin n,
      0 < k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
        (stateFromLoaded ET FT ST u).E)
    (hσ : ∀ j : Fin n,
      0 < k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
        (stateFromLoaded ET FT ST u).F) :
    let x := stateFromLoaded ET FT ST u
    let ρ : Fin n → ℝ := fun j => k.a j * x.S j.castSucc * x.E
    let σ : Fin n → ℝ := fun j => k.alpha j * x.S j.succ * x.F
    (schurLinear
      (loadedBlockA ET FT ST k u).toLinearMap
      (loadedBlockB ET FT ST k u).toLinearMap
      (loadedBlockC ET FT ST k u).toLinearMap
      (fastBindingEquiv x hpos ρ σ hρ hσ)).charpoly =
      (LinearMap.toMatrix (Pi.basisFun ℝ (Fin n))
        (Pi.basisFun ℝ (Fin n))
        (loadedBlockA ET FT ST k u).toLinearMap -
        LinearMap.toMatrix (fastBasis n)
          (Pi.basisFun ℝ (Fin n))
          (loadedBlockB ET FT ST k u).toLinearMap *
          (fastBindingMatrix n x ρ σ)⁻¹ *
          LinearMap.toMatrix (Pi.basisFun ℝ (Fin n))
            (fastBasis n)
            (loadedBlockC ET FT ST k u).toLinearMap).charpoly := by
  dsimp only
  have hDlin :
      (fastBindingEquiv (stateFromLoaded ET FT ST u) hpos
        (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
          (stateFromLoaded ET FT ST u).E)
        (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
          (stateFromLoaded ET FT ST u).F)
        hρ hσ).toLinearMap =
        (loadedBlockD ET FT ST k u).toLinearMap := by
    apply LinearMap.ext
    intro v
    simpa [loadedBlockD, fastEmbed, fastBindingEquiv_apply] using
      (loadedFastBlock_eq_fastBinding ET FT ST k u v hpos heq).symm
  have hchar := schurLinear_charpoly_eq_matrix
    (Pi.basisFun ℝ (Fin n)) (fastBasis n)
    (loadedBlockA ET FT ST k u).toLinearMap
    (loadedBlockB ET FT ST k u).toLinearMap
    (loadedBlockC ET FT ST k u).toLinearMap
    (fastBindingEquiv (stateFromLoaded ET FT ST u) hpos
      (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
        (stateFromLoaded ET FT ST u).E)
      (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
        (stateFromLoaded ET FT ST u).F)
      hρ hσ)
  rw [hDlin,
    loadedBlockD_toMatrix_eq_fastBinding ET FT ST k u hpos heq] at hchar
  exact hchar

end
end PhosphorylationStableCapacity
