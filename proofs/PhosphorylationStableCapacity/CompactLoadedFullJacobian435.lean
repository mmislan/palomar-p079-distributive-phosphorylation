module
public import proofs.PhosphorylationStableCapacity.CompactRealFastSlow435
public import proofs.PhosphorylationStableCapacity.LoadedBlockContinuity435
public import proofs.PhosphorylationStableCapacity.LoadedFastSlowSpectralDock

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix Polynomial Filter
open scoped Topology Matrix.Norms.L2Operator

/-- One binding-scale threshold transfers a compact family of exact
finite-rate loaded Schur certificates to the literal class Jacobians. -/
theorem compact_loadedRestrictedJacobian_eventually_simple_zero_hurwitz_complement
    {α : Type*} [TopologicalSpace α] {n : ℕ}
    (K : Set α) (hK : IsCompact K)
    (ET FT ST : ℝ) (u : CoordinateSpace n)
    (k : α → Rates n)
    (hk : Continuous (fun a => rateVector (k a)))
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : ∀ a ∈ K, Equilibrium (k a) (stateFromLoaded ET FT ST u))
    (hρ : ∀ a ∈ K, ∀ j : Fin n,
      0 < (k a).a j * (stateFromLoaded ET FT ST u).S j.castSucc *
        (stateFromLoaded ET FT ST u).E)
    (hσ : ∀ a ∈ K, ∀ j : Fin n,
      0 < (k a).alpha j * (stateFromLoaded ET FT ST u).S j.succ *
        (stateFromLoaded ET FT ST u).F)
    (q : α → ℝ[X])
    (hSchur : ∀ a ∈ K,
      let A := LinearMap.toMatrix (Pi.basisFun ℝ (Fin n))
        (Pi.basisFun ℝ (Fin n))
        (loadedBlockA ET FT ST (k a) u).toLinearMap
      let B := LinearMap.toMatrix (fastBasis n)
        (Pi.basisFun ℝ (Fin n))
        (loadedBlockB ET FT ST (k a) u).toLinearMap
      let C := LinearMap.toMatrix (Pi.basisFun ℝ (Fin n))
        (fastBasis n)
        (loadedBlockC ET FT ST (k a) u).toLinearMap
      let D := LinearMap.toMatrix (fastBasis n) (fastBasis n)
        (loadedBlockD ET FT ST (k a) u).toLinearMap
      (A - B * D⁻¹ * C).charpoly = q a * Polynomial.X)
    (hq : ∀ a ∈ K, (q a).eval 0 ≠ 0)
    (hqleft : ∀ a ∈ K, ∀ z : ℂ,
      ((q a).map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0) :
    ∀ᶠ ε : ℝ in 𝓝 0,
      ∀ a ∈ K, 0 < ε →
        SimpleNeutralHurwitzComplement
          (restrictedJacobianMatrix ET FT ST (relaxRates (k a) ε)
            (fromLoadedCoord u)) := by
  let A : α → Matrix (Fin n) (Fin n) ℝ := fun a =>
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin n))
      (Pi.basisFun ℝ (Fin n))
      (loadedBlockA ET FT ST (k a) u).toLinearMap
  let B : α → Matrix (Fin n) (Fin n ⊕ Fin n) ℝ := fun a =>
    LinearMap.toMatrix (fastBasis n) (Pi.basisFun ℝ (Fin n))
      (loadedBlockB ET FT ST (k a) u).toLinearMap
  let C : α → Matrix (Fin n ⊕ Fin n) (Fin n) ℝ := fun a =>
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (fastBasis n)
      (loadedBlockC ET FT ST (k a) u).toLinearMap
  let D : α → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := fun a =>
    LinearMap.toMatrix (fastBasis n) (fastBasis n)
      (loadedBlockD ET FT ST (k a) u).toLinearMap
  obtain ⟨hA, hB, hC, hDcont⟩ :=
    continuous_loadedJacobianBlocks_of_rateVector ET FT ST u k hk
  have hD : ∀ a ∈ K, IsHurwitz (D a) := by
    intro a ha
    let x := stateFromLoaded ET FT ST u
    let ρ : Fin n → ℝ := fun j => (k a).a j * x.S j.castSucc * x.E
    let σ : Fin n → ℝ := fun j => (k a).alpha j * x.S j.succ * x.F
    have hρa : ∀ j, 0 < ρ j := hρ a ha
    have hσa : ∀ j, 0 < σ j := hσ a ha
    rw [show D a = fastBindingMatrix n x ρ σ by
      exact loadedBlockD_toMatrix_eq_fastBinding
        ET FT ST (k a) u hpos (heq a ha)]
    exact fastBindingMatrix_hurwitz x hpos ρ σ hρa hσa
  have hSc : ∀ a ∈ K,
      (A a - B a * (D a)⁻¹ * C a).charpoly = q a * Polynomial.X :=
    hSchur
  have htransfer := compact_realFastSlow_eventually_simple_zero_hurwitz_complement
    K hK A B C D q hA hB hC hDcont hD hSc hq hqleft
  filter_upwards [htransfer] with ε hε a ha hεpos
  have hεne : ε ≠ 0 := ne_of_gt hεpos
  have hblock : loadedJacobianMatrix ET FT ST (relaxRates (k a) ε) u =
      realFastSlowMatrix (A a) (B a) (C a) (D a) ε := by
    rw [loadedJacobianMatrix_relax_eq_realFastSlow ET FT ST (k a) u hεne]
  have hchart := loadedJacobianMatrix_charpoly_eq_restricted
    ET FT ST (relaxRates (k a) ε) u
  have hchar :
      ((realFastSlowMatrix (A a) (B a) (C a) (D a) ε).map
        (algebraMap ℝ ℂ)).charpoly =
      ((restrictedJacobianMatrix ET FT ST (relaxRates (k a) ε)
        (fromLoadedCoord u)).map (algebraMap ℝ ℂ)).charpoly := by
    rw [← hblock]
    simpa only [Matrix.charpoly_map] using
      congrArg (fun p : ℝ[X] => p.map (algebraMap ℝ ℂ)) hchart
  simpa only [SimpleNeutralHurwitzComplement, hchar] using
    hε a ha hεpos

end

end PhosphorylationStableCapacity
