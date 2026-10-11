module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingDifferentiability
public import proofs.PhosphorylationStableCapacity.LoadedJacobianFirstOrder435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix

/-- Full finite class-Jacobian first-order regularity of the literal
paper family at each positive fixed current. This exports the full
matrix regularity already used internally in the coefficient proof. -/
theorem paperFixedBindingSplit_restrictedJacobian_differentiableAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (ω : Fin (m+1) → ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : (coalescedAllScaledRates m r
      (Fin.lastCases τ ω)).Positive)
    (j : Fin (2*(m+1)+1)) :
    DifferentiableAt ℝ (fun δ =>
      restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (paperFixedBindingSplitRates m ξ r δ ε
          (Fin.lastCases τ ω))
        (toCoordinateSpace (chart
          (arbitrarySplitFiniteState (m+1) ξ r δ j)))) 0 :=
  restrictedJacobianMatrix_parameter_differentiableAt
    (m+2) (2*r) 2 (2*(r+1))
    (fun δ => paperFixedBindingSplitRates m ξ r δ ε
      (Fin.lastCases τ ω))
    (fun δ => toCoordinateSpace (chart
      (arbitrarySplitFiniteState (m+1) ξ r δ j)))
    (paperFixedBindingSplit_rateVector_differentiableAt
      m ξ r τ ε ω hr hD₀ hB₀ hbase)
    (arbitrarySplitState_coordinate_differentiableAt
      m ξ r hr hD₀ j)

theorem paperFixedBindingSplit_loadedJacobian_differentiableAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (ω : Fin (m+1) → ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : (coalescedAllScaledRates m r
      (Fin.lastCases τ ω)).Positive)
    (j : Fin (2*(m+1)+1)) :
    DifferentiableAt ℝ (fun δ =>
      loadedJacobianMatrix (2*r) 2 (2*(r+1))
        (paperFixedBindingSplitRates m ξ r δ ε
          (Fin.lastCases τ ω))
        (loadedCoordOfState
          (arbitrarySplitFiniteState (m+1) ξ r δ j))) 0 := by
  have hrestricted :=
    paperFixedBindingSplit_restrictedJacobian_differentiableAt
      m ξ r τ ε ω hr hD₀ hB₀ hbase j
  have hcoord (δ : ℝ) :
      fromLoadedCoord (loadedCoordOfState
        (arbitrarySplitFiniteState (m+1) ξ r δ j)) =
      toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j)) :=
    from_toLoadedCoord _
  simp_rw [loadedJacobianMatrix_eq_fixed_conjugate, hcoord]
  let A (δ : ℝ) := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
    (paperFixedBindingSplitRates m ξ r δ ε
      (Fin.lastCases τ ω))
    (toCoordinateSpace (chart
      (arbitrarySplitFiniteState (m+1) ξ r δ j)))
  let L := LinearMap.toMatrix (coordinateBasis (m+2))
    (coordinateBasis (m+2)) (loadedCoordLinear (m+2)).toLinearMap
  let R := LinearMap.toMatrix (coordinateBasis (m+2))
    (coordinateBasis (m+2)) (loadedCoordLinear (m+2)).symm.toLinearMap
  have hentry (i q) : DifferentiableAt ℝ (fun δ => A δ i q) 0 :=
    (differentiableAt_pi.mp (differentiableAt_pi.mp hrestricted i)) q
  change DifferentiableAt ℝ (fun δ => L * A δ * R) 0
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro q
  simp only [Matrix.mul_apply]
  apply DifferentiableAt.fun_sum
  intro p hp
  apply DifferentiableAt.mul
  · apply DifferentiableAt.fun_sum
    intro l hl
    exact (differentiableAt_const _).mul (hentry l p)
  · exact differentiableAt_const _

/-- Full-edge formulation used by the all-one and two-at-site positive
probe family. It permits the final catalytic current to vary between
probes while keeping each probe fixed during the split limit. -/
theorem paperFixedBindingSplit_loadedJacobian_differentiableAt_full
    (m : ℕ) (ξ : ℕ → ℝ) (r ε : ℝ)
    (w : Fin (m+2) → ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : (coalescedFiniteRates (m+1) r).Positive)
    (hw : ∀ i, 0 < w i)
    (j : Fin (2*(m+1)+1)) :
    DifferentiableAt ℝ (fun δ =>
      loadedJacobianMatrix (2*r) 2 (2*(r+1))
        (paperFixedBindingSplitRates m ξ r δ ε w)
        (loadedCoordOfState
          (arbitrarySplitFiniteState (m+1) ξ r δ j))) 0 := by
  let τ := w (Fin.last (m+1))
  let ω : Fin (m+1) → ℝ := fun i => w i.castSucc
  have hweta : Fin.lastCases τ ω = w := by
    funext i
    cases i using Fin.lastCases with
    | last => simp [τ, ω]
    | cast i => simp [τ, ω]
  have hscaled : (coalescedAllScaledRates m r
      (Fin.lastCases τ ω)).Positive := by
    rw [hweta]
    exact edgeScaledRates_positive w
      (coalescedFiniteRates (m+1) r) hw hbase
  simpa only [hweta] using
    paperFixedBindingSplit_loadedJacobian_differentiableAt
      m ξ r τ ε ω hr hD₀ hB₀ hscaled j

end

end PhosphorylationStableCapacity
