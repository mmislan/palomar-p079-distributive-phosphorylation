module
public import proofs.PhosphorylationStableCapacity.CoalescedLoadedCoordinatePathDerivative
public import proofs.PhosphorylationStableCapacity.CoalescedProjectedFastDerivative
public import proofs.PhosphorylationStableCapacity.CoalescedInverseReducedDerivative
public import proofs.PhosphorylationStableCapacity.LoadedProjectionSlowField
public import proofs.PhosphorylationStableCapacity.LoadedFieldDifferentiability
public import proofs.PhosphorylationStableCapacity.CoalescedBindingStateIdentity

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- Incidence assembly of the exact finite current-matrix response to an
arbitrary inverse-loaded-mass forcing, in the nonzero loaded levels. -/
def coalescedInverseSlowAction (m : ℕ) (r : ℝ)
    (q : Fin (m + 3) → ℝ) : Fin (m + 2) → ℝ :=
  fun j => ∑ i : Fin (m + 2),
    ((if i.succ = j.succ then
      (coalescedCurrentJacobianMatrix m r).mulVec
        (coalescedInverseResponse m r q) i else 0) -
    (if i.castSucc = j.succ then
      (coalescedCurrentJacobianMatrix m r).mulVec
        (coalescedInverseResponse m r q) i else 0))

/-- The literal fixed-class loaded Jacobian, evaluated on the actual
coalesced inverse-response binding tangent, has the finite incidence slow
action and zero fast action. This is the model-specific derivative chain
rule needed before Schur elimination. -/
theorem coalescedLoadedFderiv_inverseResponse_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (q : Fin (m + 3) → ℝ),
        (∑ k, q k) = 0 →
        fderiv ℝ
          (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
            (coalescedFiniteRates (m + 1) r))
          (loadedCoordOfState (coalescedFiniteState (m + 1) r))
          (coalescedBindingCoordTangent m r q) =
            (coalescedInverseSlowAction m r q,
              (0 : (Fin (m + 2) → ℝ) × (Fin (m + 2) → ℝ))) := by
  filter_upwards [coalescedLoadedCoordPath_eventually_hasDerivAt m,
    coalescedProjectedFast_eventually_hasDerivAt_zero m,
    coalescedInverseReducedSlow_eventually_hasDerivAt m,
    coalescedBindingState_eventually_eq_finiteState m]
    with r hcoord hfast hslow hstate
  intro q hq
  let u : ℝ → CoordinateSpace (m + 2) := fun t =>
    loadedCoordOfState (bindingState (2 * r) 2
      (coalescedBindingP m r) (coalescedBindingQ m r)
      (bindingLinearPath (coalescedFiniteState (m + 1) r).S
        (coalescedInverseResponse m r q) t))
  have hpath0 : bindingLinearPath (coalescedFiniteState (m + 1) r).S
      (coalescedInverseResponse m r q) 0 =
        (coalescedFiniteState (m + 1) r).S := by
    funext j
    simp [bindingLinearPath]
  have hbase : u 0 =
      loadedCoordOfState (coalescedFiniteState (m + 1) r) := by
    change loadedCoordOfState (bindingState (2 * r) 2
      (coalescedBindingP m r) (coalescedBindingQ m r)
      (bindingLinearPath (coalescedFiniteState (m + 1) r).S
        (coalescedInverseResponse m r q) 0)) = _
    rw [hpath0, hstate]
  have hpath : HasDerivAt u (coalescedBindingCoordTangent m r q) 0 :=
    hcoord q
  have hfield : HasDerivAt (fun t : ℝ =>
      loadedRestrictedField (2 * r) 2 (2 * (r + 1))
        (coalescedFiniteRates (m + 1) r) (u t))
      (fderiv ℝ
        (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
          (coalescedFiniteRates (m + 1) r))
        (u 0) (coalescedBindingCoordTangent m r q)) 0 := by
    simpa only [Function.comp_def] using
      (((differentiable_loadedRestrictedField (2 * r) 2 (2 * (r + 1))
        (coalescedFiniteRates (m + 1) r)).differentiableAt
        (x := u 0)).hasFDerivAt.comp_hasDerivAt 0 hpath)
  have hs : HasDerivAt (fun t : ℝ =>
      (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
        (coalescedFiniteRates (m + 1) r) (u t)).1)
      (coalescedInverseSlowAction m r q) 0 := by
    apply hasDerivAt_pi.mpr
    intro j
    simpa only [u, coalescedInverseSlowAction,
      loadedRestrictedField_bindingState_slow] using
        hslow q j.succ
  have hf : HasDerivAt (fun t : ℝ =>
      (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
        (coalescedFiniteRates (m + 1) r) (u t)).2)
      (0 : (Fin (m + 2) → ℝ) × (Fin (m + 2) → ℝ)) 0 := by
    simpa only [u] using hfast q hq
  have hboth : HasDerivAt (fun t : ℝ =>
      loadedRestrictedField (2 * r) 2 (2 * (r + 1))
        (coalescedFiniteRates (m + 1) r) (u t))
      (coalescedInverseSlowAction m r q,
        (0 : (Fin (m + 2) → ℝ) × (Fin (m + 2) → ℝ))) 0 := by
    simpa using hs.prodMk hf
  have heq := hfield.unique hboth
  rw [hbase] at heq
  exact heq

end
end PhosphorylationStableCapacity
