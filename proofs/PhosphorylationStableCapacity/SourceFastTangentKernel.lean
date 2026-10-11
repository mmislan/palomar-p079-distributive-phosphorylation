module
public import proofs.PhosphorylationStableCapacity.SourceProjectedFastDerivative
public import proofs.PhosphorylationStableCapacity.SourceProjectedSlowDerivative
public import proofs.PhosphorylationStableCapacity.LoadedJacobianBlockAction
public import proofs.PhosphorylationStableCapacity.LoadedFieldDifferentiability

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The literal fixed-class loaded Jacobian on a compensated binding
tangent has the incidence-assembled current derivative and zero fast
action. -/
theorem equilibrium_sourceBindingTangent_loadedFderiv_action {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) (j : Fin n) :
    let A := (totalAndLevelOutputMatrix n) *
      loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
        (totalE x) (totalF x)
    let σ := firstPivotFixedTangent A j
    let v := sourceBindingLoadedCoordinateTangent k x σ
    fderiv ℝ (loadedRestrictedField (totalE x) (totalF x)
      (totalS x) k) (loadedCoordOfState x) v =
      ((projectedPathIncidence n).mulVec
        (fun e => sourceConstrainedCurrentDerivative k x e j),
        (0 : FastSpace n)) := by
  dsimp only
  let A := (totalAndLevelOutputMatrix n) *
    loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
      (totalE x) (totalF x)
  let σ := firstPivotFixedTangent A j
  let v := sourceBindingLoadedCoordinateTangent k x σ
  let u : ℝ → CoordinateSpace n := fun t =>
    loadedCoordOfState (bindingState (totalE x) (totalF x)
      (sourceBindingP k) (sourceBindingQ k)
      (bindingLinearPath x.S σ t))
  have hpath0 : bindingLinearPath x.S σ 0 = x.S := by
    funext l
    simp [bindingLinearPath]
  have hbase : u 0 = loadedCoordOfState x := by
    change loadedCoordOfState (bindingState (totalE x) (totalF x)
      (sourceBindingP k) (sourceBindingQ k)
      (bindingLinearPath x.S σ 0)) = loadedCoordOfState x
    rw [hpath0, equilibrium_bindingState_eq_source k x hk hx heq]
  have hpath : HasDerivAt u v 0 :=
    equilibrium_sourceBindingLoadedCoordinate_hasDerivAt
      k x hk hx heq σ
  have hfield : HasDerivAt (fun t : ℝ =>
      loadedRestrictedField (totalE x) (totalF x) (totalS x)
        k (u t))
      (fderiv ℝ (loadedRestrictedField (totalE x) (totalF x)
        (totalS x) k) (u 0) v) 0 := by
    simpa only [Function.comp_def] using
      (((differentiable_loadedRestrictedField (totalE x)
        (totalF x) (totalS x) k).differentiableAt
        (x := u 0)).hasFDerivAt.comp_hasDerivAt 0 hpath)
  have hfast : HasDerivAt (fun t : ℝ =>
      (loadedRestrictedField (totalE x) (totalF x) (totalS x)
        k (u t)).2) (0 : FastSpace n) 0 :=
    equilibrium_sourceProjectedFast_hasDerivAt_zero
      k x hk hx heq j
  have hslow : HasDerivAt (fun t : ℝ =>
      (loadedRestrictedField (totalE x) (totalF x) (totalS x)
        k (u t)).1)
      ((projectedPathIncidence n).mulVec
        (fun e => sourceConstrainedCurrentDerivative k x e j)) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    exact equilibrium_sourceProjectedSlow_hasDerivAt
      k x hk hx heq j i
  have hboth : HasDerivAt (fun t : ℝ =>
      loadedRestrictedField (totalE x) (totalF x) (totalS x)
        k (u t))
      ((projectedPathIncidence n).mulVec
        (fun e => sourceConstrainedCurrentDerivative k x e j),
        (0 : FastSpace n)) 0 := by
    simpa using hslow.prodMk hfast
  have heqFull := hfield.unique hboth
  rw [hbase] at heqFull
  exact heqFull

/-- The literal binding-manifold tangent solves the fast block's
linearized complex-balance equation in the fixed loaded class chart. -/
theorem equilibrium_sourceBindingFastTangent_kernel {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) (j : Fin n) :
    let A := (totalAndLevelOutputMatrix n) *
      loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
        (totalE x) (totalF x)
    let σ := firstPivotFixedTangent A j
    let v := sourceBindingLoadedCoordinateTangent k x σ
    loadedBlockC (totalE x) (totalF x) (totalS x) k
      (loadedCoordOfState x) v.1 +
      loadedBlockD (totalE x) (totalF x) (totalS x) k
        (loadedCoordOfState x) v.2 = 0 := by
  have h := equilibrium_sourceBindingTangent_loadedFderiv_action
    k x hk hx heq j
  dsimp only at h ⊢
  let A := (totalAndLevelOutputMatrix n) *
    loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
      (totalE x) (totalF x)
  let σ := firstPivotFixedTangent A j
  let v := sourceBindingLoadedCoordinateTangent k x σ
  have hblock := loadedFderiv_block_action
    (totalE x) (totalF x) (totalS x) k
    (loadedCoordOfState x) v.1 v.2
  have hv : (v.1, v.2) = v := rfl
  rw [hv] at hblock
  exact (congrArg Prod.snd hblock).symm.trans (congrArg Prod.snd h)

end
end PhosphorylationStableCapacity
