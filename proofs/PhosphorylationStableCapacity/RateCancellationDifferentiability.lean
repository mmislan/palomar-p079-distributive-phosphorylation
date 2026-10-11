module
public import proofs.PhosphorylationStableCapacity.RateSelectedResponseInjective
public import proofs.PhosphorylationStableCapacity.FullDerivative

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

private theorem differentiableAt_pointwise_div {n : ℕ}
    {f g : CoordinateSpace n → ℝ} {u : CoordinateSpace n}
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
    (hne : g u ≠ 0) :
    DifferentiableAt ℝ (fun z => f z / g z) u := by
  have hfun : (fun z => f z / g z) = f * g⁻¹ := by
    funext z
    simp [div_eq_mul_inv]
  rw [hfun]
  exact hf.mul (hg.inv hne)

/-- The explicit rate-cancellation graph is differentiable at every
positive class state. -/
theorem differentiableAt_cancellationParameter {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    (hx : (stateFromLoaded ET FT ST u).Positive) :
    DifferentiableAt ℝ (cancellationParameter ET FT ST k) u := by
  have hfield : DifferentiableAt ℝ (loadedRestrictedField ET FT ST k) u :=
    (differentiable_loadedRestrictedField ET FT ST k).differentiableAt
  have hstate : DifferentiableAt ℝ
      (fun z : CoordinateSpace n =>
        classEmbedding ET FT ST (fromLoadedCoord z)) u :=
    have hclass : DifferentiableAt ℝ (classEmbedding ET FT ST)
        (fromLoadedCoord u) :=
      (differentiable_classEmbedding ET FT ST).differentiableAt
    have hload : DifferentiableAt ℝ (fromLoadedCoord (n := n)) u := by
      have hlin : DifferentiableAt ℝ
          ((loadedCoordContinuous n).symm : CoordinateSpace n → CoordinateSpace n) u :=
        (loadedCoordContinuous n).symm.differentiableAt
      have heq : ((loadedCoordContinuous n).symm :
          CoordinateSpace n → CoordinateSpace n) = fromLoadedCoord := by
        funext z
        exact loadedCoordContinuous_symm_apply z
      rwa [heq] at hlin
    hclass.comp u hload
  have hs (j : Fin (n + 1)) : DifferentiableAt ℝ
      (fun z : CoordinateSpace n => (stateFromLoaded ET FT ST z).S j) u := by
    simpa [classEmbedding, stateFromLoaded, toFullSpace] using
      (differentiableAt_pi.mp hstate.fst) j
  have he : DifferentiableAt ℝ
      (fun z : CoordinateSpace n => (stateFromLoaded ET FT ST z).E) u := by
    simpa [classEmbedding, stateFromLoaded, toFullSpace] using
      hstate.snd.fst.fst
  have hf : DifferentiableAt ℝ
      (fun z : CoordinateSpace n => (stateFromLoaded ET FT ST z).F) u := by
    simpa [classEmbedding, stateFromLoaded, toFullSpace] using
      hstate.snd.fst.snd
  have hc (i : Fin n) : DifferentiableAt ℝ
      (fun z : CoordinateSpace n => (stateFromLoaded ET FT ST z).C i) u := by
    simpa [classEmbedding, stateFromLoaded, toFullSpace] using
      (differentiableAt_pi.mp hstate.snd.snd.fst) i
  have hR : DifferentiableAt ℝ
      (fun z : CoordinateSpace n =>
        (projectedPathIncidence n)⁻¹.mulVec
          (-(loadedRestrictedField ET FT ST k z).1)) u := by
    let L := (Matrix.mulVecLin (projectedPathIncidence n)⁻¹).toContinuousLinearMap
    have hlin : DifferentiableAt ℝ
        (fun z : CoordinateSpace n =>
          L (-(loadedRestrictedField ET FT ST k z).1)) u :=
      L.differentiableAt.comp u hfield.fst.neg
    simpa [L, Matrix.mulVecLin_apply] using hlin
  rcases hx with ⟨hS, hE, hF, hC, _⟩
  have hA : DifferentiableAt ℝ
      (fun z : CoordinateSpace n =>
        fun i : Fin n =>
          (-(loadedRestrictedField ET FT ST k z).2.1 i +
            (projectedPathIncidence n)⁻¹.mulVec
              (-(loadedRestrictedField ET FT ST k z).1) i) /
            ((stateFromLoaded ET FT ST z).S i.castSucc *
              (stateFromLoaded ET FT ST z).E)) u := by
    apply differentiableAt_pi.mpr
    intro i
    have hden : (stateFromLoaded ET FT ST u).S i.castSucc *
        (stateFromLoaded ET FT ST u).E ≠ 0 :=
      mul_ne_zero (ne_of_gt (hS _)) (ne_of_gt hE)
    have hnum : DifferentiableAt ℝ
        (fun z : CoordinateSpace n =>
          -(loadedRestrictedField ET FT ST k z).2.1 i +
          (projectedPathIncidence n)⁻¹.mulVec
            (-(loadedRestrictedField ET FT ST k z).1) i) u :=
      (((differentiableAt_pi.mp hfield.snd.fst) i).neg.add
        ((differentiableAt_pi.mp hR) i))
    have hdenDiff : DifferentiableAt ℝ
        (fun z : CoordinateSpace n =>
          (stateFromLoaded ET FT ST z).S i.castSucc *
          (stateFromLoaded ET FT ST z).E) u :=
      (hs i.castSucc).mul he
    exact differentiableAt_pointwise_div hnum hdenDiff hden
  have hC : DifferentiableAt ℝ
      (fun z : CoordinateSpace n =>
        fun i : Fin n =>
          (projectedPathIncidence n)⁻¹.mulVec
            (-(loadedRestrictedField ET FT ST k z).1) i /
            (stateFromLoaded ET FT ST z).C i) u := by
    apply differentiableAt_pi.mpr
    intro i
    have hnum : DifferentiableAt ℝ
        (fun z : CoordinateSpace n =>
          (projectedPathIncidence n)⁻¹.mulVec
            (-(loadedRestrictedField ET FT ST k z).1) i) u :=
      (differentiableAt_pi.mp hR) i
    exact differentiableAt_pointwise_div hnum (hc i) (ne_of_gt (hC i))
  have hD : DifferentiableAt ℝ
      (fun z : CoordinateSpace n =>
        fun i : Fin n =>
          -(loadedRestrictedField ET FT ST k z).2.2 i /
            ((stateFromLoaded ET FT ST z).S i.succ *
              (stateFromLoaded ET FT ST z).F)) u := by
    apply differentiableAt_pi.mpr
    intro i
    have hden : (stateFromLoaded ET FT ST u).S i.succ *
        (stateFromLoaded ET FT ST u).F ≠ 0 :=
      mul_ne_zero (ne_of_gt (hS _)) (ne_of_gt hF)
    have hnum : DifferentiableAt ℝ
        (fun z : CoordinateSpace n =>
          -(loadedRestrictedField ET FT ST k z).2.2 i) u :=
      ((differentiableAt_pi.mp hfield.snd.snd) i).neg
    have hdenDiff : DifferentiableAt ℝ
        (fun z : CoordinateSpace n =>
          (stateFromLoaded ET FT ST z).S i.succ *
          (stateFromLoaded ET FT ST z).F) u :=
      (hs i.succ).mul hf
    exact differentiableAt_pointwise_div hnum hdenDiff hden
  change DifferentiableAt ℝ (fun z => cancellationParameter ET FT ST k z) u
  simpa [cancellationParameter, selectedRateRightInverse] using
    hA.prodMk (hC.prodMk hD)

end
end PhosphorylationStableCapacity
