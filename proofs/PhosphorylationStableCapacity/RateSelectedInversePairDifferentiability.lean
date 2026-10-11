module
public import proofs.PhosphorylationStableCapacity.RateCancellationDifference
public import proofs.PhosphorylationStableCapacity.FullDerivative

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

private theorem differentiableAt_pair_pointwise_div {n : ℕ}
    {f g : CoordinateSpace n × CoordinateSpace n → ℝ}
    {p : CoordinateSpace n × CoordinateSpace n}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p)
    (hne : g p ≠ 0) :
    DifferentiableAt ℝ (fun q => f q / g q) p := by
  have hfun : (fun q => f q / g q) = f * g⁻¹ := by
    funext q
    simp [div_eq_mul_inv]
  rw [hfun]
  exact hf.mul (hg.inv hne)

/-- The explicit selected-rate inverse is differentiable jointly in
the positive class state and the requested class velocity. -/
theorem differentiableAt_selectedRateRightInverse_pair {n : ℕ}
    (ET FT ST : ℝ) (u y : CoordinateSpace n)
    (hx : (stateFromLoaded ET FT ST u).Positive) :
    DifferentiableAt ℝ (fun p : CoordinateSpace n × CoordinateSpace n =>
      selectedRateRightInverse (stateFromLoaded ET FT ST p.1) p.2) (u, y) := by
  have hp1 : DifferentiableAt ℝ
      (fun p : CoordinateSpace n × CoordinateSpace n => p.1) (u, y) := by
    fun_prop
  have hp2 : DifferentiableAt ℝ
      (fun p : CoordinateSpace n × CoordinateSpace n => p.2) (u, y) := by
    fun_prop
  have hstate : DifferentiableAt ℝ
      (fun p : CoordinateSpace n × CoordinateSpace n =>
        classEmbedding ET FT ST (fromLoadedCoord p.1)) (u, y) := by
    have hclass : DifferentiableAt ℝ (classEmbedding ET FT ST)
        (fromLoadedCoord u) :=
      (differentiable_classEmbedding ET FT ST).differentiableAt
    have hload : DifferentiableAt ℝ
        (fun p : CoordinateSpace n × CoordinateSpace n =>
          fromLoadedCoord p.1) (u, y) := by
      have heq : ((loadedCoordContinuous n).symm :
          CoordinateSpace n → CoordinateSpace n) = fromLoadedCoord := by
        funext z
        exact loadedCoordContinuous_symm_apply z
      have hlin : DifferentiableAt ℝ (fromLoadedCoord (n := n)) u := by
        rw [← heq]
        exact (loadedCoordContinuous n).symm.differentiableAt
      exact hlin.comp
        (f := fun p : CoordinateSpace n × CoordinateSpace n => p.1)
        (u, y) hp1
    exact hclass.comp
      (f := fun p : CoordinateSpace n × CoordinateSpace n =>
        fromLoadedCoord p.1) (u, y) hload
  have hs (j : Fin (n + 1)) : DifferentiableAt ℝ
      (fun p : CoordinateSpace n × CoordinateSpace n =>
        (stateFromLoaded ET FT ST p.1).S j) (u, y) := by
    simpa [classEmbedding, stateFromLoaded, toFullSpace] using
      (differentiableAt_pi.mp hstate.fst) j
  have he : DifferentiableAt ℝ
      (fun p : CoordinateSpace n × CoordinateSpace n =>
        (stateFromLoaded ET FT ST p.1).E) (u, y) := by
    simpa [classEmbedding, stateFromLoaded, toFullSpace] using
      hstate.snd.fst.fst
  have hf : DifferentiableAt ℝ
      (fun p : CoordinateSpace n × CoordinateSpace n =>
        (stateFromLoaded ET FT ST p.1).F) (u, y) := by
    simpa [classEmbedding, stateFromLoaded, toFullSpace] using
      hstate.snd.fst.snd
  have hc (i : Fin n) : DifferentiableAt ℝ
      (fun p : CoordinateSpace n × CoordinateSpace n =>
        (stateFromLoaded ET FT ST p.1).C i) (u, y) := by
    simpa [classEmbedding, stateFromLoaded, toFullSpace] using
      (differentiableAt_pi.mp hstate.snd.snd.fst) i
  have hR : DifferentiableAt ℝ
      (fun p : CoordinateSpace n × CoordinateSpace n =>
        (projectedPathIncidence n)⁻¹.mulVec p.2.1) (u, y) := by
    let L := (Matrix.mulVecLin (projectedPathIncidence n)⁻¹).toContinuousLinearMap
    have hy : DifferentiableAt ℝ
        (fun p : CoordinateSpace n × CoordinateSpace n => p.2.1) (u, y) :=
      hp2.fst
    have hlin : DifferentiableAt ℝ
        (fun p : CoordinateSpace n × CoordinateSpace n => L p.2.1) (u, y) :=
      L.differentiableAt.comp (u, y) hy
    simpa [L, Matrix.mulVecLin_apply] using hlin
  rcases hx with ⟨hS, hE, hF, hC, _⟩
  have hA : DifferentiableAt ℝ
      (fun p : CoordinateSpace n × CoordinateSpace n =>
        fun i : Fin n =>
          (p.2.2.1 i + (projectedPathIncidence n)⁻¹.mulVec p.2.1 i) /
            ((stateFromLoaded ET FT ST p.1).S i.castSucc *
              (stateFromLoaded ET FT ST p.1).E)) (u, y) := by
    apply differentiableAt_pi.mpr
    intro i
    have hnum : DifferentiableAt ℝ
        (fun p : CoordinateSpace n × CoordinateSpace n =>
          p.2.2.1 i + (projectedPathIncidence n)⁻¹.mulVec p.2.1 i)
        (u, y) :=
      ((differentiableAt_pi.mp hp2.snd.fst) i).add
        ((differentiableAt_pi.mp hR) i)
    have hdenDiff : DifferentiableAt ℝ
        (fun p : CoordinateSpace n × CoordinateSpace n =>
          (stateFromLoaded ET FT ST p.1).S i.castSucc *
          (stateFromLoaded ET FT ST p.1).E) (u, y) :=
      (hs i.castSucc).mul he
    have hden : (stateFromLoaded ET FT ST u).S i.castSucc *
        (stateFromLoaded ET FT ST u).E ≠ 0 :=
      mul_ne_zero (ne_of_gt (hS _)) (ne_of_gt hE)
    exact differentiableAt_pair_pointwise_div hnum hdenDiff hden
  have hC : DifferentiableAt ℝ
      (fun p : CoordinateSpace n × CoordinateSpace n =>
        fun i : Fin n =>
          (projectedPathIncidence n)⁻¹.mulVec p.2.1 i /
            (stateFromLoaded ET FT ST p.1).C i) (u, y) := by
    apply differentiableAt_pi.mpr
    intro i
    have hnum : DifferentiableAt ℝ
        (fun p : CoordinateSpace n × CoordinateSpace n =>
          (projectedPathIncidence n)⁻¹.mulVec p.2.1 i) (u, y) :=
      (differentiableAt_pi.mp hR) i
    exact differentiableAt_pair_pointwise_div hnum (hc i) (ne_of_gt (hC i))
  have hD : DifferentiableAt ℝ
      (fun p : CoordinateSpace n × CoordinateSpace n =>
        fun i : Fin n => p.2.2.2 i /
          ((stateFromLoaded ET FT ST p.1).S i.succ *
            (stateFromLoaded ET FT ST p.1).F)) (u, y) := by
    apply differentiableAt_pi.mpr
    intro i
    have hnum : DifferentiableAt ℝ
        (fun p : CoordinateSpace n × CoordinateSpace n => p.2.2.2 i)
        (u, y) :=
      (differentiableAt_pi.mp hp2.snd.snd) i
    have hdenDiff : DifferentiableAt ℝ
        (fun p : CoordinateSpace n × CoordinateSpace n =>
          (stateFromLoaded ET FT ST p.1).S i.succ *
          (stateFromLoaded ET FT ST p.1).F) (u, y) :=
      (hs i.succ).mul hf
    have hden : (stateFromLoaded ET FT ST u).S i.succ *
        (stateFromLoaded ET FT ST u).F ≠ 0 :=
      mul_ne_zero (ne_of_gt (hS _)) (ne_of_gt hF)
    exact differentiableAt_pair_pointwise_div hnum hdenDiff hden
  simpa [selectedRateRightInverse] using hA.prodMk (hC.prodMk hD)

end
end PhosphorylationStableCapacity
