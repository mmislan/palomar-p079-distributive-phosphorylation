module
public import proofs.PhosphorylationStableCapacity.RateSelectedInversePairDerivative
public import proofs.PhosphorylationStableCapacity.RateCancellationPositiveDomain

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness
open Filter
open scoped Topology

noncomputable section

/-- At a positive equilibrium for a fixed selected rate parameter, the
derivative of the cancellation graph is the negative inverse rate
response composed with the literal class Jacobian. -/
theorem cancellationParameter_fderiv_eq_inverse_jacobian {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u v : CoordinateSpace n)
    (hx : (stateFromLoaded ET FT ST u).Positive)
    (hzero : loadedRestrictedField ET FT ST
      (ratesAdd k (selectedRates v)) u = 0) :
    fderiv ℝ (cancellationParameter ET FT ST k) u =
      -((selectedRateRightInverseLinear
          (stateFromLoaded ET FT ST u)).toContinuousLinearMap.comp
        (fderiv ℝ
          (loadedRestrictedField ET FT ST (ratesAdd k (selectedRates v))) u)) := by
  let F : CoordinateSpace n → CoordinateSpace n :=
    loadedRestrictedField ET FT ST (ratesAdd k (selectedRates v))
  let g : CoordinateSpace n × CoordinateSpace n → CoordinateSpace n :=
    fun q => selectedRateRightInverse (stateFromLoaded ET FT ST q.1) q.2
  let B : CoordinateSpace n →L[ℝ] CoordinateSpace n :=
    (selectedRateRightInverseLinear
      (stateFromLoaded ET FT ST u)).toContinuousLinearMap
  have hF : DifferentiableAt ℝ F u :=
    (differentiable_loadedRestrictedField ET FT ST
      (ratesAdd k (selectedRates v))).differentiableAt
  have hpair : DifferentiableAt ℝ
      (fun z : CoordinateSpace n => (z, F z)) u := by
    fun_prop
  have hg : DifferentiableAt ℝ g (u, 0) :=
    differentiableAt_selectedRateRightInverse_pair ET FT ST u 0 hx
  have hEq :
      (fun z : CoordinateSpace n => cancellationParameter ET FT ST k z - v)
        =ᶠ[𝓝 u]
      (fun z : CoordinateSpace n => -g (z, F z)) := by
    have hU : {z : CoordinateSpace n |
        (stateFromLoaded ET FT ST z).Positive} ∈ 𝓝 u :=
      (isOpen_stateFromLoaded_positive ET FT ST).mem_nhds hx
    filter_upwards [hU] with z hz
    exact cancellationParameter_sub_eq_inverse_field ET FT ST k z v hz
  have hEqD := hEq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_sub_const, fderiv_fun_neg] at hEqD
  have hgAt : DifferentiableAt ℝ g (u, F u) := by
    simpa [F, hzero] using hg
  have hchain := fderiv_comp u hgAt hpair
  simp only [Function.comp_def] at hchain
  have hpairD : fderiv ℝ
      (fun z : CoordinateSpace n => (z, F z)) u =
      (ContinuousLinearMap.id ℝ (CoordinateSpace n)).prod
        (fderiv ℝ F u) := by
    have hid : DifferentiableAt ℝ
        (fun z : CoordinateSpace n => z) u := by fun_prop
    simpa using hid.fderiv_prodMk hF
  apply ContinuousLinearMap.ext
  intro d
  have hd := congrArg
    (fun T : CoordinateSpace n →L[ℝ] CoordinateSpace n => T d) hEqD
  change (fderiv ℝ (cancellationParameter ET FT ST k) u) d =
    -(fderiv ℝ (fun z : CoordinateSpace n => g (z, F z)) u) d at hd
  rw [hchain, hpairD] at hd
  rw [show F u = 0 from hzero] at hd
  let P := (ContinuousLinearMap.id ℝ (CoordinateSpace n)).prod
    (fderiv ℝ F u)
  have hDg := fderiv_selectedRateRightInverse_pair_zero ET FT ST u hx
    (P d)
  change (fderiv ℝ g (u, 0)) (P d) = B (P d).2 at hDg
  simp only [ContinuousLinearMap.comp_apply] at hd
  rw [hDg] at hd
  simpa [F, B, P] using hd

end
end PhosphorylationStableCapacity
