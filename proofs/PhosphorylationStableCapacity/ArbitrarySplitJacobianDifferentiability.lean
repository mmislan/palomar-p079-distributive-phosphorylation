module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitStateDifferentiability
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitJacobianContinuity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix Polynomial

/-- The literal restricted Jacobian is continuously differentiable in all
    rate and class-coordinate inputs. -/
theorem contDiff_restrictedJacobian_fromVector {n : ℕ}
    (ET FT ST : ℝ) :
    ContDiff ℝ 1 (fun p : RateVector n × CoordinateSpace n =>
      restrictedJacobian ET FT ST (ratesFromVector p.1) p.2) := by
  have hproj : ContDiff ℝ 2
      (fun q : (RateVector n × CoordinateSpace n) × CoordinateSpace n =>
        (q.1.1, q.2)) := by fun_prop
  have hf : ContDiff ℝ 2
      (fun q : (RateVector n × CoordinateSpace n) × CoordinateSpace n =>
        jointRestrictedField ET FT ST (q.1.1, q.2)) :=
    (contDiff_jointRestrictedField ET FT ST).comp hproj
  have hg : ContDiff ℝ 1
      (fun p : RateVector n × CoordinateSpace n => p.2) := by fun_prop
  have h := ContDiff.fderiv
    (f := fun p : RateVector n × CoordinateSpace n =>
      fun u : CoordinateSpace n => jointRestrictedField ET FT ST (p.1, u))
    hf hg (by norm_num)
  simpa only [restrictedJacobian, jointRestrictedField] using h

theorem differentiable_coordinateJacobian_matrix (n : ℕ) :
    Differentiable ℝ
      (fun L : CoordinateSpace n →L[ℝ] CoordinateSpace n =>
        LinearMap.toMatrix (coordinateBasis n) (coordinateBasis n)
          L.toLinearMap) := by
  apply differentiable_pi.mpr
  intro i
  apply differentiable_pi.mpr
  intro j
  have heval : Differentiable ℝ
      (fun L : CoordinateSpace n →L[ℝ] CoordinateSpace n =>
        L (coordinateBasis n j)) :=
    (ContinuousLinearMap.apply ℝ (CoordinateSpace n)
      (coordinateBasis n j)).differentiable
  have hrepr : Differentiable ℝ (fun x : CoordinateSpace n =>
      (coordinateBasis n).repr x i) := by
    let hlin : CoordinateSpace n →ₗ[ℝ] ℝ :=
      (Finsupp.lapply i :
        ((Fin n ⊕ Fin n ⊕ Fin n) →₀ ℝ) →ₗ[ℝ] ℝ).comp
          (coordinateBasis n).repr.toLinearMap
    have hident : (fun x : CoordinateSpace n =>
        (coordinateBasis n).repr x i) = hlin := by
      funext x
      simp [hlin]
    rw [hident]
    exact hlin.toContinuousLinearMap.differentiable
  simpa [Function.comp_def, LinearMap.toMatrix_apply] using
    hrepr.comp heval

theorem arbitrarySplitRetuned_rateVector_differentiableAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1)) :
    DifferentiableAt ℝ
      (fun δ => rateVector (arbitrarySplitRetunedRates m ξ r τ δ ε)) 0 := by
  apply differentiableAt_pi.mpr
  intro j
  apply differentiableAt_pi.mpr
  intro i
  obtain ⟨ha, hb, hc, hα, hβ, hγ⟩ :=
    arbitrarySplitRetunedRates_components_differentiableAt
      m ξ r τ ε hr hD₀ hB₀ i
  fin_cases j <;>
    first
    | simpa [rateVector] using ha
    | simpa [rateVector] using hb
    | simpa [rateVector] using hc
    | simpa [rateVector] using hα
    | simpa [rateVector] using hβ
    | simpa [rateVector] using hγ

theorem arbitrarySplitState_coordinate_differentiableAt
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1)) :
    DifferentiableAt ℝ (fun δ =>
      toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j))) 0 := by
  obtain ⟨hS, _, _, hC, hD⟩ :=
    arbitrarySplitFiniteState_components_differentiableAt
      (m+1) ξ r hr hD₀ j
  exact (differentiableAt_pi.mpr
    (fun i : Fin (m+2) => hS i.succ)).prodMk
      ((differentiableAt_pi.mpr hC).prodMk (differentiableAt_pi.mpr hD))

/-- A matrix-valued differentiability bridge with kinetics and class state
    left abstract, so network-specific rate expressions are elaborated once. -/
theorem restrictedJacobianMatrix_parameter_differentiableAt
    (n : ℕ) (ET FT ST : ℝ)
    (k : ℝ → Rates n) (u : ℝ → CoordinateSpace n)
    (hk : DifferentiableAt ℝ (fun δ => rateVector (k δ)) 0)
    (hu : DifferentiableAt ℝ u 0) :
    DifferentiableAt ℝ (fun δ =>
      restrictedJacobianMatrix ET FT ST (k δ) (u δ)) 0 := by
  have houter : Differentiable ℝ
      (fun p : RateVector n × CoordinateSpace n =>
        restrictedJacobian ET FT ST (ratesFromVector p.1) p.2) :=
    (contDiff_restrictedJacobian_fromVector ET FT ST).differentiable
      (by norm_num)
  have houterAt : DifferentiableAt ℝ
      (fun p : RateVector n × CoordinateSpace n =>
        restrictedJacobian ET FT ST (ratesFromVector p.1) p.2)
      (rateVector (k 0), u 0) := houter.differentiableAt
  have hinput : DifferentiableAt ℝ
      (fun δ => (rateVector (k δ), u δ)) 0 := hk.prodMk hu
  have hjoint : DifferentiableAt ℝ (fun δ =>
      restrictedJacobian ET FT ST
        (ratesFromVector (rateVector (k δ))) (u δ)) 0 :=
    by simpa only [Function.comp_def] using houterAt.comp 0 hinput
  have hjoint' : DifferentiableAt ℝ (fun δ =>
      restrictedJacobian ET FT ST (k δ) (u δ)) 0 := by
    simpa only [ratesFromVector_rateVector] using hjoint
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  have heval : DifferentiableAt ℝ (fun δ =>
      restrictedJacobian ET FT ST (k δ) (u δ)
        (coordinateBasis n j)) 0 :=
    hjoint'.clm_apply (differentiableAt_const _)
  have hrepr : Differentiable ℝ (fun x : CoordinateSpace n =>
      (coordinateBasis n).repr x i) := by
    let hlin : CoordinateSpace n →ₗ[ℝ] ℝ :=
      (Finsupp.lapply i :
        ((Fin n ⊕ Fin n ⊕ Fin n) →₀ ℝ) →ₗ[ℝ] ℝ).comp
          (coordinateBasis n).repr.toLinearMap
    have hident : (fun x : CoordinateSpace n =>
        (coordinateBasis n).repr x i) = hlin := by
      funext x
      simp [hlin]
    rw [hident]
    exact hlin.toContinuousLinearMap.differentiable
  simpa only [restrictedJacobianMatrix, LinearMap.toMatrix_apply,
    ContinuousLinearMap.coe_coe, Function.comp_def] using
      hrepr.differentiableAt.comp 0 heval

theorem arbitrarySplit_restrictedJacobianMatrix_differentiableAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1)) :
    DifferentiableAt ℝ (fun δ =>
      restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (arbitrarySplitRetunedRates m ξ r τ δ ε)
        (toCoordinateSpace (chart
          (arbitrarySplitFiniteState (m+1) ξ r δ j)))) 0 :=
  restrictedJacobianMatrix_parameter_differentiableAt
    (m+2) (2*r) 2 (2*(r+1))
    (fun δ => arbitrarySplitRetunedRates m ξ r τ δ ε)
    (fun δ => toCoordinateSpace (chart
      (arbitrarySplitFiniteState (m+1) ξ r δ j)))
    (arbitrarySplitRetuned_rateVector_differentiableAt
      m ξ r τ ε hr hD₀ hB₀)
    (arbitrarySplitState_coordinate_differentiableAt
      m ξ r hr hD₀ j)

end
end PhosphorylationStableCapacity
