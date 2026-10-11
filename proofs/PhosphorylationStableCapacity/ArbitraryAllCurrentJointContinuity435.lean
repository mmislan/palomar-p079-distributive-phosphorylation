module
public import proofs.PhosphorylationStableCapacity.ArbitraryAllCurrentContinuity435
public import proofs.PhosphorylationStableCapacity.CompactAllCurrentFiniteSlow435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter
open scoped Topology

/-- At every positive prefix-current vector, the literal split rate
vector is jointly continuous in the currents and split parameter. -/
theorem arbitrarySplitAllCurrent_rateVector_joint_continuousAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (ω : PositivePrefixCurrents m) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1)) :
    ContinuousAt (fun p : PositivePrefixCurrents m × ℝ =>
      rateVector (arbitrarySplitAllCurrentRates m ξ r
        (Fin.lastCases τ p.1.val) p.2 ε)) (ω, 0) := by
  apply continuousAt_pi.mpr
  intro j
  apply continuousAt_pi.mpr
  intro i
  have hw : ContinuousAt
      (fun p : PositivePrefixCurrents m × ℝ =>
        Fin.lastCases (motive := fun _ => ℝ) τ p.1.val i) (ω, 0) := by
    cases i using Fin.lastCases with
    | last => simpa using (continuousAt_const : ContinuousAt
        (fun _ : PositivePrefixCurrents m × ℝ => τ) (ω, 0))
    | cast i =>
        simpa [Function.comp_def] using
          (((continuous_apply i).comp continuous_subtype_val).comp
          continuous_fst).continuousAt
  obtain ⟨ha, hb, hc, hα, hβ, hγ⟩ :=
    arbitrarySplitFiniteRates_components_continuousAt
      (m+1) ξ r hr hD₀ hB₀ i
  have hsnd : ContinuousAt
      (fun p : PositivePrefixCurrents m × ℝ => p.2) (ω, 0) :=
    continuousAt_snd
  have hwa : ContinuousAt (fun p : PositivePrefixCurrents m × ℝ =>
      Fin.lastCases τ p.1.val i *
        (arbitrarySplitFiniteRates (m+1) ξ r p.2).a i) (ω, 0) :=
    hw.mul (ha.comp
      (f := fun p : PositivePrefixCurrents m × ℝ => p.2)
      (x := (ω, 0)) hsnd)
  have hwb : ContinuousAt (fun p : PositivePrefixCurrents m × ℝ =>
      Fin.lastCases τ p.1.val i *
        (arbitrarySplitFiniteRates (m+1) ξ r p.2).b i) (ω, 0) :=
    hw.mul (hb.comp
      (f := fun p : PositivePrefixCurrents m × ℝ => p.2)
      (x := (ω, 0)) hsnd)
  have hwc : ContinuousAt (fun p : PositivePrefixCurrents m × ℝ =>
      Fin.lastCases τ p.1.val i *
        (arbitrarySplitFiniteRates (m+1) ξ r p.2).c i) (ω, 0) :=
    hw.mul (hc.comp
      (f := fun p : PositivePrefixCurrents m × ℝ => p.2)
      (x := (ω, 0)) hsnd)
  have hwα : ContinuousAt (fun p : PositivePrefixCurrents m × ℝ =>
      Fin.lastCases τ p.1.val i *
        (arbitrarySplitFiniteRates (m+1) ξ r p.2).alpha i) (ω, 0) :=
    hw.mul (hα.comp
      (f := fun p : PositivePrefixCurrents m × ℝ => p.2)
      (x := (ω, 0)) hsnd)
  have hwβ : ContinuousAt (fun p : PositivePrefixCurrents m × ℝ =>
      Fin.lastCases τ p.1.val i *
        (arbitrarySplitFiniteRates (m+1) ξ r p.2).beta i) (ω, 0) :=
    hw.mul (hβ.comp
      (f := fun p : PositivePrefixCurrents m × ℝ => p.2)
      (x := (ω, 0)) hsnd)
  have hwγ : ContinuousAt (fun p : PositivePrefixCurrents m × ℝ =>
      Fin.lastCases τ p.1.val i *
        (arbitrarySplitFiniteRates (m+1) ξ r p.2).gamma i) (ω, 0) :=
    hw.mul (hγ.comp
      (f := fun p : PositivePrefixCurrents m × ℝ => p.2)
      (x := (ω, 0)) hsnd)
  fin_cases j
  · simpa [rateVector, arbitrarySplitAllCurrentRates, relaxRates,
      edgeScaledRates] using hwa.div_const ε
  · change ContinuousAt
      ((fun p : PositivePrefixCurrents m × ℝ =>
        (Fin.lastCases τ p.1.val i *
          (arbitrarySplitFiniteRates (m+1) ξ r p.2).b i +
          Fin.lastCases τ p.1.val i *
            (arbitrarySplitFiniteRates (m+1) ξ r p.2).c i) / ε) -
        (fun p : PositivePrefixCurrents m × ℝ =>
          Fin.lastCases τ p.1.val i *
            (arbitrarySplitFiniteRates (m+1) ξ r p.2).c i)) (ω, 0)
    exact ((hwb.add hwc).div_const ε).sub hwc
  · simpa [rateVector, arbitrarySplitAllCurrentRates, relaxRates,
      edgeScaledRates] using hwc
  · simpa [rateVector, arbitrarySplitAllCurrentRates, relaxRates,
      edgeScaledRates] using hwα.div_const ε
  · change ContinuousAt
      ((fun p : PositivePrefixCurrents m × ℝ =>
        (Fin.lastCases τ p.1.val i *
          (arbitrarySplitFiniteRates (m+1) ξ r p.2).beta i +
          Fin.lastCases τ p.1.val i *
            (arbitrarySplitFiniteRates (m+1) ξ r p.2).gamma i) / ε) -
        (fun p : PositivePrefixCurrents m × ℝ =>
          Fin.lastCases τ p.1.val i *
            (arbitrarySplitFiniteRates (m+1) ξ r p.2).gamma i)) (ω, 0)
    exact ((hwβ.add hwγ).div_const ε).sub hwγ
  · simpa [rateVector, arbitrarySplitAllCurrentRates, relaxRates,
      edgeScaledRates] using hwγ

/-- The literal compatibility-class Jacobian varies jointly with every
independent prefix current and the root-splitting parameter at the
coalesced compact-current slice. -/
theorem arbitrarySplitAllCurrent_restrictedJacobianMatrix_joint_continuousAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (ω : PositivePrefixCurrents m) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1)) :
    ContinuousAt (fun p : PositivePrefixCurrents m × ℝ =>
      restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (arbitrarySplitAllCurrentRates m ξ r
          (Fin.lastCases τ p.1.val) p.2 ε)
        (toCoordinateSpace (chart
          (arbitrarySplitFiniteState (m+1) ξ r p.2 j)))) (ω, 0) := by
  have hk := arbitrarySplitAllCurrent_rateVector_joint_continuousAt
    m ξ r τ ε ω hr hD₀ hB₀
  have hu : ContinuousAt (fun p : PositivePrefixCurrents m × ℝ =>
      toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r p.2 j))) (ω, 0) := by
    exact (arbitrarySplitState_coordinate_continuousAt
      m ξ r hr hD₀ j).comp
        (f := fun p : PositivePrefixCurrents m × ℝ => p.2)
        (x := (ω, 0)) continuousAt_snd
  have h := (continuous_restrictedJacobian_fromVector
    (n := m+2) (2*r) 2 (2*(r+1))).continuousAt.comp (hk.prodMk hu)
  have hJ : ContinuousAt (fun p : PositivePrefixCurrents m × ℝ =>
      restrictedJacobian (2*r) 2 (2*(r+1))
        (arbitrarySplitAllCurrentRates m ξ r
          (Fin.lastCases τ p.1.val) p.2 ε)
        (toCoordinateSpace (chart
          (arbitrarySplitFiniteState (m+1) ξ r p.2 j)))) (ω, 0) := by
    simpa [Function.comp_def, ratesFromVector_rateVector] using h
  exact (continuous_coordinateJacobian_matrix (m+2)).continuousAt.comp hJ

end

end PhosphorylationStableCapacity
