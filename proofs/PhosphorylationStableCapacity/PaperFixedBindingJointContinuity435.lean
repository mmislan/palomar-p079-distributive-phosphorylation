module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingSplitCount435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCoalescence435
public import proofs.PhosphorylationStableCapacity.ArbitraryAllCurrentJointContinuity435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter
open scoped Topology

theorem relaxRates_one {n : ℕ} (k : Rates n) : relaxRates k 1 = k := by
  cases k with
  | mk a b c alpha beta gamma =>
      simp only [relaxRates, div_one]
      congr 1 <;> funext i <;> ring

/-- The paper's fixed-binding rates followed by one fixed relaxation
scale are continuous at any positive unrelaxed kinetic vector. -/
theorem paperFixedBinding_relaxed_rateVector_continuousAt
    {α : Type*} [TopologicalSpace α] {n : ℕ}
    (k : α → Rates n) (t₀ : α) (ε : ℝ)
    (hk : ContinuousAt (fun t => rateVector (k t)) t₀)
    (hpos : (k t₀).Positive) :
    ContinuousAt (fun t =>
      rateVector (relaxRates (paperFixedBindingRates (k t)) ε)) t₀ := by
  apply continuousAt_pi.mpr
  intro j
  apply continuousAt_pi.mpr
  intro i
  have hcoord (q : Fin 6) :
      ContinuousAt (fun t => rateVector (k t) q i) t₀ :=
    continuousAt_pi.mp (continuousAt_pi.mp hk q) i
  have ha : ContinuousAt (fun t => (k t).a i) t₀ := by
    simpa [rateVector] using hcoord 0
  have hb : ContinuousAt (fun t => (k t).b i) t₀ := by
    simpa [rateVector] using hcoord 1
  have hc : ContinuousAt (fun t => (k t).c i) t₀ := by
    simpa [rateVector] using hcoord 2
  have halpha : ContinuousAt (fun t => (k t).alpha i) t₀ := by
    simpa [rateVector] using hcoord 3
  have hbeta : ContinuousAt (fun t => (k t).beta i) t₀ := by
    simpa [rateVector] using hcoord 4
  have hgamma : ContinuousAt (fun t => (k t).gamma i) t₀ := by
    simpa [rateVector] using hcoord 5
  have hbc : (k t₀).b i + (k t₀).c i ≠ 0 :=
    ne_of_gt (add_pos (hpos i).2.1 (hpos i).2.2.1)
  have hbg : (k t₀).beta i + (k t₀).gamma i ≠ 0 :=
    ne_of_gt (add_pos (hpos i).2.2.2.2.1 (hpos i).2.2.2.2.2)
  fin_cases j
  · simpa [rateVector, relaxRates, paperFixedBindingRates,
      sourceBindingP_castSucc] using
      ((continuousAt_const.add hc).mul
        (ha.div (hb.add hc) hbc)).div_const ε
  · simpa [rateVector, relaxRates, paperFixedBindingRates] using
      ((continuousAt_const.add hc).div_const ε).fun_sub hc
  · simpa [rateVector, relaxRates, paperFixedBindingRates] using hc
  · simpa [rateVector, relaxRates, paperFixedBindingRates,
      sourceBindingQ_succ] using
      ((continuousAt_const.add hgamma).mul
        (halpha.div (hbeta.add hgamma) hbg)).div_const ε
  · simpa [rateVector, relaxRates, paperFixedBindingRates] using
      ((continuousAt_const.add hgamma).div_const ε).fun_sub hgamma
  · simpa [rateVector, relaxRates, paperFixedBindingRates] using hgamma

/-- The actual paper split rate vector is jointly continuous in its
independent prefix currents and the splitting parameter at the
coalesced slice. -/
theorem paperFixedBindingSplit_rateVector_joint_continuousAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (ω : PositivePrefixCurrents m) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : (coalescedAllScaledRates m r
      (Fin.lastCases τ ω.val)).Positive) :
    ContinuousAt (fun p : PositivePrefixCurrents m × ℝ =>
      rateVector (paperFixedBindingSplitRates m ξ r p.2 ε
        (Fin.lastCases τ p.1.val))) (ω, 0) := by
  let k : PositivePrefixCurrents m × ℝ → Rates (m+2) := fun p =>
    edgeScaledRates (Fin.lastCases τ p.1.val)
      (arbitrarySplitFiniteRates (m+1) ξ r p.2)
  have hraw : ContinuousAt (fun p => rateVector (k p)) (ω, 0) := by
    have h := arbitrarySplitAllCurrent_rateVector_joint_continuousAt
      m ξ r τ 1 ω hr hD₀ hB₀
    convert h using 1
    funext p
    simp [k, arbitrarySplitAllCurrentRates, relaxRates_one]
  have hzero : k (ω, 0) =
      coalescedAllScaledRates m r (Fin.lastCases τ ω.val) := by
    simp [k, coalescedAllScaledRates,
      arbitrarySplitFiniteRates_zero_eq_coalesced]
  have hp : (k (ω, 0)).Positive := by simpa [hzero] using hbase
  simpa only [paperFixedBindingSplitRates, k] using
    paperFixedBinding_relaxed_rateVector_continuousAt
      k (ω, 0) ε hraw hp

theorem paperFixedBindingSplit_restrictedJacobianMatrix_joint_continuousAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (ω : PositivePrefixCurrents m) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : (coalescedAllScaledRates m r
      (Fin.lastCases τ ω.val)).Positive)
    (j : Fin (2*(m+1)+1)) :
    ContinuousAt (fun p : PositivePrefixCurrents m × ℝ =>
      restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (paperFixedBindingSplitRates m ξ r p.2 ε
          (Fin.lastCases τ p.1.val))
        (toCoordinateSpace (chart
          (arbitrarySplitFiniteState (m+1) ξ r p.2 j)))) (ω, 0) := by
  have hk := paperFixedBindingSplit_rateVector_joint_continuousAt
    m ξ r τ ε ω hr hD₀ hB₀ hbase
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
        (paperFixedBindingSplitRates m ξ r p.2 ε
          (Fin.lastCases τ p.1.val))
        (toCoordinateSpace (chart
          (arbitrarySplitFiniteState (m+1) ξ r p.2 j)))) (ω, 0) := by
    simpa [Function.comp_def, ratesFromVector_rateVector] using h
  exact (continuous_coordinateJacobian_matrix (m+2)).continuousAt.comp hJ

end

end PhosphorylationStableCapacity
