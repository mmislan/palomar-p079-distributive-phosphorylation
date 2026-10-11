module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingSplitCount435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitJacobianDifferentiability
public import proofs.PhosphorylationStableCapacity.MatrixCharpolyDifferentiability

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix Polynomial

/-- The paper's fixed-binding realization and one fixed relaxation scale
preserve first-order regularity at a positive kinetic vector. -/
theorem paperFixedBinding_relaxed_rateVector_differentiableAt
    {n : ℕ} (k : ℝ → Rates n) (ε : ℝ)
    (hk : DifferentiableAt ℝ (fun δ => rateVector (k δ)) 0)
    (hpos : (k 0).Positive) :
    DifferentiableAt ℝ (fun δ =>
      rateVector (relaxRates (paperFixedBindingRates (k δ)) ε)) 0 := by
  apply differentiableAt_pi.mpr
  intro j
  apply differentiableAt_pi.mpr
  intro i
  have hcoord (q : Fin 6) :
      DifferentiableAt ℝ (fun δ => rateVector (k δ) q i) 0 :=
    (differentiableAt_pi.mp (differentiableAt_pi.mp hk q)) i
  have ha : DifferentiableAt ℝ (fun δ => (k δ).a i) 0 := by
    simpa [rateVector] using hcoord 0
  have hb : DifferentiableAt ℝ (fun δ => (k δ).b i) 0 := by
    simpa [rateVector] using hcoord 1
  have hc : DifferentiableAt ℝ (fun δ => (k δ).c i) 0 := by
    simpa [rateVector] using hcoord 2
  have halpha : DifferentiableAt ℝ (fun δ => (k δ).alpha i) 0 := by
    simpa [rateVector] using hcoord 3
  have hbeta : DifferentiableAt ℝ (fun δ => (k δ).beta i) 0 := by
    simpa [rateVector] using hcoord 4
  have hgamma : DifferentiableAt ℝ (fun δ => (k δ).gamma i) 0 := by
    simpa [rateVector] using hcoord 5
  have hbc : (k 0).b i + (k 0).c i ≠ 0 :=
    ne_of_gt (add_pos (hpos i).2.1 (hpos i).2.2.1)
  have hbg : (k 0).beta i + (k 0).gamma i ≠ 0 :=
    ne_of_gt (add_pos (hpos i).2.2.2.2.1
      (hpos i).2.2.2.2.2)
  fin_cases j
  · simpa [rateVector, relaxRates, paperFixedBindingRates,
      sourceBindingP_castSucc] using
      (((differentiableAt_const _).add hc).mul
        (ha.div (hb.add hc) hbc)).div_const ε
  · change DifferentiableAt ℝ
      (fun δ => (1+(k δ).c i)/ε-(k δ).c i) 0
    convert (((differentiableAt_const _).add hc).div_const ε).sub hc using 1
  · simpa [rateVector, relaxRates, paperFixedBindingRates] using hc
  · simpa [rateVector, relaxRates, paperFixedBindingRates,
      sourceBindingQ_succ] using
      (((differentiableAt_const _).add hgamma).mul
        (halpha.div (hbeta.add hgamma) hbg)).div_const ε
  · change DifferentiableAt ℝ
      (fun δ => (1+(k δ).gamma i)/ε-(k δ).gamma i) 0
    convert (((differentiableAt_const _).add hgamma).div_const ε).sub hgamma using 1
  · simpa [rateVector, relaxRates, paperFixedBindingRates] using hgamma

/-- The literal fixed-binding split kinetics are differentiable at the
coalesced parameter for every fixed independent positive-current vector. -/
theorem paperFixedBindingSplit_rateVector_differentiableAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (ω : Fin (m+1) → ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : (coalescedAllScaledRates m r
      (Fin.lastCases τ ω)).Positive) :
    DifferentiableAt ℝ (fun δ =>
      rateVector (paperFixedBindingSplitRates m ξ r δ ε
        (Fin.lastCases τ ω))) 0 := by
  let k : ℝ → Rates (m+2) := fun δ =>
    edgeScaledRates (Fin.lastCases τ ω)
      (arbitrarySplitFiniteRates (m+1) ξ r δ)
  have hraw : DifferentiableAt ℝ
      (fun δ => rateVector (k δ)) 0 := by
    apply differentiableAt_pi.mpr
    intro q
    apply differentiableAt_pi.mpr
    intro i
    obtain ⟨ha, hb, hc, hα, hβ, hγ⟩ :=
      arbitrarySplitFiniteRates_components_differentiableAt
        (m+1) ξ r hr hD₀ hB₀ i
    fin_cases q
    · change DifferentiableAt ℝ
        (fun δ => Fin.lastCases τ ω i *
          (arbitrarySplitFiniteRates (m+1) ξ r δ).a i) 0
      convert (differentiableAt_const (Fin.lastCases τ ω i)).mul ha using 1
    · change DifferentiableAt ℝ
        (fun δ => Fin.lastCases τ ω i *
          (arbitrarySplitFiniteRates (m+1) ξ r δ).b i) 0
      convert (differentiableAt_const (Fin.lastCases τ ω i)).mul hb using 1
    · change DifferentiableAt ℝ
        (fun δ => Fin.lastCases τ ω i *
          (arbitrarySplitFiniteRates (m+1) ξ r δ).c i) 0
      convert (differentiableAt_const (Fin.lastCases τ ω i)).mul hc using 1
    · change DifferentiableAt ℝ
        (fun δ => Fin.lastCases τ ω i *
          (arbitrarySplitFiniteRates (m+1) ξ r δ).alpha i) 0
      convert (differentiableAt_const (Fin.lastCases τ ω i)).mul hα using 1
    · change DifferentiableAt ℝ
        (fun δ => Fin.lastCases τ ω i *
          (arbitrarySplitFiniteRates (m+1) ξ r δ).beta i) 0
      convert (differentiableAt_const (Fin.lastCases τ ω i)).mul hβ using 1
    · change DifferentiableAt ℝ
        (fun δ => Fin.lastCases τ ω i *
          (arbitrarySplitFiniteRates (m+1) ξ r δ).gamma i) 0
      convert (differentiableAt_const (Fin.lastCases τ ω i)).mul hγ using 1
  have hzero : k 0 =
      coalescedAllScaledRates m r (Fin.lastCases τ ω) := by
    simp [k, coalescedAllScaledRates,
      arbitrarySplitFiniteRates_zero_eq_coalesced]
  have hp : (k 0).Positive := by simpa [hzero] using hbase
  simpa only [paperFixedBindingSplitRates, k] using
    paperFixedBinding_relaxed_rateVector_differentiableAt k ε hraw hp

/-- Each literal class characteristic coefficient of the paper's kinetic
family is differentiable at coalescence. -/
theorem paperFixedBindingSplit_charpoly_coeff_differentiableAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (ω : Fin (m+1) → ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : (coalescedAllScaledRates m r
      (Fin.lastCases τ ω)).Positive)
    (j : Fin (2*(m+1)+1)) (q : ℕ) :
    DifferentiableAt ℝ (fun δ =>
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (paperFixedBindingSplitRates m ξ r δ ε
          (Fin.lastCases τ ω))
        (toCoordinateSpace (chart
          (arbitrarySplitFiniteState (m+1) ξ r δ j)))).charpoly.coeff q) 0 := by
  let J : ℝ → Matrix (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2)))
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) ℝ := fun δ =>
    restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (paperFixedBindingSplitRates m ξ r δ ε
        (Fin.lastCases τ ω))
      (toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j)))
  have hJ : DifferentiableAt ℝ J 0 :=
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
  have hentry (i l) : DifferentiableAt ℝ (fun δ => J δ i l) 0 :=
    (differentiableAt_pi.mp (differentiableAt_pi.mp hJ i)) l
  exact matrix_charpoly_coeff_differentiableAt J hentry q

end
end PhosphorylationStableCapacity
