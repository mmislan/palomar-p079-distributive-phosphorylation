module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingSplitCount435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitRatesAnalytic
public import proofs.PhosphorylationStableCapacity.AnalyticRestrictedJacobian
public import proofs.PhosphorylationStableCapacity.MatrixCharpolyAnalytic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix Polynomial

/-- Fixed binding followed by binding relaxation preserves analytic
dependence on a parameter near any positive source kinetic vector. -/
theorem paperFixedBinding_relaxed_rateVector_analyticAt
    {n : ℕ} (k : ℝ → Rates n) (ε : ℝ)
    (hk : AnalyticAt ℝ (fun δ => rateVector (k δ)) 0)
    (hpos : (k 0).Positive) :
    AnalyticAt ℝ (fun δ =>
      rateVector (relaxRates (paperFixedBindingRates (k δ)) ε)) 0 := by
  apply analyticAt_pi_iff.mpr
  intro j
  apply analyticAt_pi_iff.mpr
  intro i
  have hcoord (q : Fin 6) :
      AnalyticAt ℝ (fun δ => rateVector (k δ) q i) 0 :=
    (analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hk q)) i
  have ha : AnalyticAt ℝ (fun δ => (k δ).a i) 0 := by
    simpa [rateVector] using hcoord 0
  have hb : AnalyticAt ℝ (fun δ => (k δ).b i) 0 := by
    simpa [rateVector] using hcoord 1
  have hc : AnalyticAt ℝ (fun δ => (k δ).c i) 0 := by
    simpa [rateVector] using hcoord 2
  have halpha : AnalyticAt ℝ (fun δ => (k δ).alpha i) 0 := by
    simpa [rateVector] using hcoord 3
  have hbeta : AnalyticAt ℝ (fun δ => (k δ).beta i) 0 := by
    simpa [rateVector] using hcoord 4
  have hgamma : AnalyticAt ℝ (fun δ => (k δ).gamma i) 0 := by
    simpa [rateVector] using hcoord 5
  have hbc : (k 0).b i + (k 0).c i ≠ 0 :=
    ne_of_gt (add_pos (hpos i).2.1 (hpos i).2.2.1)
  have hbg : (k 0).beta i + (k 0).gamma i ≠ 0 :=
    ne_of_gt (add_pos (hpos i).2.2.2.2.1
      (hpos i).2.2.2.2.2)
  fin_cases j
  · simpa [rateVector, relaxRates, paperFixedBindingRates,
      sourceBindingP_castSucc] using
      (((analyticAt_const).add hc).mul
        (ha.div (hb.add hc) hbc)).div_const
  · change AnalyticAt ℝ
      (fun δ => (1+(k δ).c i)/ε-(k δ).c i) 0
    exact (((analyticAt_const).add hc).div_const).sub hc
  · simpa [rateVector, relaxRates, paperFixedBindingRates] using hc
  · simpa [rateVector, relaxRates, paperFixedBindingRates,
      sourceBindingQ_succ] using
      (((analyticAt_const).add hgamma).mul
        (halpha.div (hbeta.add hgamma) hbg)).div_const
  · change AnalyticAt ℝ
      (fun δ => (1+(k δ).gamma i)/ε-(k δ).gamma i) 0
    exact (((analyticAt_const).add hgamma).div_const).sub hgamma
  · simpa [rateVector, relaxRates, paperFixedBindingRates] using hgamma

theorem paperFixedBindingSplit_rateVector_analyticAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (ω : Fin (m+1) → ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : (coalescedAllScaledRates m r
      (Fin.lastCases τ ω)).Positive) :
    AnalyticAt ℝ (fun δ =>
      rateVector (paperFixedBindingSplitRates m ξ r δ ε
        (Fin.lastCases τ ω))) 0 := by
  let w : Fin (m+2) → ℝ := Fin.lastCases τ ω
  let k : ℝ → Rates (m+2) := fun δ =>
    edgeScaledRates w (arbitrarySplitFiniteRates (m+1) ξ r δ)
  have hcomp (i : Fin (m+2)) :=
    arbitrarySplitFiniteRates_components_analyticAt
      (m+1) ξ r hr hD₀ hB₀ i
  have hraw : AnalyticAt ℝ (fun δ => rateVector (k δ)) 0 := by
    apply analyticAt_pi_iff.mpr
    intro q
    apply analyticAt_pi_iff.mpr
    intro i
    obtain ⟨ha, hb, hc, hα, hβ, hγ⟩ := hcomp i
    have hw : AnalyticAt ℝ (fun _ : ℝ => w i) 0 := analyticAt_const
    fin_cases q
    · change AnalyticAt ℝ
        (fun δ => w i*(arbitrarySplitFiniteRates (m+1) ξ r δ).a i) 0
      exact hw.mul ha
    · change AnalyticAt ℝ
        (fun δ => w i*(arbitrarySplitFiniteRates (m+1) ξ r δ).b i) 0
      exact hw.mul hb
    · change AnalyticAt ℝ
        (fun δ => w i*(arbitrarySplitFiniteRates (m+1) ξ r δ).c i) 0
      exact hw.mul hc
    · change AnalyticAt ℝ
        (fun δ => w i*(arbitrarySplitFiniteRates (m+1) ξ r δ).alpha i) 0
      exact hw.mul hα
    · change AnalyticAt ℝ
        (fun δ => w i*(arbitrarySplitFiniteRates (m+1) ξ r δ).beta i) 0
      exact hw.mul hβ
    · change AnalyticAt ℝ
        (fun δ => w i*(arbitrarySplitFiniteRates (m+1) ξ r δ).gamma i) 0
      exact hw.mul hγ
  have hzero : k 0 =
      coalescedAllScaledRates m r w := by
    simp [k, coalescedAllScaledRates,
      arbitrarySplitFiniteRates_zero_eq_coalesced]
  have hp : (k 0).Positive := by simpa [hzero, w] using hbase
  simpa only [paperFixedBindingSplitRates, k, w] using
    paperFixedBinding_relaxed_rateVector_analyticAt k ε hraw hp

theorem paperFixedBindingSplit_charpoly_coeff_analyticAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (ω : Fin (m+1) → ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : (coalescedAllScaledRates m r
      (Fin.lastCases τ ω)).Positive)
    (j : Fin (2*(m+1)+1)) (q : ℕ) :
    AnalyticAt ℝ (fun δ =>
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
  have hstate : AnalyticAt ℝ (fun δ =>
      toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j))) 0 := by
    obtain ⟨hS, _, _, hC, hD⟩ :=
      arbitrarySplitFiniteState_components_analyticAt
        (m+1) ξ r hr hD₀ j
    exact (analyticAt_pi_iff.mpr
      (fun i : Fin (m+2) => hS i.succ)).prod
        ((analyticAt_pi_iff.mpr hC).prod (analyticAt_pi_iff.mpr hD))
  have hentry : ∀ i l, AnalyticAt ℝ (fun δ => J δ i l) 0 :=
    restrictedJacobianMatrix_parameter_analyticAt
      (m+2) (2*r) 2 (2*(r+1))
      (fun δ => paperFixedBindingSplitRates m ξ r δ ε
        (Fin.lastCases τ ω))
      (fun δ => toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j)))
      (paperFixedBindingSplit_rateVector_analyticAt
        m ξ r τ ε ω hr hD₀ hB₀ hbase)
      hstate
  exact matrix_charpoly_coeff_analyticAt J hentry q

end
end PhosphorylationStableCapacity
