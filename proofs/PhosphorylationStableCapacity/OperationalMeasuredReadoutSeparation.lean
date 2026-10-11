module
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalFullCertificate

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- The three printed physical readout intervals are strictly separated.
The bounds already include an independent measurement error of
`0.001` micromolar at each sink. -/
theorem operational_printed_readout_intervals_strictly_ordered :
    (437971/100000000 : ℝ) < (1439001/20000000 : ℝ) ∧
    (3697503/50000000 : ℝ) < (10757833/50000000 : ℝ) := by
  constructor <;> norm_num

/-- The literal readout in physical concentration units, including one
independent measurement error for the first sink. -/
def operationalZeroMeasuredReadout (θ : Fin 21 → ℝ)
    (e : Fin 9 → ℝ) (error : ℝ) : ℝ :=
  operationalPhysicalReadout
    (fun i => (operationalZeroIntervalCoordinates i : ℝ))
    (fun i => (operationalZeroIntervalScales i : ℝ)) θ e + error

/-- The literal physical readout for the second sink. -/
def operationalTwoMeasuredReadout (θ : Fin 21 → ℝ)
    (e : Fin 9 → ℝ) (error : ℝ) : ℝ :=
  operationalPhysicalReadout
    (fun i => (operationalTwoIntervalCoordinates i : ℝ))
    (fun i => (operationalTwoIntervalScales i : ℝ)) θ e + error

/-- The literal physical readout for the third sink. -/
def operationalFourMeasuredReadout (θ : Fin 21 → ℝ)
    (e : Fin 9 → ℝ) (error : ℝ) : ℝ :=
  operationalPhysicalReadout
    (fun i => (operationalFourIntervalCoordinates i : ℝ))
    (fun i => (operationalFourIntervalScales i : ℝ)) θ e + error

/-- Proposition 9.4(iii) as a direct same-witness consequence: for one
admitted parameter vector and its three shifted physical sinks, all three
readouts stay strictly ordered under three independently chosen errors of
magnitude at most `0.001` micromolar.  The hypotheses retain the complete
printed sink outcomes, including their equilibrium and recovery claims. -/
theorem operational_three_measured_readouts_strictly_ordered
    {θ : Fin 21 → ℝ} {e0 e2 e4 : Fin 9 → ℝ}
    (h0 : operationalZeroPrintedOutcome θ e0)
    (h2 : operationalTwoPrintedOutcome θ e2)
    (h4 : operationalFourPrintedOutcome θ e4)
    (error0 error2 error4 : ℝ)
    (herr0 : |error0| ≤ (1/1000 : ℝ))
    (herr2 : |error2| ≤ (1/1000 : ℝ))
    (herr4 : |error4| ≤ (1/1000 : ℝ)) :
    operationalZeroMeasuredReadout θ e0 error0 <
      operationalTwoMeasuredReadout θ e2 error2 ∧
    operationalTwoMeasuredReadout θ e2 error2 <
      operationalFourMeasuredReadout θ e4 error4 := by
  rcases h0.1 with ⟨_Q0, _Q0inv, _hnom0, hs0⟩
  rcases h2.1 with ⟨_Q2, _Q2inv, _hnom2, hs2⟩
  rcases h4.1 with ⟨_Q4, _Q4inv, _hnom4, hs4⟩
  have hr0 := hs0.measured_readout error0 herr0
  have hr2 := hs2.measured_readout error2 herr2
  have hr4 := hs4.measured_readout error4 herr4
  change (23797/10000000 : ℝ) ≤
      operationalZeroMeasuredReadout θ e0 error0 ∧
      operationalZeroMeasuredReadout θ e0 error0 ≤
        (437971/100000000 : ℝ) at hr0
  change (1439001/20000000 : ℝ) ≤
      operationalTwoMeasuredReadout θ e2 error2 ∧
      operationalTwoMeasuredReadout θ e2 error2 ≤
        (3697503/50000000 : ℝ) at hr2
  change (10757833/50000000 : ℝ) ≤
      operationalFourMeasuredReadout θ e4 error4 ∧
      operationalFourMeasuredReadout θ e4 error4 ≤
        (2714459/12500000 : ℝ) at hr4
  obtain ⟨hgap02, hgap24⟩ :=
    operational_printed_readout_intervals_strictly_ordered
  constructor
  · exact lt_of_lt_of_le (lt_of_le_of_lt hr0.2 hgap02) hr2.1
  · exact lt_of_lt_of_le (lt_of_le_of_lt hr2.2 hgap24) hr4.1

/-- Strengthens the existing full operational submission theorem on exactly
its same parameter vector and shifted equilibria.  It preserves all three
printed outcomes (including closed-boundary recovery), their physical-state
inequalities, and adds the strict measured-readout order for every independent
triple of admissible measurement errors. -/
theorem three_site_printed_operational_submission_with_measured_separation
    (φ : Fin 21 → ℝ)
    (hφ : ∀ i,
      |φ i-operationalPhysicalParameters benchmarkThreeSiteOperationalNominal i| ≤
        (1/671088640000 : ℝ)*
          operationalPhysicalParameters benchmarkThreeSiteOperationalNominal i) :
    ∃ θ : Fin 21 → ℝ, operationalPhysicalParameters θ = φ ∧
      InOperationalParameterBox θ ∧
      ∃ e0 e2 e4 : Fin 9 → ℝ,
        operationalZeroPrintedOutcome θ e0 ∧
        operationalTwoPrintedOutcome θ e2 ∧
        operationalFourPrintedOutcome θ e4 ∧
        operationalPhysicalState
          (fun i => (operationalZeroIntervalCoordinates i : ℝ))
          (fun i => (operationalZeroIntervalScales i : ℝ)) θ e0 ≠
        operationalPhysicalState
          (fun i => (operationalTwoIntervalCoordinates i : ℝ))
          (fun i => (operationalTwoIntervalScales i : ℝ)) θ e2 ∧
        operationalPhysicalState
          (fun i => (operationalTwoIntervalCoordinates i : ℝ))
          (fun i => (operationalTwoIntervalScales i : ℝ)) θ e2 ≠
        operationalPhysicalState
          (fun i => (operationalFourIntervalCoordinates i : ℝ))
          (fun i => (operationalFourIntervalScales i : ℝ)) θ e4 ∧
        operationalPhysicalState
          (fun i => (operationalZeroIntervalCoordinates i : ℝ))
          (fun i => (operationalZeroIntervalScales i : ℝ)) θ e0 ≠
        operationalPhysicalState
          (fun i => (operationalFourIntervalCoordinates i : ℝ))
          (fun i => (operationalFourIntervalScales i : ℝ)) θ e4 ∧
        ∀ error0 error2 error4 : ℝ,
          |error0| ≤ (1/1000 : ℝ) →
          |error2| ≤ (1/1000 : ℝ) →
          |error4| ≤ (1/1000 : ℝ) →
          operationalZeroMeasuredReadout θ e0 error0 <
            operationalTwoMeasuredReadout θ e2 error2 ∧
          operationalTwoMeasuredReadout θ e2 error2 <
            operationalFourMeasuredReadout θ e4 error4 := by
  obtain ⟨θ, hconvert, hbox, e0, e2, e4, h0, h2, h4,
      h02, h24, h04⟩ := three_site_printed_operational_submission φ hφ
  refine ⟨θ, hconvert, hbox, e0, e2, e4,
    h0, h2, h4, h02, h24, h04, ?_⟩
  intro error0 error2 error4 herr0 herr2 herr4
  exact operational_three_measured_readouts_strictly_ordered
    h0 h2 h4 error0 error2 error4 herr0 herr2 herr4

end
end PhosphorylationStableCapacity
