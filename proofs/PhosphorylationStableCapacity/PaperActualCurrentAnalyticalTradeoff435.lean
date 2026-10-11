module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingActualCurrentDesign
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCompleteLaw
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitUniformReadout435
public import proofs.PhosphorylationStableCapacity.ReadoutDerivative435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Polynomial
open scoped Topology

/-- The two conditioning formulas in the manuscript's tradeoff corollary
hold in one actual-current family. The selected analytic eigenvalues,
their printed coefficient, the full equilibrium configuration, and the
quadratic physical readout estimate use the same dyadic design choices.
In particular the reciprocal formula is retained inside CompletePoint;
it is not combined with a separate existential spectral construction. -/
theorem paperActualCurrent_readout_relaxation_tradeoff
    (m : ℕ) (ξ : ℕ → ℝ) (hξ : StrictMono ξ) :
    ∃ a b c : ℕ,
      let r : ℝ := (2 : ℝ)^a
      let t : ℝ := (1/2 : ℝ)^b
      let ε : ℝ := (1/2 : ℝ)^c
      let x₀ := coalescedFiniteState (m+1) r
      let τ : ℝ := t / x₀.D (Fin.last (m+1))
      let θ : Fin (m+1) → ℝ := fun i => 1 / x₀.D i.castSucc
      let k₀ := relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r (Fin.lastCases τ θ))) ε
      (3*(m+2 : ℝ))/2 ≤ r ∧ 0 < t ∧ 0 < ε ∧ ε ≤ 1 ∧
        (∀ i : Fin (m+1), k₀.gamma i.castSucc*x₀.D i.castSucc = 1) ∧
        k₀.gamma (Fin.last (m+1))*x₀.D (Fin.last (m+1)) = t ∧
        ∃ lam : Fin (2*(m+1)+1) → ℝ → ℝ,
          (∀ j, AnalyticAt ℝ (lam j) 0 ∧ lam j 0 = 0) ∧
          0 < paperFixedBindingPrintedCoefficient m r τ ε θ ∧
          ∃ α K Cread : ℝ,
            0 < α ∧ 0 < K ∧ 0 < Cread ∧
            0 < deriv (splitReadoutScalar (m+1)
              (coalescedRawD (m+1) r)) 3 ∧
            ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
              PaperFixedBindingCompletePoint
                m ξ r τ ε α K δ θ lam ∧
              ∀ j k : Fin (2*(m+1)+1),
                |(fullyPhosphorylatedReadout (m+1)
                    (arbitrarySplitFiniteState (m+1) ξ r δ j) -
                  fullyPhosphorylatedReadout (m+1)
                    (arbitrarySplitFiniteState (m+1) ξ r δ k)) -
                  (ξ j.val-ξ k.val) *
                    deriv (splitReadoutScalar (m+1)
                      (coalescedRawD (m+1) r)) 3 * δ| ≤ Cread*δ^2 := by
  obtain ⟨a, b, c, hr, hrAdequate, ht, hτ, hε, hε1, hD, hB,
    hθ, hbase, hk, hx, heq, hET, hFT, hspec,
    hprefix, hfinal⟩ := paperFixedBinding_actual_unit_current_design m
  let r : ℝ := (2 : ℝ)^a
  let t : ℝ := (1/2 : ℝ)^b
  let ε : ℝ := (1/2 : ℝ)^c
  let x₀ := coalescedFiniteState (m+1) r
  let τ : ℝ := t / x₀.D (Fin.last (m+1))
  let θ : Fin (m+1) → ℝ := fun i => 1 / x₀.D i.castSucc
  obtain ⟨lam, hlam, ha, α, K, hα, hK, hcomplete⟩ :=
    paperFixedBinding_complete_analytic_law m ξ hξ r τ ε θ
      hθ hr hτ hε hε1 hD hB hbase hk hx heq hET hFT hspec
  have hr0 : r ≠ 0 := ne_of_gt (lt_trans zero_lt_one hr)
  obtain ⟨Cread, hCread, hread⟩ :=
    arbitrarySplitReadout_uniform_quadratic_remainder
      (m+1) ξ r hr0 hD hB
  have hderiv := splitReadoutScalar_deriv_three_pos
    (m+1) (coalescedRawD (m+1) r) hD
  refine ⟨a, b, c, hrAdequate, ht, hε, hε1, hprefix, hfinal,
    lam, hlam, ha, α, K, Cread, hα, hK, hCread, hderiv, ?_⟩
  filter_upwards [hcomplete, hread] with δ hc hd
  exact ⟨hc, hd⟩

end
end PhosphorylationStableCapacity
