module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitStateAnalytic
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitRetunedSource

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- The six physical rate arrays are analytic in the split parameter. -/
theorem arbitrarySplitFiniteRates_components_analyticAt
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD m r) m)
    (hB₀ : DensePositive (coalescedRawB m r) m) :
    ∀ i : Fin (m+1),
      AnalyticAt ℝ (fun δ => (arbitrarySplitFiniteRates m ξ r δ).a i) 0 ∧
      AnalyticAt ℝ (fun δ => (arbitrarySplitFiniteRates m ξ r δ).b i) 0 ∧
      AnalyticAt ℝ (fun δ => (arbitrarySplitFiniteRates m ξ r δ).c i) 0 ∧
      AnalyticAt ℝ (fun δ => (arbitrarySplitFiniteRates m ξ r δ).alpha i) 0 ∧
      AnalyticAt ℝ (fun δ => (arbitrarySplitFiniteRates m ξ r δ).beta i) 0 ∧
      AnalyticAt ℝ (fun δ => (arbitrarySplitFiniteRates m ξ r δ).gamma i) 0 := by
  have hA₀ : DensePositive ((1 + Polynomial.X) * coalescedRawD m r) (m+1) :=
    dense_inventory_product hD₀
  intro i
  have hD : AnalyticAt ℝ
      (fun δ => (arbitrarySplitRawD m ξ r δ).coeff i) 0 :=
    arbitrarySplitRawD_coeff_analyticAt m ξ r hr i
  have hB : AnalyticAt ℝ
      (fun δ => (arbitrarySplitRawB m ξ r δ).coeff i) 0 :=
    arbitrarySplitRawB_coeff_analyticAt m ξ r hr i
  have hAc : AnalyticAt ℝ (fun δ =>
      (((1 + Polynomial.X) * arbitrarySplitRawD m ξ r δ : ℝ[X]).coeff i.castSucc)) 0 :=
    arbitrarySplitInventory_coeff_analyticAt m ξ r hr i.castSucc
  have hAs : AnalyticAt ℝ (fun δ =>
      (((1 + Polynomial.X) * arbitrarySplitRawD m ξ r δ : ℝ[X]).coeff i.succ)) 0 :=
    arbitrarySplitInventory_coeff_analyticAt m ξ r hr i.succ
  have hAc0 :
      (((1 + Polynomial.X) * arbitrarySplitRawD m ξ r 0 : ℝ[X]).coeff i.castSucc) ≠ 0 := by
    have h := hA₀.1 i.castSucc (by omega)
    simpa [arbitrarySplitRawD, coalescedRawD,
      arbitrarySplitPair_zero_eq_coalesced] using ne_of_gt h
  have hAs0 :
      (((1 + Polynomial.X) * arbitrarySplitRawD m ξ r 0 : ℝ[X]).coeff i.succ) ≠ 0 := by
    have h := hA₀.1 i.succ (by omega)
    simpa [arbitrarySplitRawD, coalescedRawD,
      arbitrarySplitPair_zero_eq_coalesced] using ne_of_gt h
  have hB0 : (arbitrarySplitRawB m ξ r 0).coeff i ≠ 0 := by
    have h := hB₀.1 i (by omega)
    simpa [arbitrarySplitRawB, coalescedRawB,
      arbitrarySplitPair_zero_eq_coalesced] using ne_of_gt h
  dsimp [arbitrarySplitFiniteRates, realize]
  exact ⟨(analyticAt_const.mul hD).div hAc hAc0,
    hD.div hB hB0, hD.div hB hB0,
    (analyticAt_const.mul hD).div hAs hAs0,
    analyticAt_const, analyticAt_const⟩

theorem arbitrarySplitRetunedRates_components_analyticAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1)) :
    ∀ i : Fin (m+2),
      AnalyticAt ℝ (fun δ => (arbitrarySplitRetunedRates m ξ r τ δ ε).a i) 0 ∧
      AnalyticAt ℝ (fun δ => (arbitrarySplitRetunedRates m ξ r τ δ ε).b i) 0 ∧
      AnalyticAt ℝ (fun δ => (arbitrarySplitRetunedRates m ξ r τ δ ε).c i) 0 ∧
      AnalyticAt ℝ (fun δ => (arbitrarySplitRetunedRates m ξ r τ δ ε).alpha i) 0 ∧
      AnalyticAt ℝ (fun δ => (arbitrarySplitRetunedRates m ξ r τ δ ε).beta i) 0 ∧
      AnalyticAt ℝ (fun δ => (arbitrarySplitRetunedRates m ξ r τ δ ε).gamma i) 0 := by
  intro i
  obtain ⟨ha, hb, hc, hα, hβ, hγ⟩ :=
    arbitrarySplitFiniteRates_components_analyticAt
      (m+1) ξ r hr hD₀ hB₀ i
  have hw (f : Rates (m+2) → Fin (m+2) → ℝ)
      (hf : AnalyticAt ℝ
        (fun δ => f (arbitrarySplitFiniteRates (m+1) ξ r δ) i) 0) :
      AnalyticAt ℝ (fun δ =>
        coalescedFinalCurrentWeights m τ i *
          f (arbitrarySplitFiniteRates (m+1) ξ r δ) i) 0 :=
    analyticAt_const.mul hf
  dsimp [arbitrarySplitRetunedRates, relaxRates, edgeScaledRates]
  exact ⟨(hw _ ha).div_const,
    (((hw _ hb).add (hw _ hc)).div_const).sub (hw _ hc),
    hw _ hc, (hw _ hα).div_const,
    (((hw _ hβ).add (hw _ hγ)).div_const).sub (hw _ hγ),
    hw _ hγ⟩

end
end PhosphorylationStableCapacity
