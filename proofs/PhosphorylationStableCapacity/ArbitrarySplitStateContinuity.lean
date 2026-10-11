module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitEvaluation
public import proofs.PhosphorylationStableCapacity.SplitStateContinuity
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitRetunedSource

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Filter
open scoped Topology

theorem arbitrarySplitState_scalar_factors_continuousAt
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD m r) m)
    (j : Fin (2*m+1)) :
    ContinuousAt (fun δ => ratio (offsetSplitRoot ξ δ j.val)) 0 ∧
      ContinuousAt (fun δ =>
        rootS (offsetSplitRoot ξ δ j.val)
          ((arbitrarySplitRawD m ξ r δ).eval
            (ratio (offsetSplitRoot ξ δ j.val)))) 0 ∧
      ContinuousAt (fun δ => rootF (offsetSplitRoot ξ δ j.val)) 0 := by
  have hx : Continuous (fun δ : ℝ => offsetSplitRoot ξ δ j.val) := by
    dsimp [offsetSplitRoot]
    fun_prop
  have hu : Continuous (fun δ : ℝ => ratio (offsetSplitRoot ξ δ j.val)) := by
    dsimp [ratio, offsetSplitRoot]
    fun_prop
  have hd := arbitrarySplitRawD_eval_continuous m ξ r hr
    (fun δ => ratio (offsetSplitRoot ξ δ j.val)) hu
  have hd0 : 0 < (arbitrarySplitRawD m ξ r 0).eval 1 := by
    simpa [arbitrarySplitRawD, coalescedRawD,
      arbitrarySplitPair_zero_eq_coalesced] using
      hD₀.eval_pos (by norm_num : (0 : ℝ) < 1)
  have hden :
      2 * ratio (offsetSplitRoot ξ 0 j.val) *
        (arbitrarySplitRawD m ξ r 0).eval
          (ratio (offsetSplitRoot ξ 0 j.val)) ≠ 0 := by
    have hratio : ratio (offsetSplitRoot ξ 0 j.val) = 1 := by
      norm_num [offsetSplitRoot, ratio]
    rw [hratio]
    simpa only [mul_one] using
      mul_ne_zero (show (2 : ℝ) ≠ 0 by norm_num) (ne_of_gt hd0)
  constructor
  · exact hu.continuousAt
  constructor
  · unfold rootS
    exact (hx.sub continuous_const).continuousAt.div
      ((continuous_const.mul hu).mul hd).continuousAt hden
  · unfold rootF
    have hdenF : offsetSplitRoot ξ 0 j.val + 1 ≠ 0 := by
      norm_num [offsetSplitRoot]
    exact continuous_const.continuousAt.div
      (hx.add continuous_const).continuousAt hdenF

/-- Each reconstructed concentration tends to its coalesced value for any
fixed prescribed offset. -/
theorem arbitrarySplitFiniteState_components_continuousAt
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD m r) m)
    (j : Fin (2*m+1)) :
    (∀ i : Fin (m+2), ContinuousAt
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).S i) 0) ∧
    ContinuousAt (fun δ => (arbitrarySplitFiniteState m ξ r δ j).E) 0 ∧
    ContinuousAt (fun δ => (arbitrarySplitFiniteState m ξ r δ j).F) 0 ∧
    (∀ i : Fin (m+1), ContinuousAt
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).C i) 0) ∧
    (∀ i : Fin (m+1), ContinuousAt
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).D i) 0) := by
  obtain ⟨hu, hs, hf⟩ :=
    arbitrarySplitState_scalar_factors_continuousAt m ξ r hr hD₀ j
  have hB (i : Fin (m+1)) : ContinuousAt
      (fun δ => (arbitrarySplitRawB m ξ r δ).coeff i) 0 :=
    (arbitrarySplitRawB_coeff_continuous m ξ r hr i).continuousAt
  have hD (i : Fin (m+1)) : ContinuousAt
      (fun δ => (arbitrarySplitRawD m ξ r δ).coeff i) 0 :=
    (arbitrarySplitRawD_coeff_continuous m ξ r hr i).continuousAt
  have hA (i : Fin (m+2)) : ContinuousAt
      (fun δ => (((1 + Polynomial.X) *
        arbitrarySplitRawD m ξ r δ : ℝ[X]).coeff i)) 0 :=
    (arbitrarySplitInventory_coeff_continuous m ξ r hr i).continuousAt
  have hS (i : Fin (m+2)) : ContinuousAt
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).S i) 0 := by
    change ContinuousAt (fun δ =>
      (((1 + Polynomial.X) * arbitrarySplitRawD m ξ r δ : ℝ[X]).coeff i) *
        (ratio (offsetSplitRoot ξ δ j.val))^i.val *
        rootS (offsetSplitRoot ξ δ j.val)
          ((arbitrarySplitRawD m ξ r δ).eval
            (ratio (offsetSplitRoot ξ δ j.val)))) 0
    exact ((hA i).mul (hu.pow i.val)).mul hs
  have hE : ContinuousAt
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).E) 0 := by
    change ContinuousAt (fun δ =>
      ratio (offsetSplitRoot ξ δ j.val) *
        rootF (offsetSplitRoot ξ δ j.val)) 0
    exact hu.mul hf
  have hF : ContinuousAt
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).F) 0 := by
    change ContinuousAt (fun δ => rootF (offsetSplitRoot ξ δ j.val)) 0
    exact hf
  have hC (i : Fin (m+1)) : ContinuousAt
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).C i) 0 := by
    change ContinuousAt (fun δ =>
      (arbitrarySplitRawB m ξ r δ).coeff i *
        (ratio (offsetSplitRoot ξ δ j.val))^(i.val+1) *
        rootS (offsetSplitRoot ξ δ j.val)
          ((arbitrarySplitRawD m ξ r δ).eval
            (ratio (offsetSplitRoot ξ δ j.val))) *
        rootF (offsetSplitRoot ξ δ j.val)) 0
    exact (((hB i).mul (hu.pow (i.val+1))).mul hs).mul hf
  have hY (i : Fin (m+1)) : ContinuousAt
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).D i) 0 := by
    change ContinuousAt (fun δ =>
      (arbitrarySplitRawD m ξ r δ).coeff i *
        (ratio (offsetSplitRoot ξ δ j.val))^(i.val+1) *
        rootS (offsetSplitRoot ξ δ j.val)
          ((arbitrarySplitRawD m ξ r δ).eval
            (ratio (offsetSplitRoot ξ δ j.val))) *
        rootF (offsetSplitRoot ξ δ j.val)) 0
    exact (((hD i).mul (hu.pow (i.val+1))).mul hs).mul hf
  exact ⟨hS, hE, hF, hC, hY⟩

theorem arbitrarySplitFiniteRates_components_continuousAt
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD m r) m)
    (hB₀ : DensePositive (coalescedRawB m r) m) :
    ∀ i : Fin (m+1),
      ContinuousAt (fun δ => (arbitrarySplitFiniteRates m ξ r δ).a i) 0 ∧
      ContinuousAt (fun δ => (arbitrarySplitFiniteRates m ξ r δ).b i) 0 ∧
      ContinuousAt (fun δ => (arbitrarySplitFiniteRates m ξ r δ).c i) 0 ∧
      ContinuousAt (fun δ => (arbitrarySplitFiniteRates m ξ r δ).alpha i) 0 ∧
      ContinuousAt (fun δ => (arbitrarySplitFiniteRates m ξ r δ).beta i) 0 ∧
      ContinuousAt (fun δ => (arbitrarySplitFiniteRates m ξ r δ).gamma i) 0 := by
  have hA₀ : DensePositive ((1 + Polynomial.X) * coalescedRawD m r) (m+1) :=
    dense_inventory_product hD₀
  intro i
  have hD : ContinuousAt (fun δ => (arbitrarySplitRawD m ξ r δ).coeff i) 0 :=
    (arbitrarySplitRawD_coeff_continuous m ξ r hr i).continuousAt
  have hB : ContinuousAt (fun δ => (arbitrarySplitRawB m ξ r δ).coeff i) 0 :=
    (arbitrarySplitRawB_coeff_continuous m ξ r hr i).continuousAt
  have hAc : ContinuousAt (fun δ =>
      (((1 + Polynomial.X) * arbitrarySplitRawD m ξ r δ : ℝ[X]).coeff i.castSucc)) 0 :=
    (arbitrarySplitInventory_coeff_continuous m ξ r hr i.castSucc).continuousAt
  have hAs : ContinuousAt (fun δ =>
      (((1 + Polynomial.X) * arbitrarySplitRawD m ξ r δ : ℝ[X]).coeff i.succ)) 0 :=
    (arbitrarySplitInventory_coeff_continuous m ξ r hr i.succ).continuousAt
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
  exact ⟨(continuousAt_const.mul hD).div hAc hAc0,
    hD.div hB hB0, hD.div hB hB0,
    (continuousAt_const.mul hD).div hAs hAs0,
    continuousAt_const, continuousAt_const⟩

theorem arbitrarySplitRetunedRates_components_continuousAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1)) :
    ∀ i : Fin (m+2),
      ContinuousAt (fun δ => (arbitrarySplitRetunedRates m ξ r τ δ ε).a i) 0 ∧
      ContinuousAt (fun δ => (arbitrarySplitRetunedRates m ξ r τ δ ε).b i) 0 ∧
      ContinuousAt (fun δ => (arbitrarySplitRetunedRates m ξ r τ δ ε).c i) 0 ∧
      ContinuousAt (fun δ => (arbitrarySplitRetunedRates m ξ r τ δ ε).alpha i) 0 ∧
      ContinuousAt (fun δ => (arbitrarySplitRetunedRates m ξ r τ δ ε).beta i) 0 ∧
      ContinuousAt (fun δ => (arbitrarySplitRetunedRates m ξ r τ δ ε).gamma i) 0 := by
  intro i
  obtain ⟨ha, hb, hc, hα, hβ, hγ⟩ :=
    arbitrarySplitFiniteRates_components_continuousAt (m+1) ξ r hr hD₀ hB₀ i
  have hwa : ContinuousAt (fun δ =>
      coalescedFinalCurrentWeights m τ i * (arbitrarySplitFiniteRates (m+1) ξ r δ).a i) 0 :=
    continuousAt_const.mul ha
  have hwb : ContinuousAt (fun δ =>
      coalescedFinalCurrentWeights m τ i * (arbitrarySplitFiniteRates (m+1) ξ r δ).b i) 0 :=
    continuousAt_const.mul hb
  have hwc : ContinuousAt (fun δ =>
      coalescedFinalCurrentWeights m τ i * (arbitrarySplitFiniteRates (m+1) ξ r δ).c i) 0 :=
    continuousAt_const.mul hc
  have hwα : ContinuousAt (fun δ =>
      coalescedFinalCurrentWeights m τ i * (arbitrarySplitFiniteRates (m+1) ξ r δ).alpha i) 0 :=
    continuousAt_const.mul hα
  have hwβ : ContinuousAt (fun δ =>
      coalescedFinalCurrentWeights m τ i * (arbitrarySplitFiniteRates (m+1) ξ r δ).beta i) 0 :=
    continuousAt_const.mul hβ
  have hwγ : ContinuousAt (fun δ =>
      coalescedFinalCurrentWeights m τ i * (arbitrarySplitFiniteRates (m+1) ξ r δ).gamma i) 0 :=
    continuousAt_const.mul hγ
  dsimp [arbitrarySplitRetunedRates, relaxRates, edgeScaledRates]
  exact ⟨hwa.div_const ε, ((hwb.add hwc).div_const ε).sub hwc,
    hwc, hwα.div_const ε, ((hwβ.add hwγ).div_const ε).sub hwγ,
    hwγ⟩

end
end PhosphorylationStableCapacity
