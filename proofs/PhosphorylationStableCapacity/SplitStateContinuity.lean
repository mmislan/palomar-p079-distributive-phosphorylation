module
public import proofs.PhosphorylationStableCapacity.SplitAttainmentPreparation

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Filter
open scoped Topology

/-- The rational source reconstruction has continuous scalar factors at
the coalesced point, provided its denominator is positive there. -/
theorem splitState_scalar_factors_continuousAt
    (m : ℕ) (r : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD m r) m)
    (j : Fin (2*m+1)) :
    ContinuousAt (fun δ => ratio (splitRoot δ j.val)) 0 ∧
      ContinuousAt (fun δ =>
        rootS (splitRoot δ j.val)
          ((splitRawD m r δ).eval (ratio (splitRoot δ j.val)))) 0 ∧
      ContinuousAt (fun δ => rootF (splitRoot δ j.val)) 0 := by
  have hx : Continuous (fun δ : ℝ => splitRoot δ j.val) := by
    dsimp [splitRoot]
    fun_prop
  have hu : Continuous (fun δ : ℝ => ratio (splitRoot δ j.val)) := by
    dsimp [ratio]
    fun_prop
  have hd := splitRawD_eval_continuous m r hr
    (fun δ => ratio (splitRoot δ j.val)) hu
  have hd0 : 0 < (splitRawD m r 0).eval 1 := by
    simpa [splitRawD, coalescedRawD, splitPair_zero_eq_coalesced]
      using hD₀.eval_pos (by norm_num : (0 : ℝ) < 1)
  have hden :
      2 * ratio (splitRoot 0 j.val) *
        (splitRawD m r 0).eval (ratio (splitRoot 0 j.val)) ≠ 0 := by
    have hratio : ratio (splitRoot 0 j.val) = 1 := by
      norm_num [splitRoot, ratio]
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
    have hdenF : splitRoot 0 j.val + 1 ≠ 0 := by norm_num [splitRoot]
    exact continuous_const.continuousAt.div
      (hx.add continuous_const).continuousAt hdenF

/-- Every literal concentration in a fixed split state depends
continuously on the common splitting parameter at `δ=0`. -/
theorem splitFiniteState_components_continuousAt
    (m : ℕ) (r : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD m r) m)
    (j : Fin (2*m+1)) :
    (∀ i : Fin (m+2), ContinuousAt
      (fun δ => (splitFiniteState m r δ j).S i) 0) ∧
    ContinuousAt (fun δ => (splitFiniteState m r δ j).E) 0 ∧
    ContinuousAt (fun δ => (splitFiniteState m r δ j).F) 0 ∧
    (∀ i : Fin (m+1), ContinuousAt
      (fun δ => (splitFiniteState m r δ j).C i) 0) ∧
    (∀ i : Fin (m+1), ContinuousAt
      (fun δ => (splitFiniteState m r δ j).D i) 0) := by
  obtain ⟨hu, hs, hf⟩ :=
    splitState_scalar_factors_continuousAt m r hr hD₀ j
  have hB (i : Fin (m+1)) : ContinuousAt
      (fun δ => (splitRawB m r δ).coeff i) 0 :=
    (splitRawB_coeff_continuous m r hr i).continuousAt
  have hD (i : Fin (m+1)) : ContinuousAt
      (fun δ => (splitRawD m r δ).coeff i) 0 :=
    (splitRawD_coeff_continuous m r hr i).continuousAt
  have hA (i : Fin (m+2)) : ContinuousAt
      (fun δ => (((1 + Polynomial.X) * splitRawD m r δ : ℝ[X]).coeff i)) 0 :=
    (splitInventory_coeff_continuous m r hr i).continuousAt
  have hS (i : Fin (m+2)) : ContinuousAt
      (fun δ => (splitFiniteState m r δ j).S i) 0 := by
    change ContinuousAt (fun δ =>
      (((1 + Polynomial.X) * splitRawD m r δ : ℝ[X]).coeff i) *
        (ratio (splitRoot δ j.val))^i.val *
        rootS (splitRoot δ j.val)
          ((splitRawD m r δ).eval (ratio (splitRoot δ j.val)))) 0
    exact ((hA i).mul (hu.pow i.val)).mul hs
  have hE : ContinuousAt
      (fun δ => (splitFiniteState m r δ j).E) 0 := by
    change ContinuousAt (fun δ =>
      ratio (splitRoot δ j.val) * rootF (splitRoot δ j.val)) 0
    exact hu.mul hf
  have hF : ContinuousAt
      (fun δ => (splitFiniteState m r δ j).F) 0 := by
    change ContinuousAt (fun δ => rootF (splitRoot δ j.val)) 0
    exact hf
  have hC (i : Fin (m+1)) : ContinuousAt
      (fun δ => (splitFiniteState m r δ j).C i) 0 := by
    change ContinuousAt (fun δ =>
      (splitRawB m r δ).coeff i *
        (ratio (splitRoot δ j.val))^(i.val+1) *
        rootS (splitRoot δ j.val)
          ((splitRawD m r δ).eval (ratio (splitRoot δ j.val))) *
        rootF (splitRoot δ j.val)) 0
    exact (((hB i).mul (hu.pow (i.val+1))).mul hs).mul hf
  have hY (i : Fin (m+1)) : ContinuousAt
      (fun δ => (splitFiniteState m r δ j).D i) 0 := by
    change ContinuousAt (fun δ =>
      (splitRawD m r δ).coeff i *
        (ratio (splitRoot δ j.val))^(i.val+1) *
        rootS (splitRoot δ j.val)
          ((splitRawD m r δ).eval (ratio (splitRoot δ j.val))) *
        rootF (splitRoot δ j.val)) 0
    exact (((hD i).mul (hu.pow (i.val+1))).mul hs).mul hf
  exact ⟨hS, hE, hF, hC, hY⟩

/-- Every literal rate in the split reconstruction varies continuously at
the coalesced source. -/
theorem splitFiniteRates_components_continuousAt
    (m : ℕ) (r : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD m r) m)
    (hB₀ : DensePositive (coalescedRawB m r) m) :
    ∀ i : Fin (m+1),
      ContinuousAt (fun δ => (splitFiniteRates m r δ).a i) 0 ∧
      ContinuousAt (fun δ => (splitFiniteRates m r δ).b i) 0 ∧
      ContinuousAt (fun δ => (splitFiniteRates m r δ).c i) 0 ∧
      ContinuousAt (fun δ => (splitFiniteRates m r δ).alpha i) 0 ∧
      ContinuousAt (fun δ => (splitFiniteRates m r δ).beta i) 0 ∧
      ContinuousAt (fun δ => (splitFiniteRates m r δ).gamma i) 0 := by
  have hA₀ : DensePositive ((1 + Polynomial.X) * coalescedRawD m r) (m+1) :=
    dense_inventory_product hD₀
  intro i
  have hD : ContinuousAt (fun δ => (splitRawD m r δ).coeff i) 0 :=
    (splitRawD_coeff_continuous m r hr i).continuousAt
  have hB : ContinuousAt (fun δ => (splitRawB m r δ).coeff i) 0 :=
    (splitRawB_coeff_continuous m r hr i).continuousAt
  have hAc : ContinuousAt (fun δ =>
      (((1 + Polynomial.X) * splitRawD m r δ : ℝ[X]).coeff i.castSucc)) 0 :=
    (splitInventory_coeff_continuous m r hr i.castSucc).continuousAt
  have hAs : ContinuousAt (fun δ =>
      (((1 + Polynomial.X) * splitRawD m r δ : ℝ[X]).coeff i.succ)) 0 :=
    (splitInventory_coeff_continuous m r hr i.succ).continuousAt
  have hAc0 : (((1 + Polynomial.X) * splitRawD m r 0 : ℝ[X]).coeff i.castSucc) ≠ 0 := by
    have h := hA₀.1 i.castSucc (by omega)
    simpa [splitRawD, coalescedRawD, splitPair_zero_eq_coalesced] using ne_of_gt h
  have hAs0 : (((1 + Polynomial.X) * splitRawD m r 0 : ℝ[X]).coeff i.succ) ≠ 0 := by
    have h := hA₀.1 i.succ (by omega)
    simpa [splitRawD, coalescedRawD, splitPair_zero_eq_coalesced] using ne_of_gt h
  have hB0 : (splitRawB m r 0).coeff i ≠ 0 := by
    have h := hB₀.1 i (by omega)
    simpa [splitRawB, coalescedRawB, splitPair_zero_eq_coalesced] using ne_of_gt h
  dsimp [splitFiniteRates, realize]
  exact ⟨(continuousAt_const.mul hD).div hAc hAc0,
    hD.div hB hB0, hD.div hB hB0,
    (continuousAt_const.mul hD).div hAs hAs0,
    continuousAt_const, continuousAt_const⟩

/-- The equilibrium-preserving edge retune and binding relaxation preserve
coefficientwise continuity for fixed positive relaxation scale. -/
theorem splitRetunedRates_components_continuousAt
    (m : ℕ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1)) :
    ∀ i : Fin (m+2),
      ContinuousAt (fun δ => (splitRetunedRates m r τ δ ε).a i) 0 ∧
      ContinuousAt (fun δ => (splitRetunedRates m r τ δ ε).b i) 0 ∧
      ContinuousAt (fun δ => (splitRetunedRates m r τ δ ε).c i) 0 ∧
      ContinuousAt (fun δ => (splitRetunedRates m r τ δ ε).alpha i) 0 ∧
      ContinuousAt (fun δ => (splitRetunedRates m r τ δ ε).beta i) 0 ∧
      ContinuousAt (fun δ => (splitRetunedRates m r τ δ ε).gamma i) 0 := by
  intro i
  obtain ⟨ha, hb, hc, hα, hβ, hγ⟩ :=
    splitFiniteRates_components_continuousAt (m+1) r hr hD₀ hB₀ i
  have hwa : ContinuousAt (fun δ =>
      coalescedFinalCurrentWeights m τ i * (splitFiniteRates (m+1) r δ).a i) 0 :=
    continuousAt_const.mul ha
  have hwb : ContinuousAt (fun δ =>
      coalescedFinalCurrentWeights m τ i * (splitFiniteRates (m+1) r δ).b i) 0 :=
    continuousAt_const.mul hb
  have hwc : ContinuousAt (fun δ =>
      coalescedFinalCurrentWeights m τ i * (splitFiniteRates (m+1) r δ).c i) 0 :=
    continuousAt_const.mul hc
  have hwα : ContinuousAt (fun δ =>
      coalescedFinalCurrentWeights m τ i * (splitFiniteRates (m+1) r δ).alpha i) 0 :=
    continuousAt_const.mul hα
  have hwβ : ContinuousAt (fun δ =>
      coalescedFinalCurrentWeights m τ i * (splitFiniteRates (m+1) r δ).beta i) 0 :=
    continuousAt_const.mul hβ
  have hwγ : ContinuousAt (fun δ =>
      coalescedFinalCurrentWeights m τ i * (splitFiniteRates (m+1) r δ).gamma i) 0 :=
    continuousAt_const.mul hγ
  dsimp [splitRetunedRates, relaxRates, edgeScaledRates]
  exact ⟨hwa.div_const ε, ((hwb.add hwc).div_const ε).sub hwc,
    hwc, hwα.div_const ε, ((hwβ.add hwγ).div_const ε).sub hwγ,
    hwγ⟩

end
end PhosphorylationStableCapacity
