module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitEvaluationDifferentiability
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitStateContinuity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- At the coalesced parameter every reconstructed state coordinate has a
    first-order expansion in the root separation parameter. -/
theorem arbitrarySplitFiniteState_components_differentiableAt
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD m r) m)
    (j : Fin (2*m+1)) :
    (∀ i : Fin (m+2), DifferentiableAt ℝ
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).S i) 0) ∧
    DifferentiableAt ℝ (fun δ => (arbitrarySplitFiniteState m ξ r δ j).E) 0 ∧
    DifferentiableAt ℝ (fun δ => (arbitrarySplitFiniteState m ξ r δ j).F) 0 ∧
    (∀ i : Fin (m+1), DifferentiableAt ℝ
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).C i) 0) ∧
    (∀ i : Fin (m+1), DifferentiableAt ℝ
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).D i) 0) := by
  have hx : Differentiable ℝ (fun δ : ℝ => offsetSplitRoot ξ δ j.val) := by
    dsimp [offsetSplitRoot]
    fun_prop
  have hu : Differentiable ℝ
      (fun δ : ℝ => ratio (offsetSplitRoot ξ δ j.val)) := by
    dsimp [ratio, offsetSplitRoot]
    fun_prop
  have hd := arbitrarySplitRawD_eval_differentiable m ξ r hr
    (fun δ => ratio (offsetSplitRoot ξ δ j.val)) hu
  have hd0 : 0 < (arbitrarySplitRawD m ξ r 0).eval 1 := by
    simpa [arbitrarySplitRawD, coalescedRawD,
      arbitrarySplitPair_zero_eq_coalesced] using
      hD₀.eval_pos (by norm_num : (0 : ℝ) < 1)
  have hratio : ratio (offsetSplitRoot ξ 0 j.val) = 1 := by
    norm_num [offsetSplitRoot, ratio]
  have hden :
      2 * ratio (offsetSplitRoot ξ 0 j.val) *
        (arbitrarySplitRawD m ξ r 0).eval
          (ratio (offsetSplitRoot ξ 0 j.val)) ≠ 0 := by
    rw [hratio]
    simpa only [mul_one] using
      mul_ne_zero (show (2 : ℝ) ≠ 0 by norm_num) (ne_of_gt hd0)
  have hs : DifferentiableAt ℝ (fun δ =>
      rootS (offsetSplitRoot ξ δ j.val)
        ((arbitrarySplitRawD m ξ r δ).eval
          (ratio (offsetSplitRoot ξ δ j.val)))) 0 := by
    unfold rootS
    exact (hx.sub (differentiable_const _)).differentiableAt.div
      (((differentiable_const _).mul hu).mul hd).differentiableAt hden
  have hf : DifferentiableAt ℝ
      (fun δ => rootF (offsetSplitRoot ξ δ j.val)) 0 := by
    unfold rootF
    have hdenF : offsetSplitRoot ξ 0 j.val + 1 ≠ 0 := by
      norm_num [offsetSplitRoot]
    exact (differentiableAt_const _).div
      (hx.add (differentiable_const _)).differentiableAt hdenF
  have hu0 : DifferentiableAt ℝ
      (fun δ => ratio (offsetSplitRoot ξ δ j.val)) 0 :=
    hu.differentiableAt
  have hB (i : Fin (m+1)) : DifferentiableAt ℝ
      (fun δ => (arbitrarySplitRawB m ξ r δ).coeff i) 0 :=
    (arbitrarySplitRawB_coeff_differentiable m ξ r hr i).differentiableAt
  have hD (i : Fin (m+1)) : DifferentiableAt ℝ
      (fun δ => (arbitrarySplitRawD m ξ r δ).coeff i) 0 :=
    (arbitrarySplitRawD_coeff_differentiable m ξ r hr i).differentiableAt
  have hA (i : Fin (m+2)) : DifferentiableAt ℝ
      (fun δ => (((1 + Polynomial.X) *
        arbitrarySplitRawD m ξ r δ : ℝ[X]).coeff i)) 0 :=
    (arbitrarySplitInventory_coeff_differentiable m ξ r hr i).differentiableAt
  have hS (i : Fin (m+2)) : DifferentiableAt ℝ
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).S i) 0 := by
    change DifferentiableAt ℝ (fun δ =>
      (((1 + Polynomial.X) * arbitrarySplitRawD m ξ r δ : ℝ[X]).coeff i) *
        (ratio (offsetSplitRoot ξ δ j.val))^i.val *
        rootS (offsetSplitRoot ξ δ j.val)
          ((arbitrarySplitRawD m ξ r δ).eval
            (ratio (offsetSplitRoot ξ δ j.val)))) 0
    exact ((hA i).mul (hu0.pow i.val)).mul hs
  have hE : DifferentiableAt ℝ
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).E) 0 := by
    change DifferentiableAt ℝ (fun δ =>
      ratio (offsetSplitRoot ξ δ j.val) *
        rootF (offsetSplitRoot ξ δ j.val)) 0
    exact hu0.mul hf
  have hF : DifferentiableAt ℝ
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).F) 0 := by
    change DifferentiableAt ℝ
      (fun δ => rootF (offsetSplitRoot ξ δ j.val)) 0
    exact hf
  have hC (i : Fin (m+1)) : DifferentiableAt ℝ
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).C i) 0 := by
    change DifferentiableAt ℝ (fun δ =>
      (arbitrarySplitRawB m ξ r δ).coeff i *
        (ratio (offsetSplitRoot ξ δ j.val))^(i.val+1) *
        rootS (offsetSplitRoot ξ δ j.val)
          ((arbitrarySplitRawD m ξ r δ).eval
            (ratio (offsetSplitRoot ξ δ j.val))) *
        rootF (offsetSplitRoot ξ δ j.val)) 0
    exact (((hB i).mul (hu0.pow (i.val+1))).mul hs).mul hf
  have hY (i : Fin (m+1)) : DifferentiableAt ℝ
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).D i) 0 := by
    change DifferentiableAt ℝ (fun δ =>
      (arbitrarySplitRawD m ξ r δ).coeff i *
        (ratio (offsetSplitRoot ξ δ j.val))^(i.val+1) *
        rootS (offsetSplitRoot ξ δ j.val)
          ((arbitrarySplitRawD m ξ r δ).eval
            (ratio (offsetSplitRoot ξ δ j.val))) *
        rootF (offsetSplitRoot ξ δ j.val)) 0
    exact (((hD i).mul (hu0.pow (i.val+1))).mul hs).mul hf
  exact ⟨hS, hE, hF, hC, hY⟩

theorem arbitrarySplitFiniteRates_components_differentiableAt
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD m r) m)
    (hB₀ : DensePositive (coalescedRawB m r) m) :
    ∀ i : Fin (m+1),
      DifferentiableAt ℝ (fun δ => (arbitrarySplitFiniteRates m ξ r δ).a i) 0 ∧
      DifferentiableAt ℝ (fun δ => (arbitrarySplitFiniteRates m ξ r δ).b i) 0 ∧
      DifferentiableAt ℝ (fun δ => (arbitrarySplitFiniteRates m ξ r δ).c i) 0 ∧
      DifferentiableAt ℝ (fun δ => (arbitrarySplitFiniteRates m ξ r δ).alpha i) 0 ∧
      DifferentiableAt ℝ (fun δ => (arbitrarySplitFiniteRates m ξ r δ).beta i) 0 ∧
      DifferentiableAt ℝ (fun δ => (arbitrarySplitFiniteRates m ξ r δ).gamma i) 0 := by
  have hA₀ : DensePositive ((1 + Polynomial.X) * coalescedRawD m r) (m+1) :=
    dense_inventory_product hD₀
  intro i
  have hD : DifferentiableAt ℝ
      (fun δ => (arbitrarySplitRawD m ξ r δ).coeff i) 0 :=
    (arbitrarySplitRawD_coeff_differentiable m ξ r hr i).differentiableAt
  have hB : DifferentiableAt ℝ
      (fun δ => (arbitrarySplitRawB m ξ r δ).coeff i) 0 :=
    (arbitrarySplitRawB_coeff_differentiable m ξ r hr i).differentiableAt
  have hAc : DifferentiableAt ℝ (fun δ =>
      (((1 + Polynomial.X) * arbitrarySplitRawD m ξ r δ : ℝ[X]).coeff i.castSucc)) 0 :=
    (arbitrarySplitInventory_coeff_differentiable m ξ r hr i.castSucc).differentiableAt
  have hAs : DifferentiableAt ℝ (fun δ =>
      (((1 + Polynomial.X) * arbitrarySplitRawD m ξ r δ : ℝ[X]).coeff i.succ)) 0 :=
    (arbitrarySplitInventory_coeff_differentiable m ξ r hr i.succ).differentiableAt
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
  exact ⟨((differentiableAt_const _).mul hD).div hAc hAc0,
    hD.div hB hB0, hD.div hB hB0,
    ((differentiableAt_const _).mul hD).div hAs hAs0,
    differentiableAt_const _, differentiableAt_const _⟩

theorem arbitrarySplitRetunedRates_components_differentiableAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1)) :
    ∀ i : Fin (m+2),
      DifferentiableAt ℝ (fun δ => (arbitrarySplitRetunedRates m ξ r τ δ ε).a i) 0 ∧
      DifferentiableAt ℝ (fun δ => (arbitrarySplitRetunedRates m ξ r τ δ ε).b i) 0 ∧
      DifferentiableAt ℝ (fun δ => (arbitrarySplitRetunedRates m ξ r τ δ ε).c i) 0 ∧
      DifferentiableAt ℝ (fun δ => (arbitrarySplitRetunedRates m ξ r τ δ ε).alpha i) 0 ∧
      DifferentiableAt ℝ (fun δ => (arbitrarySplitRetunedRates m ξ r τ δ ε).beta i) 0 ∧
      DifferentiableAt ℝ (fun δ => (arbitrarySplitRetunedRates m ξ r τ δ ε).gamma i) 0 := by
  intro i
  obtain ⟨ha, hb, hc, hα, hβ, hγ⟩ :=
    arbitrarySplitFiniteRates_components_differentiableAt
      (m+1) ξ r hr hD₀ hB₀ i
  have hw (f : (Rates (m+2)) → Fin (m+2) → ℝ)
      (hf : DifferentiableAt ℝ
        (fun δ => f (arbitrarySplitFiniteRates (m+1) ξ r δ) i) 0) :
      DifferentiableAt ℝ (fun δ =>
        coalescedFinalCurrentWeights m τ i *
          f (arbitrarySplitFiniteRates (m+1) ξ r δ) i) 0 :=
    (differentiableAt_const _).mul hf
  dsimp [arbitrarySplitRetunedRates, relaxRates, edgeScaledRates]
  exact ⟨(hw _ ha).div_const ε,
    (((hw _ hb).add (hw _ hc)).div_const ε).sub (hw _ hc),
    hw _ hc, (hw _ hα).div_const ε,
    (((hw _ hβ).add (hw _ hγ)).div_const ε).sub (hw _ hγ),
    hw _ hγ⟩

end
end PhosphorylationStableCapacity
