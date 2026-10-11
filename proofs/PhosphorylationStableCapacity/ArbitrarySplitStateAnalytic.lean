module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitEvaluationAnalytic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- All physical species coordinates of the arbitrary prescribed-root
family are analytic at coalescence. -/
theorem arbitrarySplitFiniteState_components_analyticAt
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD m r) m)
    (j : Fin (2*m+1)) :
    (∀ i : Fin (m+2), AnalyticAt ℝ
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).S i) 0) ∧
    AnalyticAt ℝ (fun δ => (arbitrarySplitFiniteState m ξ r δ j).E) 0 ∧
    AnalyticAt ℝ (fun δ => (arbitrarySplitFiniteState m ξ r δ j).F) 0 ∧
    (∀ i : Fin (m+1), AnalyticAt ℝ
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).C i) 0) ∧
    (∀ i : Fin (m+1), AnalyticAt ℝ
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).D i) 0) := by
  have hx : AnalyticAt ℝ
      (fun δ : ℝ => offsetSplitRoot ξ δ j.val) 0 := by
    dsimp [offsetSplitRoot]
    fun_prop
  have hu : AnalyticAt ℝ
      (fun δ : ℝ => ratio (offsetSplitRoot ξ δ j.val)) 0 := by
    dsimp [ratio, offsetSplitRoot]
    fun_prop
  have hd := arbitrarySplitRawD_eval_analyticAt m ξ r hr
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
  have hs : AnalyticAt ℝ (fun δ =>
      rootS (offsetSplitRoot ξ δ j.val)
        ((arbitrarySplitRawD m ξ r δ).eval
          (ratio (offsetSplitRoot ξ δ j.val)))) 0 := by
    unfold rootS
    exact (hx.sub analyticAt_const).div
      ((analyticAt_const.mul hu).mul hd) hden
  have hf : AnalyticAt ℝ
      (fun δ => rootF (offsetSplitRoot ξ δ j.val)) 0 := by
    unfold rootF
    have hdenF : offsetSplitRoot ξ 0 j.val + 1 ≠ 0 := by
      norm_num [offsetSplitRoot]
    exact analyticAt_const.div (hx.add analyticAt_const) hdenF
  have hB (i : Fin (m+1)) : AnalyticAt ℝ
      (fun δ => (arbitrarySplitRawB m ξ r δ).coeff i) 0 :=
    arbitrarySplitRawB_coeff_analyticAt m ξ r hr i
  have hD (i : Fin (m+1)) : AnalyticAt ℝ
      (fun δ => (arbitrarySplitRawD m ξ r δ).coeff i) 0 :=
    arbitrarySplitRawD_coeff_analyticAt m ξ r hr i
  have hA (i : Fin (m+2)) : AnalyticAt ℝ
      (fun δ => (((1 + Polynomial.X) *
        arbitrarySplitRawD m ξ r δ : ℝ[X]).coeff i)) 0 :=
    arbitrarySplitInventory_coeff_analyticAt m ξ r hr i
  have hS (i : Fin (m+2)) : AnalyticAt ℝ
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).S i) 0 := by
    change AnalyticAt ℝ (fun δ =>
      (((1 + Polynomial.X) * arbitrarySplitRawD m ξ r δ : ℝ[X]).coeff i) *
        (ratio (offsetSplitRoot ξ δ j.val))^i.val *
        rootS (offsetSplitRoot ξ δ j.val)
          ((arbitrarySplitRawD m ξ r δ).eval
            (ratio (offsetSplitRoot ξ δ j.val)))) 0
    exact ((hA i).mul (hu.pow i.val)).mul hs
  have hE : AnalyticAt ℝ
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).E) 0 := by
    change AnalyticAt ℝ (fun δ =>
      ratio (offsetSplitRoot ξ δ j.val) *
        rootF (offsetSplitRoot ξ δ j.val)) 0
    exact hu.mul hf
  have hF : AnalyticAt ℝ
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).F) 0 := by
    change AnalyticAt ℝ
      (fun δ => rootF (offsetSplitRoot ξ δ j.val)) 0
    exact hf
  have hC (i : Fin (m+1)) : AnalyticAt ℝ
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).C i) 0 := by
    change AnalyticAt ℝ (fun δ =>
      (arbitrarySplitRawB m ξ r δ).coeff i *
        (ratio (offsetSplitRoot ξ δ j.val))^(i.val+1) *
        rootS (offsetSplitRoot ξ δ j.val)
          ((arbitrarySplitRawD m ξ r δ).eval
            (ratio (offsetSplitRoot ξ δ j.val))) *
        rootF (offsetSplitRoot ξ δ j.val)) 0
    exact (((hB i).mul (hu.pow (i.val+1))).mul hs).mul hf
  have hY (i : Fin (m+1)) : AnalyticAt ℝ
      (fun δ => (arbitrarySplitFiniteState m ξ r δ j).D i) 0 := by
    change AnalyticAt ℝ (fun δ =>
      (arbitrarySplitRawD m ξ r δ).coeff i *
        (ratio (offsetSplitRoot ξ δ j.val))^(i.val+1) *
        rootS (offsetSplitRoot ξ δ j.val)
          ((arbitrarySplitRawD m ξ r δ).eval
            (ratio (offsetSplitRoot ξ δ j.val))) *
        rootF (offsetSplitRoot ξ δ j.val)) 0
    exact (((hD i).mul (hu.pow (i.val+1))).mul hs).mul hf
  exact ⟨hS, hE, hF, hC, hY⟩

end
end PhosphorylationStableCapacity
