module
public import proofs.PhosphorylationStableCapacity.SplitRetunedSource
public import proofs.PhosphorylationStableCapacity.LoadedBindingMassOrientation

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Difference of phosphatase and kinase bound-enzyme fractions attached
to each substrate level. -/
def sourceOccupancyDifference {n : ℕ} (x : State n)
    (j : Fin (n+1)) : ℝ :=
  sourceLevelD x j / totalF x - sourceLevelC x j / totalE x

/-- Summing those level fractions leaves the free-enzyme fraction
difference; this is the scalar factor in the augmented-current chart. -/
theorem sourceOccupancyDifference_sum {n : ℕ}
    (x : State n) (hx : x.Positive) :
    (∑ j : Fin (n+1), sourceOccupancyDifference x j) =
      x.E / totalE x - x.F / totalF x := by
  have hET : totalE x ≠ 0 := by
    have hsum : 0 ≤ ∑ i, x.C i :=
      Finset.sum_nonneg (fun i _ => (hx.2.2.2.1 i).le)
    exact ne_of_gt (add_pos_of_pos_of_nonneg hx.2.1 hsum)
  have hFT : totalF x ≠ 0 := by
    have hsum : 0 ≤ ∑ i, x.D i :=
      Finset.sum_nonneg (fun i _ => (hx.2.2.2.2 i).le)
    exact ne_of_gt (add_pos_of_pos_of_nonneg hx.2.2.1 hsum)
  simp only [sourceOccupancyDifference, Finset.sum_sub_distrib,
    ← Finset.sum_div, sourceLevelD_sum, sourceLevelC_sum]
  dsimp [totalE, totalF] at hET hFT ⊢
  field_simp [hET, hFT]
  ring

/-- The occupancy difference is negative when the free-enzyme ratio
is below the ratio of the two fixed enzyme totals. -/
theorem sourceOccupancyDifference_sum_neg_of_ratio {n : ℕ}
    (x : State n) (hx : x.Positive) (r : ℝ) (hr : 0 < r)
    (hET : totalE x = 2*r) (hFT : totalF x = 2)
    (hratio : x.E / x.F < r) :
    (∑ j : Fin (n+1), sourceOccupancyDifference x j) < 0 := by
  rw [sourceOccupancyDifference_sum x hx, hET, hFT]
  have hE : x.E < r*x.F := (div_lt_iff₀ hx.2.2.1).mp hratio
  have hformula : x.E / (2*r) - x.F / 2 =
      (x.E - r*x.F) / (2*r) := by
    field_simp
  rw [hformula]
  exact div_neg_of_neg_of_pos (sub_neg.mpr hE) (mul_pos (by norm_num) hr)

/-- At every prescribed split root the enzyme-occupancy factor needed
for the determinant-to-scalar-slope orientation is strictly negative. -/
theorem split_sourceOccupancyDifference_sum_neg
    (m : ℕ) (r δ : ℝ) (hr : 0 < r) (hδ : 0 ≤ δ)
    (hD : DensePositive (splitRawD m r δ) m)
    (hB : DensePositive (splitRawB m r δ) m)
    (j : Fin (2*m+1))
    (hv : 0 < r - ratio (splitRoot δ j.val)) :
    (∑ l : Fin (m+2), sourceOccupancyDifference
      (splitFiniteState m r δ j) l) < 0 := by
  obtain ⟨_, hx, _, hET, hFT, _⟩ :=
    splitFiniteState_source_of_conversion_positive m r δ hδ hD hB j
  have hxroot : 1 < splitRoot δ j.val := by
    have hnonneg : 0 ≤ δ * (j.val : ℝ) :=
      mul_nonneg hδ (Nat.cast_nonneg _)
    dsimp [splitRoot]
    linarith
  have hf : rootF (splitRoot δ j.val) ≠ 0 := by
    unfold rootF
    exact ne_of_gt (div_pos (by norm_num) (by linarith))
  have hratio :
      (splitFiniteState m r δ j).E /
        (splitFiniteState m r δ j).F =
      ratio (splitRoot δ j.val) := by
    exact reconstruct_ratio _ _ _ _ _ _ hf
  apply sourceOccupancyDifference_sum_neg_of_ratio
    (splitFiniteState m r δ j) hx r hr hET hFT
  rw [hratio]
  linarith

end
end PhosphorylationStableCapacity
