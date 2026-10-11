module
public import proofs.PhosphorylationStableCapacity.ReadoutQuadraticTaylor435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter
open scoped Topology

/-- The quadratic remainder applies to the literal fully phosphorylated
species at two members of one common-class split equilibrium family. -/
theorem arbitrarySplitReadout_actual_quadratic_remainder
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD m r) m)
    (hB₀ : DensePositive (coalescedRawB m r) m)
    (j k : Fin (2*m+1)) :
    ∃ C : ℝ, ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      |(fullyPhosphorylatedReadout m (arbitrarySplitFiniteState m ξ r δ j) -
          fullyPhosphorylatedReadout m (arbitrarySplitFiniteState m ξ r δ k)) -
        (ξ j.val-ξ k.val) *
          deriv (splitReadoutScalar m (coalescedRawD m r)) 3 * δ| ≤
        C * δ^2 := by
  have hDval : (coalescedRawD m r).eval 1 ≠ 0 :=
    ne_of_gt (hD₀.eval_pos (by norm_num))
  obtain ⟨δ₀, C, hδ₀, hbound⟩ :=
    arbitrarySplitReadout_scalar_quadratic_remainder m ξ r
      (ξ j.val) (ξ k.val) hr hDval
  have hsmall : Set.Iio δ₀ ∈ 𝓝[>] (0 : ℝ) :=
    nhdsWithin_le_nhds (Iio_mem_nhds hδ₀)
  have hDnear := arbitrarySplit_conversion_positive_near_zero
    m ξ r hr hD₀ hB₀
  have hroot (i : Fin (2*m+1)) :
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        1 < offsetSplitRoot ξ δ i.val := by
    have hc : Continuous (fun δ : ℝ => offsetSplitRoot ξ δ i.val) := by
      unfold offsetSplitRoot
      fun_prop
    have ht : Tendsto (fun δ : ℝ => offsetSplitRoot ξ δ i.val)
        (𝓝[>] (0 : ℝ)) (𝓝 (3 : ℝ)) := by
      simpa [offsetSplitRoot] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    exact ht.eventually (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 3))
  refine ⟨C, ?_⟩
  filter_upwards [hDnear, hroot j, hroot k, self_mem_nhdsWithin, hsmall]
    with δ hDB hj hk hδpos hδsmall
  have hscalar := hbound δ (le_of_lt hδpos) (le_of_lt hδsmall)
  rw [show fullyPhosphorylatedReadout m
        (arbitrarySplitFiniteState m ξ r δ j) =
        splitReadoutScalar m (arbitrarySplitRawD m ξ r δ)
          (offsetSplitRoot ξ δ j.val) by
        simpa only [splitReadoutScalar] using
          arbitrarySplitReadout_closed_form m ξ r δ hDB.1 j hj,
      show fullyPhosphorylatedReadout m
        (arbitrarySplitFiniteState m ξ r δ k) =
        splitReadoutScalar m (arbitrarySplitRawD m ξ r δ)
          (offsetSplitRoot ξ δ k.val) by
        simpa only [splitReadoutScalar] using
          arbitrarySplitReadout_closed_form m ξ r δ hDB.1 k hk]
  simpa only [offsetSplitRoot] using hscalar

/-- Ordered prescribed roots yield strictly ordered literal readouts for
all sufficiently small positive splitting parameters. -/
theorem arbitrarySplitReadout_actual_strict_order_eventually
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD m r) m)
    (hB₀ : DensePositive (coalescedRawB m r) m)
    (j k : Fin (2*m+1)) (hξ : ξ k.val < ξ j.val) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      fullyPhosphorylatedReadout m (arbitrarySplitFiniteState m ξ r δ k) <
        fullyPhosphorylatedReadout m (arbitrarySplitFiniteState m ξ r δ j) := by
  let Rj : ℝ → ℝ := fun δ =>
    fullyPhosphorylatedReadout m (arbitrarySplitFiniteState m ξ r δ j)
  let Rk : ℝ → ℝ := fun δ =>
    fullyPhosphorylatedReadout m (arbitrarySplitFiniteState m ξ r δ k)
  have hcoef : 0 < (ξ j.val-ξ k.val) *
      deriv (splitReadoutScalar m (coalescedRawD m r)) 3 :=
    mul_pos (sub_pos.mpr hξ)
      (splitReadoutScalar_deriv_three_pos m (coalescedRawD m r) hD₀)
  have hlim := arbitrarySplitReadout_actual_spacing_limit
    m ξ r hr hD₀ hB₀ j k
  have hquot : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      0 < (Rj δ - Rk δ) / δ :=
    hlim.eventually (Ioi_mem_nhds hcoef)
  filter_upwards [hquot, self_mem_nhdsWithin] with δ hq hδ
  have hgap : 0 < Rj δ - Rk δ := by
    have hδpos : 0 < δ := hδ
    have h := mul_pos hq hδpos
    rw [div_mul_cancel₀ _ (ne_of_gt hδpos)] at h
    exact h
  exact sub_pos.mp hgap

end

end PhosphorylationStableCapacity
