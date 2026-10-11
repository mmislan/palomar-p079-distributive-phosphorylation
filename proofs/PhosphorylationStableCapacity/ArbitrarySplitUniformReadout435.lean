module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitActualSecondOrder435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter
open scoped Topology

/-- One positive error constant and one split neighborhood control all
pairs of the actual physical readouts. Since the states depend only on
the split data, the same bound also holds across every set of currents. -/
theorem arbitrarySplitReadout_uniform_quadratic_remainder
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD m r) m)
    (hB₀ : DensePositive (coalescedRawB m r) m) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j k : Fin (2*m+1),
        |(fullyPhosphorylatedReadout m (arbitrarySplitFiniteState m ξ r δ j) -
            fullyPhosphorylatedReadout m (arbitrarySplitFiniteState m ξ r δ k)) -
          (ξ j.val-ξ k.val) *
            deriv (splitReadoutScalar m (coalescedRawD m r)) 3 * δ| ≤
          C * δ^2 := by
  classical
  choose c hc using fun j k : Fin (2*m+1) =>
    arbitrarySplitReadout_actual_quadratic_remainder m ξ r hr hD₀ hB₀ j k
  let C : ℝ := 1 + ∑ j : Fin (2*m+1), ∑ k : Fin (2*m+1), |c j k|
  have hnonneg : 0 ≤ ∑ j : Fin (2*m+1), ∑ k : Fin (2*m+1), |c j k| :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hC : 0 < C := by dsimp [C]; linarith
  have hle (j k : Fin (2*m+1)) : c j k ≤ C := by
    have hk : |c j k| ≤ ∑ b : Fin (2*m+1), |c j b| :=
      Finset.single_le_sum (f := fun b => |c j b|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have hj : (∑ b : Fin (2*m+1), |c j b|) ≤
        ∑ a : Fin (2*m+1), ∑ b : Fin (2*m+1), |c a b| :=
      Finset.single_le_sum (f := fun a => ∑ b : Fin (2*m+1), |c a b|)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
        (Finset.mem_univ j)
    have hcabs := le_abs_self (c j k)
    dsimp [C]
    linarith
  have hall : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j k : Fin (2*m+1),
        |(fullyPhosphorylatedReadout m (arbitrarySplitFiniteState m ξ r δ j) -
            fullyPhosphorylatedReadout m (arbitrarySplitFiniteState m ξ r δ k)) -
          (ξ j.val-ξ k.val) *
            deriv (splitReadoutScalar m (coalescedRawD m r)) 3 * δ| ≤
          c j k * δ^2 :=
    Filter.eventually_all.2 (fun j => Filter.eventually_all.2 (hc j))
  refine ⟨C, hC, ?_⟩
  filter_upwards [hall] with δ hδ j k
  exact (hδ j k).trans (mul_le_mul_of_nonneg_right (hle j k) (sq_nonneg δ))

end
end PhosphorylationStableCapacity
