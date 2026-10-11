module
public import proofs.PhosphorylationStableCapacity.SplitAttainmentPreparation

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter
open scoped Topology

/-- Every eventual at-top condition succeeds after finitely many doublings. -/
theorem eventually_atTop_has_doubling_index
    (P : ℝ → Prop) (hP : ∀ᶠ r : ℝ in atTop, P r) :
    ∃ a : ℕ, P ((2 : ℝ)^a) := by
  have ht : Tendsto (fun a : ℕ => (2 : ℝ)^a) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  exact (ht.eventually hP).exists

/-- Every right-neighborhood condition succeeds after finitely many
    halvings. The selected parameter remains strictly positive. -/
theorem eventually_right_has_halving_index
    (P : ℝ → Prop) (hP : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), P t) :
    ∃ b : ℕ, P ((1/2 : ℝ)^b) := by
  have ht : Tendsto (fun b : ℕ => (1/2 : ℝ)^b) atTop
      (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : 0 ≤ (1/2 : ℝ))
        (by norm_num : (1/2 : ℝ) < 1)
    · exact Filter.Eventually.of_forall (fun b => by
        exact pow_pos (by norm_num : (0 : ℝ) < 1/2) b)
  exact (ht.eventually hP).exists

end
end PhosphorylationStableCapacity
