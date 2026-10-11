module
public import proofs.PhosphorylationStableCapacity.FullCutoffConservation
public import proofs.PhosphorylationStableCapacity.ClassPolytopeTopology

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- Every nonnegative state in a fixed compatibility class lies in a
closed full-species box bounded by the three conserved totals. -/
theorem full_state_norm_le_of_class {n : ℕ}
    (ET FT ST B : ℝ)
    (hB : 0 ≤ B) (hETB : ET ≤ B)
    (hFTB : FT ≤ B) (hSTB : ST ≤ B)
    (x : State n) (hx : NonnegativeState x)
    (hclass : InClass ET FT ST x) :
    ‖toFullSpace x‖ ≤ B := by
  obtain ⟨hS, hE, hF, hC, hD⟩ :=
    nonnegative_class_species_bounds ET FT ST x hx hclass
  change ‖(x.S, (x.E, x.F), (x.C, x.D))‖ ≤ B
  rw [norm_prod_le_iff]
  constructor
  · apply (pi_norm_le_iff_of_nonneg hB).2
    intro i
    simpa [Real.norm_eq_abs, abs_of_nonneg (hx.1 i)] using
      (hS i).trans hSTB
  · rw [norm_prod_le_iff]
    constructor
    · rw [norm_prod_le_iff]
      constructor
      · simpa [Real.norm_eq_abs, abs_of_nonneg hx.2.1] using
          hE.trans hETB
      · simpa [Real.norm_eq_abs, abs_of_nonneg hx.2.2.1] using
          hF.trans hFTB
    · rw [norm_prod_le_iff]
      constructor
      · apply (pi_norm_le_iff_of_nonneg hB).2
        intro i
        simpa [Real.norm_eq_abs,
          abs_of_nonneg (hx.2.2.2.1 i)] using
          (hC i).trans (min_le_left ET ST |>.trans hETB)
      · apply (pi_norm_le_iff_of_nonneg hB).2
        intro i
        simpa [Real.norm_eq_abs,
          abs_of_nonneg (hx.2.2.2.2 i)] using
          (hD i).trans (min_le_left FT ST |>.trans hFTB)

/-- Every nonnegative literal class initial state has a global
forward integral curve of the *physical* full mass-action field.
The construction uses a bounded species cutoff and then proves the
cutoff is inactive along all forward times. -/
theorem exists_full_physical_forward_curve {n : ℕ}
    (ET FT ST : ℝ)
    (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x₀ : State n) (hx₀ : NonnegativeState x₀)
    (hclass₀ : InClass ET FT ST x₀) :
    ∃ γ : ℝ → FullSpace n,
      γ 0 = toFullSpace x₀ ∧
      ∀ t : ℝ, 0 ≤ t →
        HasDerivAt γ (fullFieldEuclid k (γ t)) t ∧
        NonnegativeState (ofFullSpace (γ t)) ∧
        InClass ET FT ST (ofFullSpace (γ t)) := by
  let B : ℝ := max ET (max FT ST)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact le_trans hET.le (le_max_left _ _)
  have hETB : ET ≤ B := le_max_left _ _
  have hFTB : FT ≤ B :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hSTB : ST ≤ B :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨γ, hγ0, hγcut⟩ :=
    fullFieldEuclid_cutoff_global_curve k B hB (toFullSpace x₀)
  have hpositive := full_cutoff_curve_nonnegative
    k hk B hB γ hγcut (by simpa [hγ0, of_toFullSpace] using hx₀)
  have htot := full_cutoff_curve_conserves_totals k B γ hγcut
  refine ⟨γ, hγ0, ?_⟩
  intro t ht
  have hxt : NonnegativeState (ofFullSpace (γ t)) :=
    hpositive t ht
  have hclass : InClass ET FT ST (ofFullSpace (γ t)) := by
    have h := htot t
    rw [hγ0, of_toFullSpace] at h
    exact ⟨h.1.trans hclass₀.1,
      h.2.1.trans hclass₀.2.1,
      h.2.2.trans hclass₀.2.2⟩
  have hnorm : ‖γ t‖ ≤ B := by
    simpa [to_ofFullSpace] using
      full_state_norm_le_of_class ET FT ST B
        hB hETB hFTB hSTB
        (ofFullSpace (γ t)) hxt hclass
  have hclamp : clampFullSpace B (γ t) = γ t :=
    clampFullSpace_eq_of_norm_le B (γ t) hxt hnorm
  exact ⟨by simpa [hclamp] using hγcut t, hxt, hclass⟩

end
end PhosphorylationStableCapacity
