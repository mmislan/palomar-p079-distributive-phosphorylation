module
public import proofs.PhosphorylationStableCapacity.RatioResidualEndpointSmall
public import proofs.PhosphorylationStableCapacity.RatioResidualEndpointLarge

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Every positive literal rate list and positive compatibility
triple has at least one positive equilibrium, for every chain size.
The proof uses the strictly verified scalar chart and opposite
endpoint signs, without a degree or fixed-point axiom. -/
theorem positive_equilibrium_exists_for_positive_totals {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST : ℝ) (hET : 0 < ET)
    (hFT : 0 < FT) (hST : 0 < ST) :
    ∃ x : State n, x.Positive ∧ Equilibrium k x ∧
      InClass ET FT ST x := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    ratioEnzymeResidual_negative_near_zero
      hn k hk ET FT ST hET hFT hST
  obtain ⟨R, hR, hlarge⟩ :=
    ratioEnzymeResidual_positive_for_large_ratio
      hn k hk ET FT ST hET hFT hST
  let a := min (δ/2) (R/2)
  let b := R+1
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have haδ : a < δ := lt_of_le_of_lt (min_le_left ..) (by linarith)
  have hab : a ≤ b := by
    have h := min_le_right (δ/2) (R/2)
    dsimp [a, b]
    linarith
  have hRb : R < b := by dsimp [b]; linarith
  have hneg : ratioEnzymeResidual k ET FT ST a < 0 :=
    hsmall a ha haδ
  have hpos : 0 < ratioEnzymeResidual k ET FT ST b :=
    hlarge b hRb
  have hcont : ContinuousOn (ratioEnzymeResidual k ET FT ST)
      (Set.Icc a b) := by
    intro u hu
    have hu : 0 < u := lt_of_lt_of_le ha hu.1
    exact (ratioEnzymeResidual_differentiableAt
      hn k hk ET FT ST u hST hu).continuousAt.continuousWithinAt
  have hzero : (0 : ℝ) ∈ Set.Icc
      (ratioEnzymeResidual k ET FT ST a)
      (ratioEnzymeResidual k ET FT ST b) :=
    ⟨hneg.le, hpos.le⟩
  obtain ⟨u, hu, hroot⟩ := (Set.mem_image _ _ _).mp
    (intermediate_value_Icc hab hcont hzero)
  have hu' : 0 < u := lt_of_lt_of_le ha hu.1
  obtain ⟨x, hx, heq, hclass, _hratio⟩ :=
    positive_ratioEnzymeResidual_root_realizes_equilibrium
      hn k hk ET FT ST u hFT hST hu' hroot
  exact ⟨x, hx, heq, hclass⟩

end
end PhosphorylationStableCapacity
