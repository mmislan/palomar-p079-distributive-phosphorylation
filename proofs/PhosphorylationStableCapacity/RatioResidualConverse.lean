module
public import proofs.PhosphorylationStableCapacity.RatioProfileTotals

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Every positive root of the smooth scalar residual reconstructs a
literal positive mass-action equilibrium with the prescribed three
conserved totals and exactly that free-enzyme ratio. -/
theorem positive_ratioEnzymeResidual_root_realizes_equilibrium {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u)
    (hroot : ratioEnzymeResidual k ET FT ST u = 0) :
    ∃ x : State n, x.Positive ∧ Equilibrium k x ∧
      InClass ET FT ST x ∧ x.E/x.F = u := by
  let T := freeSubstrateInventory k u
  let B := kinaseComplexInventory k u
  let D := phosphataseComplexInventory k u
  let s := modelRatioSubstrateLevel k FT ST u
  let f := FT/(1+s*D)
  let x := ratioProfileState k u s f
  obtain ⟨hs, hsub⟩ :=
    modelRatioSubstrateLevel_pos_and_inventory hn k hk FT ST u hST hu
  have hD : 0 < D := phosphataseComplexInventory_pos k hk hu hn
  have hdenpos : 0 < 1+s*D := by nlinarith [mul_pos hs hD]
  have hden : 1+s*D ≠ 0 := ne_of_gt hdenpos
  have hf : 0 < f := div_pos hFT hdenpos
  have hFtotal : f*(1+s*D) = FT := by
    dsimp [f]
    field_simp
  have hEres : FT*(u+s*B)-ET*(1+s*D)=0 := by
    simpa only [ratioEnzymeResidual, B, D, s] using hroot
  have hEtotal : f*(u+s*B) = ET := by
    dsimp [f]
    field_simp
    nlinarith [hEres]
  have hStotal : s*T+f*s*(B+D) = ST := by
    calc
      s*T+f*s*(B+D) = ratioSubstrateInventory FT T (B+D) D s := by
        dsimp [f, ratioSubstrateInventory]
        ring
      _ = ST := hsub
  obtain ⟨htE, htF, htS⟩ :=
    ratioProfileState_totals k hk u s f hu hs hf
  have hx : x.Positive := ratioProfileState_positive k hk u s f hu hs hf
  have heq : Equilibrium k x := ratioProfileState_equilibrium k hk u s f
  refine ⟨x, hx, heq, ?_, ?_⟩
  · exact ⟨htE.trans hEtotal, htF.trans hFtotal,
      htS.trans hStotal⟩
  · dsimp [x, ratioProfileState]
    field_simp [ne_of_gt hf]

end
end PhosphorylationStableCapacity
