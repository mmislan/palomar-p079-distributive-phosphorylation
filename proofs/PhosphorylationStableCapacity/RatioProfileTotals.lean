module
public import proofs.PhosphorylationStableCapacity.RatioProfileState

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The exact conserved totals of every positive profile state. -/
theorem ratioProfileState_totals {n : ℕ}
    (k : Rates n) (hk : k.Positive)
    (u s f : ℝ) (hu : 0 < u) (hs : 0 < s) (hf : 0 < f) :
    totalE (ratioProfileState k u s f) =
      f*(u+s*kinaseComplexInventory k u) ∧
    totalF (ratioProfileState k u s f) =
      f*(1+s*phosphataseComplexInventory k u) ∧
    totalS (ratioProfileState k u s f) =
      s*freeSubstrateInventory k u +
        f*s*(kinaseComplexInventory k u+
          phosphataseComplexInventory k u) := by
  let x := ratioProfileState k u s f
  have hx : x.Positive := ratioProfileState_positive k hk u s f hu hs hf
  have heq : Equilibrium k x := ratioProfileState_equilibrium k hk u s f
  have hratio : x.E/x.F = u := by
    dsimp [x, ratioProfileState]
    field_simp [ne_of_gt hf]
  have hS0 : x.S 0 = s := by
    simp [x, ratioProfileState, equilibriumWeight]
  have hE := equilibrium_totalE_profile k x hk hx heq
  obtain ⟨hF, hS⟩ := equilibrium_total_profiles k x hk hx heq
  dsimp at hE hF hS
  rw [hratio, hS0] at hE hF hS
  exact ⟨hE, hF, hS⟩

end
end PhosphorylationStableCapacity
