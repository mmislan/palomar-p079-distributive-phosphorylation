module
public import proofs.PhosphorylationStableCapacity.RatioSubstrateChart
public import proofs.PhosphorylationStableCapacity.GeneralEquilibriumElimination

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The remaining kinase-total equation after the positive
substrate-total pivot has been solved explicitly. -/
def ratioEnzymeResidual {n : ℕ} (k : Rates n)
    (ET FT ST u : ℝ) : ℝ :=
  let s := modelRatioSubstrateLevel k FT ST u
  FT * (u + s * kinaseComplexInventory k u) -
    ET * (1 + s * phosphataseComplexInventory k u)

theorem ratioEnzymeResidual_differentiableAt {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST u : ℝ) (hST : 0 < ST) (hu : 0 < u) :
    DifferentiableAt ℝ (ratioEnzymeResidual k ET FT ST) u := by
  have hs := modelRatioSubstrateLevel_differentiableAt
    hn k hk FT ST u hST hu
  unfold ratioEnzymeResidual
  simp only [kinaseComplexInventory, phosphataseComplexInventory]
  fun_prop (disch := assumption)

/-- Every positive literal equilibrium in the fixed compatibility
class lies at a root of the new scalar residual. This statement is
valid even when the older enzyme-total pivot vanishes. -/
theorem positive_equilibrium_ratioEnzymeResidual_zero {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (x : State n) (hx : x.Positive)
    (heq : Equilibrium k x) (hclass : InClass ET FT ST x) :
    ratioEnzymeResidual k ET FT ST (x.E/x.F) = 0 := by
  let u := x.E/x.F
  let T := freeSubstrateInventory k u
  let B := kinaseComplexInventory k u
  let D := phosphataseComplexInventory k u
  let K := B+D
  let s := x.S 0
  have hu : 0 < u := div_pos hx.2.1 hx.2.2.1
  have hs : 0 < s := hx.1 0
  have hD : 0 < D := phosphataseComplexInventory_pos k hk hu hn
  have hden : 1+D*s ≠ 0 := ne_of_gt (by nlinarith [mul_pos hD hs])
  obtain ⟨hF, hS⟩ := equilibrium_total_profiles k x hk hx heq
  have hF' : FT = x.F*(1+D*s) := by
    rw [← hclass.2.1]
    simpa only [u, D, s, mul_comm] using hF
  have hS' : ST = s*T+x.F*s*K := by
    rw [← hclass.2.2]
    simpa only [u, T, B, D, K, s] using hS
  have hf : x.F = FT/(1+D*s) := by
    apply (eq_div_iff hden).2
    linarith [hF']
  have hsub : ratioSubstrateInventory FT T K D s = ST := by
    calc
      ratioSubstrateInventory FT T K D s =
          s*T + (FT/(1+D*s))*s*K := by
        dsimp [ratioSubstrateInventory]
        ring
      _ = ST := by rw [←hf]; exact hS'.symm
  obtain ⟨sw, hsw, hunique⟩ :=
    model_ratio_substrate_inventory_exists_unique
      hn k hk FT ST u hFT hST hu
  have hformula :=
    modelRatioSubstrateLevel_pos_and_inventory hn k hk FT ST u hST hu
  have hchart : modelRatioSubstrateLevel k FT ST u = s := by
    exact (hunique _ hformula).trans (hunique _ ⟨hs, hsub⟩).symm
  have hE : ET = x.F*(u+s*B) := by
    rw [←hclass.1]
    simpa only [u, B, s] using
      (equilibrium_totalE_profile k x hk hx heq)
  dsimp [ratioEnzymeResidual]
  change FT*(u+modelRatioSubstrateLevel k FT ST u*B) -
    ET*(1+modelRatioSubstrateLevel k FT ST u*D)=0
  rw [hchart, hE, hF']
  ring

end
end PhosphorylationStableCapacity
