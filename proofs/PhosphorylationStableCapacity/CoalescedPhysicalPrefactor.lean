module
public import proofs.PhosphorylationStableCapacity.SourcePhysicalPrefactor
public import proofs.PhosphorylationStableCapacity.GeneralEquilibriumElimination

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
open scoped BigOperators

/-- The manuscript's inventory difference at a coalesced positive
equilibrium is fixed by the literal two enzyme totals. -/
theorem equilibrium_unit_enzymes_inventory_difference {n : ℕ}
    (k : Rates n) (x : State n) (r : ℝ)
    (hk : k.Positive) (hx : x.Positive) (heq : Equilibrium k x)
    (hE : x.E = 1) (hF : x.F = 1)
    (hET : totalE x = 2*r) (hFT : totalF x = 2) :
    x.S 0 * (kinaseComplexInventory k 1 - phosphataseComplexInventory k 1) =
      2*(r-1) := by
  have hkin := equilibrium_totalE_profile k x hk hx heq
  have hphos := (equilibrium_total_profiles k x hk hx heq).1
  dsimp only at hkin hphos
  rw [hE, hF, hET] at hkin
  rw [hE, hF, hFT] at hphos
  norm_num only [one_div, one_mul] at hkin hphos
  nlinarith

theorem equilibrium_unit_enzymes_physical_prefactor {n : ℕ}
    (k : Rates n) (x : State n) (r : ℝ)
    (hk : k.Positive) (hx : x.Positive) (heq : Equilibrium k x)
    (hE : x.E = 1) (hF : x.F = 1)
    (hET : totalE x = 2*r) (hFT : totalF x = 2) (hr : r ≠ 1) :
    let D := LinearMap.toMatrix (fastBasis n) (fastBasis n)
      (loadedBlockD (totalE x) (totalF x) (totalS x) k
        (loadedCoordOfState x)).toLinearMap
    D.det * (∏ i : Fin (n+1), sourceAugmentedRowWeight k x i) /
      ((sourceConstrainedBindingMass x).det * sourceAugmentedCurrentMatrix k x 0 0) =
    (2*r*(kinaseComplexInventory k 1-phosphataseComplexInventory k 1)/(r-1)) *
      (∏ i : Fin n, (k.b i + k.c i) * k.alpha i * k.gamma i) := by
  dsimp only
  rw [equilibrium_loaded_fast_prefactor_quotient k x hx heq]
  rw [hET, hFT, hE, hF]
  simp only [one_pow, mul_one]
  congr 1
  have h := equilibrium_unit_enzymes_inventory_difference k x r hk hx heq hE hF hET hFT
  have hs := ne_of_gt (hx.1 0)
  have hr1 : r-1 ≠ 0 := sub_ne_zero.mpr hr
  field_simp
  have hscaled := congrArg (fun z : ℝ => r*z) h
  nlinarith [hscaled]

end
end PhosphorylationStableCapacity
