module
public import proofs.PhosphorylationStableCapacity.GeneralEquilibriumTotals

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The enzyme ratio injects the set of positive literal equilibria
in a fixed class into the positive real line. This handles the
exceptional denominator case of the universal polynomial reduction
without a case split. -/
theorem positive_equilibria_enzyme_ratio_injective {n : ℕ}
    (k : Rates n) (x y : State n)
    (hn : 0 < n) (hk : k.Positive)
    (hx : x.Positive) (hy : y.Positive)
    (heqx : Equilibrium k x) (heqy : Equilibrium k y)
    (hFT : totalF x = totalF y)
    (hST : totalS x = totalS y)
    (hEF : x.E/x.F = y.E/y.F) : x = y := by
  let u := x.E/x.F
  let T := freeSubstrateInventory k u
  let B := kinaseComplexInventory k u
  let D := phosphataseComplexInventory k u
  let K := B+D
  have hu : 0 < u := div_pos hx.2.1 hx.2.2.1
  have hT : 0 < T := freeSubstrateInventory_pos k hk hu
  have hB : 0 < B := kinaseComplexInventory_pos k hk hu hn
  have hD : 0 < D := phosphataseComplexInventory_pos k hk hu hn
  have hK : 0 < K := add_pos hB hD
  obtain ⟨hFx, hSx⟩ := equilibrium_total_profiles k x hk hx heqx
  obtain ⟨hFy, hSy⟩ := equilibrium_total_profiles k y hk hy heqy
  have hFy' : totalF x = y.F*(1+y.S 0*D) := by
    rw [hFT]
    simpa only [u, D, hEF.symm] using hFy
  have hSy' : totalS x = y.S 0*T+y.F*y.S 0*K := by
    rw [hST]
    simpa only [u, T, B, D, K, hEF.symm] using hSy
  have hFTpos : 0 < totalF x := by
    rw [hFx]
    exact mul_pos hx.2.2.1
      (by nlinarith [mul_nonneg (hx.1 0).le hD.le])
  have hFx' : totalF x = x.F*(1+D*x.S 0) := by
    calc
      totalF x = x.F*(1+x.S 0*D) := hFx
      _ = x.F*(1+D*x.S 0) := by ring
  have hFy'' : totalF x = y.F*(1+D*y.S 0) := by
    calc
      totalF x = y.F*(1+y.S 0*D) := hFy'
      _ = y.F*(1+D*y.S 0) := by ring
  have hunique := fixedRatioTotals_unique
    (totalF x) (totalS x) T K D (x.S 0) (y.S 0) x.F y.F
    hFTpos hT hK hD.le (hx.1 0) (hy.1 0)
    hFx' hFy'' hSx hSy'
  obtain ⟨hS0, hF⟩ := hunique
  have hE : x.E = y.E := by
    rw [hF] at hEF
    exact (div_left_inj' (ne_of_gt hy.2.2.1)).mp hEF
  have hS : ∀ j : Fin (n+1), x.S j = y.S j :=
    equilibrium_substrate_profile_unique k x y hk hx hy
      heqx heqy hEF hS0
  have hC (i : Fin n) : x.C i = y.C i := by
    have hCx := (equilibrium_complex_profile k x hk hx heqx i).1
    have hCy := (equilibrium_complex_profile k y hk hy heqy i).1
    rw [hF, hS0, hE] at hCx
    exact hCx.trans hCy.symm
  have hDspecies (i : Fin n) : x.D i = y.D i := by
    have hDx := (equilibrium_complex_profile k x hk hx heqx i).2
    have hDy := (equilibrium_complex_profile k y hk hy heqy i).2
    rw [hF, hS0, hE] at hDx
    exact hDx.trans hDy.symm
  cases x with
  | mk Sx Ex Fx Cx Dx =>
    cases y with
    | mk Sy Ey Fy Cy Dy =>
      congr 1
      · funext j
        exact hS j
      · funext i
        exact hC i
      · funext i
        exact hDspecies i

end
end PhosphorylationStableCapacity
