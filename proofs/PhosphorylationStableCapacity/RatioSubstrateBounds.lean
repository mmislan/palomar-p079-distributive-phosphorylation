module
public import proofs.PhosphorylationStableCapacity.RatioResidualBijection

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

theorem freeSubstrateInventory_ge_one {n : ℕ}
    (k : Rates n) (hk : k.Positive)
    (u : ℝ) (hu : 0 ≤ u) :
    1 ≤ freeSubstrateInventory k u := by
  have h := Finset.single_le_sum
    (s := Finset.univ) (a := (0 : Fin (n+1)))
    (f := fun j : Fin (n+1) =>
      equilibriumWeight k j.val * u^j.val)
    (by
      intro j _
      exact mul_nonneg (equilibriumWeight_pos k hk j.val).le
        (pow_nonneg hu _))
    (Finset.mem_univ (0 : Fin (n+1)))
  simpa [freeSubstrateInventory, equilibriumWeight] using h

/-- The substrate profile spends a strictly positive part of the
substrate total in complexes, so the free-substrate term is smaller
than the prescribed total. -/
theorem ratioSubstrateFormula_mul_T_lt_ST
    (FT ST T K D : ℝ)
    (hFT : 0 < FT) (hST : 0 < ST) (hT : 0 < T)
    (hK : 0 < K) (hD : 0 < D) :
    ratioSubstrateFormula FT ST T K D * T < ST := by
  let s := ratioSubstrateFormula FT ST T K D
  obtain ⟨hs, hvalue⟩ :=
    ratioSubstrateFormula_pos_and_inventory FT ST T K D hST hT hD
  have hden : 0 < 1+D*s := by nlinarith [mul_pos hD hs]
  have hextra : 0 < (FT*K)*(s/(1+D*s)) :=
    mul_pos (mul_pos hFT hK) (div_pos hs hden)
  dsimp [ratioSubstrateInventory] at hvalue
  linarith

theorem modelRatioSubstrateLevel_lt_ST_div_T {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u) :
    modelRatioSubstrateLevel k FT ST u <
      ST / freeSubstrateInventory k u := by
  have hT : 0 < freeSubstrateInventory k u :=
    freeSubstrateInventory_pos k hk hu
  have hK : 0 < kinaseComplexInventory k u +
      phosphataseComplexInventory k u :=
    add_pos (kinaseComplexInventory_pos k hk hu hn)
      (phosphataseComplexInventory_pos k hk hu hn)
  have hD : 0 < phosphataseComplexInventory k u :=
    phosphataseComplexInventory_pos k hk hu hn
  apply (lt_div_iff₀ hT).2
  exact ratioSubstrateFormula_mul_T_lt_ST FT ST
    (freeSubstrateInventory k u)
    (kinaseComplexInventory k u + phosphataseComplexInventory k u)
    (phosphataseComplexInventory k u)
    hFT hST hT hK hD

theorem modelRatioSubstrateLevel_lt_ST {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u) :
    modelRatioSubstrateLevel k FT ST u < ST := by
  have hs := (modelRatioSubstrateLevel_pos_and_inventory
    hn k hk FT ST u hST hu).1
  have hT := freeSubstrateInventory_ge_one k hk u hu.le
  have hmul := ratioSubstrateFormula_mul_T_lt_ST FT ST
    (freeSubstrateInventory k u)
    (kinaseComplexInventory k u + phosphataseComplexInventory k u)
    (phosphataseComplexInventory k u)
    hFT hST (freeSubstrateInventory_pos k hk hu)
    (add_pos (kinaseComplexInventory_pos k hk hu hn)
      (phosphataseComplexInventory_pos k hk hu hn))
    (phosphataseComplexInventory_pos k hk hu hn)
  have hsle : modelRatioSubstrateLevel k FT ST u ≤
      modelRatioSubstrateLevel k FT ST u *
        freeSubstrateInventory k u := by
    nlinarith
  exact lt_of_le_of_lt hsle hmul

end
end PhosphorylationStableCapacity
