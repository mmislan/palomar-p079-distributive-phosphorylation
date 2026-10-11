module
public import Mathlib.Topology.Algebra.Ring.Real
public import proofs.PhosphorylationStableCapacity.FixedRatioTotals
public import proofs.PhosphorylationStableCapacity.GeneralEquilibriumTotals
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The substrate total along the positive fixed-enzyme-ratio
equilibrium profile. The denominator is positive for `s ≥ 0` and
`D ≥ 0`. -/
def ratioSubstrateInventory (FT T K D s : ℝ) : ℝ :=
  s * T + (FT * K) * (s / (1 + D * s))

/-- At every positive enzyme ratio, positive total substrate picks
exactly one positive level-zero substrate. This pivot remains valid
when the enzyme-total pivot `B-uD` vanishes. -/
theorem ratioSubstrateInventory_exists_unique
    (FT ST T K D : ℝ)
    (hFT : 0 < FT) (hST : 0 < ST) (hT : 0 < T)
    (hK : 0 < K) (hD : 0 ≤ D) :
    ∃! s : ℝ, 0 < s ∧ ratioSubstrateInventory FT T K D s = ST := by
  let R : ℝ := ST / T + 1
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hden : ∀ s ∈ Set.Icc (0 : ℝ) R, 1 + D * s ≠ 0 := by
    intro s hs
    have : 0 ≤ D * s := mul_nonneg hD hs.1
    positivity
  have hcont : ContinuousOn (ratioSubstrateInventory FT T K D)
      (Set.Icc (0 : ℝ) R) := by
    unfold ratioSubstrateInventory
    fun_prop (disch := exact hden)
  have hzero : ratioSubstrateInventory FT T K D 0 = 0 := by
    simp [ratioSubstrateInventory]
  have htop : ST < ratioSubstrateInventory FT T K D R := by
    have hRT : ST < R * T := by
      have hcancel : ST / T * T = ST := div_mul_cancel₀ ST (ne_of_gt hT)
      dsimp [R]
      nlinarith
    have hfrac : 0 ≤ (FT * K) * (R / (1 + D * R)) := by
      positivity
    dsimp [ratioSubstrateInventory]
    linarith
  obtain ⟨s, hs, hvalue⟩ :=
    (intermediate_value_Icc hR.le hcont)
      ⟨by rw [hzero]; exact hST.le, htop.le⟩
  have hspos : 0 < s := by
    rcases hs.1.lt_or_eq with h | h
    · exact h
    · subst s
      simp [ratioSubstrateInventory] at hvalue
      linarith
  refine ⟨s, ⟨hspos, hvalue⟩, ?_⟩
  intro s' hs'
  rcases lt_trichotomy s s' with hlt | heq | hgt
  · have h := fixedRatioSubstrateTotal_strict
      FT T K D s s' hFT hT hK hD hspos.le hs'.1.le hlt
    change ratioSubstrateInventory FT T K D s <
      ratioSubstrateInventory FT T K D s' at h
    rw [hvalue, hs'.2] at h
    exact (lt_irrefl ST h).elim
  · exact heq.symm
  · have h := fixedRatioSubstrateTotal_strict
      FT T K D s' s hFT hT hK hD hs'.1.le hspos.le hgt
    change ratioSubstrateInventory FT T K D s' <
      ratioSubstrateInventory FT T K D s at h
    rw [hvalue, hs'.2] at h
    exact (lt_irrefl ST h).elim

/-- The positive substrate-total pivot holds at every positive ratio
for the literal arbitrary-rate phosphorylation system, for every
chain size. It also covers the zero enzyme-total pivot. -/
theorem model_ratio_substrate_inventory_exists_unique {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u) :
    ∃! s : ℝ, 0 < s ∧
      ratioSubstrateInventory FT (freeSubstrateInventory k u)
        (kinaseComplexInventory k u + phosphataseComplexInventory k u)
        (phosphataseComplexInventory k u) s = ST := by
  exact ratioSubstrateInventory_exists_unique FT ST
    (freeSubstrateInventory k u)
    (kinaseComplexInventory k u + phosphataseComplexInventory k u)
    (phosphataseComplexInventory k u)
    hFT hST (freeSubstrateInventory_pos k hk hu)
    (add_pos (kinaseComplexInventory_pos k hk hu hn)
      (phosphataseComplexInventory_pos k hk hu hn))
    (phosphataseComplexInventory_pos k hk hu hn).le

end
end PhosphorylationStableCapacity
