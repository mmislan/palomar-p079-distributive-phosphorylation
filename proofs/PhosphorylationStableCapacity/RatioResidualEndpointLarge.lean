module
public import proofs.PhosphorylationStableCapacity.RatioSubstrateBounds

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Each phosphatase-complex profile monomial is a positive multiple
of one term in the full free-substrate inventory. -/
theorem phosphataseComplexInventory_le_ratio_sum_T {n : ℕ}
    (k : Rates n) (hk : k.Positive)
    (u : ℝ) (hu : 0 ≤ u) :
    phosphataseComplexInventory k u ≤
      (∑ i : Fin n, phosphataseBindingRatio k i) *
        freeSubstrateInventory k u := by
  unfold phosphataseComplexInventory
  calc
    (∑ i : Fin n, phosphataseBindingRatio k i *
      equilibriumWeight k (i.val+1) * u^(i.val+1)) ≤
        ∑ i : Fin n, phosphataseBindingRatio k i *
          freeSubstrateInventory k u := by
            apply Finset.sum_le_sum
            intro i _
            have hterm : equilibriumWeight k (i.val+1) *
                u^(i.val+1) ≤ freeSubstrateInventory k u := by
              have h := Finset.single_le_sum
                (s := Finset.univ) (a := i.succ)
                (f := fun j : Fin (n+1) =>
                  equilibriumWeight k j.val * u^j.val)
                (by
                  intro j _
                  exact mul_nonneg (equilibriumWeight_pos k hk j.val).le
                    (pow_nonneg hu _))
                (Finset.mem_univ i.succ)
              simpa only [Fin.val_succ, freeSubstrateInventory] using h
            calc
              _ = phosphataseBindingRatio k i *
                  (equilibriumWeight k (i.val+1) *
                    u^(i.val+1)) := by ring
              _ ≤ phosphataseBindingRatio k i *
                  freeSubstrateInventory k u :=
                    mul_le_mul_of_nonneg_left hterm
                      (phosphataseBindingRatio_pos k hk i).le
    _ = (∑ i : Fin n, phosphataseBindingRatio k i) *
        freeSubstrateInventory k u := by rw [Finset.sum_mul]

/-- The positive profile cannot accumulate unbounded phosphatase
complex inventory as `u` grows: the substrate total controls it. -/
theorem modelRatioSubstrateLevel_mul_D_le_ST_ratio_sum {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u) :
    modelRatioSubstrateLevel k FT ST u *
      phosphataseComplexInventory k u ≤
      ST * (∑ i : Fin n, phosphataseBindingRatio k i) := by
  let s := modelRatioSubstrateLevel k FT ST u
  let T := freeSubstrateInventory k u
  let D := phosphataseComplexInventory k u
  let M := ∑ i : Fin n, phosphataseBindingRatio k i
  have hs : 0 < s :=
    (modelRatioSubstrateLevel_pos_and_inventory
      hn k hk FT ST u hST hu).1
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ =>
    (phosphataseBindingRatio_pos k hk i).le
  have hDle : D ≤ M*T :=
    phosphataseComplexInventory_le_ratio_sum_T k hk u hu.le
  have hsT : s*T < ST := ratioSubstrateFormula_mul_T_lt_ST FT ST
    T (kinaseComplexInventory k u + D) D hFT hST
    (freeSubstrateInventory_pos k hk hu)
    (add_pos (kinaseComplexInventory_pos k hk hu hn)
      (phosphataseComplexInventory_pos k hk hu hn))
    (phosphataseComplexInventory_pos k hk hu hn)
  calc
    s*D ≤ s*(M*T) := mul_le_mul_of_nonneg_left hDle hs.le
    _ = M*(s*T) := by ring
    _ ≤ ST*M := by
      rw [mul_comm ST M]
      exact mul_le_mul_of_nonneg_left hsT.le hM

/-- The enzyme-total scalar residual is positive at every
sufficiently large positive ratio. -/
theorem ratioEnzymeResidual_positive_for_large_ratio {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST : ℝ) (hET : 0 < ET)
    (hFT : 0 < FT) (hST : 0 < ST) :
    ∃ R : ℝ, 0 < R ∧ ∀ u : ℝ, R < u →
      0 < ratioEnzymeResidual k ET FT ST u := by
  let M := ∑ i : Fin n, phosphataseBindingRatio k i
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ =>
    (phosphataseBindingRatio_pos k hk i).le
  let R := ET*(1+ST*M)/FT
  have hR : 0 < R := by
    dsimp [R]
    positivity
  refine ⟨R, hR, ?_⟩
  intro u hRu
  have hu : 0 < u := lt_trans hR hRu
  have hmain : ET*(1+ST*M) < FT*u := by
    simpa only [mul_comm u FT] using (div_lt_iff₀ hFT).mp hRu
  let s := modelRatioSubstrateLevel k FT ST u
  let B := kinaseComplexInventory k u
  let D := phosphataseComplexInventory k u
  have hs : 0 < s :=
    (modelRatioSubstrateLevel_pos_and_inventory
      hn k hk FT ST u hST hu).1
  have hB : 0 < B := kinaseComplexInventory_pos k hk hu hn
  have hsd : s*D ≤ ST*M :=
    modelRatioSubstrateLevel_mul_D_le_ST_ratio_sum
      hn k hk FT ST u hFT hST hu
  have hBnonneg : 0 ≤ FT*(s*B) := by positivity
  have hETbound : ET*(1+s*D) ≤ ET*(1+ST*M) := by
    nlinarith [mul_le_mul_of_nonneg_left hsd hET.le]
  change 0 < FT*(u+s*B)-ET*(1+s*D)
  linarith

end
end PhosphorylationStableCapacity
