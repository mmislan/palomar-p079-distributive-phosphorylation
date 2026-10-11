module
public import proofs.PhosphorylationStableCapacity.CoalescedFiniteTotals
public import proofs.PhosphorylationStableCapacity.CoalescedTwoModeBlock

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness
open scoped Topology

noncomputable section

theorem coalescedFiniteCLevel_occupied_sum (m : ℕ) (r : ℝ) :
    (∑ i : Fin (m + 2), coalescedFiniteCLevel m r i.castSucc) =
      ∑ i : Fin (m + 2), (coalescedFiniteState (m + 1) r).C i := by
  apply Finset.sum_congr rfl
  intro i _
  simp [coalescedFiniteCLevel, i.isLt]

theorem coalescedFiniteSLevel_occupied_sum (m : ℕ) (r : ℝ)
    (hS : (∑ i : Fin (m + 3),
      (coalescedFiniteState (m + 1) r).S i) = 2) :
    (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).S i.castSucc) =
      2 - (coalescedFiniteState (m + 1) r).D (Fin.last (m + 1)) := by
  rw [Fin.sum_univ_castSucc] at hS
  rw [coalescedFiniteState_lastS_eq_lastD (m + 1) r] at hS
  linarith

theorem coalescedFullMass_occupied_row_sum (m : ℕ) (r : ℝ)
    (i : Fin (m + 2)) :
    (∑ j : Fin (m + 2),
      coalescedFullMass m r i.castSucc j.castSucc) =
      (coalescedFiniteState (m + 1) r).S i.castSucc +
        coalescedFiniteCLevel m r i.castSucc +
        coalescedFiniteYLevel m r i.castSucc -
        coalescedFiniteCLevel m r i.castSucc *
          (∑ j : Fin (m + 2), coalescedFiniteCLevel m r j.castSucc) /
            (2 * r) -
        coalescedFiniteYLevel m r i.castSucc *
          (∑ j : Fin (m + 2), coalescedFiniteYLevel m r j.castSucc) / 2 := by
  simp only [coalescedFullMass, Fin.castSucc_inj,
    Finset.sum_sub_distrib]
  rw [← Finset.sum_div, ← Finset.sum_div]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp

theorem coalescedFullMass_occupied_double_sum (m : ℕ) (r : ℝ) :
    (∑ i : Fin (m + 2), ∑ j : Fin (m + 2),
      coalescedFullMass m r i.castSucc j.castSucc) =
      (∑ i : Fin (m + 2),
        (coalescedFiniteState (m + 1) r).S i.castSucc) +
      (∑ i : Fin (m + 2), coalescedFiniteCLevel m r i.castSucc) +
      (∑ i : Fin (m + 2), coalescedFiniteYLevel m r i.castSucc) -
      (∑ i : Fin (m + 2), coalescedFiniteCLevel m r i.castSucc) ^ 2 /
        (2 * r) -
      (∑ i : Fin (m + 2), coalescedFiniteYLevel m r i.castSucc) ^ 2 / 2 := by
  simp_rw [coalescedFullMass_occupied_row_sum]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.sum_div, ← Finset.sum_div]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

theorem coalescedFiniteYLevel_sum (m : ℕ) (r : ℝ) :
    (∑ i : Fin (m + 3), coalescedFiniteYLevel m r i) =
      ∑ i : Fin (m + 2), (coalescedFiniteState (m + 1) r).D i := by
  rw [Fin.sum_univ_succ]
  simp [coalescedFiniteYLevel, Fin.val_succ]

theorem coalescedFiniteYLevel_last (m : ℕ) (r : ℝ) :
    coalescedFiniteYLevel m r (Fin.last (m + 2)) =
      (coalescedFiniteState (m + 1) r).D (Fin.last (m + 1)) := by
  simp [coalescedFiniteYLevel, Fin.val_last]
  congr 1

theorem coalescedFiniteYLevel_occupied_sum (m : ℕ) (r : ℝ)
    (hD : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).D i) = 1) :
    (∑ i : Fin (m + 2), coalescedFiniteYLevel m r i.castSucc) =
      1 - (coalescedFiniteState (m + 1) r).D (Fin.last (m + 1)) := by
  have hsum := coalescedFiniteYLevel_sum m r
  rw [Fin.sum_univ_castSucc] at hsum
  rw [coalescedFiniteYLevel_last, hD] at hsum
  linarith

theorem coalescedFullMass_occupied_sum_formula (m : ℕ) (r : ℝ)
    (hr : r ≠ 0)
    (hC : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).C i) = 2 * r - 1)
    (hD : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).D i) = 1)
    (hS : (∑ i : Fin (m + 3),
      (coalescedFiniteState (m + 1) r).S i) = 2) :
    (∑ i : Fin (m + 2), ∑ j : Fin (m + 2),
      coalescedFullMass m r i.castSucc j.castSucc) =
      7 / 2 - (coalescedFiniteState (m + 1) r).D (Fin.last (m + 1)) -
        ((coalescedFiniteState (m + 1) r).D (Fin.last (m + 1))) ^ 2 / 2 -
        1 / (2 * r) := by
  rw [coalescedFullMass_occupied_double_sum,
    coalescedFiniteSLevel_occupied_sum m r hS,
    coalescedFiniteCLevel_occupied_sum m r,
    coalescedFiniteYLevel_occupied_sum m r hD, hC]
  field_simp [hr]
  ring

theorem coalescedFullMass_occupied_sum_tendsto (m : ℕ) :
    Tendsto (fun r : ℝ => ∑ i : Fin (m + 2), ∑ j : Fin (m + 2),
      coalescedFullMass m r i.castSucc j.castSucc) atTop
      (𝓝 (7 / 2 - coalescedV m - (coalescedV m) ^ 2 / 2)) := by
  have hv : Tendsto (fun r : ℝ =>
      (coalescedFiniteState (m + 1) r).D (Fin.last (m + 1)))
      atTop (𝓝 (coalescedV m)) := by
    simpa [coalescedV, coalescedYNext] using
      coalescedFiniteState_D_tendsto (m + 1) (Fin.last (m + 1))
  have hinv : Tendsto (fun r : ℝ => 1 / (2 * r)) atTop (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => (1 / 2 : ℝ) * r⁻¹)
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun r : ℝ => (1 / 2 : ℝ) * r⁻¹) atTop
          (𝓝 ((1 / 2 : ℝ) * 0)))
    simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm] using h
  have hconst : Tendsto (fun _ : ℝ => (7 / 2 : ℝ))
      atTop (𝓝 (7 / 2 : ℝ)) := tendsto_const_nhds
  have hlim : Tendsto (fun r : ℝ =>
      7 / 2 - (coalescedFiniteState (m + 1) r).D (Fin.last (m + 1)) -
        ((coalescedFiniteState (m + 1) r).D (Fin.last (m + 1))) ^ 2 / 2 -
        1 / (2 * r)) atTop
      (𝓝 (7 / 2 - coalescedV m - (coalescedV m) ^ 2 / 2)) := by
    simpa using ((hconst.sub hv).sub ((hv.pow 2).div_const 2)).sub hinv
  apply hlim.congr'
  filter_upwards [coalescedFiniteState_eventually_component_totals (m + 1),
    eventually_gt_atTop (0 : ℝ)] with r h hr
  exact (coalescedFullMass_occupied_sum_formula m r (ne_of_gt hr)
    h.1 h.2.1 h.2.2).symm

theorem coalescedFullMass_occupied_final_entry (m : ℕ) (r : ℝ)
    (i : Fin (m + 2)) :
    coalescedFullMass m r i.castSucc (Fin.last (m + 2)) =
      -coalescedFiniteYLevel m r i.castSucc *
        coalescedFiniteYLevel m r (Fin.last (m + 2)) / 2 := by
  have hne : i.castSucc ≠ Fin.last (m + 2) := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  simp [coalescedFullMass, coalescedFiniteCLevel, hne,
    Fin.val_last]
  ring

theorem coalescedFullMass_cross_sum (m : ℕ) (r : ℝ)
    (hD : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).D i) = 1) :
    (∑ i : Fin (m + 2),
      coalescedFullMass m r i.castSucc (Fin.last (m + 2))) =
      (coalescedFiniteState (m + 1) r).D (Fin.last (m + 1)) *
        ((coalescedFiniteState (m + 1) r).D (Fin.last (m + 1)) - 1) / 2 := by
  calc
    (∑ i : Fin (m + 2),
      coalescedFullMass m r i.castSucc (Fin.last (m + 2))) =
        ∑ i : Fin (m + 2),
          -(coalescedFiniteYLevel m r i.castSucc *
            coalescedFiniteYLevel m r (Fin.last (m + 2))) / 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [coalescedFullMass_occupied_final_entry]
      ring
    _ = -(∑ i : Fin (m + 2), coalescedFiniteYLevel m r i.castSucc) *
        coalescedFiniteYLevel m r (Fin.last (m + 2)) / 2 := by
      rw [← Finset.sum_div, Finset.sum_neg_distrib, ← Finset.sum_mul]
      ring
    _ = (coalescedFiniteState (m + 1) r).D (Fin.last (m + 1)) *
        ((coalescedFiniteState (m + 1) r).D (Fin.last (m + 1)) - 1) / 2 := by
      rw [coalescedFiniteYLevel_occupied_sum m r hD,
        coalescedFiniteYLevel_last]
      ring

theorem coalescedFullMass_cross_sum_tendsto (m : ℕ) :
    Tendsto (fun r : ℝ => ∑ i : Fin (m + 2),
      coalescedFullMass m r i.castSucc (Fin.last (m + 2))) atTop
      (𝓝 (coalescedV m * (coalescedV m - 1) / 2)) := by
  have hv : Tendsto (fun r : ℝ =>
      (coalescedFiniteState (m + 1) r).D (Fin.last (m + 1)))
      atTop (𝓝 (coalescedV m)) := by
    simpa [coalescedV, coalescedYNext] using
      coalescedFiniteState_D_tendsto (m + 1) (Fin.last (m + 1))
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hlim := (hv.mul (hv.sub hone)).div_const 2
  apply hlim.congr'
  filter_upwards [coalescedFiniteState_eventually_component_totals (m + 1)]
    with r h
  exact (coalescedFullMass_cross_sum m r h.2.1).symm

theorem coalescedFullMass_symm (m : ℕ) (r : ℝ)
    (i j : Fin (m + 3)) :
    coalescedFullMass m r i j = coalescedFullMass m r j i := by
  unfold coalescedFullMass
  by_cases hij : i = j
  · subst j
    ring
  · have hji : j ≠ i := Ne.symm hij
    simp [hij, hji]
    ring

theorem coalescedFullMass_reverse_cross_sum_tendsto (m : ℕ) :
    Tendsto (fun r : ℝ => ∑ i : Fin (m + 2),
      coalescedFullMass m r (Fin.last (m + 2)) i.castSucc) atTop
      (𝓝 (coalescedV m * (coalescedV m - 1) / 2)) := by
  have h := coalescedFullMass_cross_sum_tendsto m
  apply h.congr'
  filter_upwards [] with r
  apply Finset.sum_congr rfl
  intro i _
  exact (coalescedFullMass_symm m r _ _).symm

/-- The final-level diagonal entry of the literal candidate loaded mass
matrix is exactly the lower-right two-mode expression. -/
theorem coalescedFullMass_final_entry (m : ℕ) (r : ℝ) :
    coalescedFullMass m r (Fin.last (m + 2)) (Fin.last (m + 2)) =
      2 * (coalescedFiniteState (m + 1) r).D (Fin.last (m + 1)) -
        ((coalescedFiniteState (m + 1) r).D (Fin.last (m + 1))) ^ 2 / 2 := by
  have hS := coalescedFiniteState_lastS_eq_lastD (m + 1) r
  simp only [coalescedFullMass, ite_true]
  simp [coalescedFiniteCLevel, coalescedFiniteYLevel,
    Fin.val_last, hS]
  have hindex : (⟨m + 1, by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) := by
    ext
    simp [Fin.val_last]
  rw [hindex]
  ring

theorem coalescedFullMass_final_entry_tendsto (m : ℕ) :
    Tendsto (fun r : ℝ =>
      coalescedFullMass m r (Fin.last (m + 2)) (Fin.last (m + 2)))
      atTop (𝓝 (2 * coalescedV m - (coalescedV m) ^ 2 / 2)) := by
  have hv : Tendsto (fun r : ℝ =>
      (coalescedFiniteState (m + 1) r).D (Fin.last (m + 1)))
      atTop (𝓝 (coalescedV m)) := by
    simpa [coalescedV, coalescedYNext] using
      coalescedFiniteState_D_tendsto (m + 1) (Fin.last (m + 1))
  have htwo : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (𝓝 2) :=
    tendsto_const_nhds
  have h := (htwo.mul hv).sub ((hv.pow 2).div_const 2)
  simpa [coalescedFullMass_final_entry] using h

/-- The literal candidate loaded mass matrix, projected onto the two
leading kernel modes. This is a matrix of finite-parameter concentration
expressions; identifying it with a slow-field derivative remains open. -/
def coalescedProjectedMass (m : ℕ) (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(∑ i : Fin (m + 2), ∑ j : Fin (m + 2),
      coalescedFullMass m r i.castSucc j.castSucc),
    (∑ i : Fin (m + 2),
      coalescedFullMass m r i.castSucc (Fin.last (m + 2)));
    (∑ i : Fin (m + 2),
      coalescedFullMass m r (Fin.last (m + 2)) i.castSucc),
    coalescedFullMass m r (Fin.last (m + 2)) (Fin.last (m + 2))]

/-- All four entries of the projected literal candidate mass matrix converge
to the proposed order-one two-mode block. -/
theorem coalescedProjectedMass_tendsto (m : ℕ) (i j : Fin 2) :
    Tendsto (fun r : ℝ => coalescedProjectedMass m r i j) atTop
      (𝓝 (coalescedTwoModeBlock (coalescedV m) i j)) := by
  fin_cases i <;> fin_cases j
  · simpa [coalescedProjectedMass, coalescedTwoModeBlock] using
      coalescedFullMass_occupied_sum_tendsto m
  · simpa [coalescedProjectedMass, coalescedTwoModeBlock] using
      coalescedFullMass_cross_sum_tendsto m
  · simpa [coalescedProjectedMass, coalescedTwoModeBlock] using
      coalescedFullMass_reverse_cross_sum_tendsto m
  · simpa [coalescedProjectedMass, coalescedTwoModeBlock] using
      coalescedFullMass_final_entry_tendsto m

end
end PhosphorylationStableCapacity
