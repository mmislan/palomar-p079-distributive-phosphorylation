module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitPair
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Order.Filter.AtTopBot.Field
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter Finset
open scoped Topology BigOperators

/-- The phase of the odd prescribed-root product on the positive imaginary axis.
Repeated prescribed roots are retained as separate summands. -/
def arbitrarySplitPhase (m : ℕ) (ξ : ℕ → ℝ) (δ y : ℝ) : ℝ :=
  ∑ j ∈ range (2*m+1), Real.arctan (y / offsetSplitRoot ξ δ j)

theorem arbitrarySplitPhase_continuous (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ) :
    Continuous (arbitrarySplitPhase m ξ δ) := by
  unfold arbitrarySplitPhase
  fun_prop

theorem arbitrarySplitPhase_zero (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ) :
    arbitrarySplitPhase m ξ δ 0 = 0 := by
  simp [arbitrarySplitPhase]

theorem arbitrarySplitPhase_strictMono (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 0 < offsetSplitRoot ξ δ j) :
    StrictMono (arbitrarySplitPhase m ξ δ) := by
  intro a b hab
  apply Finset.sum_lt_sum_of_nonempty
  · exact ⟨0, by simp⟩
  · intro j hj
    exact Real.arctan_strictMono
      ((div_lt_div_iff_of_pos_right (hroot j (by
        have := Finset.mem_range.mp hj
        omega))).2 hab)

theorem arbitrarySplitPhase_tendsto_atTop
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 0 < offsetSplitRoot ξ δ j) :
    Tendsto (arbitrarySplitPhase m ξ δ) atTop
      (𝓝 (((2*m+1 : ℕ) : ℝ) * (Real.pi/2))) := by
  have hterm (j : ℕ) (hj : j ∈ range (2*m+1)) :
      Tendsto (fun y : ℝ => Real.arctan (y / offsetSplitRoot ξ δ j))
        atTop (𝓝 (Real.pi/2)) := by
    have hx := hroot j (by have := Finset.mem_range.mp hj; omega)
    exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      ((tendsto_div_const_atTop_of_pos hx).2 tendsto_id)
  change Tendsto (fun y : ℝ =>
    ∑ j ∈ range (2*m+1), Real.arctan (y / offsetSplitRoot ξ δ j)) atTop
      (𝓝 (((2*m+1 : ℕ) : ℝ) * (Real.pi/2)))
  simpa [nsmul_eq_mul] using
    tendsto_finsetSum (range (2*m+1)) hterm

/-- Every interior phase level has exactly one positive preimage. The endpoint
is an actual finite sum of arctangents, without distinctness of the data. -/
theorem arbitrarySplitPhase_existsUnique_positive_level
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 0 < offsetSplitRoot ξ δ j)
    (v : ℝ) (hv : 0 < v)
    (hvend : v < ((2*m+1 : ℕ) : ℝ) * (Real.pi/2)) :
    ∃! y : ℝ, 0 < y ∧ arbitrarySplitPhase m ξ δ y = v := by
  have hlim := arbitrarySplitPhase_tendsto_atTop m ξ δ hroot
  have hevent := (tendsto_order.mp hlim).1 v hvend
  obtain ⟨b, hb, hbpos⟩ := (hevent.and (eventually_gt_atTop (0 : ℝ))).exists
  have hc := arbitrarySplitPhase_continuous m ξ δ
  obtain ⟨y, hy, hyv⟩ :=
    (intermediate_value_Ioo hbpos.le hc.continuousOn)
      (show v ∈ Set.Ioo (arbitrarySplitPhase m ξ δ 0)
          (arbitrarySplitPhase m ξ δ b) by
        rw [arbitrarySplitPhase_zero]; exact ⟨hv, hb⟩)
  refine ⟨y, ⟨hy.1, hyv⟩, ?_⟩
  intro z hz
  exact (arbitrarySplitPhase_strictMono m ξ δ hroot).injective
    (hz.2.trans hyv.symm)

theorem arbitrarySplitPhase_existsUnique_nat_pi
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 0 < offsetSplitRoot ξ δ j)
    (j : Fin m) :
    ∃! y : ℝ, 0 < y ∧
      arbitrarySplitPhase m ξ δ y = ((j.val+1 : ℕ) : ℝ) * Real.pi := by
  apply arbitrarySplitPhase_existsUnique_positive_level m ξ δ hroot
  · positivity
  · have hj : (j.val+1 : ℝ) ≤ m := by exact_mod_cast (show j.val+1 ≤ m by omega)
    have hpi := Real.pi_pos
    have hjpi := mul_le_mul_of_nonneg_right hj hpi.le
    push_cast
    nlinarith [hjpi]

/-- Positive imaginary-axis abscissa of the j-th numerator phase crossing. -/
def arbitrarySplitPhaseAbscissa
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 0 < offsetSplitRoot ξ δ j)
    (j : Fin m) : ℝ :=
  Classical.choose (arbitrarySplitPhase_existsUnique_nat_pi m ξ δ hroot j)

theorem arbitrarySplitPhaseAbscissa_spec
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 0 < offsetSplitRoot ξ δ j)
    (j : Fin m) :
    0 < arbitrarySplitPhaseAbscissa m ξ δ hroot j ∧
      arbitrarySplitPhase m ξ δ (arbitrarySplitPhaseAbscissa m ξ δ hroot j) =
        ((j.val+1 : ℕ) : ℝ) * Real.pi :=
  (Classical.choose_spec (arbitrarySplitPhase_existsUnique_nat_pi m ξ δ hroot j)).1

theorem arbitrarySplitPhaseAbscissa_strictMono
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 0 < offsetSplitRoot ξ δ j) :
    StrictMono (arbitrarySplitPhaseAbscissa m ξ δ hroot) := by
  intro j k hjk
  apply (arbitrarySplitPhase_strictMono m ξ δ hroot).lt_iff_lt.mp
  rw [(arbitrarySplitPhaseAbscissa_spec m ξ δ hroot j).2,
    (arbitrarySplitPhaseAbscissa_spec m ξ δ hroot k).2]
  have hcast : ((j.val+1 : ℕ) : ℝ) < ((k.val+1 : ℕ) : ℝ) := by
    exact_mod_cast (show j.val+1 < k.val+1 from Nat.add_lt_add_right hjk 1)
  exact mul_lt_mul_of_pos_right hcast Real.pi_pos

/-- Negative numerator root candidate, ordered from right to left. -/
def arbitrarySplitPhaseNRoot
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 0 < offsetSplitRoot ξ δ j)
    (j : Fin m) : ℝ :=
  -(1 + arbitrarySplitPhaseAbscissa m ξ δ hroot j ^ 2) / 8

theorem arbitrarySplitPhaseNRoot_lt_neg_one_eighth
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 0 < offsetSplitRoot ξ δ j)
    (j : Fin m) :
    arbitrarySplitPhaseNRoot m ξ δ hroot j < -(1 : ℝ)/8 := by
  have hy := (arbitrarySplitPhaseAbscissa_spec m ξ δ hroot j).1
  unfold arbitrarySplitPhaseNRoot
  nlinarith [sq_pos_of_pos hy]

theorem arbitrarySplitPhaseNRoot_strictAnti
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 0 < offsetSplitRoot ξ δ j) :
    StrictAnti (arbitrarySplitPhaseNRoot m ξ δ hroot) := by
  intro j k hjk
  have hj := (arbitrarySplitPhaseAbscissa_spec m ξ δ hroot j).1
  have hk := (arbitrarySplitPhaseAbscissa_spec m ξ δ hroot k).1
  have hlt := arbitrarySplitPhaseAbscissa_strictMono m ξ δ hroot hjk
  have hsquare := (sq_lt_sq₀ hj.le hk.le).2 hlt
  unfold arbitrarySplitPhaseNRoot
  linarith [hsquare]

end
end PhosphorylationStableCapacity
