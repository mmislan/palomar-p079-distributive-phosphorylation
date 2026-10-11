module
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open NNReal

theorem unique_fixedPoint_in_closedBall_of_contraction
    {E : Type*} [MetricSpace E] [CompleteSpace E]
    (F : E → E) (x₀ : E) (ρ : ℝ) (hρ : 0 < ρ)
    (C : ℝ≥0) (hC : C < 1)
    (hF : LipschitzOnWith C F (Metric.closedBall x₀ ρ))
    (hshift : dist (F x₀) x₀ ≤ (1-(C : ℝ))*ρ/4) :
    ∃ x, x ∈ Metric.closedBall x₀ ρ ∧ F x = x ∧
      dist x x₀ ≤ ρ/4 ∧
      ∀ y ∈ Metric.closedBall x₀ ρ, F y = y → y = x := by
  have hCr : (C : ℝ) < 1 := hC
  have hx₀ : x₀ ∈ Metric.closedBall x₀ ρ := by simp [hρ.le]
  have hmaps : Set.MapsTo F (Metric.closedBall x₀ ρ) (Metric.closedBall x₀ ρ) := by
    intro x hx
    rw [Metric.mem_closedBall] at hx ⊢
    have hl := hF.dist_le_mul x (Metric.mem_closedBall.mpr hx) x₀ hx₀
    have ht := dist_triangle (F x) (F x₀) x₀
    have hb := mul_le_mul_of_nonneg_left hx C.coe_nonneg
    nlinarith
  let B := Metric.closedBall x₀ ρ
  let G : B → B := fun x => ⟨F x, hmaps x.property⟩
  let : CompleteSpace B := Metric.isClosed_closedBall.completeSpace_coe
  let : Nonempty B := ⟨⟨x₀, hx₀⟩⟩
  have hG : ContractingWith C G :=
    ⟨hC, LipschitzWith.of_dist_le_mul (fun x y => hF.dist_le_mul x x.property y y.property)⟩
  let x : B := hG.fixedPoint G
  have hfix : G x = x := hG.fixedPoint_isFixedPt
  have hfixval : F x.val = x.val := congrArg Subtype.val hfix
  have hdist : dist x.val x₀ ≤ ρ/4 := by
    have h := hG.dist_le_of_fixedPoint (⟨x₀, hx₀⟩ : B) hfix
    change dist x₀ x.val ≤ dist x₀ (F x₀) / (1-(C : ℝ)) at h
    rw [dist_comm x₀ (F x₀)] at h
    have hb : dist (F x₀) x₀ / (1-(C : ℝ)) ≤ ρ/4 := by
      apply (div_le_iff₀ (sub_pos.mpr hCr)).mpr
      nlinarith
    rw [dist_comm]
    exact h.trans hb
  refine ⟨x.val, x.property, hfixval, hdist, ?_⟩
  intro y hy hfy
  have hyfix : G (⟨y, hy⟩ : B) = ⟨y, hy⟩ := Subtype.ext hfy
  exact congrArg Subtype.val (hG.fixedPoint_unique' hyfix hfix)

/-- A uniform half-contraction with a centre displacement at most `ρ/8`
has exactly one fixed point in the closed box, within `ρ/4` of its centre.
Applied in the coordinate sup norm this is the quantitative persistence
step of the benchmark's independent-parameter certificate. -/
theorem unique_fixedPoint_in_closedBall_of_half_contraction
    {E : Type*} [MetricSpace E] [CompleteSpace E]
    (F : E → E) (x₀ : E) (ρ : ℝ) (hρ : 0 < ρ)
    (hF : LipschitzOnWith (1/2 : ℝ≥0) F (Metric.closedBall x₀ ρ))
    (hshift : dist (F x₀) x₀ ≤ ρ/8) :
    ∃ x, x ∈ Metric.closedBall x₀ ρ ∧ F x = x ∧
      dist x x₀ ≤ ρ/4 ∧
      ∀ y ∈ Metric.closedBall x₀ ρ, F y = y → y = x := by
  have hx₀ : x₀ ∈ Metric.closedBall x₀ ρ := by
    simp [hρ.le]
  have hmaps : Set.MapsTo F (Metric.closedBall x₀ ρ) (Metric.closedBall x₀ ρ) := by
    intro x hx
    rw [Metric.mem_closedBall] at hx ⊢
    have hl := hF.dist_le_mul x (Metric.mem_closedBall.mpr hx) x₀ hx₀
    have ht := dist_triangle (F x) (F x₀) x₀
    norm_num at hl
    linarith
  let C := Metric.closedBall x₀ ρ
  let G : C → C := fun x => ⟨F x, hmaps x.property⟩
  let : CompleteSpace C := Metric.isClosed_closedBall.completeSpace_coe
  let : Nonempty C := ⟨⟨x₀, hx₀⟩⟩
  have hG : ContractingWith (1/2 : ℝ≥0) G := by
    constructor
    · norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      exact hF.dist_le_mul x x.property y y.property
  let x : C := hG.fixedPoint G
  have hfix : G x = x := hG.fixedPoint_isFixedPt
  have hfixval : F x.val = x.val := congrArg Subtype.val hfix
  have hdist : dist x.val x₀ ≤ ρ/4 := by
    have h := hG.dist_le_of_fixedPoint (⟨x₀, hx₀⟩ : C) hfix
    change dist x₀ x.val ≤ dist x₀ (F x₀) / (1 - ((1/2 : ℝ≥0) : ℝ)) at h
    norm_num at h
    rw [dist_comm x₀ (F x₀)] at h
    rw [dist_comm]
    linarith
  refine ⟨x.val, x.property, hfixval, hdist, ?_⟩
  intro y hy hfy
  have hyfix : G (⟨y, hy⟩ : C) = ⟨y, hy⟩ := Subtype.ext hfy
  exact congrArg Subtype.val (hG.fixedPoint_unique' hyfix hfix)

end
end PhosphorylationStableCapacity
