module
public import proofs.PhosphorylationStableCapacity.ClassForwardUniqueness
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Filter
open scoped Topology

noncomputable section

/-- A uniform exponential estimate on forward solutions supplies
Lyapunov stability and attraction in the exact nonlinear predicate.
This isolates the quantitative conclusion still needed from a
Hurwitz linearization theorem. -/
theorem locally_asymptotically_stable_of_exponential_bound {n : ℕ}
    (f : CoordinateSpace n → CoordinateSpace n)
    (x : CoordinateSpace n) (heq : f x = 0)
    (C α δ₀ : ℝ) (hC : 0 ≤ C) (hα : 0 < α) (hδ₀ : 0 < δ₀)
    (hdecay : ∀ y : CoordinateSpace n, dist y x < δ₀ →
      ∀ γ : ℝ → CoordinateSpace n, IsForwardClassCurve f y γ →
        ∀ t : ℝ, 0 ≤ t →
          dist (γ t) x ≤ C * Real.exp (-(α * t)) * dist y x)
    (hexist : ∀ y : CoordinateSpace n, dist y x < δ₀ →
      ∃ γ : ℝ → CoordinateSpace n, IsForwardClassCurve f y γ) :
    IsLocallyAsymptoticallyStableClassField f x := by
  refine ⟨heq, ?_, ?_, ?_⟩
  · intro ε hε
    let δ := min δ₀ (ε / (C + 1))
    have hC1 : 0 < C + 1 := by linarith
    have hδ : 0 < δ := lt_min hδ₀ (div_pos hε hC1)
    refine ⟨δ, hδ, ?_⟩
    intro y hy γ hγ t ht
    have hy₀ : dist y x < δ₀ := lt_of_lt_of_le hy (min_le_left _ _)
    have hyε : dist y x < ε / (C + 1) :=
      lt_of_lt_of_le hy (min_le_right _ _)
    have hExp : Real.exp (-(α * t)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hbound := hdecay y hy₀ γ hγ t ht
    have hmiddle : C * Real.exp (-(α * t)) * dist y x ≤
        C * dist y x := by
      exact mul_le_mul_of_nonneg_right
        (by simpa using mul_le_mul_of_nonneg_left hExp hC)
        (dist_nonneg)
    have hsmall : (C + 1) * dist y x < ε :=
      by simpa [mul_comm] using (lt_div_iff₀ hC1).mp hyε
    nlinarith [dist_nonneg (x := y) (y := x)]
  · refine ⟨δ₀, hδ₀, ?_⟩
    intro y hy γ hγ
    have hExp : Tendsto (fun t : ℝ => Real.exp (-(α * t)))
        atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hα)
    apply tendsto_iff_dist_tendsto_zero.mpr
    refine squeeze_zero'
      (Eventually.of_forall (fun _ => dist_nonneg)) ?_
      (by simpa using (hExp.const_mul (C * dist y x)))
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      hdecay y hy γ hγ t ht
  · exact ⟨δ₀, hδ₀, hexist⟩

/-- For the literal fixed-class field, it suffices to establish an
exponential estimate for one forward curve from each nearby state.
Strict uniqueness then transfers that estimate to every curve in
the nonlinear stability predicate. -/
theorem class_las_of_exponential_witness {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n)
    (x : CoordinateSpace n)
    (heq : restrictedFieldEuclid ET FT ST k x = 0)
    (C α δ₀ : ℝ) (hC : 0 ≤ C) (hα : 0 < α) (hδ₀ : 0 < δ₀)
    (hestimate : ∀ y : CoordinateSpace n, dist y x < δ₀ →
      ∃ γ : ℝ → CoordinateSpace n,
        IsForwardClassCurve (restrictedFieldEuclid ET FT ST k) y γ ∧
          ∀ t : ℝ, 0 ≤ t →
            dist (γ t) x ≤ C * Real.exp (-(α * t)) * dist y x) :
    IsLocallyAsymptoticallyStableClass ET FT ST k x := by
  apply locally_asymptotically_stable_of_exponential_bound
    (restrictedFieldEuclid ET FT ST k) x heq
    C α δ₀ hC hα hδ₀
  · intro y hy η hη t ht
    obtain ⟨γ, hγ, hbound⟩ := hestimate y hy
    rw [forward_class_curves_unique ET FT ST k y η γ hη hγ t ht]
    exact hbound t ht
  · intro y hy
    obtain ⟨γ, hγ, _⟩ := hestimate y hy
    exact ⟨γ, hγ⟩

end
end PhosphorylationStableCapacity
