module
public import proofs.PhosphorylationStableCapacity.ClassFlowSmallTimeError
public import Mathlib.Order.Filter.AtTopBot.Field

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Filter
open scoped Topology

noncomputable section

/-- A forward class trajectory that converges to an equilibrium
cannot return to its initial point at positive time unless it started
at the equilibrium. The proof uses the literal class-flow uniqueness. -/
theorem attracting_forward_curve_no_positive_return {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n)
    (x y : CoordinateSpace n) (γ : ℝ → CoordinateSpace n)
    (hγ : IsForwardClassCurve
      (restrictedFieldEuclid ET FT ST k) y γ)
    (hattract : Tendsto γ atTop (𝓝 x))
    (T : ℝ) (hT : 0 < T) (hreturn : γ T = y) :
    y = x := by
  have hshift : IsForwardClassCurve
      (restrictedFieldEuclid ET FT ST k) y
      (fun t => γ (t + T)) := by
    simpa [hreturn] using forward_class_curve_shift hγ T hT.le
  have hperiod : ∀ t : ℝ, 0 ≤ t → γ (t + T) = γ t :=
    forward_class_curves_unique ET FT ST k y
      (fun t => γ (t + T)) γ hshift hγ
  have hrepeat : ∀ m : ℕ, γ ((m : ℝ) * T) = y := by
    intro m
    induction m with
    | zero => simpa using hγ.1
    | succ m ih =>
        have hm : 0 ≤ (m : ℝ) * T :=
          mul_nonneg (Nat.cast_nonneg _) hT.le
        calc
          γ (((m + 1 : ℕ) : ℝ) * T) = γ ((m : ℝ) * T + T) := by
            congr 1
            push_cast
            ring
          _ = γ ((m : ℝ) * T) := hperiod _ hm
          _ = y := ih
  have hseq : Tendsto (fun m : ℕ => (m : ℝ) * T) atTop atTop :=
    (tendsto_mul_const_atTop_of_pos hT).mpr tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun m : ℕ => γ ((m : ℝ) * T))
      atTop (𝓝 x) := hattract.comp hseq
  have hconst : (fun m : ℕ => γ ((m : ℝ) * T)) = fun _ => y :=
    funext hrepeat
  rw [hconst] at hlim
  exact tendsto_const_nhds_iff.mp hlim

/-- Every point in a local attractor's basin except its center is
free of positive-time fixed points of the physical flow. -/
theorem local_attractor_no_positive_time_return {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n)
    (hx : IsLocallyAsymptoticallyStableClass ET FT ST k x) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (z : classPolytope n ET FT ST),
        dist z.1 x < δ →
        ∀ T : ℝ, 0 < T →
          physicalForwardCurve ET FT ST hET k hk z T = z.1 →
          z.1 = x := by
  obtain ⟨δ, hδ, hattract⟩ := hx.2.2.1
  refine ⟨δ, hδ, ?_⟩
  intro z hz T hT hreturn
  exact attracting_forward_curve_no_positive_return ET FT ST k x z.1
    (physicalForwardCurve ET FT ST hET k hk z)
    (physicalForwardCurve_spec ET FT ST hET k hk z).1
    (hattract z.1 hz _ (physicalForwardCurve_spec ET FT ST hET k hk z).1)
    T hT hreturn

end
end PhosphorylationStableCapacity
