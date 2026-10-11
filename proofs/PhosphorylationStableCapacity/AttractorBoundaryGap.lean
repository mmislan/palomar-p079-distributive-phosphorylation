module
public import proofs.PhosphorylationStableCapacity.LocalAsymptoticStability
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- An isolated zero of a continuous field in a proper metric space
has a positive uniform field norm on a sufficiently small sphere. -/
theorem isolated_zero_exists_sphere_gap
    {E F : Type*} [MetricSpace E] [ProperSpace E]
    [NormedAddCommGroup F]
    (f : E → F) (hf : Continuous f) (x : E)
    (δ : ℝ) (hδ : 0 < δ)
    (hiso : ∀ y : E, dist y x < δ → f y = 0 → y = x) :
    ∃ r ε : ℝ, 0 < r ∧ r < δ ∧ 0 < ε ∧
      ∀ y : E, dist y x = r → ε ≤ ‖f y‖ := by
  let r : ℝ := δ / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hrδ : r < δ := by dsimp [r]; linarith
  have hfield (y : E) (hy : y ∈ Metric.sphere x r) : f y ≠ 0 := by
    intro hzero
    have hdist : dist y x = r := Metric.mem_sphere.mp hy
    have hyx := hiso y (by linarith) hzero
    subst y
    simp only [dist_self] at hdist
    linarith
  by_cases hnon : (Metric.sphere x r).Nonempty
  · obtain ⟨y, hy, hmin⟩ :=
      (isCompact_sphere x r).exists_isMinOn hnon hf.norm.continuousOn
    refine ⟨r, ‖f y‖, hr, hrδ, norm_pos_iff.mpr (hfield y hy), ?_⟩
    intro z hz
    exact hmin (Metric.mem_sphere.mpr hz)
  · refine ⟨r, 1, hr, hrδ, by norm_num, ?_⟩
    intro y hy
    exact (hnon ⟨y, Metric.mem_sphere.mpr hy⟩).elim

/-- A possibly nonhyperbolic local attractor of the literal class
field has a compact enclosing sphere with a positive field margin. -/
theorem local_attractor_exists_boundary_gap {n : ℕ}
    (ET FT ST : ℝ) (k : PhosphorylationSharpness.Rates n)
    (x : CoordinateSpace n)
    (hx : IsLocallyAsymptoticallyStableClass ET FT ST k x) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧
      ∀ y : CoordinateSpace n, dist y x = r →
        ε ≤ ‖restrictedFieldEuclid ET FT ST k y‖ := by
  obtain ⟨δ, hδ, hiso⟩ :=
    locally_asymptotically_stable_class_isolated ET FT ST k x hx
  obtain ⟨r, ε, hr, _, hε, hgap⟩ :=
    isolated_zero_exists_sphere_gap
      (restrictedFieldEuclid ET FT ST k)
      (differentiable_restrictedFieldEuclid ET FT ST k).continuous
      x δ hδ hiso
  exact ⟨r, ε, hr, hε, hgap⟩

end
end PhosphorylationStableCapacity
