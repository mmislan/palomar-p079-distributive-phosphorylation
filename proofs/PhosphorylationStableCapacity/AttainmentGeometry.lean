module
public import proofs.PhosphorylationStableCapacity.Jacobian
public import proofs.PhosphorylationSharpness.Resolution

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Positive equilibria counted in one actual fixed-class coordinate chart. -/
def ClassAttains (n count : ℕ) : Prop :=
  ∃ (k : Rates n) (ET FT ST : ℝ) (u : Fin count → CoordinateSpace n),
    k.Positive ∧ 0 < ET ∧ 0 < FT ∧ 0 < ST ∧ Function.Injective u ∧
      ∀ j, (unChart ET FT ST (ofCoordinateSpace (u j))).Positive ∧
        restrictedFieldEuclid ET FT ST k (u j) = 0

/-- The actual Hurwitz attainment target: the same rates and totals at every sink. -/
def LinearlyStableClassAttains (n count : ℕ) : Prop :=
  ∃ (k : Rates n) (ET FT ST : ℝ) (u : Fin count → CoordinateSpace n),
    k.Positive ∧ 0 < ET ∧ 0 < FT ∧ 0 < ST ∧ Function.Injective u ∧
      ∀ j, (unChart ET FT ST (ofCoordinateSpace (u j))).Positive ∧
        restrictedFieldEuclid ET FT ST k (u j) = 0 ∧
          IsLinearlyStable ET FT ST k (u j)

theorem classAttains_of_linearlyStable {n count : ℕ}
    (h : LinearlyStableClassAttains n count) : ClassAttains n count := by
  rcases h with ⟨k, ET, FT, ST, u, hk, hET, hFT, hST, hu, hstates⟩
  exact ⟨k, ET, FT, ST, u, hk, hET, hFT, hST, hu,
    fun j => ⟨(hstates j).1, (hstates j).2.1⟩⟩

/-- The source's common-class equilibrium construction survives the class chart. -/
theorem classAttains_of_attains {n count : ℕ} (h : Attains n count) :
    ClassAttains n count := by
  rcases h with ⟨k, ET, FT, ST, z, hk, hET, hFT, hST, hz, hstates⟩
  let u : Fin count → CoordinateSpace n :=
    fun j => toCoordinateSpace (chart (z j))
  have hback (j : Fin count) :
      unChart ET FT ST (ofCoordinateSpace (u j)) = z j := by
    rw [show ofCoordinateSpace (u j) = chart (z j) by
      simp only [u, of_toCoordinateSpace]]
    exact unChart_chart_of_inClass ET FT ST (z j)
      ⟨(hstates j).2.2.1, (hstates j).2.2.2.1,
        (hstates j).2.2.2.2⟩
  refine ⟨k, ET, FT, ST, u, hk, hET, hFT, hST, ?_, ?_⟩
  · intro a b hab
    apply hz
    rw [← hback a, ← hback b, hab]
  · intro j
    constructor
    · rw [hback]
      exact (hstates j).1
    · apply (restrictedFieldEuclid_eq_zero_iff ET FT ST k (u j)).2
      rw [hback]
      exact (hstates j).2.1

/-- The verified `2n-1` equilibrium count is a restricted-field count, not a sink count. -/
theorem sharp_class_equilibrium_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    ClassAttains n (2*n-1) :=
  classAttains_of_attains (sharp_lower_bound n hn)

end
end PhosphorylationStableCapacity
