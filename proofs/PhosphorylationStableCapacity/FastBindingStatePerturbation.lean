module
public import proofs.PhosphorylationStableCapacity.FastBindingLinearMap

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Insert a pure complex perturbation into loaded class coordinates. -/
def fastEmbed {n : ℕ} (v : FastSpace n) : CoordinateSpace n :=
  (0, v.1, v.2)

/-- Every complex is counted once in the total loaded substrate inventory. -/
theorem boundComplexAt_total {n : ℕ} (C D : Fin n → ℝ) :
    (∑ j : Fin (n + 1), boundComplexAt C D j) =
      (∑ i, C i) + (∑ i, D i) := by
  simpa only [mul_one] using
    boundComplexAt_pairing C D (fun _ : Fin (n + 1) => 1)

theorem boundComplexAt_succ_sum {n : ℕ} (C D : Fin n → ℝ) :
    (∑ i : Fin n, boundComplexAt C D i.succ) =
      (∑ i, C i) + (∑ i, D i) - boundComplexAt C D 0 := by
  have h := boundComplexAt_total C D
  rw [Fin.sum_univ_succ] at h
  linarith

theorem stateFromLoaded_fast_C {n : ℕ} (ET FT ST : ℝ)
    (u : CoordinateSpace n) (v : FastSpace n) (i : Fin n) :
    (stateFromLoaded ET FT ST (u + fastEmbed v)).C i =
      (stateFromLoaded ET FT ST u).C i + v.1 i := by
  rfl

theorem stateFromLoaded_fast_D {n : ℕ} (ET FT ST : ℝ)
    (u : CoordinateSpace n) (v : FastSpace n) (i : Fin n) :
    (stateFromLoaded ET FT ST (u + fastEmbed v)).D i =
      (stateFromLoaded ET FT ST u).D i + v.2 i := by
  rfl

theorem stateFromLoaded_fast_E {n : ℕ} (ET FT ST : ℝ)
    (u : CoordinateSpace n) (v : FastSpace n) :
    (stateFromLoaded ET FT ST (u + fastEmbed v)).E =
      (stateFromLoaded ET FT ST u).E + fastDeltaE v := by
  simp [stateFromLoaded, unChart, ofCoordinateSpace, fromLoadedCoord,
    fastEmbed, fastDeltaE, Finset.sum_add_distrib]
  ring

theorem stateFromLoaded_fast_F {n : ℕ} (ET FT ST : ℝ)
    (u : CoordinateSpace n) (v : FastSpace n) :
    (stateFromLoaded ET FT ST (u + fastEmbed v)).F =
      (stateFromLoaded ET FT ST u).F + fastDeltaF v := by
  simp [stateFromLoaded, unChart, ofCoordinateSpace, fromLoadedCoord,
    fastEmbed, fastDeltaF, Finset.sum_add_distrib]
  ring

theorem stateFromLoaded_fast_S_succ {n : ℕ} (ET FT ST : ℝ)
    (u : CoordinateSpace n) (v : FastSpace n) (i : Fin n) :
    (stateFromLoaded ET FT ST (u + fastEmbed v)).S i.succ =
      (stateFromLoaded ET FT ST u).S i.succ + fastDeltaS v i.succ := by
  simp [stateFromLoaded, unChart, ofCoordinateSpace, fromLoadedCoord,
    fastEmbed, fastDeltaS, boundComplexAt_add]
  ring

theorem stateFromLoaded_fast_S_zero {n : ℕ} (ET FT ST : ℝ)
    (u : CoordinateSpace n) (v : FastSpace n) :
    (stateFromLoaded ET FT ST (u + fastEmbed v)).S 0 =
      (stateFromLoaded ET FT ST u).S 0 + fastDeltaS v 0 := by
  simp [stateFromLoaded, unChart, ofCoordinateSpace, fromLoadedCoord,
    fastEmbed, fastDeltaS, boundComplexAt_add, Finset.sum_add_distrib]
  rw [boundComplexAt_succ_sum v.1 v.2]
  ring

theorem stateFromLoaded_fast_S {n : ℕ} (ET FT ST : ℝ)
    (u : CoordinateSpace n) (v : FastSpace n) (j : Fin (n + 1)) :
    (stateFromLoaded ET FT ST (u + fastEmbed v)).S j =
      (stateFromLoaded ET FT ST u).S j + fastDeltaS v j := by
  refine Fin.cases ?_ ?_ j
  · exact stateFromLoaded_fast_S_zero ET FT ST u v
  · intro i
    exact stateFromLoaded_fast_S_succ ET FT ST u v i

end
end PhosphorylationStableCapacity
