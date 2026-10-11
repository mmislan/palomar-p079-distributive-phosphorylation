module
public import proofs.PhosphorylationStableCapacity.RateCancellationPositiveDomain

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- The raw selected `a,c,alpha` coordinates used by the cancellation
graph stay inside positive literal rates near the zero parameter. -/
theorem selectedRates_positive_neighborhood {n : ℕ}
    (k : Rates n) (hk : k.Positive) :
    ∃ U : Set (CoordinateSpace n),
      IsOpen U ∧ (0 : CoordinateSpace n) ∈ U ∧
      ∀ v ∈ U, (ratesAdd k (selectedRates v)).Positive := by
  let U : Set (CoordinateSpace n) :=
    {v | ∀ i : Fin n,
      0 < k.a i + v.1 i ∧
      0 < k.c i + v.2.1 i ∧
      0 < k.alpha i + v.2.2 i}
  refine ⟨U, ?_, ?_, ?_⟩
  · have hU : U = ⋂ i : Fin n,
        {v : CoordinateSpace n |
          0 < k.a i + v.1 i ∧
          0 < k.c i + v.2.1 i ∧
          0 < k.alpha i + v.2.2 i} := by
      ext v
      simp [U]
    rw [hU]
    apply isOpen_iInter_of_finite
    intro i
    have ha : Continuous (fun v : CoordinateSpace n => k.a i + v.1 i) := by
      fun_prop
    have hc : Continuous (fun v : CoordinateSpace n => k.c i + v.2.1 i) := by
      fun_prop
    have halpha : Continuous
        (fun v : CoordinateSpace n => k.alpha i + v.2.2 i) := by
      fun_prop
    exact (isOpen_lt continuous_const ha).inter
      ((isOpen_lt continuous_const hc).inter
        (isOpen_lt continuous_const halpha))
  · simpa [U] using (show ∀ i : Fin n,
        0 < k.a i ∧ 0 < k.c i ∧ 0 < k.alpha i from by
          intro i
          exact ⟨(hk i).1, (hk i).2.2.1, (hk i).2.2.2.1⟩)
  · intro v hv i
    have hi := hv i
    change 0 < k.a i + v.1 i ∧ 0 < k.b i + 0 ∧
      0 < k.c i + v.2.1 i ∧ 0 < k.alpha i + v.2.2 i ∧
      0 < k.beta i + 0 ∧ 0 < k.gamma i + 0
    exact ⟨hi.1, by simpa using (hk i).2.1,
      hi.2.1, hi.2.2, by simpa using (hk i).2.2.2.2.1,
      by simpa using (hk i).2.2.2.2.2⟩

end
end PhosphorylationStableCapacity
