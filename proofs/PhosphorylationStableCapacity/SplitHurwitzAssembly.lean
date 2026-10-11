module
public import proofs.PhosphorylationStableCapacity.SplitSlowComplexIsolation
public import proofs.PhosphorylationStableCapacity.AttainmentGeometry

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness

/-- Select the even-indexed roots from the full `2m+3` split family. -/
def splitEvenIndex (m : ℕ) (i : Fin (m+2)) : Fin (2*(m+1)+1) :=
  ⟨2*i.val, by omega⟩

theorem splitEvenIndex_injective (m : ℕ) :
    Function.Injective (splitEvenIndex m) := by
  intro i j hij
  apply Fin.ext
  have h : 2*i.val = 2*j.val := congrArg Fin.val hij
  omega

/-- Once the even-indexed split states are proved Hurwitz, the existing
common-rate family supplies the exact all-size linear attainment target. -/
theorem split_even_hurwitz_attains (m : ℕ) (r τ δ ε : ℝ)
    (hr : 0 < r)
    (hadm : SplitRetunedFamilyAdmissible m r τ δ ε)
    (hstable : ∀ i : Fin (m+2),
      IsLinearlyStable (2*r) 2 (2*(r+1))
        (splitRetunedRates m r τ δ ε)
        (toCoordinateSpace (chart
          (splitFiniteState (m+1) r δ (splitEvenIndex m i))))) :
    LinearlyStableClassAttains (m+2) (m+2) := by
  let k := splitRetunedRates m r τ δ ε
  let z : Fin (m+2) → State (m+2) := fun i =>
    splitFiniteState (m+1) r δ (splitEvenIndex m i)
  let u : Fin (m+2) → CoordinateSpace (m+2) := fun i =>
    toCoordinateSpace (chart (z i))
  have hfamily := hadm.2.2
  have hback (i : Fin (m+2)) :
      unChart (2*r) 2 (2*(r+1))
        (ofCoordinateSpace (u i)) = z i := by
    rw [show ofCoordinateSpace (u i) = chart (z i) by
      simp only [u, of_toCoordinateSpace]]
    exact unChart_chart_of_inClass (2*r) 2 (2*(r+1)) (z i)
      ⟨(hfamily (splitEvenIndex m i)).2.2.1,
       (hfamily (splitEvenIndex m i)).2.2.2.1,
       (hfamily (splitEvenIndex m i)).2.2.2.2⟩
  refine ⟨k, 2*r, 2, 2*(r+1), u, hadm.1,
    by positivity, by norm_num, by positivity, ?_, ?_⟩
  · intro i j hij
    have hz : z i = z j := by
      rw [← hback i, ← hback j, hij]
    exact splitEvenIndex_injective m
      (hadm.2.1 hz)
  · intro i
    constructor
    · rw [hback]
      exact (hfamily (splitEvenIndex m i)).1
    constructor
    · apply (restrictedFieldEuclid_eq_zero_iff (2*r) 2 (2*(r+1)) k (u i)).2
      rw [hback]
      exact (hfamily (splitEvenIndex m i)).2.1
    · exact hstable i

end
end PhosphorylationStableCapacity
