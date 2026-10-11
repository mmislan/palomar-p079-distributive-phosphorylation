module
public import proofs.PhosphorylationStableCapacity.FastBindingBilinear

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The affinity map is symmetric in the standard complex-coordinate pairing. -/
theorem fastAffinity_pairing_symmetric {n : ℕ} (x : State n)
    (v w : FastSpace n) :
    (∑ i, v.1 i * fastAffinityC x w i) +
      (∑ i, v.2 i * fastAffinityD x w i) =
    (∑ i, w.1 i * fastAffinityC x v i) +
      (∑ i, w.2 i * fastAffinityD x v i) := by
  have hC :
      (∑ i, v.1 i * w.1 i / x.C i) =
        ∑ i, w.1 i * v.1 i / x.C i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hD :
      (∑ i, v.2 i * w.2 i / x.D i) =
        ∑ i, w.2 i * v.2 i / x.D i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hS :
      (∑ j, boundComplexAt v.1 v.2 j *
        boundComplexAt w.1 w.2 j / x.S j) =
      ∑ j, boundComplexAt w.1 w.2 j *
        boundComplexAt v.1 v.2 j / x.S j := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [fastAffinity_cross_formula x v w,
    fastAffinity_cross_formula x w v]
  rw [hC, hD, hS]
  ring

end
end PhosphorylationStableCapacity
