module
public import proofs.PhosphorylationStableCapacity.FastBindingMatrixFactorization

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Cross-pairing formula for the affinity map. Each term is symmetric in
the two fast complex perturbations. -/
theorem fastAffinity_cross_formula {n : ℕ} (x : State n)
    (v w : FastSpace n) :
    (∑ i, v.1 i * fastAffinityC x w i) +
      (∑ i, v.2 i * fastAffinityD x w i) =
      (∑ i, v.1 i * w.1 i / x.C i) +
      (∑ i, v.2 i * w.2 i / x.D i) +
      (∑ j, boundComplexAt v.1 v.2 j *
        boundComplexAt w.1 w.2 j / x.S j) +
      (∑ i, v.1 i) * (∑ i, w.1 i) / x.E +
      (∑ i, v.2 i) * (∑ i, w.2 i) / x.F := by
  classical
  have hS :
      (∑ i, v.1 i *
        (boundComplexAt w.1 w.2 i.castSucc / x.S i.castSucc)) +
      (∑ i, v.2 i *
        (boundComplexAt w.1 w.2 i.succ / x.S i.succ)) =
      ∑ j, boundComplexAt v.1 v.2 j *
        boundComplexAt w.1 w.2 j / x.S j := by
    rw [← boundComplexAt_pairing v.1 v.2
      (fun j => boundComplexAt w.1 w.2 j / x.S j)]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hC :
      (∑ i, v.1 i * (w.1 i / x.C i)) =
        ∑ i, v.1 i * w.1 i / x.C i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hD :
      (∑ i, v.2 i * (w.2 i / x.D i)) =
        ∑ i, v.2 i * w.2 i / x.D i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hE :
      (∑ i, v.1 i * ((∑ j, w.1 j) / x.E)) =
        (∑ i, v.1 i) * (∑ j, w.1 j) / x.E := by
    rw [← Finset.sum_mul]
    ring
  have hF :
      (∑ i, v.2 i * ((∑ j, w.2 j) / x.F)) =
        (∑ i, v.2 i) * (∑ j, w.2 j) / x.F := by
    rw [← Finset.sum_mul]
    ring
  simp only [fastAffinityC, fastAffinityD, mul_add,
    Finset.sum_add_distrib]
  rw [hC, hD, hE, hF]
  rw [← hS]
  ring

end
end PhosphorylationStableCapacity
