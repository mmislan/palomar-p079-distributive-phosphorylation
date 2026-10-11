module
public import proofs.PhosphorylationStableCapacity.LoadedFieldCurrent

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The loaded inventories partition the literal total substrate count. -/
theorem sum_loadedLevel_eq_totalS {n : ℕ} (x : State n) :
    (∑ j : Fin (n + 1), loadedLevel x j) = totalS x := by
  have hC :
      (∑ j : Fin (n + 1),
        ∑ i : Fin n, if i.castSucc = j then x.C i else 0) =
          ∑ i : Fin n, x.C i := by
    rw [Finset.sum_comm]
    simp
  have hD :
      (∑ j : Fin (n + 1),
        ∑ i : Fin n, if i.succ = j then x.D i else 0) =
          ∑ i : Fin n, x.D i := by
    rw [Finset.sum_comm]
    simp
  simp only [loadedLevel, totalS, Finset.sum_add_distrib]
  rw [hC, hD]

end
end PhosphorylationStableCapacity
