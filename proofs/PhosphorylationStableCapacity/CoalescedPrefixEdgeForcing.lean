module
public import proofs.PhosphorylationStableCapacity.CoalescedNormalizedEdgeActionLimit

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- A first-prefix edge column of the path incidence transpose, extended
by zero at the final substrate level. -/
def coalescedPrefixEdgeForcing (m : ℕ)
    (j : Fin (m + 1)) : Fin (m + 3) → ℝ :=
  fun k => (if k = j.succ.castSucc then 1 else 0) -
    (if k = j.castSucc.castSucc then 1 else 0)

theorem coalescedPrefixEdgeForcing_sum (m : ℕ)
    (j : Fin (m + 1)) :
    (∑ k : Fin (m + 3), coalescedPrefixEdgeForcing m j k) = 0 := by
  unfold coalescedPrefixEdgeForcing
  rw [Finset.sum_sub_distrib]
  simp only [Fintype.sum_ite_eq']
  ring

theorem coalescedPrefixEdgeForcing_last (m : ℕ)
    (j : Fin (m + 1)) :
    coalescedPrefixEdgeForcing m j (Fin.last (m + 2)) = 0 := by
  have hnext : Fin.last (m + 2) ≠ j.castSucc.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  have hprev : Fin.last (m + 2) ≠ j.castSucc.castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  simp [coalescedPrefixEdgeForcing, hnext, hprev]

theorem coalescedPrefixEdgeForcing_occupied (m : ℕ)
    (j : Fin (m + 1)) (k : Fin (m + 2)) :
    coalescedPrefixEdgeForcing m j k.castSucc =
      (if k = j.succ then 1 else 0) -
        (if k = j.castSucc then 1 else 0) := by
  have hidx : (j.castSucc.succ : Fin (m + 3)) = j.succ.castSucc := by
    ext
    rfl
  have hfirst : (k.castSucc = j.castSucc.succ) ↔ k = j.succ := by
    constructor
    · intro h
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa only [Fin.val_castSucc, Fin.val_succ] using hv
    · intro h
      subst k
      exact hidx.symm
  change (if k.castSucc = j.castSucc.succ then (1 : ℝ) else 0) -
      (if k.castSucc = j.castSucc.castSucc then 1 else 0) = _
  simp only [hfirst, Fin.castSucc_inj]

/-- A weighted edge column takes the difference of its two endpoint
weights. -/
theorem coalescedPrefixEdgeForcing_weighted_sum (m : ℕ)
    (j : Fin (m + 1)) (f : Fin (m + 2) → ℝ) :
    (∑ k : Fin (m + 2),
      f k * coalescedPrefixEdgeForcing m j k.castSucc) =
      f j.succ - f j.castSucc := by
  simp_rw [coalescedPrefixEdgeForcing_occupied, mul_sub]
  rw [Finset.sum_sub_distrib]
  simp

end
end PhosphorylationStableCapacity
