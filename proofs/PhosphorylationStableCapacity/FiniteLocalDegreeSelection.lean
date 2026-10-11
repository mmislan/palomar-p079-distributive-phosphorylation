module
public import proofs.PhosphorylationStableCapacity.RegularDegreeCountContradiction

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Once degree theory supplies local signed sum `+1` on each of
`n+1` disjoint regions and total signed sum `+1`, the regular
`≤ 2n` equilibrium budget is impossible. This theorem performs the
exact finite selection from local sums needed for P079's ceiling. -/
theorem no_n_succ_disjoint_local_degree_one_regions
    {α : Type*} [DecidableEq α]
    (all : Finset α) (index : α → ℤ) (n : ℕ)
    (B : Fin (n + 1) → Set α)
    [∀ i, DecidablePred (B i)]
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hreg : ∀ z ∈ all, index z = 1 ∨ index z = -1)
    (htotal : (∑ z ∈ all, index z) = 1)
    (hbudget : all.card ≤ 2 * n)
    (hlocal : ∀ i, (∑ z ∈ all.filter (B i), index z) = 1) :
    False := by
  classical
  have hpositive : ∀ i : Fin (n + 1),
      ∃ z, z ∈ all.filter (B i) ∧ index z = 1 := by
    intro i
    by_contra hnone
    push Not at hnone
    have hneg : ∀ z ∈ all.filter (B i), index z = -1 := by
      intro z hz
      rcases hreg z (Finset.mem_filter.mp hz).1 with hpos | hminus
      · exact (hnone z hz hpos).elim
      · exact hminus
    have hsum : (∑ z ∈ all.filter (B i), index z) =
        -((all.filter (B i)).card : ℤ) := by
      calc
        (∑ z ∈ all.filter (B i), index z) =
            ∑ _z ∈ all.filter (B i), (-1 : ℤ) := by
          apply Finset.sum_congr rfl
          intro z hz
          exact hneg z hz
        _ = -((all.filter (B i)).card : ℤ) := by simp
    have hcard : 0 ≤ ((all.filter (B i)).card : ℤ) := by
      exact_mod_cast Nat.zero_le _
    have hloc := hlocal i
    rw [hsum] at hloc
    omega
  choose points hpoints using hpositive
  have hinj : Function.Injective points := by
    intro i j hij
    by_contra hne
    have hi : points i ∈ B i := (Finset.mem_filter.mp (hpoints i).1).2
    have hj : points i ∈ B j := by
      rw [hij]
      exact (Finset.mem_filter.mp (hpoints j).1).2
    exact (Set.disjoint_left.mp (hdisj i j hne) hi hj).elim
  apply no_n_succ_distinct_positive_index_points
    all index n
    (by
      intro z hz
      rcases hreg z hz with hpos | hminus <;> omega)
    htotal hbudget points hinj
  intro i
  exact ⟨(Finset.mem_filter.mp (hpoints i).1).1, (hpoints i).2⟩

end
end PhosphorylationStableCapacity
