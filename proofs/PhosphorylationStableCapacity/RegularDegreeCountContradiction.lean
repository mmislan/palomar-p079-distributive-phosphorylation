module
public import proofs.PhosphorylationStableCapacity.StableIndexCeilingCombinatorics

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The exact finite contradiction needed after degree theory has
provided `+1` local indices in `n+1` disjoint balls. Every remaining
regular equilibrium contributes at least `-1`, the total signed count
is `+1`, and there are at most `2n` equilibria. -/
theorem no_n_succ_distinct_positive_index_points
    {α : Type*} [DecidableEq α]
    (all : Finset α) (index : α → ℤ) (n : ℕ)
    (hlower : ∀ z ∈ all, -1 ≤ index z)
    (htotal : (∑ z ∈ all, index z) = 1)
    (hbudget : all.card ≤ 2 * n)
    (points : Fin (n + 1) → α)
    (hinj : Function.Injective points)
    (hpoints : ∀ i, points i ∈ all ∧ index (points i) = 1) :
    False := by
  let P := all.filter (fun z => index z = 1)
  let N := all.filter (fun z => index z ≠ 1)
  have hdegree : (∑ z ∈ P, index z) +
      (∑ z ∈ N, index z) = 1 := by
    change (∑ z ∈ all.filter (fun z => index z = 1), index z) +
      (∑ z ∈ all.filter (fun z => index z ≠ 1), index z) = 1
    rw [Finset.sum_filter_add_sum_filter_not]
    exact htotal
  have hcard : P.card + N.card ≤ 2 * n := by
    have hp := all.card_filter_add_card_filter_not
      (fun z => index z = 1)
    dsimp [P, N]
    omega
  have hPle : P.card ≤ n :=
    stable_index_count_le_of_regular_budget P N index n
      (by intro z hz; exact (Finset.mem_filter.mp hz).2)
      (by intro z hz; exact hlower z (Finset.mem_filter.mp hz).1)
      hdegree hcard
  have hge : n + 1 ≤ P.card := by
    have hle := Finset.card_le_card_of_injOn points
      (s := Finset.univ) (t := P)
      (by intro i _; exact Finset.mem_filter.mpr (hpoints i))
      (by intro i _ j _ hij; exact hinj hij)
    simpa using hle
  omega

end
end PhosphorylationStableCapacity
