module
public import proofs.PhosphorylationStableCapacity.FiniteDisjointAttractorBalls
public import proofs.PhosphorylationStableCapacity.LocalStableEquilibriumBudget
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness

/-- A cardinality violation supplies an explicitly indexed family of
`n+1` distinct elements of a finite set. -/
theorem finite_set_gt_n_has_n_succ_distinct
    {α : Type*} {S : Set α} (hfinite : S.Finite) (n : ℕ)
    (hmore : n < S.ncard) :
    ∃ xs : Fin (n + 1) → α,
      Function.Injective xs ∧ ∀ i, xs i ∈ S := by
  classical
  have hmore' : n < hfinite.toFinset.card := by
    simpa only [Set.ncard_eq_toFinset_card S hfinite] using hmore
  have hcard : Fintype.card (Fin (n + 1)) ≤ hfinite.toFinset.card := by
    simpa using (Nat.succ_le_of_lt hmore')
  obtain ⟨e, he⟩ :=
    Function.Embedding.exists_of_card_le_finset (α := Fin (n + 1)) hcard
  refine ⟨e, e.injective, ?_⟩
  intro i
  exact hfinite.mem_toFinset.mp (he ⟨i, rfl⟩)

/-- Any counterexample to the claimed `n` ceiling contains `n+1`
distinct literal positive nonlinear attractors in one class. -/
theorem stable_state_ceiling_violation_has_n_succ_attractors {n : ℕ}
    (hn : 0 < n) (ET FT ST : ℝ)
    (hET : 0 < ET) (hFT : 0 < FT)
    (k : Rates n) (hk : k.Positive)
    (hmore : n < (locallyStablePositiveStates ET FT ST k).ncard) :
    ∃ states : Fin (n + 1) → State n,
      Function.Injective states ∧
        ∀ i, states i ∈ locallyStablePositiveStates ET FT ST k := by
  have hfinite :=
    (locally_stable_positive_states_finite_ncard_le_two_n
      hn ET FT ST hET hFT k hk).1
  exact finite_set_gt_n_has_n_succ_distinct hfinite n hmore

/-- Distinct literal stable states in a fixed class give distinct
class-chart centers satisfying the precise hypotheses of the
disjoint-ball regular-perturbation theorem. -/
theorem stable_state_family_chart_data {n m : ℕ}
    (ET FT ST : ℝ) (k : Rates n)
    (states : Fin m → State n)
    (hinj : Function.Injective states)
    (hstates : ∀ i, states i ∈ locallyStablePositiveStates ET FT ST k) :
    Function.Injective
      (fun i => toCoordinateSpace (chart (states i))) ∧
    (∀ i, IsLocallyAsymptoticallyStableClass ET FT ST k
      (toCoordinateSpace (chart (states i)))) ∧
    (∀ i, toCoordinateSpace (chart (states i)) ∈
      classPolytopeStrict n ET FT ST) := by
  refine ⟨?_, (fun i => (hstates i).2.2), ?_⟩
  · intro i j hij
    apply hinj
    have hchart : chart (states i) = chart (states j) := by
      have h := congrArg ofCoordinateSpace hij
      simpa only [of_toCoordinateSpace] using h
    calc
      states i = unChart ET FT ST (chart (states i)) :=
        (unChart_chart_of_inClass ET FT ST (states i)
          (hstates i).2.1).symm
      _ = unChart ET FT ST (chart (states j)) := by rw [hchart]
      _ = states j :=
        unChart_chart_of_inClass ET FT ST (states j)
          (hstates j).2.1
  · intro i
    exact positive_state_mem_classPolytopeStrict ET FT ST
      (states i) (hstates i).1 (hstates i).2.1

end
end PhosphorylationStableCapacity
