module
public import proofs.PhosphorylationStableCapacity.PathVector

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- A finite level vector extended by zero outside its index range. -/
def pathLevelAt {m : ℕ} (q : Fin (m + 1) → ℝ) (k : ℕ) : ℝ :=
  if hk : k < m + 1 then q ⟨k, hk⟩ else 0

theorem pathLevelAt_fin {m : ℕ} (q : Fin (m + 1) → ℝ)
    (k : Fin (m + 1)) : pathLevelAt q k.val = q k := by
  simp [pathLevelAt, k.isLt]

/-- The edge flow formed by negative prefix sums of level data. -/
def pathPrefixFlow {m : ℕ} (q : Fin (m + 1) → ℝ)
    (i : Fin m) : ℝ :=
  -(∑ k ∈ Finset.range (i.val + 1), pathLevelAt q k)

theorem pathPrefixFlow_increment {m : ℕ}
    (q : Fin (m + 1) → ℝ) (i : Fin m)
    (hi : i.val + 1 < m) :
    pathPrefixFlow q ⟨i.val + 1, hi⟩ - pathPrefixFlow q i =
      -pathLevelAt q (i.val + 1) := by
  simp only [pathPrefixFlow, Finset.sum_range_succ]
  ring

/-- Every zero-sum level vector is an incidence-transpose edge flow on a
finite path. The explicit witness is a negative prefix sum. -/
theorem pathIncidence_transpose_zero_sum_range {m : ℕ} (hm : 0 < m)
    (q : Fin (m + 1) → ℝ)
    (hq : (∑ k : Fin (m + 1), q k) = 0) :
    ∃ z : Fin m → ℝ,
      ∀ k : Fin (m + 1),
        (pathIncidence m).transpose.mulVec z k = q k := by
  let z := pathPrefixFlow q
  have htotal :
      (∑ k ∈ Finset.range (m + 1), pathLevelAt q k) = 0 := by
    rw [← Fin.sum_univ_eq_sum_range (pathLevelAt q) (m + 1)]
    simpa only [pathLevelAt_fin] using hq
  refine ⟨z, ?_⟩
  intro k
  induction k using Fin.cases with
  | zero =>
      rw [pathIncidence_transpose_zero hm]
      simpa [z, pathPrefixFlow] using
        (pathLevelAt_fin q (0 : Fin (m + 1)))
  | succ i =>
      by_cases hi : i.val + 1 < m
      · rw [pathIncidence_transpose_succ_interior z i hi]
        have hinc := pathPrefixFlow_increment q i hi
        have hval : pathLevelAt q (i.val + 1) = q i.succ := by
          simpa only [Fin.val_succ] using pathLevelAt_fin q i.succ
        calc
          z i - z ⟨i.val + 1, hi⟩ =
              -(z ⟨i.val + 1, hi⟩ - z i) := by ring
          _ = pathLevelAt q (i.val + 1) := by rw [hinc]; ring
          _ = q i.succ := hval
      · rw [pathIncidence_transpose_succ_last z i hi]
        have him : i.val + 1 = m := by omega
        have hval : pathLevelAt q m = q i.succ := by
          simpa only [Fin.val_succ, him] using pathLevelAt_fin q i.succ
        change -(∑ k ∈ Finset.range (i.val + 1),
          pathLevelAt q k) = q i.succ
        rw [him]
        rw [Finset.sum_range_succ] at htotal
        linarith

end
end PhosphorylationStableCapacity
