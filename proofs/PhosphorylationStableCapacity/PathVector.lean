module
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.BigOperators.Intervals
public import proofs.PhosphorylationStableCapacity.PathMatrixBridge

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The incidence of an affine level potential with unit slope is the constant
edge vector. -/
theorem pathIncidence_affine (m : ℕ) (μ : ℝ) (i : Fin m) :
    (pathIncidence m).mulVec (fun k : Fin (m+1) => (k.val : ℝ) - μ) i = 1 := by
  rw [pathIncidence_mulVec]
  simp only [Fin.val_succ, Fin.val_castSucc]
  push_cast
  ring

/-- An edge vector whose level flux is the weighted affine potential solves
the path Poisson equation. This isolates the all-n linear identity from the
still required construction and positivity of that vector. -/
theorem pathH_mulVec_eq_one_of_affine_flux {m : ℕ}
    (d : Fin (m+1) → ℝ) (hd : ∀ k, d k ≠ 0)
    (z : Fin m → ℝ) (μ : ℝ)
    (hflux : ∀ k : Fin (m+1),
      (pathIncidence m).transpose.mulVec z k = d k * ((k.val : ℝ) - μ)) :
    ∀ i : Fin m, (pathH d).mulVec z i = 1 := by
  intro i
  rw [pathH_eq_incidence, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hdiag :
      (Matrix.diagonal (fun k : Fin (m+1) => (d k)⁻¹)).mulVec
        ((pathIncidence m).transpose.mulVec z) =
        (fun k : Fin (m+1) => (k.val : ℝ) - μ) := by
    funext k
    simp [Matrix.mulVec_diagonal, hflux k, hd k]
  rw [hdiag]
  exact pathIncidence_affine m μ i

/-- Every cross pair between two nonempty, ordered blocks contributes
strictly positively to the path vector's pair formula. -/
theorem positive_cross_gap (s t : Finset ℕ) (d : ℕ → ℝ)
    (hs : s.Nonempty) (ht : t.Nonempty)
    (hd : ∀ k ∈ s ∪ t, 0 < d k)
    (horder : ∀ a ∈ s, ∀ b ∈ t, a < b) :
    0 < ∑ a ∈ s, ∑ b ∈ t, d a * d b * ((b : ℝ) - (a : ℝ)) := by
  apply Finset.sum_pos
  · intro a ha
    apply Finset.sum_pos
    · intro b hb
      exact mul_pos (mul_pos (hd a (Finset.mem_union_left t ha))
        (hd b (Finset.mem_union_right s hb)))
        (sub_pos.mpr (Nat.cast_lt.mpr (horder a ha b hb)))
    · exact ht
  · exact hs

/-- Expansion of the weighted cross gap between two finite level blocks. -/
theorem cross_gap_identity (s t : Finset ℕ) (d : ℕ → ℝ) :
    (∑ a ∈ s, d a) * (∑ b ∈ t, d b * (b : ℝ)) -
      (∑ a ∈ s, d a * (a : ℝ)) * (∑ b ∈ t, d b) =
      ∑ a ∈ s, ∑ b ∈ t, d a * d b * ((b : ℝ) - (a : ℝ)) := by
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  simp only [← Finset.sum_sub_distrib]
  congr 1
  ext a
  congr 1
  ext b
  ring

/-- The weighted mean of two ordered positive blocks exceeds the weighted
mean of the left block, expressed as a positive left deviation sum. -/
theorem weighted_left_deviation_pos (s t : Finset ℕ) (d : ℕ → ℝ)
    (hs : s.Nonempty) (ht : t.Nonempty)
    (hd : ∀ k ∈ s ∪ t, 0 < d k)
    (horder : ∀ a ∈ s, ∀ b ∈ t, a < b) :
    0 < ∑ a ∈ s, d a *
      (((∑ k ∈ s, d k * (k : ℝ)) + (∑ k ∈ t, d k * (k : ℝ))) /
        ((∑ k ∈ s, d k) + (∑ k ∈ t, d k)) - (a : ℝ)) := by
  let A : ℝ := ∑ k ∈ s, d k
  let B : ℝ := ∑ k ∈ t, d k
  let C : ℝ := ∑ k ∈ s, d k * (k : ℝ)
  let E : ℝ := ∑ k ∈ t, d k * (k : ℝ)
  have hA : 0 < A := Finset.sum_pos
    (fun a ha => hd a (Finset.mem_union_left t ha)) hs
  have hB : 0 < B := Finset.sum_pos
    (fun b hb => hd b (Finset.mem_union_right s hb)) ht
  have hgap : 0 < A * E - C * B := by
    change 0 < (∑ a ∈ s, d a) * (∑ b ∈ t, d b * (b : ℝ)) -
      (∑ a ∈ s, d a * (a : ℝ)) * (∑ b ∈ t, d b)
    rw [cross_gap_identity]
    exact positive_cross_gap s t d hs ht hd horder
  have hsum :
      (∑ a ∈ s, d a * ((C + E) / (A + B) - (a : ℝ))) =
        A * ((C + E) / (A + B)) - C := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rfl
  have hmul : 0 < (A + B) *
      (∑ a ∈ s, d a * ((C + E) / (A + B) - (a : ℝ))) := by
    rw [hsum]
    have hden : A + B ≠ 0 := ne_of_gt (add_pos hA hB)
    have heq : (A + B) * (A * ((C + E) / (A + B)) - C) =
        A * E - C * B := by
      field_simp
      ring
    rw [heq]
    exact hgap
  change 0 < ∑ a ∈ s, d a * ((C + E) / (A + B) - (a : ℝ))
  nlinarith [add_pos hA hB]

/-- Every proper prefix of positive level weights has a strictly positive
weighted deviation from the global level mean. -/
theorem path_prefix_pos {m : ℕ} (d : ℕ → ℝ)
    (hd : ∀ k ≤ m, 0 < d k) (i : Fin m) :
    0 < ∑ k ∈ Finset.range (i.val + 1), d k *
      ((∑ j ∈ Finset.range (m + 1), d j * (j : ℝ)) /
        (∑ j ∈ Finset.range (m + 1), d j) - (k : ℝ)) := by
  let s := Finset.range (i.val + 1)
  let t := Finset.Ico (i.val + 1) (m + 1)
  have hs : s.Nonempty := by
    refine ⟨0, ?_⟩
    simp [s]
  have ht : t.Nonempty := by
    refine ⟨i.val + 1, ?_⟩
    simp [t, i.isLt]
  have hpositive : ∀ k ∈ s ∪ t, 0 < d k := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · exact hd k (by have := Finset.mem_range.mp hk; omega)
    · exact hd k (by have := (Finset.mem_Ico.mp hk).2; omega)
  have horder : ∀ a ∈ s, ∀ b ∈ t, a < b := by
    intro a ha b hb
    have ha' := Finset.mem_range.mp ha
    have hb' := (Finset.mem_Ico.mp hb).1
    omega
  have hbase := weighted_left_deviation_pos s t d hs ht hpositive horder
  have hsplitD : (∑ k ∈ s, d k) + (∑ k ∈ t, d k) =
      ∑ k ∈ Finset.range (m + 1), d k := by
    exact Finset.sum_range_add_sum_Ico d (by omega)
  have hsplitW : (∑ k ∈ s, d k * (k : ℝ)) +
      (∑ k ∈ t, d k * (k : ℝ)) =
      ∑ k ∈ Finset.range (m + 1), d k * (k : ℝ) := by
    exact Finset.sum_range_add_sum_Ico _ (by omega)
  simpa only [s, t, hsplitD, hsplitW] using hbase

/-- The weighted level mean of a path with `m` edges. -/
def pathMean (m : ℕ) (d : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Finset.range (m + 1), d k * (k : ℝ)) /
    (∑ k ∈ Finset.range (m + 1), d k)

/-- Cumulative weighted deviation at each edge. -/
def pathVectorNat {m : ℕ} (d : ℕ → ℝ) (i : Fin m) : ℝ :=
  ∑ k ∈ Finset.range (i.val + 1), d k * (pathMean m d - (k : ℝ))

theorem pathVectorNat_pos {m : ℕ} (d : ℕ → ℝ)
    (hd : ∀ k ≤ m, 0 < d k) (i : Fin m) :
    0 < pathVectorNat d i := by
  exact path_prefix_pos d hd i

theorem pathVectorNat_increment {m : ℕ} (d : ℕ → ℝ)
    (i : Fin m) (hi : i.val + 1 < m) :
    pathVectorNat d ⟨i.val + 1, hi⟩ - pathVectorNat d i =
      d (i.val + 1) * (pathMean m d - (i.val + 1 : ℕ)) := by
  simp only [pathVectorNat, Finset.sum_range_succ]
  ring

theorem path_total_deviation_zero (m : ℕ) (d : ℕ → ℝ)
    (hd : ∀ k ≤ m, 0 < d k) :
    (∑ k ∈ Finset.range (m + 1), d k * (pathMean m d - (k : ℝ))) = 0 := by
  let A : ℝ := ∑ k ∈ Finset.range (m + 1), d k * (k : ℝ)
  let B : ℝ := ∑ k ∈ Finset.range (m + 1), d k
  have hB : 0 < B := by
    apply Finset.sum_pos
    · intro k hk
      exact hd k (by have := Finset.mem_range.mp hk; omega)
    · exact ⟨0, by simp⟩
  have hBne : B ≠ 0 := ne_of_gt hB
  calc
    (∑ k ∈ Finset.range (m + 1), d k * (pathMean m d - (k : ℝ))) =
        B * (A / B) - A := by
      simp only [pathMean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      rfl
    _ = 0 := by field_simp; ring

/-- The transpose incidence flux is the incoming edge value minus the
outgoing edge value, before resolving the two path boundaries. -/
theorem pathIncidence_transpose_mulVec_sums {m : ℕ} (z : Fin m → ℝ)
    (k : Fin (m + 1)) :
    (pathIncidence m).transpose.mulVec z k =
      (∑ i : Fin m, if k = i.succ then z i else 0) -
        (∑ i : Fin m, if k = i.castSucc then z i else 0) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    pathIncidence, sub_mul, Finset.sum_sub_distrib]
  congr 1 <;> congr 1 <;> ext i <;> split_ifs <;> ring

theorem pathIncidence_transpose_zero {m : ℕ} (hm : 0 < m)
    (z : Fin m → ℝ) :
    (pathIncidence m).transpose.mulVec z 0 = -z ⟨0, hm⟩ := by
  rw [pathIncidence_transpose_mulVec_sums]
  have hin : (∑ i : Fin m, if (0 : Fin (m + 1)) = i.succ then z i else 0) = 0 := by
    have hnone : ∀ i : Fin m, (0 : Fin (m + 1)) ≠ i.succ := by
      intro i h
      have hval := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_succ] at hval
      omega
    simp [hnone]
  have hout : (∑ i : Fin m, if (0 : Fin (m + 1)) = i.castSucc then z i else 0) =
      z ⟨0, hm⟩ := by
    have hiff : ∀ i : Fin m, (0 : Fin (m + 1)) = i.castSucc ↔ i = ⟨0, hm⟩ := by
      intro i
      simp only [Fin.ext_iff, Fin.val_zero, Fin.val_castSucc]
      omega
    simp only [hiff]
    simp
  rw [hin, hout]
  ring

theorem pathIncidence_transpose_succ_interior {m : ℕ} (z : Fin m → ℝ)
    (i : Fin m) (hi : i.val + 1 < m) :
    (pathIncidence m).transpose.mulVec z i.succ =
      z i - z ⟨i.val + 1, hi⟩ := by
  rw [pathIncidence_transpose_mulVec_sums]
  have hin : (∑ j : Fin m, if i.succ = j.succ then z j else 0) = z i := by
    have hiff : ∀ j : Fin m, i.succ = j.succ ↔ j = i := by
      intro j
      simp only [Fin.ext_iff, Fin.val_succ]
      omega
    simp only [hiff]
    simp
  have hout : (∑ j : Fin m, if i.succ = j.castSucc then z j else 0) =
      z ⟨i.val + 1, hi⟩ := by
    have hiff : ∀ j : Fin m, i.succ = j.castSucc ↔ j = ⟨i.val + 1, hi⟩ := by
      intro j
      simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
      omega
    simp only [hiff]
    simp
  rw [hin, hout]

theorem pathIncidence_transpose_succ_last {m : ℕ} (z : Fin m → ℝ)
    (i : Fin m) (hi : ¬ i.val + 1 < m) :
    (pathIncidence m).transpose.mulVec z i.succ = z i := by
  rw [pathIncidence_transpose_mulVec_sums]
  have hin : (∑ j : Fin m, if i.succ = j.succ then z j else 0) = z i := by
    have hiff : ∀ j : Fin m, i.succ = j.succ ↔ j = i := by
      intro j
      simp only [Fin.ext_iff, Fin.val_succ]
      omega
    simp only [hiff]
    simp
  have hout : (∑ j : Fin m, if i.succ = j.castSucc then z j else 0) = 0 := by
    have hnone : ∀ j : Fin m, i.succ ≠ j.castSucc := by
      intro j h
      have hval := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_castSucc] at hval
      omega
    simp [hnone]
  rw [hin, hout]
  ring

/-- The cumulative weighted deviations have exactly the affine level flux
needed by the path Poisson equation. -/
theorem pathVectorNat_affine_flux {m : ℕ} (hm : 0 < m)
    (d : ℕ → ℝ) (hd : ∀ k ≤ m, 0 < d k) :
    ∀ k : Fin (m + 1),
      (pathIncidence m).transpose.mulVec (pathVectorNat d) k =
        d k.val * ((k.val : ℝ) - pathMean m d) := by
  intro k
  induction k using Fin.cases with
  | zero =>
      rw [pathIncidence_transpose_zero hm]
      simp [pathVectorNat]
  | succ i =>
      by_cases hi : i.val + 1 < m
      · rw [pathIncidence_transpose_succ_interior (pathVectorNat d) i hi]
        have hinc := pathVectorNat_increment d i hi
        calc
          pathVectorNat d i - pathVectorNat d ⟨i.val + 1, hi⟩ =
              -(pathVectorNat d ⟨i.val + 1, hi⟩ - pathVectorNat d i) := by ring
          _ = -(d (i.val + 1) *
              (pathMean m d - (i.val + 1 : ℕ))) := by rw [hinc]
          _ = d (i.succ.val) * ((i.succ.val : ℝ) - pathMean m d) := by
            simp only [Fin.val_succ]
            push_cast
            ring
      · rw [pathIncidence_transpose_succ_last (pathVectorNat d) i hi]
        have him : i.val + 1 = m := by omega
        have hz : pathVectorNat d i =
            ∑ k ∈ Finset.range m, d k * (pathMean m d - (k : ℝ)) := by
          simp only [pathVectorNat]
          rw [him]
        have htotal := path_total_deviation_zero m d hd
        rw [Finset.sum_range_succ] at htotal
        rw [hz]
        simp only [Fin.val_succ]
        rw [him]
        nlinarith [htotal]

/-- Every positive weighted path with at least one edge has a strictly
positive solution of its Poisson equation `H z = 1`. -/
theorem pathH_positive_solution_nat {m : ℕ} (hm : 0 < m)
    (d : ℕ → ℝ) (hd : ∀ k ≤ m, 0 < d k) :
    ∃ z : Fin m → ℝ, (∀ i, 0 < z i) ∧
      (∀ i, (pathH (fun k : Fin (m + 1) => d k.val)).mulVec z i = 1) := by
  refine ⟨pathVectorNat d, pathVectorNat_pos d hd, ?_⟩
  apply pathH_mulVec_eq_one_of_affine_flux
    (fun k : Fin (m + 1) => d k.val)
    (fun k => ne_of_gt (hd k.val (by have := k.isLt; omega)))
    (pathVectorNat d) (pathMean m d)
  exact pathVectorNat_affine_flux hm d hd

/-- Finite-index form of the positive path Poisson solution. -/
theorem pathH_positive_solution {m : ℕ} (hm : 0 < m)
    (d : Fin (m + 1) → ℝ) (hd : ∀ k, 0 < d k) :
    ∃ z : Fin m → ℝ, (∀ i, 0 < z i) ∧
      (∀ i, (pathH d).mulVec z i = 1) := by
  let dn : ℕ → ℝ := fun k => if h : k < m + 1 then d ⟨k, h⟩ else 0
  have hdn : ∀ k ≤ m, 0 < dn k := by
    intro k hk
    have hlt : k < m + 1 := by omega
    change 0 < (if h : k < m + 1 then d ⟨k, h⟩ else 0)
    simpa only [hlt, dite_true] using hd ⟨k, hlt⟩
  obtain ⟨z, hz, hH⟩ := pathH_positive_solution_nat hm dn hdn
  have hrestrict : (fun k : Fin (m + 1) => dn k.val) = d := by
    funext k
    change (if h : k.val < m + 1 then d ⟨k.val, h⟩ else 0) = d k
    simp only [k.isLt, dite_true]
  rw [hrestrict] at hH
  exact ⟨z, hz, hH⟩

end
end PhosphorylationStableCapacity
