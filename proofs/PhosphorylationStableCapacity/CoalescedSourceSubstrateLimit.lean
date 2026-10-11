module
public import proofs.PhosphorylationStableCapacity.CoalescedFiniteSource

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial Filter PhosphorylationSharpness
open scoped Topology

noncomputable section

def coalescedSubstrateLimit (m i : ℕ) : ℝ :=
  ((coalescedPair m).2.coeff i +
    if i = 0 then 0 else (coalescedPair m).2.coeff (i - 1)) /
      (36 : ℝ) ^ m

theorem coalescedFiniteState_S_eq (m : ℕ) (r : ℝ) (i : Fin (m + 2)) :
    (coalescedFiniteState m r).S i =
      finiteD (coalescedPair m).1 (coalescedPair m).2 r i.val +
        if i.val = 0 then 0 else
          finiteD (coalescedPair m).1 (coalescedPair m).2 r (i.val - 1) := by
  let D := coalescedRawD m r
  have hcoeff : ((1 + X) * D).coeff i.val =
      D.coeff i.val + if i.val = 0 then 0 else D.coeff (i.val - 1) := by
    by_cases hi : i.val = 0
    · rw [hi]
      simp [add_mul]
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hi
      rw [hj]
      simp [add_mul, coeff_X_mul]
  have hs : (coalescedFiniteState m r).S i =
      (((1 + X) * D).coeff i.val) / D.eval 1 := by
    norm_num [coalescedFiniteState, reconstruct, D, coalescedRawD,
      ratio, rootS_three, rootF, div_eq_mul_inv]
  rw [hs, hcoeff]
  simp only [finiteD, coalescedRawD, D, add_div]
  split_ifs <;> ring

theorem coalescedFiniteState_S_tendsto (m : ℕ) (i : Fin (m + 2)) :
    Tendsto (fun r : ℝ => (coalescedFiniteState m r).S i) atTop
      (𝓝 (coalescedSubstrateLimit m i.val)) := by
  have hdense := coalescedPair_dense m
  have hnow := finiteD_tendsto hdense.1 hdense.2 i.val
  rw [(coalescedPair_eval_one m).2] at hnow
  by_cases hi : i.val = 0
  · simpa [coalescedFiniteState_S_eq, coalescedSubstrateLimit, hi] using hnow
  · have hprev := finiteD_tendsto hdense.1 hdense.2 (i.val - 1)
    rw [(coalescedPair_eval_one m).2] at hprev
    convert hnow.add hprev using 1
    · ext r
      simp [coalescedFiniteState_S_eq, hi]
    · simp [coalescedSubstrateLimit, hi, add_div]

end
end PhosphorylationStableCapacity
