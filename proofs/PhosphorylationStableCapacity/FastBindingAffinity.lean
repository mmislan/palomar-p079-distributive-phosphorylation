module
public import proofs.PhosphorylationStableCapacity.FastBindingIncidence

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Fast binding affinity for a kinase complex at fixed loaded levels. -/
def fastAffinityC {n : ℕ} (x : State n) (v : FastSpace n)
    (i : Fin n) : ℝ :=
  v.1 i / x.C i +
    boundComplexAt v.1 v.2 i.castSucc / x.S i.castSucc +
    (∑ j, v.1 j) / x.E

/-- Fast binding affinity for a phosphatase complex. -/
def fastAffinityD {n : ℕ} (x : State n) (v : FastSpace n)
    (i : Fin n) : ℝ :=
  v.2 i / x.D i +
    boundComplexAt v.1 v.2 i.succ / x.S i.succ +
    (∑ j, v.2 j) / x.F

theorem fastAffinityC_eq_delta {n : ℕ} (x : State n)
    (v : FastSpace n) (i : Fin n) :
    fastAffinityC x v i =
      v.1 i / x.C i - fastDeltaS v i.castSucc / x.S i.castSucc -
        fastDeltaE v / x.E := by
  simp only [fastAffinityC, fastDeltaS, fastDeltaE]
  ring

theorem fastAffinityD_eq_delta {n : ℕ} (x : State n)
    (v : FastSpace n) (i : Fin n) :
    fastAffinityD x v i =
      v.2 i / x.D i - fastDeltaS v i.succ / x.S i.succ -
        fastDeltaF v / x.F := by
  simp only [fastAffinityD, fastDeltaS, fastDeltaF]
  ring

theorem fastBindingEnergy_eq_affinity_pairing {n : ℕ}
    (x : State n) (v : FastSpace n) :
    fastBindingEnergy x v =
      (∑ i, v.1 i * fastAffinityC x v i) +
        (∑ i, v.2 i * fastAffinityD x v i) := by
  classical
  have hS :
      (∑ i, v.1 i *
        (boundComplexAt v.1 v.2 i.castSucc / x.S i.castSucc)) +
      (∑ i, v.2 i *
        (boundComplexAt v.1 v.2 i.succ / x.S i.succ)) =
      ∑ j, boundComplexAt v.1 v.2 j ^ 2 / x.S j := by
    rw [← boundComplexAt_pairing v.1 v.2
      (fun j => boundComplexAt v.1 v.2 j / x.S j)]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hC :
      (∑ i, v.1 i * (v.1 i / x.C i)) =
        ∑ i, v.1 i ^ 2 / x.C i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hD :
      (∑ i, v.2 i * (v.2 i / x.D i)) =
        ∑ i, v.2 i ^ 2 / x.D i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hE :
      (∑ i, v.1 i * ((∑ j, v.1 j) / x.E)) =
        (∑ i, v.1 i) ^ 2 / x.E := by
    rw [← Finset.sum_mul]
    ring
  have hF :
      (∑ i, v.2 i * ((∑ j, v.2 j) / x.F)) =
        (∑ i, v.2 i) ^ 2 / x.F := by
    rw [← Finset.sum_mul]
    ring
  simp only [fastAffinityC, fastAffinityD, mul_add,
    Finset.sum_add_distrib]
  unfold fastBindingEnergy fastDeltaS fastDeltaE fastDeltaF
  simp only [neg_sq]
  rw [hC, hD, hE, hF]
  rw [← hS]
  ring

end
end PhosphorylationStableCapacity
