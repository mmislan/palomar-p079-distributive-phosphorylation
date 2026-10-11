module
public import proofs.PhosphorylationStableCapacity.CoalescedMassKernel

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter
open scoped Topology

noncomputable section

/-- Kinase complexes on all `m+3` substrate levels, extended by zero at the
last level. -/
def coalescedFiniteCLevel (m : ℕ) (r : ℝ) (i : Fin (m + 3)) : ℝ :=
  if h : i.val < m + 2 then
    (coalescedFiniteState (m + 1) r).C ⟨i.val, h⟩ else 0

/-- Phosphatase complexes on all levels, extended by zero at level zero. -/
def coalescedFiniteYLevel (m : ℕ) (r : ℝ) (i : Fin (m + 3)) : ℝ :=
  if i.val = 0 then 0 else
    (coalescedFiniteState (m + 1) r).D
      ⟨i.val - 1, by have := i.isLt; omega⟩

/-- The leading kinase-complex weight extended by zero at the last level. -/
def coalescedFullLevelWeight (m : ℕ) (i : Fin (m + 3)) : ℝ :=
  if i.val < m + 2 then coalescedLevelWeight m i.val else 0

theorem coalescedFiniteCLevel_scaled_tendsto (m : ℕ)
    (i : Fin (m + 3)) :
    Tendsto (fun r : ℝ => coalescedFiniteCLevel m r i / r) atTop
      (𝓝 (coalescedFullLevelWeight m i)) := by
  by_cases hi : i.val < m + 2
  · simpa [coalescedFiniteCLevel, coalescedFullLevelWeight, hi] using
      coalescedFinite_C_scaled_to_path m ⟨i.val, hi⟩
  · simp [coalescedFiniteCLevel, coalescedFullLevelWeight, hi]

theorem coalescedFiniteYLevel_tendsto (m : ℕ) (i : Fin (m + 3)) :
    Tendsto (fun r : ℝ => coalescedFiniteYLevel m r i) atTop
      (𝓝 (if i.val = 0 then 0 else coalescedYNext m (i.val - 1))) := by
  by_cases hi : i.val = 0
  · simp [coalescedFiniteYLevel, hi]
  · simpa [coalescedFiniteYLevel, hi] using
      coalescedFinite_D_to_path m
        ⟨i.val - 1, by have := i.isLt; omega⟩

theorem coalescedFiniteYLevel_scaled_tendsto_zero (m : ℕ)
    (i : Fin (m + 3)) :
    Tendsto (fun r : ℝ => coalescedFiniteYLevel m r i / r)
      atTop (𝓝 0) := by
  have h := (coalescedFiniteYLevel_tendsto m i).mul
    tendsto_inv_atTop_zero
  simpa [div_eq_mul_inv] using h

theorem coalescedFiniteSLevel_scaled_tendsto_zero (m : ℕ)
    (i : Fin (m + 3)) :
    Tendsto (fun r : ℝ => (coalescedFiniteState (m + 1) r).S i / r)
      atTop (𝓝 0) := by
  have h := (coalescedFiniteState_S_tendsto (m + 1) i).mul
    tendsto_inv_atTop_zero
  simpa [div_eq_mul_inv] using h

/-- The ordinary loaded mass formula on all levels, evaluated at the
literal coalesced finite-parameter equilibrium. Its derivative identity
with the actual slow system remains to be formalized. -/
def coalescedFullMass (m : ℕ) (r : ℝ) :
    Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ :=
  fun i j =>
    (if i = j then
      (coalescedFiniteState (m + 1) r).S i +
        coalescedFiniteCLevel m r i + coalescedFiniteYLevel m r i
      else 0) -
      coalescedFiniteCLevel m r i * coalescedFiniteCLevel m r j /
        (2 * r) -
      coalescedFiniteYLevel m r i * coalescedFiniteYLevel m r j / 2

def coalescedFullMassScaled (m : ℕ) (r : ℝ) :
    Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ :=
  fun i j =>
    (if i = j then
      (coalescedFiniteState (m + 1) r).S i / r +
        coalescedFiniteCLevel m r i / r +
          coalescedFiniteYLevel m r i / r else 0) -
      (coalescedFiniteCLevel m r i / r) *
        (coalescedFiniteCLevel m r j / r) / 2 -
      (coalescedFiniteYLevel m r i / r) *
        coalescedFiniteYLevel m r j / 2

theorem coalescedFullMassScaled_eq (m : ℕ) {r : ℝ} (hr : r ≠ 0)
    (i j : Fin (m + 3)) :
    coalescedFullMassScaled m r i j = coalescedFullMass m r i j / r := by
  unfold coalescedFullMassScaled coalescedFullMass
  by_cases hij : i = j <;> simp only [hij, ite_true, ite_false]
  all_goals field_simp [hr] <;> ring

/-- The full leading mass limit has one constant first-level kernel mode
and one independent final-level mode; its entries are the diagonal-minus-
rank-one matrix with a zero final row and column. -/
theorem coalescedFullMassScaled_tendsto (m : ℕ)
    (i j : Fin (m + 3)) :
    Tendsto (fun r : ℝ => coalescedFullMassScaled m r i j) atTop
      (𝓝 (rankOneMass (coalescedFullLevelWeight m) i j)) := by
  have hSi := coalescedFiniteSLevel_scaled_tendsto_zero m i
  have hCi := coalescedFiniteCLevel_scaled_tendsto m i
  have hCj := coalescedFiniteCLevel_scaled_tendsto m j
  have hYi := coalescedFiniteYLevel_scaled_tendsto_zero m i
  have hYj := coalescedFiniteYLevel_tendsto m j
  have hdiag : Tendsto
      (fun r : ℝ => (coalescedFiniteState (m + 1) r).S i / r +
        coalescedFiniteCLevel m r i / r +
          coalescedFiniteYLevel m r i / r)
      atTop (𝓝 (coalescedFullLevelWeight m i)) := by
    simpa using (hSi.add hCi).add hYi
  have hfirst : Tendsto
      (fun r : ℝ => if i = j then
        (coalescedFiniteState (m + 1) r).S i / r +
          coalescedFiniteCLevel m r i / r +
            coalescedFiniteYLevel m r i / r else 0)
      atTop (𝓝 (if i = j then coalescedFullLevelWeight m i else 0)) := by
    by_cases hij : i = j
    · simpa [hij] using hdiag
    · simp [hij]
  have hCprod := (hCi.mul hCj).div_const (2 : ℝ)
  have hYprod := (hYi.mul hYj).div_const (2 : ℝ)
  have h := (hfirst.sub hCprod).sub hYprod
  simpa [coalescedFullMassScaled, rankOneMass] using h

end
end PhosphorylationStableCapacity
