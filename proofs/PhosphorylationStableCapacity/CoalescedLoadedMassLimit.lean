module
public import proofs.PhosphorylationStableCapacity.CoalescedSourceSubstrateLimit
public import proofs.PhosphorylationStableCapacity.CoalescedSourcePathLimits
public import proofs.PhosphorylationStableCapacity.CoalescedYPrev

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter
open scoped Topology

noncomputable section

/-- The preceding phosphatase complex at each of the first `m+2` levels of
the literal finite-parameter source state. -/
def coalescedFiniteYPrev (m : ℕ) (r : ℝ) (i : Fin (m + 2)) : ℝ :=
  if i.val = 0 then 0 else
    (coalescedFiniteState (m + 1) r).D
      ⟨i.val - 1, by have := i.isLt; omega⟩

theorem coalescedFiniteYPrev_tendsto (m : ℕ) (i : Fin (m + 2)) :
    Tendsto (fun r : ℝ => coalescedFiniteYPrev m r i) atTop
      (𝓝 (coalescedYPrev m i.val)) := by
  by_cases hi : i.val = 0
  · simp [coalescedFiniteYPrev, coalescedYPrev, hi]
  · simpa [coalescedFiniteYPrev, coalescedYPrev, hi] using
      coalescedFinite_D_to_path m
        ⟨i.val - 1, by have := i.isLt; omega⟩

theorem coalescedFiniteS_scaled_tendsto_zero (m : ℕ) (i : Fin (m + 2)) :
    Tendsto (fun r : ℝ =>
      (coalescedFiniteState (m + 1) r).S i.castSucc / r)
      atTop (𝓝 0) := by
  have h := (coalescedFiniteState_S_tendsto (m + 1) i.castSucc).mul
    tendsto_inv_atTop_zero
  simpa [div_eq_mul_inv] using h

theorem coalescedFiniteYPrev_scaled_tendsto_zero (m : ℕ)
    (i : Fin (m + 2)) :
    Tendsto (fun r : ℝ => coalescedFiniteYPrev m r i / r)
      atTop (𝓝 0) := by
  have h := (coalescedFiniteYPrev_tendsto m i).mul
    tendsto_inv_atTop_zero
  simpa [div_eq_mul_inv] using h

/-- The first-level block of the ordinary loaded mass formula, evaluated at
the literal finite-parameter source concentrations. Its derivation as the
slow Jacobian's mass matrix is a separate formal obligation. -/
def coalescedLoadedMass (m : ℕ) (r : ℝ) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ :=
  fun i j =>
    (if i = j then
      (coalescedFiniteState (m + 1) r).S i.castSucc +
        (coalescedFiniteState (m + 1) r).C i +
          coalescedFiniteYPrev m r i else 0) -
      (coalescedFiniteState (m + 1) r).C i *
        (coalescedFiniteState (m + 1) r).C j / (2 * r) -
      coalescedFiniteYPrev m r i * coalescedFiniteYPrev m r j / 2

def coalescedLoadedMassScaled (m : ℕ) (r : ℝ) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ :=
  fun i j =>
    (if i = j then
      (coalescedFiniteState (m + 1) r).S i.castSucc / r +
        (coalescedFiniteState (m + 1) r).C i / r +
          coalescedFiniteYPrev m r i / r else 0) -
      ((coalescedFiniteState (m + 1) r).C i / r) *
        ((coalescedFiniteState (m + 1) r).C j / r) / 2 -
      (coalescedFiniteYPrev m r i / r) *
        coalescedFiniteYPrev m r j / 2

theorem coalescedLoadedMassScaled_eq (m : ℕ) {r : ℝ} (hr : r ≠ 0)
    (i j : Fin (m + 2)) :
    coalescedLoadedMassScaled m r i j =
      coalescedLoadedMass m r i j / r := by
  unfold coalescedLoadedMassScaled coalescedLoadedMass
  by_cases hij : i = j <;> simp only [hij, ite_true, ite_false]
  all_goals field_simp [hr] <;> ring

/-- The leading finite-parameter loaded mass block converges entrywise to
`diag(d)-ddᵀ/2`; this is the singular leading matrix in the ordinary
large-`r` calculation. -/
theorem coalescedLoadedMassScaled_tendsto (m : ℕ)
    (i j : Fin (m + 2)) :
    Tendsto (fun r : ℝ => coalescedLoadedMassScaled m r i j) atTop
      (𝓝 ((if i = j then coalescedLevelWeight m i else 0) -
        coalescedLevelWeight m i * coalescedLevelWeight m j / 2)) := by
  have hSi := coalescedFiniteS_scaled_tendsto_zero m i
  have hCi := coalescedFinite_C_scaled_to_path m i
  have hCj := coalescedFinite_C_scaled_to_path m j
  have hYi := coalescedFiniteYPrev_scaled_tendsto_zero m i
  have hYj := coalescedFiniteYPrev_tendsto m j
  have hdiag : Tendsto
      (fun r : ℝ =>
        (coalescedFiniteState (m + 1) r).S i.castSucc / r +
          (coalescedFiniteState (m + 1) r).C i / r +
            coalescedFiniteYPrev m r i / r)
      atTop (𝓝 (coalescedLevelWeight m i)) := by
    simpa using (hSi.add hCi).add hYi
  have hfirst : Tendsto
      (fun r : ℝ => if i = j then
        (coalescedFiniteState (m + 1) r).S i.castSucc / r +
          (coalescedFiniteState (m + 1) r).C i / r +
            coalescedFiniteYPrev m r i / r else 0)
      atTop (𝓝 (if i = j then coalescedLevelWeight m i else 0)) := by
    by_cases hij : i = j
    · simpa [hij] using hdiag
    · simp [hij]
  have hCprod := (hCi.mul hCj).div_const (2 : ℝ)
  have hYprod := (hYi.mul hYj).div_const (2 : ℝ)
  have h := (hfirst.sub hCprod).sub hYprod
  simpa [coalescedLoadedMassScaled] using h

end
end PhosphorylationStableCapacity
