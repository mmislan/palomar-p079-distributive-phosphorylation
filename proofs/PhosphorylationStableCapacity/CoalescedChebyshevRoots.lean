module
public import proofs.PhosphorylationStableCapacity.CoalescedChebyshevZeros

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The inverse fractional-linear image of an explicit Chebyshev zero. -/
def coalescedRoot (m j : ℕ) : ℝ :=
  (4 * Real.cos (coalescedTheta m j) - 5) /
    (4 * (Real.cos (coalescedTheta m j) + 1))

theorem coalescedCos_mem_Ioo (m j : ℕ) (hj : j < m) :
    -1 < Real.cos (coalescedTheta m j) ∧
      Real.cos (coalescedTheta m j) < 1 := by
  have hθ := coalescedTheta_mem_Ioo m j hj
  have hθmem : coalescedTheta m j ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨hθ.1.le, hθ.2.le⟩
  constructor
  · have h := Real.strictAntiOn_cos hθmem
      (show Real.pi ∈ Set.Icc (0 : ℝ) Real.pi from
        ⟨Real.pi_pos.le, le_refl _⟩) hθ.2
    simpa using h
  · have h := Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi from
        ⟨le_refl _, Real.pi_pos.le⟩) hθmem hθ.1
    simpa using h

theorem coalescedRoot_neg (m j : ℕ) (hj : j < m) :
    coalescedRoot m j < 0 := by
  have hc := coalescedCos_mem_Ioo m j hj
  unfold coalescedRoot
  apply div_neg_of_neg_of_pos
  · linarith [hc.2]
  · linarith [hc.1]

theorem coalescedT_root (m j : ℕ) (hj : j < m) :
    coalescedT (coalescedRoot m j) = Real.cos (coalescedTheta m j) := by
  have hc := coalescedCos_mem_Ioo m j hj
  let t := Real.cos (coalescedTheta m j)
  have ht : t + 1 ≠ 0 := by dsimp [t]; linarith [hc.1]
  have hden : 4 * (t + 1) ≠ 0 := by positivity
  have hnum : 5 + 4 * ((4 * t - 5) / (4 * (t + 1))) =
      9 * t / (t + 1) := by
    field_simp [ht]
    ring
  have hsub : 1 - ((4 * t - 5) / (4 * (t + 1))) =
      9 / (4 * (t + 1)) := by
    field_simp [ht]
    ring
  change (5 + 4 * ((4 * t - 5) / (4 * (t + 1)))) /
      (4 * (1 - ((4 * t - 5) / (4 * (t + 1))))) = t
  rw [hnum, hsub]
  field_simp [ht, hden]

/-- The coalesced source numerator has an explicit negative real zero for
every index below its recurrence length. -/
theorem coalescedN_eval_root (m j : ℕ) (hj : j < m) :
    (coalescedPair m).1.eval (coalescedRoot m j) = 0 := by
  have hrneg := coalescedRoot_neg m j hj
  have hrne : coalescedRoot m j ≠ 1 := by linarith
  rw [coalescedN_cheb_scale m (coalescedRoot m j) hrne,
    coalescedT_root m j hj, coalescedChebF_zero m j hj]
  ring

end
end PhosphorylationStableCapacity
