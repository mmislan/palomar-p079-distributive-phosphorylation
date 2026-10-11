module
public import proofs.PhosphorylationStableCapacity.CoalescedChebyshevTrig

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The first `m` positive angles at which the Dirichlet-kernel numerator
vanishes. -/
def coalescedTheta (m j : ℕ) : ℝ :=
  2 * ((j + 1 : ℕ) : ℝ) * Real.pi / ((2 * m + 1 : ℕ) : ℝ)

theorem coalescedTheta_mem_Ioo (m j : ℕ) (hj : j < m) :
    0 < coalescedTheta m j ∧ coalescedTheta m j < Real.pi := by
  have hkpos : 0 < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hcount : 2 * (j + 1) < 2 * m + 1 := by omega
  have hcountR : 2 * ((j + 1 : ℕ) : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcount
  have hprod := mul_lt_mul_of_pos_right hcountR Real.pi_pos
  constructor
  · unfold coalescedTheta
    positivity
  · unfold coalescedTheta
    apply (div_lt_iff₀ hkpos).2
    nlinarith [hprod]

/-- Every admissible angle is a zero of the scaled source sequence. -/
theorem coalescedChebF_zero (m j : ℕ) (hj : j < m) :
    coalescedChebF m (Real.cos (coalescedTheta m j)) = 0 := by
  let θ := coalescedTheta m j
  have hθ := coalescedTheta_mem_Ioo m j hj
  have hsin : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by dsimp [θ]; linarith [hθ.1])
      (by dsimp [θ]; linarith [hθ.2, Real.pi_pos])
  have hkpos : 0 < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hphase : ((2 * m + 1 : ℕ) : ℝ) * θ / 2 =
      ((j + 1 : ℕ) : ℝ) * Real.pi := by
    dsimp [θ, coalescedTheta]
    field_simp [ne_of_gt hkpos]
  have htrig := coalescedChebF_cos m θ
  rw [hphase, Real.sin_nat_mul_pi] at htrig
  exact (mul_eq_zero.mp htrig).resolve_right (ne_of_gt hsin)

end
end PhosphorylationStableCapacity
