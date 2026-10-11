module
public import proofs.PhosphorylationStableCapacity.CoalescedChebyshevRoots

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

theorem coalescedTheta_strictMono (m j k : ℕ) (hjk : j < k) :
    coalescedTheta m j < coalescedTheta m k := by
  have hkpos : 0 < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hjR : ((j + 1 : ℕ) : ℝ) < ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_lt_add_right hjk 1
  have hprod := mul_lt_mul_of_pos_right hjR Real.pi_pos
  have hnum : 2 * ((j + 1 : ℕ) : ℝ) * Real.pi <
      2 * ((k + 1 : ℕ) : ℝ) * Real.pi := by nlinarith [hprod]
  unfold coalescedTheta
  apply (div_lt_div_iff₀ hkpos hkpos).2
  exact mul_lt_mul_of_pos_right hnum hkpos

theorem coalescedRoot_mono_of_cos_lt (a b : ℝ)
    (ha : -1 < a) (hab : a < b) :
    (4 * a - 5) / (4 * (a + 1)) <
      (4 * b - 5) / (4 * (b + 1)) := by
  have hda : 0 < 4 * (a + 1) := by linarith
  have hdb : 0 < 4 * (b + 1) := by linarith
  apply (div_lt_div_iff₀ hda hdb).2
  nlinarith

/-- The first `m` source roots are strictly ordered, hence distinct. -/
theorem coalescedRoot_strictAnti (m j k : ℕ)
    (hj : j < m) (hk : k < m) (hjk : j < k) :
    coalescedRoot m k < coalescedRoot m j := by
  have hθj := coalescedTheta_mem_Ioo m j hj
  have hθk := coalescedTheta_mem_Ioo m k hk
  have hθ := coalescedTheta_strictMono m j k hjk
  have hc : Real.cos (coalescedTheta m k) <
      Real.cos (coalescedTheta m j) :=
    Real.strictAntiOn_cos ⟨hθj.1.le, hθj.2.le⟩
      ⟨hθk.1.le, hθk.2.le⟩ hθ
  exact coalescedRoot_mono_of_cos_lt _ _
    (coalescedCos_mem_Ioo m k hk).1
    hc

end
end PhosphorylationStableCapacity
