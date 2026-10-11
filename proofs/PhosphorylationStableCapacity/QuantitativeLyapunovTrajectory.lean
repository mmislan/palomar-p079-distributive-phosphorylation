module
public import proofs.PhosphorylationStableCapacity.EnergySublevelBarrier
public import proofs.PhosphorylationStableCapacity.QuantitativeRecoveryEnvelope

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open Set Filter

/-- The positive quadratic form's sublevel set is invariant and has the exact
recovery envelope. The derivative inequality is required only inside that
sublevel; it is therefore suitable for a certificate on a finite state box. -/
theorem quantitative_lyapunov_trajectory
    (g g' d : ℝ → ℝ) (p c M ρ : ℝ)
    (hp : 0 < p) (hc : 0 < c) (hM : 0 < M) (hρ : 0 < ρ)
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt g (g' t) (Ici (0 : ℝ)) t)
    (hlower : ∀ t : ℝ, 0 ≤ t → p * (d t)^2 ≤ g t)
    (hd : ∀ t : ℝ, 0 ≤ t → 0 ≤ d t)
    (hslope : ∀ t : ℝ, 0 ≤ t → g t < p * (ρ/2)^2 → g' t ≤ -(c/M)*g t)
    (hinit : g 0 < p * (ρ/2)^2) :
    (∀ t : ℝ, 0 ≤ t → g t < p * (ρ/2)^2 ∧ d t < ρ/2) ∧
    (∀ t : ℝ, 0 ≤ t → d t ≤ (ρ/2)*Real.exp (-(c/(2*M))*t)) ∧
    (∀ t : ℝ, 6*M/c ≤ t → d t < ρ/20) := by
  have hstay : ∀ t : ℝ, 0 ≤ t → g t < p * (ρ/2)^2 := by
    apply energy_stays_below_of_deriv_nonpos_below g g' (p * (ρ/2)^2) hderiv
    · intro t ht hlt
      have hnonneg : 0 ≤ g t := by
        exact (mul_nonneg hp.le (sq_nonneg _)).trans (hlower t ht)
      have hs := hslope t ht hlt
      have hα : 0 < c/M := div_pos hc hM
      nlinarith
    · exact hinit
  have henv : ∀ t : ℝ, 0 ≤ t → d t ≤ (ρ/2)*Real.exp (-(c/(2*M))*t) := by
    intro T hT
    apply quantitative_recovery_envelope g g' d p c M ρ T hp hc hM hρ
    · intro t ht
      exact (hderiv t ht.1).continuousWithinAt.mono (fun s hs => hs.1)
    · intro t ht
      exact (hderiv t ht.1).mono (Ici_subset_Ici.mpr ht.1)
    · intro t ht
      exact hslope t ht.1 (hstay t ht.1)
    · exact hinit.le
    · intro t ht
      exact hlower t ht.1
    · intro t ht
      exact hd t ht.1
    · exact ⟨hT, le_rfl⟩
  refine ⟨?_, henv, ?_⟩
  · intro t ht
    refine ⟨hstay t ht, ?_⟩
    have h := (hlower t ht).trans_lt (hstay t ht)
    have hsq : (d t)^2 < (ρ/2)^2 := lt_of_mul_lt_mul_left h hp.le
    exact (sq_lt_sq₀ (hd t ht) (by linarith)).mp hsq
  · intro t ht
    have ht0 : 0 ≤ t := (div_pos (by linarith : 0 < 6*M) hc).le.trans ht
    have hsmall := recovery_envelope_tenfold_at_certified_time c M t hc hM ht
    have hmul := mul_lt_mul_of_pos_left hsmall (by linarith : 0 < ρ/2)
    have h := (henv t ht0).trans_lt hmul
    convert h using 1
    ring

end
end PhosphorylationStableCapacity
