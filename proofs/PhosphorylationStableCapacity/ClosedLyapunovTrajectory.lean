module
public import proofs.PhosphorylationStableCapacity.QuantitativeLyapunovTrajectory

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open Set Filter

/-- A closed energy sublevel is invariant when the differential inequality
holds on a strictly larger sublevel. This includes initial data on the boundary
of the printed operational ellipsoid. -/
theorem closed_lyapunov_trajectory
    (g g' d : ℝ → ℝ) (p c M ρ L : ℝ)
    (hp : 0 < p) (hc : 0 < c) (hM : 0 < M) (hρ : 0 < ρ)
    (hL : p*(ρ/2)^2 < L)
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt g (g' t) (Ici (0 : ℝ)) t)
    (hlower : ∀ t : ℝ, 0 ≤ t → p*(d t)^2 ≤ g t)
    (hd : ∀ t : ℝ, 0 ≤ t → 0 ≤ d t)
    (hslope : ∀ t : ℝ, 0 ≤ t → g t < L → g' t ≤ -(c/M)*g t)
    (hinit : g 0 ≤ p*(ρ/2)^2) :
    (∀ t : ℝ, 0 ≤ t → g t ≤ p*(ρ/2)^2) ∧
    (∀ t : ℝ, 0 ≤ t → d t ≤ (ρ/2)*Real.exp (-(c/(2*M))*t)) ∧
    (∀ t : ℝ, 6*M/c ≤ t → d t < ρ/20) := by
  have hstay : ∀ t : ℝ, 0 ≤ t → g t < L := by
    apply energy_stays_below_of_deriv_nonpos_below g g' L hderiv
    · intro t ht hlt
      have hg : 0 ≤ g t := (mul_nonneg hp.le (sq_nonneg _)).trans (hlower t ht)
      have hs := hslope t ht hlt
      have hα : 0 < c/M := div_pos hc hM
      nlinarith
    · exact hinit.trans_lt hL
  have hdecay (T : ℝ) (hT : 0 ≤ T) :
      g T ≤ g 0*Real.exp (-(c/M)*T) := by
    have hG := le_gronwallBound_of_liminf_deriv_right_le
      (δ := g 0) (K := -(c/M)) (ε := 0)
      (a := 0) (b := T) (f := g) (f' := g')
      (fun t ht => (hderiv t ht.1).continuousWithinAt.mono (fun s hs => hs.1))
      (fun t ht r hr =>
        ((hderiv t ht.1).mono (Ici_subset_Ici.mpr ht.1)).liminf_right_slope_le hr)
      (le_refl (g 0)) (by
        intro t ht
        simpa only [neg_mul, add_zero] using hslope t ht.1 (hstay t ht.1))
    simpa only [gronwallBound_ε0, sub_zero] using hG T ⟨hT, le_rfl⟩
  have henv : ∀ t : ℝ, 0 ≤ t → d t ≤ (ρ/2)*Real.exp (-(c/(2*M))*t) := by
    intro T hT
    apply quantitative_recovery_envelope g g' d p c M ρ T hp hc hM hρ
    · intro t ht
      exact (hderiv t ht.1).continuousWithinAt.mono (fun s hs => hs.1)
    · intro t ht
      exact (hderiv t ht.1).mono (Ici_subset_Ici.mpr ht.1)
    · intro t ht
      exact hslope t ht.1 (hstay t ht.1)
    · exact hinit
    · intro t ht
      exact hlower t ht.1
    · intro t ht
      exact hd t ht.1
    · exact ⟨hT, le_rfl⟩
  refine ⟨?_, henv, ?_⟩
  · intro t ht
    have he : Real.exp (-(c/M)*t) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_pos hc hM).le) ht
    have hg0 : 0 ≤ g 0 := (mul_nonneg hp.le (sq_nonneg _)).trans (hlower 0 le_rfl)
    exact (hdecay t ht).trans ((mul_le_mul_of_nonneg_left he hg0).trans (by simpa using hinit))
  · intro t ht
    have ht0 : 0 ≤ t := (div_pos (by linarith : 0 < 6*M) hc).le.trans ht
    have hsmall := recovery_envelope_tenfold_at_certified_time c M t hc hM ht
    have hmul := mul_lt_mul_of_pos_left hsmall (by linarith : 0 < ρ/2)
    have h := (henv t ht0).trans_lt hmul
    convert h using 1
    ring

end
end PhosphorylationStableCapacity
