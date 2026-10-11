module
public import proofs.PhosphorylationStableCapacity.EulerLyapunovDissipation

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous linear equivalence controls the squared norm in
both directions by explicit positive constants. -/
theorem continuousLinearEquiv_sq_comparison (e : E ≃L[ℝ] F) (v : E) :
    (1 / (‖e.symm.toContinuousLinearMap‖ + 1)^2) * ‖v‖^2 ≤ ‖e v‖^2 ∧
      ‖e v‖^2 ≤ (‖e.toContinuousLinearMap‖ + 1)^2 * ‖v‖^2 := by
  have hC : 0 < ‖e.symm.toContinuousLinearMap‖ + 1 := by positivity
  have hD : 0 < ‖e.toContinuousLinearMap‖ + 1 := by positivity
  have hleft : ‖v‖ ≤ (‖e.symm.toContinuousLinearMap‖ + 1) * ‖e v‖ := by
    calc
      ‖v‖ = ‖e.symm (e v)‖ := by rw [e.symm_apply_apply]
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e v‖ := e.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ (‖e.symm.toContinuousLinearMap‖ + 1) * ‖e v‖ := by gcongr; linarith
  have hright : ‖e v‖ ≤ (‖e.toContinuousLinearMap‖ + 1) * ‖v‖ := by
    calc
      ‖e v‖ ≤ ‖e.toContinuousLinearMap‖ * ‖v‖ := e.toContinuousLinearMap.le_opNorm _
      _ ≤ (‖e.toContinuousLinearMap‖ + 1) * ‖v‖ := by gcongr; linarith
  have hleft2 : ‖v‖^2 ≤ (‖e.symm.toContinuousLinearMap‖ + 1)^2 * ‖e v‖^2 := by
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hC.le (norm_nonneg _))).mpr hleft
    simpa only [mul_pow] using hs
  have hright2 : ‖e v‖^2 ≤ (‖e.toContinuousLinearMap‖ + 1)^2 * ‖v‖^2 := by
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hD.le (norm_nonneg _))).mpr hright
    simpa only [mul_pow] using hs
  constructor
  · calc
      (1 / (‖e.symm.toContinuousLinearMap‖ + 1)^2) * ‖v‖^2 =
          ‖v‖^2 / (‖e.symm.toContinuousLinearMap‖ + 1)^2 := by ring
      _ ≤ ‖e v‖^2 :=
        (div_le_iff₀ (sq_pos_of_pos hC)).mpr
          (by simpa only [mul_comm] using hleft2)
  · exact hright2

/-- Transport a coercive, strictly dissipative bilinear form through
a continuous linear change of coordinates. -/
theorem transport_quadratic_lyapunov_certificate
    (e : E ≃L[ℝ] F) (J : E →L[ℝ] E) (K : F →L[ℝ] F)
    (hconj : ∀ v : E, e (J v) = K (e v))
    (B : F →L[ℝ] F →L[ℝ] ℝ) (b q : ℝ)
    (hb : 0 < b) (hq : 0 < q)
    (hquad : ∀ w : F, ‖w‖^2 ≤ B w w ∧ B w w ≤ b * ‖w‖^2)
    (hdiss : ∀ w : F,
      B w (K w) + B (K w) w ≤ -q * ‖w‖^2) :
    ∃ B' : E →L[ℝ] E →L[ℝ] ℝ,
      ∃ a b' q' : ℝ, 0 < a ∧ 0 < b' ∧ 0 < q' ∧
      ∀ v : E,
        a * ‖v‖^2 ≤ B' v v ∧
        B' v v ≤ b' * ‖v‖^2 ∧
        B' v (J v) + B' (J v) v ≤ -q' * ‖v‖^2 := by
  let a : ℝ := 1 / (‖e.symm.toContinuousLinearMap‖ + 1)^2
  let b' : ℝ := b * (‖e.toContinuousLinearMap‖ + 1)^2
  let q' : ℝ := q * a
  let B' : E →L[ℝ] E →L[ℝ] ℝ :=
    B.bilinearComp e.toContinuousLinearMap e.toContinuousLinearMap
  have ha : 0 < a := by dsimp [a]; positivity
  have hb' : 0 < b' := by dsimp [b']; positivity
  have hq' : 0 < q' := mul_pos hq ha
  refine ⟨B', a, b', q', ha, hb', hq', ?_⟩
  intro v
  have hcomp := continuousLinearEquiv_sq_comparison e v
  have hB := hquad (e v)
  have hL := hdiss (e v)
  have hqcomp := mul_le_mul_of_nonneg_left hcomp.1 hq.le
  dsimp [B', a, b', q']
  rw [hconj v]
  refine ⟨le_trans hcomp.1 hB.1, ?_, ?_⟩
  · exact le_trans hB.2
      (by simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left hcomp.2 hb.le))
  · nlinarith

end
end PhosphorylationStableCapacity

