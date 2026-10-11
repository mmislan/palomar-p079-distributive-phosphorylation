module
public import proofs.PhosphorylationStableCapacity.BilinearEnergySlope
public import proofs.PhosphorylationStableCapacity.QuadraticEnergyCriterion

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Filter
open scoped Topology

noncomputable section

/-- A strict quadratic Lyapunov form for the literal class Jacobian
implies full nonlinear local asymptotic stability for that equilibrium.
The remaining all-size linear-to-nonlinear issue is construction of
such a form from the Hurwitz spectrum. -/
theorem class_las_of_bilinear_lyapunov {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n)
    (x : CoordinateSpace n)
    (heq : restrictedFieldEuclid ET FT ST k x = 0)
    (B : CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ)
    (a b C M q : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hC : 0 ≤ C)
    (hM : 0 < M) (hq : 0 < q)
    (hratio : b ≤ a * C^2)
    (hquadratic : ∀ v : CoordinateSpace n,
      a * ‖v‖^2 ≤ B v v ∧ B v v ≤ b * ‖v‖^2)
    (hbound : ∀ v w : CoordinateSpace n,
      |B v w| ≤ M * ‖v‖ * ‖w‖)
    (hlinear : ∀ v : CoordinateSpace n,
      B v (restrictedJacobian ET FT ST k x v) +
        B (restrictedJacobian ET FT ST k x v) v ≤
        -q * ‖v‖^2)
    (hexist : ∃ δ : ℝ, 0 < δ ∧
      ∀ u : CoordinateSpace n, dist u x < δ →
        ∃ γ : ℝ → CoordinateSpace n,
          IsForwardClassCurve (restrictedFieldEuclid ET FT ST k) u γ) :
    IsLocallyAsymptoticallyStableClass ET FT ST k x := by
  obtain ⟨δslope, hδslope, hslope⟩ :=
    restrictedField_bilinear_slope_negative_near
      ET FT ST k x heq B M q hM hq hbound hlinear
  obtain ⟨δexist, hδexist, hcurves⟩ := hexist
  let V : CoordinateSpace n → ℝ := fun u => B (u-x) (u-x)
  let slope : CoordinateSpace n → ℝ := fun u =>
    B (u-x) (restrictedFieldEuclid ET FT ST k u) +
      B (restrictedFieldEuclid ET FT ST k u) (u-x)
  let L : ℝ := a * δslope^2
  have hL : 0 < L := mul_pos ha (sq_pos_of_pos hδslope)
  have hVx : V x = 0 := by simp [V]
  have hVcont : ContinuousAt V x := by
    dsimp [V]
    fun_prop
  have hsmall_nhds : {u : CoordinateSpace n | V u < L} ∈ 𝓝 x := by
    exact hVcont (by simpa [hVx] using (Iio_mem_nhds hL))
  obtain ⟨δsmall, hδsmall, hball⟩ :=
    Metric.mem_nhds_iff.mp hsmall_nhds
  let δ₀ := min δexist δsmall
  have hδ₀ : 0 < δ₀ := lt_min hδexist hδsmall
  apply locally_asymptotically_stable_of_quadratic_energy
    (restrictedFieldEuclid ET FT ST k) x heq V slope
    a b C (q/(2*b)) L δ₀ ha hC
    (div_pos hq (by positivity)) hδ₀ hratio
  · intro u
    simpa [V, dist_eq_norm] using (hquadratic (u-x)).1
  · intro u
    simpa [V, dist_eq_norm] using (hquadratic (u-x)).2
  · intro u hu
    exact hball (Metric.mem_ball.mpr
      (lt_of_lt_of_le hu (min_le_right _ _)))
  · intro u γ hγ t ht
    exact bilinear_energy_hasDerivWithinAt_forward
      ET FT ST k x u B γ hγ t ht
  · intro u hu
    have hlow : a * (dist u x)^2 ≤ V u := by
      simpa [V, dist_eq_norm] using (hquadratic (u-x)).1
    have hmul : a * (dist u x)^2 < a * δslope^2 :=
      lt_of_le_of_lt hlow hu
    have hsq : (dist u x)^2 < δslope^2 :=
      lt_of_mul_lt_mul_left hmul ha.le
    have hnear : dist u x < δslope :=
      (sq_lt_sq₀ dist_nonneg hδslope.le).mp hsq
    have hs := hslope u hnear
    have hupper : V u ≤ b * ‖u-x‖^2 :=
      (hquadratic (u-x)).2
    have hα : 0 ≤ q/(2*b) := (div_pos hq (by positivity)).le
    have hmul' := mul_le_mul_of_nonneg_left hupper hα
    have hcoef : (q/(2*b))*b = q/2 := by
      field_simp
    have hmul'' : (q/(2*b))*V u ≤ (q/2)*‖u-x‖^2 := by
      calc
        _ ≤ (q/(2*b))*(b*‖u-x‖^2) := hmul'
        _ = _ := by rw [← mul_assoc, hcoef]
    dsimp [slope]
    nlinarith [hs, hmul'']
  · intro u hu
    exact hcurves u (lt_of_lt_of_le hu (min_le_left _ _))

end
end PhosphorylationStableCapacity
