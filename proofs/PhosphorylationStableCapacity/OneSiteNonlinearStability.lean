module
public import proofs.PhosphorylationStableCapacity.OneSiteEnergyMetricBounds
public import proofs.PhosphorylationStableCapacity.PositiveForwardExistence
public import proofs.PhosphorylationStableCapacity.ExponentialAttractionCriterion

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- The rational quadratic certificate implies a metric exponential
bound for every one-site forward class solution. -/
theorem oneSite_metric_exponential_decay
    (u : CoordinateSpace 1)
    (hu : dist u oneCoord < (1/1000 : ℝ))
    (γ : ℝ → CoordinateSpace 1)
    (hγ : IsForwardClassCurve
      (restrictedFieldEuclid (3/2) (3/2) 3 oneRates) u γ)
    (t : ℝ) (ht : 0 ≤ t) :
    dist (γ t) oneCoord ≤
      60 * Real.exp (-(1/12 : ℝ) * t) * dist u oneCoord := by
  have hmetric0 := oneSiteEnergy_metric_bounds u
  have hmetrict := oneSiteEnergy_metric_bounds (γ t)
  have hd0 : 0 ≤ dist u oneCoord := dist_nonneg
  have hinit : oneSiteEnergy u < (1/10000 : ℝ) := by
    have hsq : (dist u oneCoord)^2 < (1/1000 : ℝ)^2 :=
      (sq_lt_sq₀ hd0 (by norm_num)).2 hu
    nlinarith [hmetric0.2]
  have hdecay := oneSiteEnergy_exponential_decay u γ hγ hinit t ht
  let e := Real.exp (-(1/12 : ℝ) * t)
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hexp : Real.exp (-(1/6 : ℝ) * t) = e^2 := by
    dsimp [e]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hmul : oneSiteEnergy u * Real.exp (-(1/6 : ℝ) * t) ≤
      9 * (dist u oneCoord)^2 * Real.exp (-(1/6 : ℝ) * t) :=
    mul_le_mul_of_nonneg_right hmetric0.2 (Real.exp_pos _).le
  have hsq : (dist (γ t) oneCoord)^2 ≤
      (60 * e * dist u oneCoord)^2 := by
    rw [hexp] at hdecay hmul
    nlinarith [sq_nonneg (e * dist u oneCoord)]
  exact (sq_le_sq₀ dist_nonneg (by positivity)).mp hsq

/-- The literal positive unit-rate one-site equilibrium satisfies the
full nonlinear class stability predicate, including global forward
existence for nearby states. -/
theorem oneSite_locally_asymptotically_stable :
    IsLocallyAsymptoticallyStableClass
      (3/2) (3/2) 3 oneRates oneCoord := by
  obtain ⟨δexist, hδexist, hexist⟩ :=
    positive_state_nearby_forward_existence
      (3/2) (3/2) 3 (by norm_num) oneRates oneRates_positive
      oneState oneState_positive oneState_inClass
  have hchart : toCoordinateSpace (chart oneState) = oneCoord := by
    rfl
  rw [hchart] at hexist
  apply locally_asymptotically_stable_of_exponential_bound
    (restrictedFieldEuclid (3/2) (3/2) 3 oneRates)
    oneCoord oneCoord_equilibrium
    60 (1/12 : ℝ) (min δexist (1/1000 : ℝ))
    (by norm_num) (by norm_num) (lt_min hδexist (by norm_num))
  · intro u hu γ hγ t ht
    simpa [neg_mul] using oneSite_metric_exponential_decay u
      (lt_of_lt_of_le hu (min_le_right _ _)) γ hγ t ht
  · intro u hu
    exact hexist u (lt_of_lt_of_le hu (min_le_left _ _))

end
end PhosphorylationStableCapacity
