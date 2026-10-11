module
public import proofs.PhosphorylationStableCapacity.OneSiteEnergyBounds
public import proofs.PhosphorylationStableCapacity.EnergySublevelBarrier

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- Below a small rational energy level, coercivity places the
literal one-site state inside the coordinate box where its exact
nonlinear energy slope is nonpositive. -/
theorem oneSiteEnergy_slope_nonpos_of_energy_lt
    (u : CoordinateSpace 1)
    (hu : oneSiteEnergy u < (1/10000 : ℝ)) :
    oneSiteEnergySlope (oneSiteDisplacement u) ≤ 0 := by
  let a := oneSiteDisplacement u 0
  let b := oneSiteDisplacement u 1
  let c := oneSiteDisplacement u 2
  have hLower := (oneSiteEnergyPoly_bounds a b c).1
  have hsum : a^2+b^2+c^2 < (1/100 : ℝ) := by
    change oneSiteEnergyPoly a b c < (1/10000 : ℝ) at hu
    linarith
  have ha : a ≤ (1/10 : ℝ) := by
    nlinarith [sq_nonneg b, sq_nonneg c]
  have hb : b ≤ (1/10 : ℝ) := by
    nlinarith [sq_nonneg a, sq_nonneg c]
  have hcl : -(1/10 : ℝ) ≤ c := by
    nlinarith [sq_nonneg a, sq_nonneg b]
  have hcu : c ≤ (1/10 : ℝ) := by
    nlinarith [sq_nonneg a, sq_nonneg b]
  have hveta : oneSiteDisplacement u = ![a,b,c] := by
    ext i
    fin_cases i <;> rfl
  rw [hveta]
  have hslope := oneSite_energy_slope_negative a b c ha hb hcl hcu
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]

/-- Inside the same rational sublevel, the energy slope is at most
`-V/6`, using the exact upper quadratic comparison `V≤3‖v‖₂²`. -/
theorem oneSiteEnergy_slope_le_neg_sixth
    (u : CoordinateSpace 1)
    (hu : oneSiteEnergy u < (1/10000 : ℝ)) :
    oneSiteEnergySlope (oneSiteDisplacement u) ≤
      -(oneSiteEnergy u)/6 := by
  let a := oneSiteDisplacement u 0
  let b := oneSiteDisplacement u 1
  let c := oneSiteDisplacement u 2
  have hBounds := oneSiteEnergyPoly_bounds a b c
  have hsum : a^2+b^2+c^2 < (1/100 : ℝ) := by
    change oneSiteEnergyPoly a b c < (1/10000 : ℝ) at hu
    linarith [hBounds.1]
  have ha : a ≤ (1/10 : ℝ) := by
    nlinarith [sq_nonneg b, sq_nonneg c]
  have hb : b ≤ (1/10 : ℝ) := by
    nlinarith [sq_nonneg a, sq_nonneg c]
  have hcl : -(1/10 : ℝ) ≤ c := by
    nlinarith [sq_nonneg a, sq_nonneg b]
  have hcu : c ≤ (1/10 : ℝ) := by
    nlinarith [sq_nonneg a, sq_nonneg b]
  have hveta : oneSiteDisplacement u = ![a,b,c] := by
    ext i
    fin_cases i <;> rfl
  have hslope := oneSite_energy_slope_negative a b c ha hb hcl hcu
  rw [hveta]
  change oneSiteEnergySlope ![a,b,c] ≤
    -(oneSiteEnergyPoly a b c)/6
  linarith [hBounds.2]

/-- Every literal one-site forward solution starting in this
small-energy sublevel remains there for all forward time. -/
theorem oneSiteEnergy_sublevel_forward_invariant
    (u : CoordinateSpace 1)
    (γ : ℝ → CoordinateSpace 1)
    (hγ : IsForwardClassCurve
      (restrictedFieldEuclid (3/2) (3/2) 3 oneRates) u γ)
    (hinit : oneSiteEnergy u < (1/10000 : ℝ)) :
    ∀ t : ℝ, 0 ≤ t →
      oneSiteEnergy (γ t) < (1/10000 : ℝ) := by
  apply energy_stays_below_of_deriv_nonpos_below
    (fun t => oneSiteEnergy (γ t))
    (fun t => oneSiteEnergySlope (oneSiteDisplacement (γ t)))
    (1/10000 : ℝ)
  · intro t ht
    exact oneSiteEnergy_hasDerivWithinAt_forward u γ hγ t ht
  · intro t ht hsmall
    exact oneSiteEnergy_slope_nonpos_of_energy_lt (γ t) hsmall
  · simpa [hγ.1] using hinit

end
end PhosphorylationStableCapacity
