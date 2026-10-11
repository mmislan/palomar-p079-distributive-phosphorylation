module
public import proofs.PhosphorylationStableCapacity.OneSiteEnergySublevel

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- Every forward solution of the literal unit-rate one-site class
field starting in the small rational energy sublevel has an explicit
global exponential energy bound. -/
theorem oneSiteEnergy_exponential_decay
    (u : CoordinateSpace 1)
    (γ : ℝ → CoordinateSpace 1)
    (hγ : IsForwardClassCurve
      (restrictedFieldEuclid (3/2) (3/2) 3 oneRates) u γ)
    (hinit : oneSiteEnergy u < (1/10000 : ℝ)) :
    ∀ T : ℝ, 0 ≤ T →
      oneSiteEnergy (γ T) ≤
        oneSiteEnergy u * Real.exp (-(1/6 : ℝ) * T) := by
  have hsmall := oneSiteEnergy_sublevel_forward_invariant u γ hγ hinit
  intro T hT
  have hcont : ContinuousOn (fun t => oneSiteEnergy (γ t))
      (Set.Icc (0 : ℝ) T) := by
    intro t ht
    exact ((oneSiteEnergy_hasDerivWithinAt_forward
      u γ hγ t ht.1).continuousWithinAt).mono
        (by intro s hs; exact hs.1)
  have hbound := scalar_energy_decay_on_Icc
    (fun t => oneSiteEnergy (γ t))
    (fun t => oneSiteEnergySlope (oneSiteDisplacement (γ t)))
    (1/6 : ℝ) T hcont
    (by
      intro t ht
      exact (oneSiteEnergy_hasDerivWithinAt_forward
        u γ hγ t ht.1).mono
          (Set.Ici_subset_Ici.mpr ht.1))
    (by
      intro t ht
      simpa [div_eq_mul_inv, mul_comm] using
        oneSiteEnergy_slope_le_neg_sixth
          (γ t) (hsmall t ht.1))
  simpa [hγ.1] using hbound T ⟨hT, le_refl T⟩

end
end PhosphorylationStableCapacity
