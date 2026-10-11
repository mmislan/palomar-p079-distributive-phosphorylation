module
public import proofs.PhosphorylationStableCapacity.EnergySublevelBarrier
public import proofs.PhosphorylationStableCapacity.ExponentialAttractionCriterion

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Filter
open scoped Topology

noncomputable section

/-- A local quadratic energy certificate yields the exact nonlinear
stability predicate for any class-coordinate field. The assumptions
refer to every forward curve, so no uniqueness is needed here. -/
theorem locally_asymptotically_stable_of_quadratic_energy {n : ℕ}
    (f : CoordinateSpace n → CoordinateSpace n)
    (x : CoordinateSpace n) (heq : f x = 0)
    (V : CoordinateSpace n → ℝ)
    (slope : CoordinateSpace n → ℝ)
    (a b C α L δ₀ : ℝ)
    (ha : 0 < a) (hC : 0 ≤ C)
    (hα : 0 < α) (hδ₀ : 0 < δ₀)
    (hratio : b ≤ a * C^2)
    (hlower : ∀ u, a * (dist u x)^2 ≤ V u)
    (hupper : ∀ u, V u ≤ b * (dist u x)^2)
    (hsmall : ∀ u, dist u x < δ₀ → V u < L)
    (hderiv : ∀ (u : CoordinateSpace n)
      (γ : ℝ → CoordinateSpace n), IsForwardClassCurve f u γ →
        ∀ t : ℝ, 0 ≤ t →
          HasDerivWithinAt (fun r => V (γ r))
            (slope (γ t)) (Set.Ici (0 : ℝ)) t)
    (hslope : ∀ u, V u < L → slope u ≤ -α * V u)
    (hexist : ∀ u, dist u x < δ₀ →
      ∃ γ : ℝ → CoordinateSpace n, IsForwardClassCurve f u γ) :
    IsLocallyAsymptoticallyStableClassField f x := by
  apply locally_asymptotically_stable_of_exponential_bound
    f x heq C (α/2) δ₀ hC (by linarith) hδ₀
  · intro u hu γ hγ T hT
    let g : ℝ → ℝ := fun t => V (γ t)
    let g' : ℝ → ℝ := fun t => slope (γ t)
    have hstay : ∀ t : ℝ, 0 ≤ t → g t < L := by
      apply energy_stays_below_of_deriv_nonpos_below g g' L
      · intro t ht
        exact hderiv u γ hγ t ht
      · intro t ht hlt
        have hVnonneg : 0 ≤ g t := by
          have h := hlower (γ t)
          nlinarith [sq_nonneg (dist (γ t) x)]
        have hs := hslope (γ t) hlt
        dsimp [g, g'] at *
        nlinarith
      · simpa [g, hγ.1] using hsmall u hu
    have hcont : ContinuousOn g (Set.Icc (0 : ℝ) T) := by
      intro t ht
      exact ((hderiv u γ hγ t ht.1).continuousWithinAt).mono
        (by intro s hs; exact hs.1)
    have henergy := scalar_energy_decay_on_Icc g g' α T hcont
      (by
        intro t ht
        exact (hderiv u γ hγ t ht.1).mono
          (Set.Ici_subset_Ici.mpr ht.1))
      (by intro t ht; exact hslope (γ t) (hstay t ht.1))
      T ⟨hT, le_refl T⟩
    have henergy' : V (γ T) ≤ V u * Real.exp (-α * T) := by
      simpa [g, hγ.1] using henergy
    let e := Real.exp (-(α/2) * T)
    have he : 0 ≤ e := (Real.exp_pos _).le
    have hexp : Real.exp (-α * T) = e^2 := by
      dsimp [e]
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have hmetric : a * (dist (γ T) x)^2 ≤
        b * (dist u x)^2 * e^2 := by
      rw [hexp] at henergy'
      have hm := mul_le_mul_of_nonneg_right (hupper u) (sq_nonneg e)
      exact (hlower (γ T)).trans (henergy'.trans hm)
    have hratio' : b * (dist u x)^2 * e^2 ≤
        a * C^2 * (dist u x)^2 * e^2 := by
      gcongr
    have hsq : (dist (γ T) x)^2 ≤
        (C * e * dist u x)^2 := by
      have h := hmetric.trans hratio'
      nlinarith
    have hdist := (sq_le_sq₀ dist_nonneg (by positivity)).mp hsq
    simpa [e, div_mul_eq_mul_div, mul_assoc, mul_comm, mul_left_comm] using hdist
  · exact hexist

end
end PhosphorylationStableCapacity
