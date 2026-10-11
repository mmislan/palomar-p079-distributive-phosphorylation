module
public import proofs.PhosphorylationStableCapacity.EdgeScaledDeterminantPreparation

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Matrix

noncomputable section

/-- At a positive literal state, these three rate variations prescribe the
kinase-complex velocity, phosphatase-complex velocity, and catalytic current
independently. The other three rate variations are zero. -/
def rateVariation {n : ℕ} (x : State n)
    (p q r : Fin n → ℝ) : Rates n where
  a i := (p i + r i) / (x.S i.castSucc * x.E)
  b _ := 0
  c i := r i / x.C i
  alpha i := q i / (x.S i.succ * x.F)
  beta _ := 0
  gamma _ := 0

theorem rateVariation_current {n : ℕ} (x : State n)
    (hx : x.Positive) (p q r : Fin n → ℝ) (i : Fin n) :
    catalyticCurrent (rateVariation x p q r) x i = r i := by
  rcases hx with ⟨_, _, _, hC, _⟩
  have h : x.C i ≠ 0 := ne_of_gt (hC i)
  simp [catalyticCurrent, rateVariation, h]

theorem rateVariation_C {n : ℕ} (x : State n)
    (hx : x.Positive) (p q r : Fin n → ℝ) (i : Fin n) :
    (field (rateVariation x p q r) x).C i = p i := by
  rcases hx with ⟨hS, hE, _, hC, _⟩
  have hSE : x.S i.castSucc * x.E ≠ 0 :=
    mul_ne_zero (ne_of_gt (hS _)) (ne_of_gt hE)
  have hCi : x.C i ≠ 0 := ne_of_gt (hC i)
  simp only [field, kinaseNet, rateVariation, zero_mul, sub_zero]
  rw [div_mul_cancel₀ _ hCi]
  calc
    (p i + r i) / (x.S i.castSucc * x.E) * x.S i.castSucc * x.E - r i =
        (p i + r i) / (x.S i.castSucc * x.E) *
          (x.S i.castSucc * x.E) - r i := by ring
    _ = p i := by rw [div_mul_cancel₀ _ hSE]; ring

theorem rateVariation_D {n : ℕ} (x : State n)
    (hx : x.Positive) (p q r : Fin n → ℝ) (i : Fin n) :
    (field (rateVariation x p q r) x).D i = q i := by
  rcases hx with ⟨hS, _, hF, _, _⟩
  have hSF : x.S i.succ * x.F ≠ 0 :=
    mul_ne_zero (ne_of_gt (hS _)) (ne_of_gt hF)
  simp only [field, phosphataseNet, rateVariation, zero_mul, sub_zero]
  calc
    q i / (x.S i.succ * x.F) * x.S i.succ * x.F =
        q i / (x.S i.succ * x.F) * (x.S i.succ * x.F) := by ring
    _ = q i := div_mul_cancel₀ _ hSF

/-- The literal rate directions span every component of the field in loaded
class coordinates at each positive state. -/
theorem loadedRestrictedField_rate_surjective {n : ℕ}
    (ET FT ST : ℝ) (u : CoordinateSpace n)
    (hx : (stateFromLoaded ET FT ST u).Positive) :
    Function.Surjective
      (fun k : Rates n => loadedRestrictedField ET FT ST k u) := by
  intro y
  obtain ⟨r, hr⟩ :=
    (Matrix.mulVec_surjective_iff_isUnit.mpr
      (projectedPathIncidence_isUnit n)) y.1
  let x := stateFromLoaded ET FT ST u
  let k := rateVariation x y.2.1 y.2.2 r
  refine ⟨k, ?_⟩
  apply Prod.ext
  · rw [loadedRestrictedField_slow_eq_incidence]
    have hc : catalyticCurrent k x = r := by
      funext i
      exact rateVariation_current x hx y.2.1 y.2.2 r i
    rw [show catalyticCurrent k (stateFromLoaded ET FT ST u) = r from hc]
    exact hr
  · apply Prod.ext
    · funext i
      simpa [loadedRestrictedField, restrictedFieldEuclid,
        restrictedField, chart, toLoadedCoord, toCoordinateSpace,
        stateFromLoaded, x, k] using
        rateVariation_C x hx y.2.1 y.2.2 r i
    · funext i
      simpa [loadedRestrictedField, restrictedFieldEuclid,
        restrictedField, chart, toLoadedCoord, toCoordinateSpace,
        stateFromLoaded, x, k] using
        rateVariation_D x hx y.2.1 y.2.2 r i

/-- The same spanning statement in the original `3n` compatibility-class
chart, rather than its loaded-coordinate conjugate. -/
theorem restrictedFieldEuclid_rate_surjective {n : ℕ}
    (ET FT ST : ℝ) (u : CoordinateSpace n)
    (hx : (unChart ET FT ST (ofCoordinateSpace u)).Positive) :
    Function.Surjective
      (fun k : Rates n => restrictedFieldEuclid ET FT ST k u) := by
  have hloaded :
      (stateFromLoaded ET FT ST (toLoadedCoord u)).Positive := by
    simpa [stateFromLoaded, from_toLoadedCoord] using hx
  intro y
  obtain ⟨k, hk⟩ := loadedRestrictedField_rate_surjective
    ET FT ST (toLoadedCoord u) hloaded (toLoadedCoord y)
  refine ⟨k, ?_⟩
  change toLoadedCoord (restrictedFieldEuclid ET FT ST k
    (fromLoadedCoord (toLoadedCoord u))) = toLoadedCoord y at hk
  rw [from_toLoadedCoord] at hk
  have := congrArg fromLoadedCoord hk
  simpa only [from_toLoadedCoord] using this

end
end PhosphorylationStableCapacity
