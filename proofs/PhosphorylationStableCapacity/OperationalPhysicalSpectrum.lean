module
public import proofs.PhosphorylationStableCapacity.OperationalCertifiedModel
public import proofs.PhosphorylationStableCapacity.OperationalSinkOutcome
public import proofs.PhosphorylationStableCapacity.UniformDissipationHurwitz
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open Matrix PhosphorylationSharpness Polynomial
open scoped BigOperators

/-- The operational coordinate readout is a linear equivalence when every
scale factor is nonzero. Its inverse is the weighted coordinate lift. -/
def operationalCoordinateEquiv (s : Fin 9 → ℝ)
    (hs : ∀ i, s i ≠ 0) : CoordinateSpace 3 ≃ₗ[ℝ] (Fin 9 → ℝ) :=
  LinearEquiv.ofBijective (operationalRead s).toLinearMap
    ⟨operationalRead_injective s hs,
      fun v => ⟨operationalLift s v, operationalRead_lift s hs v⟩⟩

theorem operationalCoordinateEquiv_symm_apply (s : Fin 9 → ℝ)
    (hs : ∀ i, s i ≠ 0) (v : Fin 9 → ℝ) :
    (operationalCoordinateEquiv s hs).symm v = operationalLift s v := by
  apply (operationalCoordinateEquiv s hs).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (operationalRead_lift s hs v).symm

/-- The actual reaction Jacobian in weighted operational coordinates is
conjugate to the literal class-restricted Fréchet derivative. -/
theorem operationalReactionJacobian_charpoly_eq_restricted
    (q s : Fin 9 → ℚ) (hs : ∀ i, (s i : ℝ) ≠ 0)
    (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) :
    (operationalReactionJacobian q s θ w).charpoly =
      (restrictedJacobianMatrix (θ 18) (θ 19) (θ 20)
        (operationalParameterRates θ)
        (operationalUnpack (fun i => (q i : ℝ)) +
          operationalLift (fun i => (s i : ℝ)) w)).charpoly := by
  let sr : Fin 9 → ℝ := fun i => (s i : ℝ)
  let qr : Fin 9 → ℝ := fun i => (q i : ℝ)
  let u : CoordinateSpace 3 := operationalUnpack qr + operationalLift sr w
  let J : Module.End ℝ (CoordinateSpace 3) :=
    (restrictedJacobian (θ 18) (θ 19) (θ 20)
      (operationalParameterRates θ) u).toLinearMap
  let e := operationalCoordinateEquiv sr hs
  have hmat : (operationalReactionJacobian q s θ w).toLin' =
      (operationalWeightedJacobian qr sr θ w).toLinearMap := by
    apply LinearMap.ext
    intro v
    simpa only [Matrix.toLin'_apply, ContinuousLinearMap.coe_coe, qr, sr] using
      (operationalReactionJacobian_action q s θ w v).symm
  have hconj : (operationalWeightedJacobian qr sr θ w).toLinearMap =
      e.conj J := by
    apply LinearMap.ext
    intro v
    change operationalRead sr
        (restrictedJacobian (θ 18) (θ 19) (θ 20)
          (operationalParameterRates θ) u (operationalLift sr v)) =
      e (J (e.symm v))
    rw [operationalCoordinateEquiv_symm_apply sr hs]
    rfl
  calc
    (operationalReactionJacobian q s θ w).charpoly =
        (operationalReactionJacobian q s θ w).toLin'.charpoly :=
          (Matrix.charpoly_toLin' _).symm
    _ = (e.conj J).charpoly := by rw [hmat, hconj]
    _ = J.charpoly := e.charpoly_conj J
    _ = (restrictedJacobianMatrix (θ 18) (θ 19) (θ 20)
          (operationalParameterRates θ) u).charpoly := by
            simpa only [J, restrictedJacobianMatrix] using
              (LinearMap.charpoly_toMatrix J (coordinateBasis 3)).symm

/-- The same certified equilibrium and parameter vector used for quantitative
recovery have a Hurwitz Jacobian throughout the interval certificate. -/
theorem OperationalPrintedSinkOutcome.weighted_hurwitz
    {q s : Fin 9 → ℚ} {nominal : Fin 21 → ℚ} {θ : Fin 21 → ℝ}
    {P : Matrix (Fin 9) (Fin 9) ℝ}
    {ρ ρin p c M recoveryTime lower upper loss : ℝ}
    {equilibrium : Fin 9 → ℝ}
    (h : OperationalPrintedSinkOutcome q s nominal θ P ρ ρin p c M
      recoveryTime lower upper loss equilibrium) :
    ∀ z : ℂ,
      (((operationalReactionJacobian q s θ equilibrium).map
        (algebraMap ℝ ℂ)).charpoly).eval z = 0 → z.re < 0 := by
  obtain ⟨Q, Qinv, hnominal, hout⟩ := h
  have hbound : ‖equilibrium‖ ≤ ρ := by
    have hρ : 0 ≤ ρ := by
      have hnorm := norm_nonneg equilibrium
      linarith [hout.shift]
    linarith [hout.shift]
  apply hurwitz_of_uniform_quadratic_dissipation
    (operationalReactionJacobian q s θ equilibrium)
    P hout.positive_definite c hout.decay_positive
  intro v
  rw [← operationalReactionJacobian_action]
  exact hout.actual_uniform_dissipation equilibrium hbound v

/-- The operational certificate therefore proves sink hyperbolicity for the
literal restricted class Jacobian on those very same physical witnesses. -/
theorem OperationalPrintedSinkOutcome.restricted_hurwitz
    {q s : Fin 9 → ℚ} {nominal : Fin 21 → ℚ} {θ : Fin 21 → ℝ}
    {P : Matrix (Fin 9) (Fin 9) ℝ}
    {ρ ρin p c M recoveryTime lower upper loss : ℝ}
    {equilibrium : Fin 9 → ℝ}
    (h : OperationalPrintedSinkOutcome q s nominal θ P ρ ρin p c M
      recoveryTime lower upper loss equilibrium)
    (hs : ∀ i, (s i : ℝ) ≠ 0) :
    IsHurwitz (restrictedJacobianMatrix (θ 18) (θ 19) (θ 20)
      (operationalParameterRates θ)
      (operationalUnpack (fun i => (q i : ℝ)) +
        operationalLift (fun i => (s i : ℝ)) equilibrium)) := by
  intro z hz
  have hpoly := operationalReactionJacobian_charpoly_eq_restricted
    q s hs θ equilibrium
  have hpolyC := congrArg
    (fun p : ℝ[X] => p.map (algebraMap ℝ ℂ)) hpoly
  simp only [← Matrix.charpoly_map] at hpolyC
  rw [← hpolyC] at hz
  exact h.weighted_hurwitz z hz

/-- Differentiating the exact ten-second unit conversion identifies the
physical weighted Jacobian at every point, including the shifted certified
equilibrium, with one tenth of the model-time Jacobian. -/
theorem operational_physical_weighted_jacobian
    (q s : Fin 9 → ℝ) (hs : ∀ i, s i ≠ 0)
    (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) :
    operationalWeightedJacobian (fun i => q i / 10) (fun i => s i / 10)
      (operationalPhysicalParameters θ) w =
        (1 / 10 : ℝ) • operationalWeightedJacobian q s θ w := by
  have hfun : operationalWeightedField (fun i => q i / 10) (fun i => s i / 10)
      (operationalPhysicalParameters θ) =
      (fun v => (1 / 10 : ℝ) • operationalWeightedField q s θ v) := by
    funext v
    exact operational_physical_weighted_field q s hs θ v
  have hcalc := (operationalWeightedField_hasFDerivAt q s θ w).const_smul (1 / 10 : ℝ)
  change HasFDerivAt (fun v => (1 / 10 : ℝ) • operationalWeightedField q s θ v)
    ((1 / 10 : ℝ) • operationalWeightedJacobian q s θ w) w at hcalc
  rw [← hfun] at hcalc
  exact (operationalWeightedField_hasFDerivAt
    (fun i => q i / 10) (fun i => s i / 10)
    (operationalPhysicalParameters θ) w).unique hcalc

/-- The paper's converted physical rates, totals, and concentrations retain
sink hyperbolicity on the very same certified shifted equilibrium. -/
theorem OperationalPrintedSinkOutcome.physical_restricted_hurwitz
    {q s : Fin 9 → ℚ} {nominal : Fin 21 → ℚ} {θ : Fin 21 → ℝ}
    {P : Matrix (Fin 9) (Fin 9) ℝ}
    {ρ ρin p c M recoveryTime lower upper loss : ℝ}
    {equilibrium : Fin 9 → ℝ}
    (h : OperationalPrintedSinkOutcome q s nominal θ P ρ ρin p c M
      recoveryTime lower upper loss equilibrium)
    (hs : ∀ i, (s i : ℝ) ≠ 0) :
    IsHurwitz (restrictedJacobianMatrix
      (operationalPhysicalParameters θ 18)
      (operationalPhysicalParameters θ 19)
      (operationalPhysicalParameters θ 20)
      (operationalParameterRates (operationalPhysicalParameters θ))
      (operationalUnpack (fun i => ((q i / 10 : ℚ) : ℝ)) +
        operationalLift (fun i => ((s i / 10 : ℚ) : ℝ)) equilibrium)) := by
  obtain ⟨Q, Qinv, hnominal, hout⟩ := h
  let qreal : Fin 9 → ℝ := fun i => (q i : ℝ)
  let sreal : Fin 9 → ℝ := fun i => (s i : ℝ)
  have hsphys : ∀ i, ((s i / 10 : ℚ) : ℝ) ≠ 0 := by
    intro i
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (div_ne_zero (hs i) (by norm_num : (10 : ℝ) ≠ 0))
  have hbound : ‖equilibrium‖ ≤ ρ := by
    have hρ : 0 ≤ ρ := by
      have hnorm := norm_nonneg equilibrium
      linarith [hout.shift]
    linarith [hout.shift]
  have hmodel : ∀ v : Fin 9 → ℝ,
      2 * (v ⬝ᵥ (P *ᵥ
        (operationalWeightedJacobian qreal sreal θ equilibrium v))) ≤
        -c * (∑ i, v i ^ 2) :=
    hout.actual_uniform_dissipation equilibrium hbound
  have hphysical : ∀ v : Fin 9 → ℝ,
      2 * (v ⬝ᵥ (P *ᵥ
        (operationalReactionJacobian
          (fun i => q i / 10) (fun i => s i / 10)
          (operationalPhysicalParameters θ) equilibrium *ᵥ v))) ≤
        -(c / 10) * (∑ i, v i ^ 2) := by
    intro v
    have hsource := hmodel v
    have hscale := operational_physical_weighted_jacobian
      qreal sreal hs θ equilibrium
    have hcastq : (fun i => ((q i / 10 : ℚ) : ℝ)) =
        (fun i => qreal i / 10) := by
      funext i
      simp only [qreal, Rat.cast_div, Rat.cast_ofNat]
    have hcasts : (fun i => ((s i / 10 : ℚ) : ℝ)) =
        (fun i => sreal i / 10) := by
      funext i
      simp only [sreal, Rat.cast_div, Rat.cast_ofNat]
    rw [← operationalReactionJacobian_action, hcastq, hcasts, hscale]
    simp only [_root_.smul_apply, Matrix.mulVec_smul,
      dotProduct_smul, smul_eq_mul]
    nlinarith
  have hweighted := hurwitz_of_uniform_quadratic_dissipation
    (operationalReactionJacobian (fun i => q i / 10) (fun i => s i / 10)
      (operationalPhysicalParameters θ) equilibrium)
    P hout.positive_definite (c / 10)
    (div_pos hout.decay_positive (by norm_num)) hphysical
  intro z hz
  have hpoly := operationalReactionJacobian_charpoly_eq_restricted
    (fun i => q i / 10) (fun i => s i / 10) hsphys
    (operationalPhysicalParameters θ) equilibrium
  have hpolyC := congrArg
    (fun p : ℝ[X] => p.map (algebraMap ℝ ℂ)) hpoly
  simp only [← Matrix.charpoly_map] at hpolyC
  rw [← hpolyC] at hz
  exact hweighted z hz

end
end PhosphorylationStableCapacity
