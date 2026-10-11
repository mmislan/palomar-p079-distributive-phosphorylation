module
public import proofs.PhosphorylationStableCapacity.AttainmentGeometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- A symmetric one-site kinetic system with all six rates equal to one. -/
def oneRates : Rates 1 where
  a _ := 1
  b _ := 1
  c _ := 1
  alpha _ := 1
  beta _ := 1
  gamma _ := 1

def oneCoord : CoordinateSpace 1 :=
  (fun _ => 1, fun _ => 1/2, fun _ => 1/2)

def oneState : State 1 where
  S _ := 1
  E := 1
  F := 1
  C _ := 1/2
  D _ := 1/2

theorem oneRates_positive : oneRates.Positive := by
  intro i
  simp [oneRates]

theorem oneState_positive : oneState.Positive := by
  simp [State.Positive, oneState]

theorem oneState_inClass : InClass (3/2) (3/2) 3 oneState := by
  unfold InClass totalE totalF totalS oneState
  simp
  norm_num

theorem oneState_eq_unChart :
    unChart (3/2) (3/2) 3 (ofCoordinateSpace oneCoord) = oneState := by
  have hchart : chart oneState = ofCoordinateSpace oneCoord := by
    rfl
  rw [← hchart]
  exact unChart_chart_of_inClass (3/2) (3/2) 3 oneState oneState_inClass

theorem oneState_equilibrium : Equilibrium oneRates oneState := by
  apply equilibrium_of_currents
  · intro i
    fin_cases i
    norm_num [kinaseNet, oneRates, oneState]
  · intro i
    fin_cases i
    norm_num [phosphataseNet, oneRates, oneState]
  · intro i
    fin_cases i
    norm_num [oneRates, oneState]

theorem oneCoord_equilibrium :
    restrictedFieldEuclid (3/2) (3/2) 3 oneRates oneCoord = 0 := by
  apply (restrictedFieldEuclid_eq_zero_iff (3/2) (3/2) 3 oneRates oneCoord).2
  rw [oneState_eq_unChart]
  exact oneState_equilibrium

/-- The one-site restricted polynomial in the chart order `S₁,C₀,D₀`. -/
def oneField (u : CoordinateSpace 1) : CoordinateSpace 1 :=
  (fun _ => u.2.1 0 - u.1 0 * (3/2 - u.2.2 0) + u.2.2 0,
   fun _ => (3 - u.1 0 - u.2.1 0 - u.2.2 0) * (3/2 - u.2.1 0)
     - 2 * u.2.1 0,
   fun _ => u.1 0 * (3/2 - u.2.2 0) - 2 * u.2.2 0)

theorem restrictedFieldEuclid_one (u : CoordinateSpace 1) :
    restrictedFieldEuclid (3/2) (3/2) 3 oneRates u = oneField u := by
  ext i <;> fin_cases i <;>
    simp [restrictedFieldEuclid, restrictedField, chart, field, unChart,
      ofCoordinateSpace, toCoordinateSpace, oneRates, oneField,
      kinaseNet, phosphataseNet] <;> ring

private abbrev OnePi := Fin 1 → ℝ

private def pS : CoordinateSpace 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (0 : Fin 1)).comp
    (ContinuousLinearMap.fst ℝ OnePi (OnePi × OnePi))

private def pC : CoordinateSpace 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (0 : Fin 1)).comp
    ((ContinuousLinearMap.fst ℝ OnePi OnePi).comp
      (ContinuousLinearMap.snd ℝ OnePi (OnePi × OnePi)))

private def pD : CoordinateSpace 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (0 : Fin 1)).comp
    ((ContinuousLinearMap.snd ℝ OnePi OnePi).comp
      (ContinuousLinearMap.snd ℝ OnePi (OnePi × OnePi)))

@[simp] private theorem pS_apply (u : CoordinateSpace 1) : pS u = u.1 0 := rfl
@[simp] private theorem pC_apply (u : CoordinateSpace 1) : pC u = u.2.1 0 := rfl
@[simp] private theorem pD_apply (u : CoordinateSpace 1) : pD u = u.2.2 0 := rfl

private def oneJacobianCLM : CoordinateSpace 1 →L[ℝ] CoordinateSpace 1 :=
  (ContinuousLinearMap.pi fun _ : Fin 1 => -pS + pC + 2 • pD).prod
    ((ContinuousLinearMap.pi fun _ : Fin 1 => -pS - 4 • pC - pD).prod
      (ContinuousLinearMap.pi fun _ : Fin 1 => pS - 3 • pD))

private theorem oneField_hasFDerivAt :
    HasFDerivAt oneField oneJacobianCLM oneCoord := by
  have hs : HasFDerivAt (fun u : CoordinateSpace 1 => u.1 0) pS oneCoord :=
    pS.hasFDerivAt
  have hc : HasFDerivAt (fun u : CoordinateSpace 1 => u.2.1 0) pC oneCoord :=
    pC.hasFDerivAt
  have hd : HasFDerivAt (fun u : CoordinateSpace 1 => u.2.2 0) pD oneCoord :=
    pD.hasFDerivAt
  have ha : HasFDerivAt
      (fun u : CoordinateSpace 1 =>
        u.2.1 0 - u.1 0 * (3/2 - u.2.2 0) + u.2.2 0)
      (-pS + pC + 2 • pD) oneCoord := by
    convert ((hc.sub (hs.mul (hd.const_sub (3/2)))).add hd) using 1
    apply ContinuousLinearMap.ext
    intro v
    simp [oneCoord]
    ring
  have hb : HasFDerivAt
      (fun u : CoordinateSpace 1 =>
        (3 - u.1 0 - u.2.1 0 - u.2.2 0) * (3/2 - u.2.1 0)
          - 2 * u.2.1 0)
      (-pS - 4 • pC - pD) oneCoord := by
    convert (((((hs.const_sub 3).sub hc).sub hd).mul
      (hc.const_sub (3/2))).sub (hc.const_mul 2)) using 1
    apply ContinuousLinearMap.ext
    intro v
    simp [oneCoord]
    ring
  have hd' : HasFDerivAt
      (fun u : CoordinateSpace 1 =>
        u.1 0 * (3/2 - u.2.2 0) - 2 * u.2.2 0)
      (pS - 3 • pD) oneCoord := by
    convert ((hs.mul (hd.const_sub (3/2))).sub (hd.const_mul 2)) using 1
    apply ContinuousLinearMap.ext
    intro v
    simp [oneCoord]
    ring
  have ha' : HasFDerivAt
      (fun u : CoordinateSpace 1 => fun _ : Fin 1 =>
        u.2.1 0 - u.1 0 * (3/2 - u.2.2 0) + u.2.2 0)
      (ContinuousLinearMap.pi fun _ : Fin 1 => -pS + pC + 2 • pD)
      oneCoord := by
    apply hasFDerivAt_pi'.2
    intro i
    exact ha
  have hb' : HasFDerivAt
      (fun u : CoordinateSpace 1 => fun _ : Fin 1 =>
        (3 - u.1 0 - u.2.1 0 - u.2.2 0) * (3/2 - u.2.1 0)
          - 2 * u.2.1 0)
      (ContinuousLinearMap.pi fun _ : Fin 1 => -pS - 4 • pC - pD)
      oneCoord := by
    apply hasFDerivAt_pi'.2
    intro i
    exact hb
  have hd'' : HasFDerivAt
      (fun u : CoordinateSpace 1 => fun _ : Fin 1 =>
        u.1 0 * (3/2 - u.2.2 0) - 2 * u.2.2 0)
      (ContinuousLinearMap.pi fun _ : Fin 1 => pS - 3 • pD)
      oneCoord := by
    apply hasFDerivAt_pi'.2
    intro i
    exact hd'
  exact ha'.prodMk (hb'.prodMk hd'')

theorem oneJacobian_eq :
    restrictedJacobian (3/2) (3/2) 3 oneRates oneCoord = oneJacobianCLM := by
  have hfield : restrictedFieldEuclid (3/2) (3/2) 3 oneRates = oneField :=
    funext restrictedFieldEuclid_one
  simp only [restrictedJacobian, hfield]
  exact oneField_hasFDerivAt.fderiv

def oneIndexEquiv : (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) ≃ Fin 3 :=
  { toFun := fun i => match i with
      | .inl _ => 0
      | .inr (.inl _) => 1
      | .inr (.inr _) => 2
    invFun := fun i => if i = 0 then .inl 0 else
      if i = 1 then .inr (.inl 0) else .inr (.inr 0)
    left_inv := by
      intro i
      rcases i with i | i
      · fin_cases i
        simp
      · rcases i with i | i <;> fin_cases i <;> simp
    right_inv := by
      intro i
      fin_cases i <;> simp }

def oneMatrixFin : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.reindex oneIndexEquiv oneIndexEquiv
    (restrictedJacobianMatrix (3/2) (3/2) 3 oneRates oneCoord)

theorem oneMatrixFin_eq : oneMatrixFin =
    !![-1, 1, 2; -1, -4, -1; 1, 0, -3] := by
  rw [oneMatrixFin, restrictedJacobianMatrix, oneJacobian_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.reindex, oneIndexEquiv, coordinateBasis,
      oneJacobianCLM, pS, pC, pD, LinearMap.toMatrix_apply]

theorem oneMatrixFin_charpoly_eval (z : ℂ) :
    ((oneMatrixFin.map (algebraMap ℝ ℂ)).charpoly).eval z =
      z^3 + 8*z^2 + 18*z + 8 := by
  rw [Matrix.eval_charpoly, oneMatrixFin_eq]
  simp [Matrix.det_fin_three, Matrix.scalar, Matrix.diagonal]
  ring

theorem oneMatrixFin_hurwitz : IsHurwitz oneMatrixFin := by
  intro z hz
  rw [oneMatrixFin_charpoly_eval] at hz
  let r : ℝ := Real.sqrt 2
  have hr2 : r^2 = (2 : ℝ) := by
    dsimp [r]
    norm_num
  have hrnonneg : 0 ≤ r := Real.sqrt_nonneg 2
  have hrlt : r < 2 := by nlinarith
  have hr2c : (r : ℂ)^2 = 2 := by exact_mod_cast hr2
  have hfactor : z^3 + 8*z^2 + 18*z + 8 =
      (z+4)*(z+2-(r:ℂ))*(z+2+(r:ℂ)) := by
    calc
      z^3 + 8*z^2 + 18*z + 8 = (z+4)*((z+2)^2-2) := by ring
      _ = (z+4)*(z+2-(r:ℂ))*(z+2+(r:ℂ)) := by
        rw [← hr2c]
        ring
  rw [hfactor] at hz
  rcases mul_eq_zero.mp hz with h | h
  · rcases mul_eq_zero.mp h with h | h
    · have hz' : z = -4 := by linear_combination h
      simp [hz']
    · have hz' : z = (r:ℂ)-2 := by linear_combination h
      have hneg : r-2 < 0 := sub_lt_zero.mpr hrlt
      simpa [hz'] using hneg
  · have hz' : z = -2-(r:ℂ) := by linear_combination h
    have hneg : -2-r < 0 := by linarith
    simpa [hz'] using hneg

theorem oneCoord_linearly_stable :
    IsLinearlyStable (3/2) (3/2) 3 oneRates oneCoord := by
  intro z hz
  have h' : ((oneMatrixFin.map (algebraMap ℝ ℂ)).charpoly).eval z = 0 := by
    change ((Matrix.reindex oneIndexEquiv oneIndexEquiv
      ((restrictedJacobianMatrix (3/2) (3/2) 3 oneRates oneCoord).map
        (algebraMap ℝ ℂ))).charpoly).eval z = 0
    rw [Matrix.charpoly_reindex]
    exact hz
  exact oneMatrixFin_hurwitz z h'

/-- The full one-site Hurwitz attainment claim, for the literal positive model. -/
theorem one_site_linearly_stable_attainment : LinearlyStableClassAttains 1 1 := by
  refine ⟨oneRates, 3/2, 3/2, 3, (fun _ => oneCoord), oneRates_positive,
    by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · intro i j _
    exact Subsingleton.elim i j
  · intro j
    refine ⟨?_, oneCoord_equilibrium, oneCoord_linearly_stable⟩
    rw [oneState_eq_unChart]
    exact oneState_positive

end
end PhosphorylationStableCapacity
