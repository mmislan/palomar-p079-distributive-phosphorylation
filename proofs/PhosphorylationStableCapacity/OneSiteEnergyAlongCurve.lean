module
public import proofs.PhosphorylationStableCapacity.OneSiteLocalEnergyInequality
public import proofs.PhosphorylationStableCapacity.ClassForwardUniqueness

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness
open scoped Matrix

noncomputable section

def oneSiteEnergyPoly (a b c : ℝ) : ℝ :=
  (13/16)*a^2 + (5/17)*a*b + (125/136)*a*c +
    (11/68)*b^2 + (23/136)*b*c + (121/272)*c^2

def oneSiteEnergyDirectional
    (a b c da db dc : ℝ) : ℝ :=
  (13/8)*a*da + (5/17)*(da*b+a*db) +
    (125/136)*(da*c+a*dc) + (11/34)*b*db +
    (23/136)*(db*c+b*dc) + (121/136)*c*dc

theorem oneSiteEnergyPoly_eq_matrix (a b c : ℝ) :
    oneSiteEnergyPoly a b c =
      star ![a,b,c] ⬝ᵥ (oneSiteP *ᵥ ![a,b,c]) := by
  simp [oneSiteEnergyPoly, oneSiteP, dotProduct,
    Matrix.mulVec, Fin.sum_univ_succ]
  ring

theorem oneSiteEnergyDirectional_eq_matrix
    (a b c da db dc : ℝ) :
    oneSiteEnergyDirectional a b c da db dc =
      2 * (star ![a,b,c] ⬝ᵥ
        (oneSiteP *ᵥ ![da,db,dc])) := by
  simp [oneSiteEnergyDirectional, oneSiteP, dotProduct,
    Matrix.mulVec, Fin.sum_univ_succ]
  ring

theorem oneSiteEnergyPoly_hasDerivWithinAt
    (a b c : ℝ → ℝ) (da db dc : ℝ)
    (s : Set ℝ) (t : ℝ)
    (ha : HasDerivWithinAt a da s t)
    (hb : HasDerivWithinAt b db s t)
    (hc : HasDerivWithinAt c dc s t) :
    HasDerivWithinAt
      (fun r => oneSiteEnergyPoly (a r) (b r) (c r))
      (oneSiteEnergyDirectional (a t) (b t) (c t) da db dc)
      s t := by
  have h1 := (ha.mul ha).const_mul (13/16 : ℝ)
  have h2 := ((ha.mul hb).const_mul (5/17 : ℝ))
  have h3 := ((ha.mul hc).const_mul (125/136 : ℝ))
  have h4 := ((hb.mul hb).const_mul (11/68 : ℝ))
  have h5 := ((hb.mul hc).const_mul (23/136 : ℝ))
  have h6 := ((hc.mul hc).const_mul (121/272 : ℝ))
  convert (((((h1.add h2).add h3).add h4).add h5).add h6) using 1
  · funext r
    simp [oneSiteEnergyPoly, Pi.add_apply]
    ring
  · dsimp [oneSiteEnergyDirectional]
    ring

theorem oneSiteEnergyPoly_vector_hasDerivWithinAt
    (v : ℝ → Fin 3 → ℝ) (w : Fin 3 → ℝ)
    (s : Set ℝ) (t : ℝ)
    (hv : HasDerivWithinAt v w s t) :
    HasDerivWithinAt
      (fun r => oneSiteEnergyPoly (v r 0) (v r 1) (v r 2))
      (2 * (star (v t) ⬝ᵥ (oneSiteP *ᵥ w))) s t := by
  have h0 := (hasDerivWithinAt_pi.mp hv) 0
  have h1 := (hasDerivWithinAt_pi.mp hv) 1
  have h2 := (hasDerivWithinAt_pi.mp hv) 2
  have h := oneSiteEnergyPoly_hasDerivWithinAt
    (fun r => v r 0) (fun r => v r 1) (fun r => v r 2)
    (w 0) (w 1) (w 2) s t h0 h1 h2
  have hveta : v t = ![v t 0, v t 1, v t 2] := by
    ext i
    fin_cases i <;> rfl
  have hweta : w = ![w 0, w 1, w 2] := by
    ext i
    fin_cases i <;> rfl
  rw [hveta, hweta]
  exact (oneSiteEnergyDirectional_eq_matrix
    (v t 0) (v t 1) (v t 2) (w 0) (w 1) (w 2)) ▸ h

theorem oneSiteDisplacement_hasDerivWithinAt
    (γ : ℝ → CoordinateSpace 1)
    (w : CoordinateSpace 1) (s : Set ℝ) (t : ℝ)
    (hγ : HasDerivWithinAt γ w s t) :
    HasDerivWithinAt
      (fun r => oneSiteDisplacement (γ r))
      (oneSiteCoordinateVector w) s t := by
  have hS : HasDerivWithinAt (fun r => (γ r).1 0) (w.1 0) s t := by
    simpa using
      (hasDerivWithinAt_pi.mp
        (hγ.hasFDerivWithinAt.fst.hasDerivWithinAt)) 0
  have hC : HasDerivWithinAt (fun r => (γ r).2.1 0) (w.2.1 0) s t := by
    simpa using
      (hasDerivWithinAt_pi.mp
        (hγ.hasFDerivWithinAt.snd.fst.hasDerivWithinAt)) 0
  have hD : HasDerivWithinAt (fun r => (γ r).2.2 0) (w.2.2 0) s t := by
    simpa using
      (hasDerivWithinAt_pi.mp
        (hγ.hasFDerivWithinAt.snd.snd.hasDerivWithinAt)) 0
  apply hasDerivWithinAt_pi.mpr
  intro i
  fin_cases i
  · simpa [oneSiteDisplacement, oneSiteCoordinateVector] using
      hS.sub_const 1
  · simpa [oneSiteDisplacement, oneSiteCoordinateVector] using
      hC.sub_const (1/2 : ℝ)
  · simpa [oneSiteDisplacement, oneSiteCoordinateVector] using
      hD.sub_const (1/2 : ℝ)

def oneSiteEnergy (u : CoordinateSpace 1) : ℝ :=
  oneSiteEnergyPoly (oneSiteDisplacement u 0)
    (oneSiteDisplacement u 1) (oneSiteDisplacement u 2)

/-- Along every forward solution of the literal unit-rate one-site
class field, the derivative of the quadratic energy is exactly the
algebraic slope verified in `OneSiteLocalEnergyInequality`. -/
theorem oneSiteEnergy_hasDerivWithinAt_forward
    (u : CoordinateSpace 1)
    (γ : ℝ → CoordinateSpace 1)
    (hγ : IsForwardClassCurve
      (restrictedFieldEuclid (3/2) (3/2) 3 oneRates) u γ)
    (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
    HasDerivWithinAt
      (fun r => oneSiteEnergy (γ r))
      (oneSiteEnergySlope (oneSiteDisplacement (γ t)))
      (Set.Ici (0 : ℝ)) t := by
  have hdisp := oneSiteDisplacement_hasDerivWithinAt γ
    (restrictedFieldEuclid (3/2) (3/2) 3 oneRates (γ t))
    (Set.Ici (0 : ℝ)) t (hγ.2 t ht)
  rw [← oneSiteDisplacementField_eq_literal (γ t)] at hdisp
  have h := oneSiteEnergyPoly_vector_hasDerivWithinAt
    (fun r => oneSiteDisplacement (γ r))
    (oneSiteDisplacementField (oneSiteDisplacement (γ t)))
    (Set.Ici (0 : ℝ)) t hdisp
  simpa [oneSiteEnergy, oneSiteEnergySlope] using h

/-- The max-product norm distance to the one-site equilibrium bounds
each shifted free coordinate used in the energy inequality. -/
theorem oneSiteDisplacement_box_of_dist_le
    (u : CoordinateSpace 1)
    (hu : dist u oneCoord ≤ (1/10 : ℝ)) :
    oneSiteDisplacement u 0 ≤ 1/10 ∧
    oneSiteDisplacement u 1 ≤ 1/10 ∧
    -(1/10 : ℝ) ≤ oneSiteDisplacement u 2 ∧
    oneSiteDisplacement u 2 ≤ 1/10 := by
  have hdiff : ‖u - oneCoord‖ ≤ (1/10 : ℝ) := by
    simpa [dist_eq_norm] using hu
  have hS : ‖(u-oneCoord).1 0‖ ≤ (1/10 : ℝ) :=
    (norm_le_pi_norm (u-oneCoord).1 0).trans
      ((norm_fst_le (u-oneCoord)).trans hdiff)
  have hC : ‖(u-oneCoord).2.1 0‖ ≤ (1/10 : ℝ) :=
    (norm_le_pi_norm (u-oneCoord).2.1 0).trans
      ((norm_fst_le (u-oneCoord).2).trans
        ((norm_snd_le (u-oneCoord)).trans hdiff))
  have hD : ‖(u-oneCoord).2.2 0‖ ≤ (1/10 : ℝ) :=
    (norm_le_pi_norm (u-oneCoord).2.2 0).trans
      ((norm_snd_le (u-oneCoord).2).trans
        ((norm_snd_le (u-oneCoord)).trans hdiff))
  have hSa : |oneSiteDisplacement u 0| ≤ (1/10 : ℝ) := by
    simpa [oneSiteDisplacement, oneSiteCoordinateVector,
      oneCoord, Real.norm_eq_abs] using hS
  have hCa : |oneSiteDisplacement u 1| ≤ (1/10 : ℝ) := by
    simpa [oneSiteDisplacement, oneSiteCoordinateVector,
      oneCoord, Real.norm_eq_abs] using hC
  have hDa : |oneSiteDisplacement u 2| ≤ (1/10 : ℝ) := by
    simpa [oneSiteDisplacement, oneSiteCoordinateVector,
      oneCoord, Real.norm_eq_abs] using hD
  exact ⟨(abs_le.mp hSa).2, (abs_le.mp hCa).2,
    (abs_le.mp hDa).1, (abs_le.mp hDa).2⟩

theorem oneSiteEnergy_slope_negative_if_close
    (u : CoordinateSpace 1)
    (hu : dist u oneCoord ≤ (1/10 : ℝ)) :
    oneSiteEnergySlope (oneSiteDisplacement u) ≤
      -((oneSiteDisplacement u 0)^2 +
        (oneSiteDisplacement u 1)^2 +
        (oneSiteDisplacement u 2)^2)/2 := by
  obtain ⟨ha,hb,hcl,hcu⟩ := oneSiteDisplacement_box_of_dist_le u hu
  have hveta : oneSiteDisplacement u =
      ![oneSiteDisplacement u 0, oneSiteDisplacement u 1,
        oneSiteDisplacement u 2] := by
    ext i
    fin_cases i <;> rfl
  rw [hveta]
  exact oneSite_energy_slope_negative
    (oneSiteDisplacement u 0)
    (oneSiteDisplacement u 1)
    (oneSiteDisplacement u 2) ha hb hcl hcu

end
end PhosphorylationStableCapacity
