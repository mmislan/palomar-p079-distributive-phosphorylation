module
public import proofs.PhosphorylationStableCapacity.OneSiteEnergyDecay

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- A convenient comparison between the exact quadratic energy and the
metric of the one-site class chart. -/
theorem oneSiteEnergy_metric_bounds (u : CoordinateSpace 1) :
    (dist u oneCoord)^2 ≤ 300 * oneSiteEnergy u ∧
      oneSiteEnergy u ≤ 9 * (dist u oneCoord)^2 := by
  let a := oneSiteDisplacement u 0
  let b := oneSiteDisplacement u 1
  let c := oneSiteDisplacement u 2
  let d := dist u oneCoord
  have hd : 0 ≤ d := dist_nonneg
  have ha : |a| ≤ d := by
    simpa [a, d, oneSiteDisplacement, oneSiteCoordinateVector,
      oneCoord, Real.norm_eq_abs, dist_eq_norm] using
      (norm_le_pi_norm (u-oneCoord).1 0).trans
        ((norm_fst_le (u-oneCoord)).trans le_rfl)
  have hb : |b| ≤ d := by
    simpa [b, d, oneSiteDisplacement, oneSiteCoordinateVector,
      oneCoord, Real.norm_eq_abs, dist_eq_norm] using
      (norm_le_pi_norm (u-oneCoord).2.1 0).trans
        ((norm_fst_le (u-oneCoord).2).trans
          ((norm_snd_le (u-oneCoord)).trans le_rfl))
  have hc : |c| ≤ d := by
    simpa [c, d, oneSiteDisplacement, oneSiteCoordinateVector,
      oneCoord, Real.norm_eq_abs, dist_eq_norm] using
      (norm_le_pi_norm (u-oneCoord).2.2 0).trans
        ((norm_snd_le (u-oneCoord).2).trans
          ((norm_snd_le (u-oneCoord)).trans le_rfl))
  have hda : d ≤ |a| + |b| + |c| := by
    change ‖u - oneCoord‖ ≤ |a| + |b| + |c|
    apply (norm_prod_le_iff).2
    constructor
    · apply (pi_norm_le_iff_of_nonneg (by positivity)).2
      intro i
      fin_cases i
      have hSa : |a| ≤ |a| + |b| + |c| := by
        linarith [abs_nonneg b, abs_nonneg c]
      simpa [a, oneSiteDisplacement, oneSiteCoordinateVector,
        oneCoord, Real.norm_eq_abs] using hSa
    · apply (norm_prod_le_iff).2
      constructor
      · apply (pi_norm_le_iff_of_nonneg (by positivity)).2
        intro i
        fin_cases i
        have hCb : |b| ≤ |a| + |b| + |c| := by
          linarith [abs_nonneg a, abs_nonneg c]
        simpa [b, oneSiteDisplacement, oneSiteCoordinateVector,
          oneCoord, Real.norm_eq_abs] using hCb
      · apply (pi_norm_le_iff_of_nonneg (by positivity)).2
        intro i
        fin_cases i
        simp [c, oneSiteDisplacement, oneSiteCoordinateVector,
          oneCoord, Real.norm_eq_abs]
        positivity
  have hpoly := oneSiteEnergyPoly_bounds a b c
  have henergy : oneSiteEnergy u = oneSiteEnergyPoly a b c := rfl
  rw [← henergy] at hpoly
  have habsq : a^2 ≤ d^2 := sq_le_sq.mpr (by simpa [abs_of_nonneg hd] using ha)
  have hbbsq : b^2 ≤ d^2 := sq_le_sq.mpr (by simpa [abs_of_nonneg hd] using hb)
  have hccsq : c^2 ≤ d^2 := sq_le_sq.mpr (by simpa [abs_of_nonneg hd] using hc)
  have hsum : (|a| + |b| + |c|)^2 ≤ 3 * (a^2+b^2+c^2) := by
    calc
      _ ≤ 3 * (|a|^2+|b|^2+|c|^2) := by
        nlinarith [sq_nonneg (|a|-|b|), sq_nonneg (|a|-|c|),
          sq_nonneg (|b|-|c|)]
      _ = _ := by rw [sq_abs, sq_abs, sq_abs]
  constructor
  · nlinarith [sq_nonneg ((|a| + |b| + |c|) - d)]
  · nlinarith

end
end PhosphorylationStableCapacity
