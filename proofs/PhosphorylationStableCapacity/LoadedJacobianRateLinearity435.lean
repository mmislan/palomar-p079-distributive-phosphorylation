module
public import proofs.PhosphorylationStableCapacity.RateVariationTranslated
public import proofs.PhosphorylationStableCapacity.LoadedJacobianBlockMatrix
public import proofs.PhosphorylationStableCapacity.LoadedFieldDifferentiability
public import proofs.PhosphorylationStableCapacity.SplitJacobianContinuity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix

def ratesScale {n : ℕ} (a : ℝ) (k : Rates n) : Rates n where
  a i := a * k.a i
  b i := a * k.b i
  c i := a * k.c i
  alpha i := a * k.alpha i
  beta i := a * k.beta i
  gamma i := a * k.gamma i

theorem rateVector_ratesScale {n : ℕ} (a : ℝ) (k : Rates n) :
    rateVector (ratesScale a k) = a • rateVector k := by
  funext j i
  fin_cases j <;> simp [rateVector, ratesScale, Pi.smul_apply, smul_eq_mul]

theorem ratesFromVector_add {n : ℕ} (v w : RateVector n) :
    ratesFromVector (v + w) = ratesAdd (ratesFromVector v) (ratesFromVector w) := by
  rfl

theorem ratesFromVector_smul {n : ℕ} (a : ℝ) (v : RateVector n) :
    ratesFromVector (a • v) = ratesScale a (ratesFromVector v) := by
  rfl

/-- The literal loaded mass-action vector field is linear in all six
rate arrays, at every state and for arbitrary real signed arrays. -/
theorem loadedRestrictedField_ratesScale {n : ℕ}
    (ET FT ST : ℝ) (a : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    loadedRestrictedField ET FT ST (ratesScale a k) u =
      a • loadedRestrictedField ET FT ST k u := by
  apply Prod.ext
  · funext i
    simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
    rw [loadedRestrictedField_slow_eq_incidence,
      loadedRestrictedField_slow_eq_incidence]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp [catalyticCurrent, ratesScale]
    ring
  · apply Prod.ext
    · funext i
      simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
      simp only [loadedRestrictedField, toLoadedCoord,
        restrictedFieldEuclid, restrictedField, toCoordinateSpace,
        chart, field, kinaseNet, ratesScale]
      ring
    · funext i
      simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      simp only [loadedRestrictedField, toLoadedCoord,
        restrictedFieldEuclid, restrictedField, toCoordinateSpace,
        chart, field, phosphataseNet, ratesScale]
      ring

/-- The full loaded class Jacobian, rather than just its slow Schur
block, is linear in the literal kinetic rate vector. -/
theorem loadedJacobianMatrix_rateVector_add {n : ℕ}
    (ET FT ST : ℝ) (v w : RateVector n) (u : CoordinateSpace n) :
    loadedJacobianMatrix ET FT ST (ratesFromVector (v + w)) u =
      loadedJacobianMatrix ET FT ST (ratesFromVector v) u +
        loadedJacobianMatrix ET FT ST (ratesFromVector w) u := by
  rw [ratesFromVector_add]
  have hv := (differentiable_loadedRestrictedField ET FT ST
    (ratesFromVector v)).differentiableAt (x := u)
  have hw := (differentiable_loadedRestrictedField ET FT ST
    (ratesFromVector w)).differentiableAt (x := u)
  simp only [loadedJacobianMatrix]
  have hfun : loadedRestrictedField ET FT ST
      (ratesAdd (ratesFromVector v) (ratesFromVector w)) =
      (fun q => loadedRestrictedField ET FT ST (ratesFromVector v) q +
        loadedRestrictedField ET FT ST (ratesFromVector w) q) := by
    funext q
    exact loadedRestrictedField_ratesAdd ET FT ST _ _ q
  rw [hfun]
  have hfun' :
      (fun q => loadedRestrictedField ET FT ST (ratesFromVector v) q +
        loadedRestrictedField ET FT ST (ratesFromVector w) q) =
      loadedRestrictedField ET FT ST (ratesFromVector v) +
        loadedRestrictedField ET FT ST (ratesFromVector w) := by
    funext q
    rfl
  rw [hfun', fderiv_add hv hw]
  simp

theorem loadedJacobianMatrix_rateVector_smul {n : ℕ}
    (ET FT ST : ℝ) (a : ℝ) (v : RateVector n)
    (u : CoordinateSpace n) :
    loadedJacobianMatrix ET FT ST (ratesFromVector (a • v)) u =
      a • loadedJacobianMatrix ET FT ST (ratesFromVector v) u := by
  rw [ratesFromVector_smul]
  have hv := (differentiable_loadedRestrictedField ET FT ST
    (ratesFromVector v)).differentiableAt (x := u)
  have hfun : loadedRestrictedField ET FT ST
      (ratesScale a (ratesFromVector v)) =
      (fun q => a • loadedRestrictedField ET FT ST (ratesFromVector v) q) := by
    funext q
    exact loadedRestrictedField_ratesScale ET FT ST a _ q
  simp only [loadedJacobianMatrix]
  rw [hfun, fderiv_fun_const_smul hv a]
  simp

theorem loadedJacobianMatrix_rateVector_sum
    {ι : Type*} [DecidableEq ι] {n : ℕ}
    (ET FT ST : ℝ) (s : Finset ι)
    (v : ι → RateVector n) (u : CoordinateSpace n) :
    loadedJacobianMatrix ET FT ST
      (ratesFromVector (∑ i ∈ s, v i)) u =
        ∑ i ∈ s, loadedJacobianMatrix ET FT ST
          (ratesFromVector (v i)) u := by
  induction s using Finset.induction_on with
  | empty =>
      have hz := loadedJacobianMatrix_rateVector_smul
        ET FT ST 0 (0 : RateVector n) u
      simpa using hz
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [loadedJacobianMatrix_rateVector_add, ih]

theorem loadedJacobianMatrix_rateVector_sub {n : ℕ}
    (ET FT ST : ℝ) (v w : RateVector n) (u : CoordinateSpace n) :
    loadedJacobianMatrix ET FT ST (ratesFromVector (v - w)) u =
      loadedJacobianMatrix ET FT ST (ratesFromVector v) u -
        loadedJacobianMatrix ET FT ST (ratesFromVector w) u := by
  have hneg : loadedJacobianMatrix ET FT ST
      (ratesFromVector (-w)) u =
        -loadedJacobianMatrix ET FT ST (ratesFromVector w) u := by
    simpa only [neg_one_smul] using
      loadedJacobianMatrix_rateVector_smul ET FT ST (-1) w u
  calc
    loadedJacobianMatrix ET FT ST (ratesFromVector (v - w)) u =
        loadedJacobianMatrix ET FT ST (ratesFromVector (v + -w)) u := by
          rw [sub_eq_add_neg]
    _ = loadedJacobianMatrix ET FT ST (ratesFromVector v) u +
          loadedJacobianMatrix ET FT ST (ratesFromVector (-w)) u :=
      loadedJacobianMatrix_rateVector_add ET FT ST v (-w) u
    _ = loadedJacobianMatrix ET FT ST (ratesFromVector v) u -
          loadedJacobianMatrix ET FT ST (ratesFromVector w) u := by
      rw [hneg]
      rfl

end

end PhosphorylationStableCapacity
