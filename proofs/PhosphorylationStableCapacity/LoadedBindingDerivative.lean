module
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import proofs.PhosphorylationStableCapacity.LoadedBindingAlgebra

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

-- Lean 4.30 and 4.35 close different conversion subgoals automatically.
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- A one-dimensional quotient derivative used for the exact binding
equilibrium map along an arbitrary substrate tangent. -/
theorem hasDerivAt_affine_div (a b c d : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun t : ℝ => (a + b * t) / (c + d * t))
      ((b * c - a * d) / c ^ 2) 0 := by
  have hn : HasDerivAt (fun t : ℝ => a + b * t) b 0 := by
    convert ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).const_mul b).const_add a using 1
    all_goals first
      | (funext t <;> simp only [id_eq])
      | simp only [mul_one]
  have hd : HasDerivAt (fun t : ℝ => c + d * t) d 0 := by
    convert ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).const_mul d).const_add c using 1
    all_goals first
      | (funext t <;> simp only [id_eq])
      | simp only [mul_one]
  have hc0 : c + d * 0 ≠ 0 := by simpa using hc
  convert hn.div hd hc0 using 1
  simp

def bindingDenominator {ι : Type*} [Fintype ι]
    (p S : ι → ℝ) : ℝ := 1 + ∑ i, p i * S i

def bindingLinearPath {ι : Type*} (S σ : ι → ℝ)
    (t : ℝ) (i : ι) : ℝ := S i + t * (S i * σ i)

def bindingWeightedTangent {ι : Type*} [Fintype ι]
    (p S σ : ι → ℝ) : ℝ := ∑ i, p i * S i * σ i

theorem bindingDenominator_linearPath {ι : Type*} [Fintype ι]
    (p S σ : ι → ℝ) (t : ℝ) :
    bindingDenominator p (bindingLinearPath S σ t) =
      bindingDenominator p S + t * bindingWeightedTangent p S σ := by
  have hsum :
      (∑ i, p i * (S i + t * (S i * σ i))) =
        (∑ i, p i * S i) + t * (∑ i, p i * S i * σ i) := by
    calc
      _ = ∑ i, (p i * S i + t * (p i * S i * σ i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, p i * S i) + ∑ i, t * (p i * S i * σ i) := by
        rw [Finset.sum_add_distrib]
      _ = _ := by rw [Finset.mul_sum]
  simp only [bindingDenominator, bindingLinearPath,
    bindingWeightedTangent]
  rw [hsum]
  ring

def bindingComplex {ι : Type*} [Fintype ι]
    (ET : ℝ) (p S : ι → ℝ) (i : ι) : ℝ :=
  ET * p i * S i / bindingDenominator p S

theorem bindingComplex_weighted_sum {ι : Type*} [Fintype ι]
    (ET : ℝ) (p S σ : ι → ℝ) :
    (∑ i, bindingComplex ET p S i * σ i) =
      ET * bindingWeightedTangent p S σ / bindingDenominator p S := by
  calc
    (∑ i, bindingComplex ET p S i * σ i) =
        ∑ i, ET * (p i * S i * σ i) / bindingDenominator p S := by
      apply Finset.sum_congr rfl
      intro i _
      unfold bindingComplex
      ring
    _ = ET * bindingWeightedTangent p S σ /
        bindingDenominator p S := by
      simp only [bindingWeightedTangent, Finset.mul_sum,
        Finset.sum_div]

/-- Exact derivative of one bound-complex coordinate along the linear
substrate path, before rewriting it in enzyme-total-correction form. -/
theorem bindingComplex_hasDerivAt_linearPath_raw
    {ι : Type*} [Fintype ι]
    (ET : ℝ) (p S σ : ι → ℝ) (i : ι)
    (hden : bindingDenominator p S ≠ 0) :
    HasDerivAt (fun t : ℝ =>
      bindingComplex ET p (bindingLinearPath S σ t) i)
      (((ET * p i * S i * σ i) * bindingDenominator p S -
          (ET * p i * S i) * bindingWeightedTangent p S σ) /
        (bindingDenominator p S) ^ 2) 0 := by
  have hfun : (fun t : ℝ =>
      bindingComplex ET p (bindingLinearPath S σ t) i) =
      fun t : ℝ =>
        ((ET * p i * S i) + (ET * p i * S i * σ i) * t) /
          (bindingDenominator p S +
            bindingWeightedTangent p S σ * t) := by
    funext t
    rw [bindingComplex, bindingDenominator_linearPath]
    simp only [bindingLinearPath]
    congr 1 <;> ring
  rw [hfun]
  exact hasDerivAt_affine_div _ _ _ _ hden

/-- The bound-complex derivative is its local logarithmic substrate
variation minus the change in free enzyme forced by its fixed total. -/
theorem bindingComplex_hasDerivAt_linearPath
    {ι : Type*} [Fintype ι]
    (ET : ℝ) (p S σ : ι → ℝ) (i : ι)
    (hET : ET ≠ 0) (hden : bindingDenominator p S ≠ 0) :
    HasDerivAt (fun t : ℝ =>
      bindingComplex ET p (bindingLinearPath S σ t) i)
      (bindingComplex ET p S i *
        (σ i - (∑ j, bindingComplex ET p S j * σ j) / ET)) 0 := by
  have hraw := bindingComplex_hasDerivAt_linearPath_raw ET p S σ i hden
  have hvalue :
      ((ET * p i * S i * σ i) * bindingDenominator p S -
          (ET * p i * S i) * bindingWeightedTangent p S σ) /
        (bindingDenominator p S) ^ 2 =
      bindingComplex ET p S i *
        (σ i - (∑ j, bindingComplex ET p S j * σ j) / ET) := by
    rw [bindingComplex_weighted_sum]
    unfold bindingComplex
    field_simp [hET, hden]
  rw [hvalue] at hraw
  exact hraw

def bindingLoadedLevel {ι : Type*} [Fintype ι]
    (ET FT : ℝ) (p q S : ι → ℝ) (i : ι) : ℝ :=
  S i + bindingComplex ET p S i + bindingComplex FT q S i

/-- The loaded mass matrix is the exact directional derivative of the
reversible binding-equilibrium level inventory along every substrate
tangent. This does not yet identify the reduced catalytic slow field. -/
theorem bindingLoadedLevel_hasDerivAt_linearPath
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ET FT : ℝ) (p q S σ : ι → ℝ) (i : ι)
    (hET : ET ≠ 0) (hFT : FT ≠ 0)
    (hp : bindingDenominator p S ≠ 0)
    (hq : bindingDenominator q S ≠ 0) :
    HasDerivAt (fun t : ℝ =>
      bindingLoadedLevel ET FT p q (bindingLinearPath S σ t) i)
      ((loadedBindingMass S (bindingComplex ET p S)
        (bindingComplex FT q S) ET FT).mulVec σ i) 0 := by
  have hS : HasDerivAt (fun t : ℝ => bindingLinearPath S σ t i)
      (S i * σ i) 0 := by
    have hfun : (fun t : ℝ => bindingLinearPath S σ t i) =
        fun t : ℝ => S i + (S i * σ i) * t := by
      funext t
      unfold bindingLinearPath
      ring
    rw [hfun]
    simpa using (((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).const_mul
      (S i * σ i)).const_add (S i))
  have hC := bindingComplex_hasDerivAt_linearPath ET p S σ i hET hp
  have hY := bindingComplex_hasDerivAt_linearPath FT q S σ i hFT hq
  rw [loadedBindingMass_action]
  convert (hS.add hC).add hY using 1
  all_goals
    funext t
    rfl

end
end PhosphorylationStableCapacity
