module
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- A real two-dimensional linear map with identity first row and a nonzero
second-column pivot is a continuous linear equivalence. The lower-left
derivative is unrestricted. -/
theorem continuousLinearEquiv_of_triangular_pair
    (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (hfirst : ∀ v, (L v).1 = v.1)
    (hpivot : (L (0, 1)).2 ≠ 0) :
    ∃ i : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      i.toContinuousLinearMap = L := by
  have hzero (v : ℝ × ℝ) (hv : L v = 0) : v = 0 := by
    have hv1 : v.1 = 0 := by
      have h := congrArg Prod.fst hv
      simpa only [hfirst v, Prod.fst_zero] using h
    have hvec : v = v.2 • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp [hv1]
    have hv2 : v.2 * (L (0, 1)).2 = 0 := by
      have hL : L v = v.2 • L ((0, 1) : ℝ × ℝ) := by
        calc
          L v = L (v.2 • ((0, 1) : ℝ × ℝ)) := congrArg L hvec
          _ = v.2 • L ((0, 1) : ℝ × ℝ) := L.map_smul _ _
      have h := congrArg Prod.snd (hL.symm.trans hv)
      simpa only [Prod.smul_snd, smul_eq_mul, Prod.snd_zero] using h
    have hv2zero : v.2 = 0 :=
      (mul_eq_zero.mp hv2).resolve_right hpivot
    exact Prod.ext hv1 hv2zero
  have hinj : Function.Injective L := by
    intro u v huv
    have hdiff : L (u-v) = 0 := by rw [map_sub, huv, sub_self]
    exact sub_eq_zero.mp (hzero (u-v) hdiff)
  have hsurj : Function.Surjective L :=
    L.toLinearMap.surjective_of_injective hinj
  let i : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    ContinuousLinearEquiv.ofBijective L
      (LinearMap.ker_eq_bot.mpr hinj)
      (LinearMap.range_eq_top.mpr hsurj)
  exact ⟨i, ContinuousLinearEquiv.coe_ofBijective L _ _⟩

end
end PhosphorylationStableCapacity
