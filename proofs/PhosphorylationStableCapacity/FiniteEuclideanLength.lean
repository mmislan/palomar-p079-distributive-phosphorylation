module
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
namespace PhosphorylationStableCapacity
noncomputable section
open scoped BigOperators
def finiteEuclideanLength {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i^2)

theorem finiteEuclideanLength_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    finiteEuclideanLength v ^ 2 = ∑ i, v i^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _i _ => sq_nonneg _))

theorem sup_norm_le_finiteEuclideanLength {ι : Type*} [Fintype ι]
    (v : ι → ℝ) : ‖v‖ ≤ finiteEuclideanLength v := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  have hi : v i^2 ≤ ∑ j, v j^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  rw [Real.norm_eq_abs]
  exact Real.le_sqrt_of_sq_le (by simpa only [sq_abs] using hi)

end
end PhosphorylationStableCapacity
