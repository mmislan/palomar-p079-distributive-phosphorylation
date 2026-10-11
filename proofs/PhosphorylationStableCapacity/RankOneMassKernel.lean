module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Ring

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The leading mass matrix on the occupied levels of the large-parameter
source. It is a positive diagonal matrix minus one rank-one term. -/
def rankOneMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => (if i = j then d i else 0) - d i * d j / 2

theorem rankOneMass_action {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d v : ι → ℝ) (i : ι) :
    (rankOneMass d).mulVec v i =
      d i * (v i - (∑ j, d j * v j) / 2) := by
  simp only [Matrix.mulVec, dotProduct, rankOneMass, sub_mul,
    Finset.sum_sub_distrib, ite_mul, zero_mul]
  have hfirst : (∑ x, if i = x then d i * v x else 0) = d i * v i := by
    simp
  rw [hfirst]
  have hsecond : (∑ x, d i * d x / 2 * v x) =
      d i / 2 * (∑ x, d x * v x) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsecond]
  ring

/-- Every kernel vector is constant when all level weights are positive. -/
theorem rankOneMass_kernel_constant {ι : Type*} [Fintype ι]
    [DecidableEq ι] (d v : ι → ℝ) (hd : ∀ i, 0 < d i)
    (hv : (rankOneMass d).mulVec v = 0) (i : ι) :
    v i = (∑ j, d j * v j) / 2 := by
  have h := congrFun hv i
  rw [rankOneMass_action] at h
  simp only [Pi.zero_apply] at h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (ne_of_gt (hd i)))

/-- With total level mass two, every constant vector lies in the kernel. -/
theorem rankOneMass_constant_kernel {ι : Type*} [Fintype ι]
    [DecidableEq ι] (d : ι → ℝ) (hd : ∑ i, d i = 2) (a : ℝ) :
    (rankOneMass d).mulVec (fun _ => a) = 0 := by
  funext i
  rw [rankOneMass_action]
  simp only [Pi.zero_apply]
  have hsum : (∑ j, d j * a) = 2 * a := by
    rw [← Finset.sum_mul, hd]
  rw [hsum]
  ring

end
end PhosphorylationStableCapacity
