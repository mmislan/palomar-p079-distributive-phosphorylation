module
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial Filter

/-- A nonempty real matrix whose characteristic polynomial is negative at zero
has a positive real eigenvalue. This isolates the topological step from any
particular determinant certificate. -/
theorem positive_charpoly_root_of_negative_constant
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hconstant : A.charpoly.coeff 0 < 0) :
    ∃ x : ℝ, 0 < x ∧ A.charpoly.eval x = 0 := by
  have hdeg : 0 < A.charpoly.degree := by
    rw [Matrix.charpoly_degree_eq_dim]
    exact_mod_cast Fintype.card_pos
  have hlead : 0 ≤ A.charpoly.leadingCoeff := by
    rw [(Matrix.charpoly_monic A).leadingCoeff]
    norm_num
  have htop : Tendsto (fun x : ℝ => A.charpoly.eval x) atTop atTop :=
    A.charpoly.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlead
  obtain ⟨b, hb, hpb⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and
      (htop.eventually_gt_atTop 0)).exists
  have hzero : A.charpoly.eval 0 < 0 := by
    simpa only [← Polynomial.coeff_zero_eq_eval_zero] using hconstant
  obtain ⟨x, hx, hpx⟩ :=
    (intermediate_value_Icc hb.le A.charpoly.continuous.continuousOn)
      ⟨hzero.le, hpb.le⟩
  refine ⟨x, ?_, hpx⟩
  have hxne : x ≠ 0 := by
    intro heq
    subst x
    linarith
  exact lt_of_le_of_ne hx.1 (Ne.symm hxne)

end PhosphorylationStableCapacity
