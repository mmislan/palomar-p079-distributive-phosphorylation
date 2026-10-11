module
public import Mathlib.Analysis.Complex.Basic
public import proofs.PhosphorylationStableCapacity.Jacobian
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly

@[expose] public section
set_option maxHeartbeats 1000000
set_option diagnostics true

namespace PhosphorylationStableCapacity

noncomputable section

/-- A real Metzler matrix with strictly negative row sums is Hurwitz. -/
theorem hurwitz_of_metzler_strict_rows {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j)
    (hrow : ∀ i, (∑ j, A i j) < 0) : IsHurwitz A := by
  intro z hz
  let B : Matrix ι ι ℂ := A.map (algebraMap ℝ ℂ)
  have heig : Module.End.HasEigenvalue (Matrix.toLin' B) z := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
    exact hz
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball heig
  have hnorm (j : ι) (hj : j ∈ Finset.univ.erase i) :
      ‖B i j‖ = A i j := by
    have hne : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    simp [B, abs_of_nonneg (hoff i j hne)]
  have hradius :
      (∑ j ∈ Finset.univ.erase i, ‖B i j‖) =
        ∑ j ∈ Finset.univ.erase i, A i j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hnorm j hj
  have hdist : ‖z - (A i i : ℂ)‖ ≤
      ∑ j ∈ Finset.univ.erase i, A i j := by
    have hi' : ‖z - B i i‖ ≤
        ∑ j ∈ Finset.univ.erase i, ‖B i j‖ := by
      simpa only [mem_closedBall_iff_norm', norm_sub_rev] using hi
    change ‖z - (A i i : ℂ)‖ ≤
      ∑ j ∈ Finset.univ.erase i, ‖B i j‖ at hi'
    rwa [hradius] at hi'
  have hre : z.re - A i i ≤ ‖z - (A i i : ℂ)‖ := by
    simpa using Complex.re_le_norm (z - (A i i : ℂ))
  have hsplit : A i i + (∑ j ∈ Finset.univ.erase i, A i j) =
      ∑ j, A i j :=
    Finset.add_sum_erase Finset.univ (fun j => A i j) (Finset.mem_univ i)
  linarith [hrow i]

end
end PhosphorylationStableCapacity
