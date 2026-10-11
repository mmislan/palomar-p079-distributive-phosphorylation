module
public import proofs.PhosphorylationStableCapacity.MatrixCharpolyCompactLipschitz435
public import proofs.PhosphorylationStableCapacity.CompactFiniteScalarBound435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open scoped Matrix.Norms.Elementwise

/-- Every coefficient of a continuous finite matrix family has one
compact bound, uniformly over the finitely many positions used by the
neutral characteristic secant. -/
theorem compact_matrix_charpoly_finite_coeff_upper
    {α ι : Type*} [TopologicalSpace α]
    [Fintype ι] [DecidableEq ι]
    (K : Set α) (hK : IsCompact K)
    (J : α → Matrix ι ι ℝ) (hJ : ContinuousOn J K)
    (N : ℕ) :
    ∃ M : ℝ, 0 < M ∧
      ∀ a ∈ K, ∀ k : Fin N,
        |(J a).charpoly.coeff (k.val+1)| ≤ M := by
  apply compact_finite_scalar_abs_upper K hK
    (fun (k : Fin N) (a : α) => (J a).charpoly.coeff (k.val+1))
  intro k
  exact (contDiff_matrix_charpoly_coeff (ι := ι) (k.val+1)).continuous
    |>.comp_continuousOn hJ

end

end PhosphorylationStableCapacity
