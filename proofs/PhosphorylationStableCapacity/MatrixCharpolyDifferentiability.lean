module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitJacobianDifferentiability

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix Polynomial

/-- The determinant of a finite real matrix family is differentiable when
    every entry is differentiable. -/
theorem matrix_det_differentiableAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ℝ → Matrix ι ι ℝ)
    (hentry : ∀ i j, DifferentiableAt ℝ (fun δ => J δ i j) 0) :
    DifferentiableAt ℝ (fun δ => (J δ).det) 0 := by
  simp_rw [Matrix.det_apply']
  apply DifferentiableAt.fun_sum
  intro σ hσ
  exact (differentiableAt_const _).mul
    (DifferentiableAt.fun_finsetProd fun i hi => hentry (σ i) i)

theorem matrix_charpoly_coeff_differentiableAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ℝ → Matrix ι ι ℝ)
    (hentry : ∀ i j, DifferentiableAt ℝ (fun δ => J δ i j) 0)
    (k : ℕ) :
    DifferentiableAt ℝ (fun δ => (J δ).charpoly.coeff k) 0 := by
  by_cases hk : k ≤ Fintype.card ι
  · have hminor (s : Finset ι) : DifferentiableAt ℝ
        (fun δ => ((J δ).submatrix
          (Subtype.val : s → ι) (Subtype.val : s → ι)).det) 0 := by
      apply matrix_det_differentiableAt
      intro i j
      exact hentry i.val j.val
    have hsum : DifferentiableAt ℝ (fun δ =>
        (-1 : ℝ)^(Fintype.card ι-k) *
          ∑ s ∈ Finset.univ.powersetCard (Fintype.card ι-k),
            ((J δ).submatrix
              (Subtype.val : s → ι) (Subtype.val : s → ι)).det) 0 := by
      apply DifferentiableAt.const_mul
      apply DifferentiableAt.fun_sum
      intro s hs
      exact hminor s
    convert hsum using 1
    funext δ
    simpa [Nat.sub_sub_self hk] using
      (Matrix.charpoly_coeff_eq_sum_minors (J δ)
        (Fintype.card ι-k) (Nat.sub_le _ _))
  · have hzero (δ : ℝ) : (J δ).charpoly.coeff k = 0 := by
      have hdegree := (J δ).charpoly_natDegree_eq_dim
      exact coeff_eq_zero_of_natDegree_lt (by omega)
    simp_rw [hzero]
    exact differentiableAt_const _

theorem arbitrarySplit_charpoly_coeff_differentiableAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1)) (k : ℕ) :
    DifferentiableAt ℝ (fun δ =>
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (arbitrarySplitRetunedRates m ξ r τ δ ε)
        (toCoordinateSpace (chart
          (arbitrarySplitFiniteState (m+1) ξ r δ j)))).charpoly.coeff k) 0 := by
  let J : ℝ → Matrix (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2)))
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) ℝ := fun δ =>
    restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (arbitrarySplitRetunedRates m ξ r τ δ ε)
      (toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j)))
  have hJ : DifferentiableAt ℝ J 0 :=
    arbitrarySplit_restrictedJacobianMatrix_differentiableAt
      m ξ r τ ε hr hD₀ hB₀ j
  have hentry (i j) : DifferentiableAt ℝ (fun δ => J δ i j) 0 :=
    (differentiableAt_pi.mp (differentiableAt_pi.mp hJ i)) j
  exact matrix_charpoly_coeff_differentiableAt J hentry k

end
end PhosphorylationStableCapacity
