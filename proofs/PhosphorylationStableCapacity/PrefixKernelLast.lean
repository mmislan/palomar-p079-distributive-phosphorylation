module
public import proofs.PhosphorylationStableCapacity.HurwitzNonsingular

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- If a square matrix has a nonsingular leading principal block, every
nonzero kernel vector has nonzero final coordinate. -/
theorem kernel_last_ne_zero_of_prefix_det_ne_zero (n : ℕ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hdet : Matrix.det (fun i j : Fin n => K i.castSucc j.castSucc) ≠ 0)
    (z : Fin (n + 1) → ℝ) (hz : z ≠ 0)
    (hKz : K.mulVec z = 0) : z (Fin.last n) ≠ 0 := by
  intro hlast
  let A : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => K i.castSucc j.castSucc
  let p : Fin n → ℝ := fun j => z j.castSucc
  have hpzero : A.mulVec p = 0 := by
    funext i
    have hi : K.mulVec z i.castSucc = 0 := congrFun hKz i.castSucc
    simpa [A, p, Matrix.mulVec, dotProduct,
      Fin.sum_univ_castSucc, hlast] using hi
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hrecover : A⁻¹.mulVec (A.mulVec p) = p := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit,
      Matrix.one_mulVec]
  have hp : p = 0 := by
    calc
      p = A⁻¹.mulVec (A.mulVec p) := hrecover.symm
      _ = 0 := by rw [hpzero]; simp
  have hz0 : z = 0 := by
    funext j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | ⟨rfl⟩
    · exact congrFun hp k
    · exact hlast
  exact hz hz0

end
end PhosphorylationStableCapacity
