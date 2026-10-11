module
public import proofs.PhosphorylationStableCapacity.PathSpectralBridge

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The exact level flux of the explicit positive path vector. -/
theorem pathVectorFin_affine_flux {m : ℕ} (hm : 0 < m)
    (d : Fin (m + 1) → ℝ) (hd : ∀ k, 0 < d k) :
    ∀ k : Fin (m + 1),
      (pathIncidence m).transpose.mulVec (pathVectorFin d) k =
        d k * ((k.val : ℝ) - pathMean m (pathWeightsNat d)) := by
  have hdn : ∀ j ≤ m, 0 < pathWeightsNat d j := by
    intro j hj
    have hlt : j < m + 1 := by omega
    change 0 < (if h : j < m + 1 then d ⟨j, h⟩ else 0)
    simpa only [hlt, dite_true] using hd ⟨j, hlt⟩
  intro k
  have hflux := pathVectorNat_affine_flux hm (pathWeightsNat d) hdn k
  have hweight : pathWeightsNat d k.val = d k := by
    change (if h : k.val < m + 1 then d ⟨k.val, h⟩ else 0) = d k
    simp only [k.isLt, dite_true]
  simpa only [pathVectorFin, hweight] using hflux

/-- Discrete integration by parts: the feedback gain on the positive edge
vector is the weighted first moment of the level feedback. -/
theorem path_feedback_gain_eq_moment {m : ℕ} (hm : 0 < m)
    (d : Fin (m + 1) → ℝ) (hd : ∀ k, 0 < d k)
    (g : Fin (m + 1) → ℝ) :
    (∑ i, (pathIncidence m).mulVec g i * pathVectorFin d i) =
      ∑ k, g k * d k * ((k.val : ℝ) - pathMean m (pathWeightsNat d)) := by
  have hflux := pathVectorFin_affine_flux hm d hd
  have hvec : Matrix.vecMul (pathVectorFin d) (pathIncidence m) =
      (pathIncidence m).transpose.mulVec (pathVectorFin d) := by
    simpa using Matrix.vecMul_transpose (pathIncidence m).transpose (pathVectorFin d)
  calc
    (∑ i, (pathIncidence m).mulVec g i * pathVectorFin d i) =
        dotProduct ((pathIncidence m).mulVec g) (pathVectorFin d) := rfl
    _ = dotProduct (pathVectorFin d) ((pathIncidence m).mulVec g) :=
      dotProduct_comm _ _
    _ = dotProduct (Matrix.vecMul (pathVectorFin d) (pathIncidence m)) g :=
      Matrix.dotProduct_mulVec _ _ _
    _ = dotProduct ((pathIncidence m).transpose.mulVec (pathVectorFin d)) g := by
      rw [hvec]
    _ = ∑ k, g k * d k * ((k.val : ℝ) - pathMean m (pathWeightsNat d)) := by
      simp [dotProduct, hflux, mul_comm, mul_left_comm, mul_assoc]

end
end PhosphorylationStableCapacity
