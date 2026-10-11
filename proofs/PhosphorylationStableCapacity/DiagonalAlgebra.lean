module
public import proofs.PhosphorylationStableCapacity.Assembly

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open scoped BigOperators

/-- The pairwise square identity behind the symmetric Metzler energy estimate. -/
theorem energy_pair (q z t x y : ℝ) (hz : z ≠ 0) (ht : t ≠ 0) :
    2*q*x*y = q*t/z*x^2+q*z/t*y^2-q*z*t*(x/z-y/t)^2 := by
  field_simp
  ring

/-- Positive diagonal rescaling preserves a diagonal Lyapunov certificate. -/
theorem diagonal_lyapunov_entry (aij aji pi pj di dj : ℝ) :
    (aji*di)*(dj*pj)+(di*pi)*(aij*dj) =
      di*(aji*pj+pi*aij)*dj := by ring

/-- Compute the symmetric Lyapunov matrix acting on the chosen positive vector. -/
theorem diagonal_feedback_action (d f p bz btw : ℝ)
    (hb : bz = -d) (hbt : btw = -d*f) :
    btw+p*bz = -d*(f+p) := by rw [hb,hbt]; ring

theorem diagonal_feedback_strict (d f p z : ℝ)
    (hd : 0<d) (hf : 0<f) (hp : 0<p) (hz : 0<z) :
    -d*(f+p)/z < 0 := by
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_neg_of_pos (neg_neg_of_pos hd) (add_pos hf hp)
  · exact hz

end
end PhosphorylationStableCapacity
