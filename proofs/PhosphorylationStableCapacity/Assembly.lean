module
public import proofs.PhosphorylationStableCapacity.StructuralAlgebra
public import proofs.PhosphorylationStableCapacity.KineticFreedom

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open scoped BigOperators

/-- The algebraic negative-vector certificate used by the ordinary Gershgorin
argument. The matrix identities are inputs, proved in the ordinary derivation;
no stability or capacity theorem is an assumption or a claimed conclusion. -/
theorem large_r_block_certificate (n : ℕ) (hn : 2 ≤ n) (v : ℝ)
    (hv : 0 < v) (hv1 : v < 1)
    (H : Matrix (Fin (n-1)) (Fin (n-1)) ℝ) (f z : Fin (n-1) → ℝ)
    (hH : ∀ i, ∑ j, H i j*z j=1)
    (hgain : (∑ j, f j*z j) =
      (10*((4:ℝ)/3-v*((n:ℝ)-(4*(n:ℝ)-3)/9))+(2+v)/3)/(14-8*v)) :
    ∀ i, (∑ j, (-H i j+f j)*z j) < 0 := by
  intro i
  rw [feedback_vector H f z hH i, hgain]
  have h := feedback_gain_lt_one n hn v hv hv1
  linarith

end
end PhosphorylationStableCapacity
