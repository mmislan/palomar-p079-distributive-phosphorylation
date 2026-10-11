module
public import proofs.PhosphorylationStableCapacity.FastSlowSpectralTransfer
public import proofs.PhosphorylationStableCapacity.HurwitzNonsingular

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix Polynomial Filter
open scoped Topology

/-- Complexification preserves the nonsingular inverse of a real fast
block. -/
theorem realMatrix_inv_map_complex
    {f : Type*} [Fintype f] [DecidableEq f]
    (D : Matrix f f ℝ) (hD : IsUnit D.det) :
    (D⁻¹).map (algebraMap ℝ ℂ) =
      (D.map (algebraMap ℝ ℂ))⁻¹ := by
  have hright : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D hD
  have hright' : D.map (algebraMap ℝ ℂ) *
      (D⁻¹).map (algebraMap ℝ ℂ) = 1 := by
    ext i j
    have hh := congrArg (fun x : ℝ => (x : ℂ))
      (congrArg (fun M : Matrix f f ℝ => M i j) hright)
    by_cases hij : i = j <;>
      simpa [Matrix.mul_apply, Matrix.map_apply, Matrix.one_apply, hij]
        using hh
  exact (Matrix.inv_eq_right_inv hright').symm

/-- The ordinary real Schur matrix complexifies to the Schur matrix of
the complexified four blocks. -/
theorem realSchur_map_complex
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℝ) (B : Matrix s f ℝ)
    (C : Matrix f s ℝ) (D : Matrix f f ℝ)
    (hD : IsUnit D.det) :
    (A - B * D⁻¹ * C).map (algebraMap ℝ ℂ) =
      A.map (algebraMap ℝ ℂ) -
        B.map (algebraMap ℝ ℂ) *
          (D.map (algebraMap ℝ ℂ))⁻¹ *
            C.map (algebraMap ℝ ℂ) := by
  rw [← realMatrix_inv_map_complex D hD]
  ext i j
  simp [Matrix.map_apply, Matrix.sub_apply, Matrix.mul_apply]

/-- The real four-block singularly perturbed matrix in the literal
reaction-system coordinate order. -/
def realFastSlowMatrix
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℝ) (B : Matrix s f ℝ)
    (C : Matrix f s ℝ) (D : Matrix f f ℝ) (ε : ℝ) :
    Matrix (s ⊕ f) (s ⊕ f) ℝ :=
  Matrix.fromBlocks A B (ε⁻¹ • C) (ε⁻¹ • D)

/-- Complexification commutes with the fast/slow block construction. -/
theorem realFastSlowMatrix_map_complex
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℝ) (B : Matrix s f ℝ)
    (C : Matrix f s ℝ) (D : Matrix f f ℝ) (ε : ℝ) :
    (realFastSlowMatrix A B C D ε).map (algebraMap ℝ ℂ) =
      fastSlowMatrix (A.map (algebraMap ℝ ℂ))
        (B.map (algebraMap ℝ ℂ))
        (C.map (algebraMap ℝ ℂ))
        (D.map (algebraMap ℝ ℂ)) (ε : ℂ) := by
  ext i j
  cases i <;> cases j <;>
    simp [realFastSlowMatrix, fastSlowMatrix, Matrix.map_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.smul_apply]

/-- Real-matrix form of the generic fast/slow transfer. A real Schur
characteristic factor and a real Hurwitz fast block suffice to control
the full complex characteristic roots. -/
theorem realFastSlow_eventually_simple_zero_hurwitz_complement
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℝ) (B : Matrix s f ℝ)
    (C : Matrix f s ℝ) (D : Matrix f f ℝ)
    (hD : IsHurwitz D)
    (q : ℝ[X])
    (hS : (A - B * D⁻¹ * C).charpoly = q * Polynomial.X)
    (hq : q.eval 0 ≠ 0)
    (hqleft : ∀ z : ℂ,
      (q.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0) :
    ∀ᶠ ε : ℝ in 𝓝 0,
      0 < ε →
        let J := (realFastSlowMatrix A B C D ε).map (algebraMap ℝ ℂ)
        ∃ r : ℂ[X], J.charpoly = Polynomial.X * r ∧
          r.eval 0 ≠ 0 ∧
          ∀ z : ℂ, r.eval z = 0 → z.re < 0 := by
  have hDunit : IsUnit D.det := isUnit_iff_ne_zero.mpr
    (isHurwitz_det_ne_zero hD)
  let Ac := A.map (algebraMap ℝ ℂ)
  let Bc := B.map (algebraMap ℝ ℂ)
  let Cc := C.map (algebraMap ℝ ℂ)
  let Dc := D.map (algebraMap ℝ ℂ)
  let qc := q.map (algebraMap ℝ ℂ)
  have hDc : ∀ z : ℂ, z ∈ spectrum ℂ Dc → z.re < 0 := by
    intro z hz
    exact hD z (by simpa [Polynomial.IsRoot, Dc] using
      (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz))
  have hSc : (Ac - Bc * Dc⁻¹ * Cc).charpoly =
      qc * Polynomial.X := by
    rw [← realSchur_map_complex A B C D hDunit,
      Matrix.charpoly_map, hS, Polynomial.map_mul]
    simp [qc]
  have hqc : qc.eval 0 ≠ 0 := by
    change (q.map (algebraMap ℝ ℂ)).eval
      ((algebraMap ℝ ℂ) (0 : ℝ)) ≠ 0
    rw [Polynomial.eval_map_apply]
    exact Complex.ofReal_ne_zero.mpr hq
  have hSleft : ∀ z : ℂ,
      z ∈ spectrum ℂ (Ac - Bc * Dc⁻¹ * Cc) →
        z.re < 0 ∨ z = 0 := by
    intro z hz
    have hroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
    rw [hSc, Polynomial.IsRoot, Polynomial.eval_mul,
      Polynomial.eval_X] at hroot
    rcases mul_eq_zero.mp hroot with hqroot | hz0
    · exact Or.inl (hqleft z hqroot)
    · exact Or.inr hz0
  have htransfer := fastSlow_eventually_simple_zero_hurwitz_complement
    Ac Bc Cc Dc hDc qc hSc hqc hSleft
  filter_upwards [htransfer] with ε hε hεpos
  simpa only [realFastSlowMatrix_map_complex] using hε hεpos

end
end PhosphorylationStableCapacity
