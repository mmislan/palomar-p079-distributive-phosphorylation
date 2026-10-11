module
public import proofs.PhosphorylationStableCapacity.CompactFastSlowTransfer435
public import proofs.PhosphorylationStableCapacity.FastSlowRealComplexMap

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix Polynomial Filter
open scoped Topology Matrix.Norms.L2Operator

/-- The finite-rate real fast/slow transfer uses one binding threshold
on a compact family of jointly continuous exact block matrices. -/
theorem compact_realFastSlow_eventually_simple_zero_hurwitz_complement
    {α s f : Type*} [TopologicalSpace α]
    [Fintype s] [Fintype f] [DecidableEq s] [DecidableEq f]
    (K : Set α) (hK : IsCompact K)
    (A : α → Matrix s s ℝ) (B : α → Matrix s f ℝ)
    (C : α → Matrix f s ℝ) (D : α → Matrix f f ℝ)
    (q : α → ℝ[X])
    (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hDcont : Continuous D)
    (hD : ∀ a ∈ K, IsHurwitz (D a))
    (hS : ∀ a ∈ K,
      (A a - B a * (D a)⁻¹ * C a).charpoly = q a * Polynomial.X)
    (hq : ∀ a ∈ K, (q a).eval 0 ≠ 0)
    (hqleft : ∀ a ∈ K, ∀ z : ℂ,
      ((q a).map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0) :
    ∀ᶠ ε : ℝ in 𝓝 0,
      ∀ a ∈ K, 0 < ε →
        let J := (realFastSlowMatrix (A a) (B a)
          (C a) (D a) ε).map (algebraMap ℝ ℂ)
        ∃ p : ℂ[X], J.charpoly = Polynomial.X * p ∧
          p.eval 0 ≠ 0 ∧
          ∀ z : ℂ, p.eval z = 0 → z.re < 0 := by
  let Ac : α → Matrix s s ℂ := fun a => (A a).map (algebraMap ℝ ℂ)
  let Bc : α → Matrix s f ℂ := fun a => (B a).map (algebraMap ℝ ℂ)
  let Cc : α → Matrix f s ℂ := fun a => (C a).map (algebraMap ℝ ℂ)
  let Dc : α → Matrix f f ℂ := fun a => (D a).map (algebraMap ℝ ℂ)
  let qc : α → ℂ[X] := fun a => (q a).map (algebraMap ℝ ℂ)
  have hAc : Continuous Ac := by
    apply continuous_matrix
    intro i j
    exact Complex.continuous_ofReal.comp (hA.matrix_elem i j)
  have hBc : Continuous Bc := by
    apply continuous_matrix
    intro i j
    exact Complex.continuous_ofReal.comp (hB.matrix_elem i j)
  have hCc : Continuous Cc := by
    apply continuous_matrix
    intro i j
    exact Complex.continuous_ofReal.comp (hC.matrix_elem i j)
  have hDc : Continuous Dc := by
    apply continuous_matrix
    intro i j
    exact Complex.continuous_ofReal.comp (hDcont.matrix_elem i j)
  have hDspec : ∀ a ∈ K, ∀ z : ℂ,
      z ∈ spectrum ℂ (Dc a) → z.re < 0 := by
    intro a ha z hz
    exact hD a ha z (by simpa [Polynomial.IsRoot, Dc] using
      (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz))
  have hSc : ∀ a ∈ K,
      (Ac a - Bc a * (Dc a)⁻¹ * Cc a).charpoly =
        qc a * Polynomial.X := by
    intro a ha
    have hDunit : IsUnit (D a).det := isUnit_iff_ne_zero.mpr
      (isHurwitz_det_ne_zero (hD a ha))
    rw [← realSchur_map_complex (A a) (B a) (C a) (D a) hDunit,
      Matrix.charpoly_map, hS a ha, Polynomial.map_mul]
    simp [qc]
  have hqc : ∀ a ∈ K, (qc a).eval 0 ≠ 0 := by
    intro a ha
    change ((q a).map (algebraMap ℝ ℂ)).eval
      ((algebraMap ℝ ℂ) (0 : ℝ)) ≠ 0
    rw [Polynomial.eval_map_apply]
    exact Complex.ofReal_ne_zero.mpr (hq a ha)
  have hSleft : ∀ a ∈ K, ∀ z : ℂ,
      z ∈ spectrum ℂ (Ac a - Bc a * (Dc a)⁻¹ * Cc a) →
        z.re < 0 ∨ z = 0 := by
    intro a ha z hz
    have hroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
    rw [hSc a ha, Polynomial.IsRoot, Polynomial.eval_mul,
      Polynomial.eval_X] at hroot
    rcases mul_eq_zero.mp hroot with hqroot | hz0
    · exact Or.inl (hqleft a ha z hqroot)
    · exact Or.inr hz0
  have htransfer := compact_fastSlow_eventually_simple_zero_hurwitz_complement
    K hK Ac Bc Cc Dc qc hAc hBc hCc hDc hDspec hSc hqc hSleft
  filter_upwards [htransfer] with ε hε a ha hεpos
  simpa only [realFastSlowMatrix_map_complex] using hε a ha hεpos

end

end PhosphorylationStableCapacity
