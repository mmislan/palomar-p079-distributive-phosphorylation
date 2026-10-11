module
public import proofs.PhosphorylationStableCapacity.SaddleSmallGainMatrix
public import proofs.PhosphorylationStableCapacity.SaddleSmallGainSimpleSpectrum
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The reusable soundness theorem for a finite rational similarity
certificate. Each instance still has to prove its characteristic-polynomial
identity and the three row/coupling inequalities. -/
theorem finiteSmallGain_unique_and_simple {n : ℕ} [NeZero n]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (μ C W K : ℝ) (hμ : 0 < μ)
    (hchar : B.charpoly = (A.map (algebraMap ℝ ℂ)).charpoly)
    (hrow : ∀ i : Fin n,
      (B i.succ i.succ).re +
        ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          ‖B i.succ j.succ‖ ≤ -μ)
    (hcol : ∀ i : Fin n, ‖B i.succ 0‖ ≤ C)
    (hCW : C ≤ μ * W) (hW : 0 ≤ W)
    (hfeedback : (∑ i : Fin n, ‖B 0 i.succ‖) ≤ K)
    (hgain : K * W < μ) :
    (∀ z z' : ℂ, 0 ≤ z.re → 0 ≤ z'.re →
      ((A.map (algebraMap ℝ ℂ)).charpoly).eval z = 0 →
      ((A.map (algebraMap ℝ ℂ)).charpoly).eval z' = 0 → z = z') ∧
    (∀ z : ℂ, 0 ≤ z.re →
      ((A.map (algebraMap ℝ ℂ)).charpoly).eval z = 0 →
      ((A.map (algebraMap ℝ ℂ)).charpoly).derivative.eval z ≠ 0) := by
  constructor
  · intro z z' hz hz' hr hr'
    apply block_spectrum_unique_right B μ C W K hμ hrow hcol hCW hW
      hfeedback hgain z z' hz hz'
    · simpa only [hchar] using hr
    · simpa only [hchar] using hr'
  · intro z hz hr
    have hrootB : B.charpoly.eval z = 0 := by
      simpa only [hchar] using hr
    have hsimpleB := block_spectrum_simple_right B μ C W K
      hμ hrow hcol hCW hW hfeedback hgain z hz hrootB
    simpa only [hchar] using hsimpleB

/-- Assemble the paper's one-unstable spectral claim from a positive real
root and a checked unique/simple right-half-plane certificate. -/
theorem one_unstable_spectrum_of_unique_simple_root
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ)
    (hroot : ∃ x : ℝ, 0 < x ∧ A.charpoly.IsRoot x)
    (hunique : ∀ z z' : ℂ, 0 ≤ z.re → 0 ≤ z'.re →
      ((A.map (algebraMap ℝ ℂ)).charpoly).eval z = 0 →
      ((A.map (algebraMap ℝ ℂ)).charpoly).eval z' = 0 → z = z')
    (hsimple : ∀ z : ℂ, 0 ≤ z.re →
      ((A.map (algebraMap ℝ ℂ)).charpoly).eval z = 0 →
      ((A.map (algebraMap ℝ ℂ)).charpoly).derivative.eval z ≠ 0) :
    ∃ x : ℝ, 0 < x ∧ A.charpoly.IsRoot x ∧
      ((A.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ, z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) →
        z.re < 0 ∨ z = (x : ℂ) := by
  obtain ⟨x, hx, hr⟩ := hroot
  have hrootC : ((A.map (algebraMap ℝ ℂ)).charpoly).eval (x : ℂ) = 0 := by
    rw [Matrix.charpoly_map]
    calc
      (A.charpoly.map (algebraMap ℝ ℂ)).eval (x : ℂ) =
          ((A.charpoly.eval x : ℝ) : ℂ) := by
            simpa using (Polynomial.eval_map_apply
              (p := A.charpoly) (f := algebraMap ℝ ℂ) x)
      _ = 0 := by
        have hr' : A.charpoly.eval x = 0 := hr
        exact_mod_cast hr'
  refine ⟨x, hx, hr, hsimple (x : ℂ) (by exact_mod_cast hx.le) hrootC, ?_⟩
  intro z hz
  by_cases hneg : z.re < 0
  · exact Or.inl hneg
  · right
    apply hunique z (x : ℂ) (le_of_not_gt hneg)
      (by exact_mod_cast hx.le)
    · exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
    · exact hrootC

end
end PhosphorylationStableCapacity
