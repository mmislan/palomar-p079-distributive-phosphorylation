module
public import proofs.PhosphorylationStableCapacity.FiniteSmallGainSpectralChecker
public import proofs.PhosphorylationStableCapacity.SmallGainEvenSinkFromOrientation

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- A positive characteristic constant and a finite checked small-gain
certificate exclude every nonnegative-real-part eigenvalue. -/
theorem finiteSmallGain_even_hurwitz {n : ℕ} [NeZero n]
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
    (hgain : K * W < μ)
    (hconstant : 0 < A.charpoly.coeff 0) :
    ∀ z : ℂ, ((A.map (algebraMap ℝ ℂ)).charpoly).eval z = 0 → z.re < 0 := by
  obtain ⟨hunique, hsimple⟩ :=
    finiteSmallGain_unique_and_simple A B μ C W K hμ hchar
      hrow hcol hCW hW hfeedback hgain
  have hunique' : ∀ z z' : ℂ, 0 ≤ z.re → 0 ≤ z'.re →
      (A.charpoly.map (algebraMap ℝ ℂ)).eval z = 0 →
      (A.charpoly.map (algebraMap ℝ ℂ)).eval z' = 0 → z = z' := by
    simpa only [Matrix.charpoly_map] using hunique
  have hsimple' : ∀ z : ℂ, 0 ≤ z.re →
      (A.charpoly.map (algebraMap ℝ ℂ)).eval z = 0 →
      ((A.charpoly.map (algebraMap ℝ ℂ)).derivative).eval z ≠ 0 := by
    simpa only [Matrix.charpoly_map] using hsimple
  have hpositive := monic_hurwitz_of_unique_simple_right_and_positive_constant
    A.charpoly (Matrix.charpoly_monic A) hconstant hunique' hsimple'
  simpa only [Matrix.charpoly_map] using hpositive

end
end PhosphorylationStableCapacity
