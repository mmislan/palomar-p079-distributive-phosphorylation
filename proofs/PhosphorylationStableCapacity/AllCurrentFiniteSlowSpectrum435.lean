module
public import proofs.PhosphorylationStableCapacity.LoadedPrefixIndependentCurrents435
public import proofs.PhosphorylationStableCapacity.FinalEdgeCharpolyFactor
public import proofs.PhosphorylationStableCapacity.OpenParameterPersistence
public import proofs.PhosphorylationStableCapacity.CoalescedNormalizedKernel

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix Filter Polynomial
open scoped Topology

/-- Hurwitz stability of a matrix survives an arbitrary finite rank-one
perturbation with sufficiently small coefficient. -/
theorem rankOneShearComplement_eventually_hurwitz_of_hurwitz
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (u c : ι → ℝ) (hA : IsHurwitz A) :
    ∀ᶠ τ : ℝ in 𝓝 (0 : ℝ),
      IsHurwitz (rankOneShearComplement A u c τ) := by
  have hcont : Continuous
      (fun τ : ℝ => rankOneShearComplement A u c τ) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun τ : ℝ => A i j - τ * u i * c j)
    fun_prop
  have hzero : rankOneShearComplement A u c 0 = A := by
    ext i j
    simp [rankOneShearComplement]
  exact (hcont.tendsto 0).eventually
    (isOpen_isHurwitz_matrix.mem_nhds (by simpa [hzero] using hA))

/-- Put independent positive prefix weights and a unit final weight into
the complete finite current matrix. -/
def coalescedPrefixWeightedLoadedMatrix (m : ℕ) (r : ℝ)
    (ω : Fin (m+1) → ℝ) :
    Matrix (Fin (m+2)) (Fin (m+2)) ℝ :=
  coalescedFullLoadedMatrix m r *
    Matrix.diagonal (Fin.lastCases 1 ω)

theorem coalescedPrefixWeightedLoadedMatrix_prefix
    (m : ℕ) (r : ℝ) (ω : Fin (m+1) → ℝ)
    (i j : Fin (m+1)) :
    coalescedPrefixWeightedLoadedMatrix m r ω i.castSucc j.castSucc =
      (coalescedPrefixLoadedMatrix m r * Matrix.diagonal ω) i j := by
  rw [coalescedPrefixWeightedLoadedMatrix, Matrix.mul_diagonal,
    coalescedFullLoadedMatrix_prefix, Matrix.mul_diagonal]
  simp

/-- The normalized kernel persists after any positive prefix current
retuning; no perturbative approximation is used here. -/
theorem coalescedPrefixWeightedLoadedMatrix_kernel
    (m : ℕ) (r : ℝ) (ω : Fin (m+1) → ℝ)
    (hω : ∀ i, 0 < ω i)
    (u : Fin (m+2) → ℝ)
    (hulast : u (Fin.last (m+1)) = 1)
    (hKu : (coalescedFullLoadedMatrix m r).mulVec u = 0) :
    ∃ v : Fin (m+2) → ℝ,
      v (Fin.last (m+1)) = 1 ∧
        (coalescedPrefixWeightedLoadedMatrix m r ω).mulVec v = 0 := by
  let w : Fin (m+2) → ℝ := Fin.lastCases 1 ω
  have hw : ∀ i, w i ≠ 0 := by
    intro i
    cases i using Fin.lastCases with
    | last => simp [w]
    | cast i => simpa [w] using (hω i).ne'
  let v : Fin (m+2) → ℝ := fun i => u i / w i
  have hmul : (Matrix.diagonal w).mulVec v = u := by
    funext i
    rw [Matrix.mulVec_diagonal]
    dsimp [v]
    exact mul_div_cancel₀ (u i) (hw i)
  refine ⟨v, ?_, ?_⟩
  · simp [v, w, hulast]
  · change (coalescedFullLoadedMatrix m r * Matrix.diagonal w).mulVec v = 0
    rw [← Matrix.mulVec_mulVec, hmul]
    exact hKu

/-- At each positive prefix current vector, a sufficiently small final
current leaves exactly one neutral mode and a Hurwitz finite slow
complement. The prefix threshold is independent of the vector. -/
theorem coalescedAllCurrentFiniteSlowSpectrum_eventually
    (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (ω : Fin (m+1) → ℝ), (∀ i, 0 < ω i) →
        ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
          ∃ q : ℝ[X],
            (coalescedPrefixWeightedLoadedMatrix m r ω *
              Matrix.diagonal (coalescedFinalCurrentWeights m τ)).charpoly =
                q * Polynomial.X ∧
            q.eval 0 ≠ 0 ∧
              ∀ z : ℂ, (q.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0 := by
  filter_upwards [coalescedPrefixLoadedMatrix_eventually_diagonal_all_currents m,
    coalescedFullLoadedMatrix_eventually_normalized_kernel m]
    with r hprefix hkernel
  intro ω hω
  obtain ⟨u, hulast, hKu⟩ := hkernel
  obtain ⟨v, hvlast, hKv⟩ :=
    coalescedPrefixWeightedLoadedMatrix_kernel m r ω hω u hulast hKu
  have hprefixHurwitz : IsHurwitz
      (fun i j : Fin (m+1) =>
        coalescedPrefixWeightedLoadedMatrix m r ω i.castSucc j.castSucc) := by
    rw [show (fun i j : Fin (m+1) =>
        coalescedPrefixWeightedLoadedMatrix m r ω i.castSucc j.castSucc) =
          coalescedPrefixLoadedMatrix m r * Matrix.diagonal ω by
        ext i j
        exact coalescedPrefixWeightedLoadedMatrix_prefix m r ω i j]
    exact (hprefix ω hω).2.2
  have hτ := rankOneShearComplement_eventually_hurwitz_of_hurwitz
    (fun i j : Fin (m+1) =>
      coalescedPrefixWeightedLoadedMatrix m r ω i.castSucc j.castSucc)
    (fun i => v i.castSucc)
    (fun j => coalescedPrefixWeightedLoadedMatrix m r ω
      (Fin.last (m+1)) j.castSucc)
    hprefixHurwitz
  filter_upwards [hτ.filter_mono nhdsWithin_le_nhds] with τ hτ
  let q := (finalEdgeShearComplement (m+1)
    (coalescedPrefixWeightedLoadedMatrix m r ω) v τ).charpoly
  refine ⟨q, ?_, ?_, ?_⟩
  · exact finalEdgeWeightedMatrix_charpoly_factor (m+1)
      (coalescedPrefixWeightedLoadedMatrix m r ω) v hvlast hKv τ
  · exact isHurwitz_charpoly_eval_zero_ne_zero (by
      simpa only [finalEdgeShearComplement] using hτ)
  · intro z hz
    apply hτ z
    rw [Matrix.charpoly_map]
    exact hz

end

end PhosphorylationStableCapacity
