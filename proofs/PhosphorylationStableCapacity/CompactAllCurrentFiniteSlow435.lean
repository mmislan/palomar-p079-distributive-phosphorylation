module
public import proofs.PhosphorylationStableCapacity.AllCurrentFiniteSlowSpectrum435
public import proofs.PhosphorylationStableCapacity.CompactCurrentShear435
public import proofs.PhosphorylationStableCapacity.PositivePrefixCurrents435

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix Filter Polynomial
open scoped Topology Matrix.Norms.L2Operator

private theorem continuous_coalescedPrefixWeightedLoadedMatrix
    (m : ℕ) (r : ℝ) :
    Continuous (fun ω : PositivePrefixCurrents m =>
      coalescedPrefixWeightedLoadedMatrix m r ω.val) := by
  apply continuous_matrix
  intro i j
  have hw : Continuous (fun ω : PositivePrefixCurrents m =>
      Fin.lastCases (motive := fun _ => ℝ) (1 : ℝ) ω.val j) := by
    cases j using Fin.lastCases with
    | last =>
        simpa using (continuous_const : Continuous
          (fun _ : PositivePrefixCurrents m => (1 : ℝ)))
    | cast q =>
        have hproj : Continuous (fun f : Fin (m+1) → ℝ => f q) :=
          continuous_apply q
        have hval : Continuous (fun ω : PositivePrefixCurrents m => ω.val) :=
          continuous_subtype_val
        simpa [Function.comp_def] using hproj.comp hval
  have hmul : Continuous
      (fun ω : PositivePrefixCurrents m =>
        coalescedFullLoadedMatrix m r i j *
          Fin.lastCases (1 : ℝ) ω.val j) := by
    have hprod :=
      (continuous_const : Continuous
        (fun _ : PositivePrefixCurrents m =>
          coalescedFullLoadedMatrix m r i j)).mul hw
    convert hprod using 1
  simpa [coalescedPrefixWeightedLoadedMatrix, Matrix.mul_diagonal] using hmul

private theorem continuous_normalized_prefix_kernel
    (m : ℕ) (u : Fin (m+2) → ℝ) :
    Continuous (fun ω : PositivePrefixCurrents m =>
      fun i : Fin (m+1) => u i.castSucc / ω.val i) := by
  apply continuous_pi
  intro i
  have hi : Continuous (fun ω : PositivePrefixCurrents m => ω.val i) :=
    (continuous_apply i).comp continuous_subtype_val
  exact continuous_const.div hi (fun ω => ne_of_gt (ω.property i))

/-- The final-edge shear has one positive-current-independent threshold
on every compact family of independent prefix currents. -/
theorem compact_coalescedAllCurrentFiniteSlowSpectrum
    (m : ℕ) (r : ℝ)
    (K : Set (PositivePrefixCurrents m)) (hK : IsCompact K)
    (hprefix : ∀ ω : PositivePrefixCurrents m,
      IsHurwitz (coalescedPrefixLoadedMatrix m r *
        Matrix.diagonal ω.val))
    (u : Fin (m+2) → ℝ)
    (hulast : u (Fin.last (m+1)) = 1)
    (hKu : (coalescedFullLoadedMatrix m r).mulVec u = 0) :
    ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ω ∈ K, ∃ q : ℝ[X],
        (coalescedPrefixWeightedLoadedMatrix m r ω.val *
          Matrix.diagonal (coalescedFinalCurrentWeights m τ)).charpoly =
            q * Polynomial.X ∧
        q.eval 0 ≠ 0 ∧
          ∀ z : ℂ, (q.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0 := by
  let A : PositivePrefixCurrents m → Matrix (Fin (m+1)) (Fin (m+1)) ℝ :=
    fun ω => fun i j =>
      coalescedPrefixWeightedLoadedMatrix m r ω.val i.castSucc j.castSucc
  let v : PositivePrefixCurrents m → Fin (m+1) → ℝ :=
    fun ω i => u i.castSucc / ω.val i
  let c : PositivePrefixCurrents m → Fin (m+1) → ℝ :=
    fun ω j => coalescedPrefixWeightedLoadedMatrix m r ω.val
      (Fin.last (m+1)) j.castSucc
  have hA : Continuous A := by
    apply continuous_matrix
    intro i j
    exact ((continuous_apply j.castSucc).comp
      (continuous_apply i.castSucc)).comp
        (continuous_coalescedPrefixWeightedLoadedMatrix m r)
  have hv : Continuous v := continuous_normalized_prefix_kernel m u
  have hc : Continuous c := by
    apply continuous_pi
    intro j
    exact ((continuous_apply j.castSucc).comp
      (continuous_apply (Fin.last (m+1)))).comp
        (continuous_coalescedPrefixWeightedLoadedMatrix m r)
  have hshear : Continuous (fun p : PositivePrefixCurrents m × ℝ =>
      rankOneShearComplement (A p.1) (v p.1) (c p.1) p.2) := by
    apply continuous_matrix
    intro i j
    change Continuous (fun p : PositivePrefixCurrents m × ℝ =>
      A p.1 i j - p.2 * v p.1 i * c p.1 j)
    fun_prop
  have hAh : ∀ ω ∈ K, IsHurwitz (A ω) := by
    intro ω hω
    change IsHurwitz (fun i j : Fin (m+1) =>
      coalescedPrefixWeightedLoadedMatrix m r ω.val
        i.castSucc j.castSucc)
    rw [show (fun i j : Fin (m+1) =>
        coalescedPrefixWeightedLoadedMatrix m r ω.val
          i.castSucc j.castSucc) =
        coalescedPrefixLoadedMatrix m r * Matrix.diagonal ω.val by
      ext i j
      exact coalescedPrefixWeightedLoadedMatrix_prefix m r ω.val i j]
    exact hprefix ω
  have hτ := compact_rankOneShear_eventually_hurwitz
    K hK A v c hAh hshear
  filter_upwards [hτ.filter_mono nhdsWithin_le_nhds] with τ hτ ω hω
  let w : Fin (m+2) → ℝ := Fin.lastCases 1 ω.val
  let vfull : Fin (m+2) → ℝ := fun i => u i / w i
  have hw : ∀ i, w i ≠ 0 := by
    intro i
    cases i using Fin.lastCases with
    | last => simp [w]
    | cast i => simpa [w] using (ω.property i).ne'
  have hvfull : vfull (Fin.last (m+1)) = 1 := by
    simp [vfull, w, hulast]
  have hvprefix (i : Fin (m+1)) : vfull i.castSucc = v ω i := by
    simp [vfull, v, w]
  have hdiag : (Matrix.diagonal w).mulVec vfull = u := by
    funext i
    rw [Matrix.mulVec_diagonal]
    dsimp [vfull]
    exact mul_div_cancel₀ (u i) (hw i)
  have hkernel :
      (coalescedPrefixWeightedLoadedMatrix m r ω.val).mulVec vfull = 0 := by
    change (coalescedFullLoadedMatrix m r * Matrix.diagonal w).mulVec vfull = 0
    rw [← Matrix.mulVec_mulVec, hdiag]
    exact hKu
  let q := (finalEdgeShearComplement (m+1)
    (coalescedPrefixWeightedLoadedMatrix m r ω.val) vfull τ).charpoly
  refine ⟨q, ?_, ?_, ?_⟩
  · exact finalEdgeWeightedMatrix_charpoly_factor (m+1)
      (coalescedPrefixWeightedLoadedMatrix m r ω.val)
      vfull hvfull hkernel τ
  · apply isHurwitz_charpoly_eval_zero_ne_zero
    simpa only [finalEdgeShearComplement, A, v, c, hvprefix] using hτ ω hω
  · intro z hz
    have hstable : IsHurwitz (finalEdgeShearComplement (m+1)
        (coalescedPrefixWeightedLoadedMatrix m r ω.val) vfull τ) := by
      simpa only [finalEdgeShearComplement, A, v, c, hvprefix]
        using hτ ω hω
    apply hstable z
    rw [Matrix.charpoly_map]
    exact hz

/-- The source scale r can be chosen once for every compact family of
positive independent prefix currents; the final-current threshold is
then common to the whole family. -/
theorem coalescedAllCurrentFiniteSlowSpectrum_compact_eventually
    (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (K : Set (PositivePrefixCurrents m)), IsCompact K →
        ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
          ∀ ω ∈ K, ∃ q : ℝ[X],
            (coalescedPrefixWeightedLoadedMatrix m r ω.val *
              Matrix.diagonal (coalescedFinalCurrentWeights m τ)).charpoly =
                q * Polynomial.X ∧
            q.eval 0 ≠ 0 ∧
              ∀ z : ℂ, (q.map (algebraMap ℝ ℂ)).eval z = 0 →
                z.re < 0 := by
  filter_upwards [coalescedPrefixLoadedMatrix_eventually_diagonal_all_currents m,
    coalescedFullLoadedMatrix_eventually_normalized_kernel m]
    with r hprefix hkernel
  intro K hK
  obtain ⟨u, hulast, hKu⟩ := hkernel
  apply compact_coalescedAllCurrentFiniteSlowSpectrum m r K hK
    (fun ω => (hprefix ω.val ω.property).2.2) u hulast hKu

end

end PhosphorylationStableCapacity
