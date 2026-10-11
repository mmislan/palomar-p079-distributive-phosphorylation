module
public import proofs.PhosphorylationStableCapacity.ContinuousNeutralMatrixFamily435
public import proofs.PhosphorylationStableCapacity.CompactLocalPersistence435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial Filter
open scoped Topology

/-- A compact family of simple zero eigenvalues has a real eigenvalue
inside any prescribed small ball throughout one common perturbation
interval. No eigenvalue selection continuity is assumed. -/
theorem compact_jointNeutralMatrix_small_real_root
    {β ι : Type*} [PseudoMetricSpace β]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (K : Set β) (hK : IsCompact K)
    (J : β × ℝ → Matrix ι ι ℝ)
    (hJ : ∀ b ∈ K, ContinuousAt J (b, 0))
    (hspec : ∀ b ∈ K, SimpleNeutralHurwitzComplement (J (b, 0)))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ b ∈ K, ∃ x : ℝ,
        |x| < η ∧ (J (b, δ)).charpoly.IsRoot x := by
  let S : Set (β × ℝ) :=
    {p | ∃ x : ℝ, |x| < η ∧ (J p).charpoly.IsRoot x}
  have hlocal : ∀ b ∈ K, S ∈ 𝓝 (b, 0) := by
    intro b hb
    have hzero : (J (b, 0)).charpoly.coeff 0 = 0 :=
      simpleNeutral_real_charpoly_coeff_zero _ (hspec b hb)
    have hsimple : (J (b, 0)).charpoly.coeff 1 ≠ 0 :=
      simpleNeutral_real_charpoly_coeff_one_ne_zero _ (hspec b hb)
    have heval (x : ℝ) : ContinuousAt
        (fun p : β × ℝ => (J p).charpoly.eval x) (b, 0) :=
      (continuousAt_matrix_charpoly_eval (J (b, 0)) x).comp (hJ b hb)
    have hroot := polynomial_simple_zero_real_root_eventually_at
      (fun p : β × ℝ => (J p).charpoly) (b, 0)
      hzero hsimple heval η hη
    filter_upwards [hroot] with p hp
    exact hp
  exact compact_eventually_of_local_neighborhoods K hK 0 S hlocal

/-- A selected real eigenvalue with a uniform transverse margin is the
small real root supplied by compact persistence. Thus it approaches
zero uniformly without choosing eigenvalues continuously. -/
theorem compact_jointNeutralMatrix_selected_root_small
    {β ι : Type*} [PseudoMetricSpace β]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (K : Set β) (hK : IsCompact K)
    (J : β × ℝ → Matrix ι ι ℝ)
    (hJ : ∀ b ∈ K, ContinuousAt J (b, 0))
    (hspec : ∀ b ∈ K, SimpleNeutralHurwitzComplement (J (b, 0)))
    (α : ℝ) (hα : 0 < α)
    (hgap : ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ b ∈ K, ∃ lam : ℝ,
        (J (b, δ)).charpoly.IsRoot lam ∧
        (((J (b, δ)).map (algebraMap ℝ ℂ)).charpoly).derivative.eval
          (lam : ℂ) ≠ 0 ∧
        ∀ z : ℂ,
          z ∈ spectrum ℂ ((J (b, δ)).map (algebraMap ℝ ℂ)) →
            z = (lam : ℂ) ∨ z.re ≤ -α)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ b ∈ K, ∃ lam : ℝ,
        |lam| < η ∧ (J (b, δ)).charpoly.IsRoot lam ∧
        (((J (b, δ)).map (algebraMap ℝ ℂ)).charpoly).derivative.eval
          (lam : ℂ) ≠ 0 ∧
        ∀ z : ℂ,
          z ∈ spectrum ℂ ((J (b, δ)).map (algebraMap ℝ ℂ)) →
            z = (lam : ℂ) ∨ z.re ≤ -α := by
  let ρ := min η (α/2)
  have hρ : 0 < ρ := lt_min hη (by positivity)
  have hsmall := compact_jointNeutralMatrix_small_real_root
    K hK J hJ hspec ρ hρ
  filter_upwards [hgap, hsmall] with δ hgapδ hsmallδ b hb
  obtain ⟨lam, hroot, hsimple, hrest⟩ := hgapδ b hb
  obtain ⟨x, hx, hxroot⟩ := hsmallδ b hb
  have hxspec : (x : ℂ) ∈
      spectrum ℂ ((J (b, δ)).map (algebraMap ℝ ℂ)) := by
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    simpa only [Matrix.charpoly_map, ← Complex.coe_algebraMap] using
      (Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) hxroot)
  have hsame : x = lam := by
    rcases hrest x hxspec with heq | hleft
    · exact_mod_cast heq
    · have hρbound : ρ ≤ α/2 := min_le_right ..
      have hxlower : -|x| ≤ x := neg_abs_le x
      have hxsmall : |x| < α/2 := lt_of_lt_of_le hx hρbound
      simp only [Complex.ofReal_re] at hleft
      linarith
  refine ⟨lam, ?_, hroot, hsimple, hrest⟩
  rw [← hsame]
  exact lt_of_lt_of_le hx (min_le_left ..)

end

end PhosphorylationStableCapacity
