module
public import proofs.PhosphorylationStableCapacity.ScalarEnergyDecay
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

namespace PhosphorylationStableCapacity

open Set Filter
open scoped Topology

noncomputable section

/-- A scalar energy cannot reach a higher level if its right
derivative is nonpositive at every earlier time below that level.
The proof takes the first point of the closed overlevel set and
applies the derivative monotonicity theorem up to that point. -/
theorem energy_stays_below_of_deriv_nonpos_below
    (g g' : ℝ → ℝ) (L : ℝ)
    (hderiv : ∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt g (g' t) (Ici (0 : ℝ)) t)
    (hnonpos : ∀ t : ℝ, 0 ≤ t → g t < L → g' t ≤ 0)
    (h0 : g 0 < L) :
    ∀ T : ℝ, 0 ≤ T → g T < L := by
  intro T hT
  by_contra hbad
  have hTbad : L ≤ g T := le_of_not_gt hbad
  have hcont : ContinuousOn g (Icc (0 : ℝ) T) := by
    intro t ht
    exact (hderiv t ht.1).continuousWithinAt.mono
      (by intro s hs; exact hs.1)
  let A : Set ℝ := Icc (0 : ℝ) T ∩ g ⁻¹' Ici L
  have hAcompact : IsCompact A := by
    exact (hcont.upperSemicontinuousOn.isCompact_inter_preimage_Ici
      isCompact_Icc L)
  have hAne : A.Nonempty :=
    ⟨T, ⟨⟨hT, le_refl T⟩, hTbad⟩⟩
  have hAbdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
  let t₀ := sInf A
  have ht₀A : t₀ ∈ A := hAcompact.isClosed.csInf_mem hAne hAbdd
  have ht₀0 : 0 ≤ t₀ := ht₀A.1.1
  have ht₀T : t₀ ≤ T := ht₀A.1.2
  have hprior : ∀ s : ℝ, 0 ≤ s → s < t₀ → g s < L := by
    intro s hs0 hst
    by_contra hge
    have hsA : s ∈ A :=
      ⟨⟨hs0, (le_of_lt hst).trans ht₀T⟩,
        le_of_not_gt hge⟩
    exact (not_le_of_gt hst) (csInf_le hAbdd hsA)
  have hcont₀ : ContinuousOn g (Icc (0 : ℝ) t₀) :=
    hcont.mono (by
      intro t ht
      exact ⟨ht.1, ht.2.trans ht₀T⟩)
  have hanti : AntitoneOn g (Icc (0 : ℝ) t₀) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos
      (convex_Icc (0 : ℝ) t₀) hcont₀
    · intro t ht
      rw [interior_Icc, Set.mem_Ioo] at ht
      exact (hderiv t ht.1.le).mono
        (by
          intro s hs
          rw [interior_Icc, Set.mem_Ioo] at hs
          exact hs.1.le)
    · intro t ht
      rw [interior_Icc, Set.mem_Ioo] at ht
      exact hnonpos t ht.1.le (hprior t ht.1.le ht.2)
  have hle : g t₀ ≤ g 0 :=
    hanti ⟨le_refl 0, ht₀0⟩
      ⟨ht₀0, le_refl t₀⟩ ht₀0
  exact (not_lt_of_ge (ht₀A.2.trans hle)) h0

end
end PhosphorylationStableCapacity
