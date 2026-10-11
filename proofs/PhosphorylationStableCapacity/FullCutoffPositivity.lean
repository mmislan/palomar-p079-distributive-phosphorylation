module
public import proofs.PhosphorylationStableCapacity.FullFieldCutoff
public import proofs.PhosphorylationStableCapacity.NegativeDerivativeBarrier

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- A global solution of the nonnegative species cutoff, starting with
nonnegative concentrations, stays in the nonnegative orthant. This
uses the literal inward-face theorem at the clamped state. -/
theorem full_cutoff_curve_nonnegative {n : ℕ}
    (k : Rates n) (hk : k.Positive)
    (B : ℝ) (hB : 0 ≤ B)
    (γ : ℝ → FullSpace n)
    (hγ : ∀ t : ℝ,
      HasDerivAt γ
        (fullFieldEuclid k (clampFullSpace B (γ t))) t)
    (h0 : NonnegativeState (ofFullSpace (γ 0))) :
    ∀ t : ℝ, 0 ≤ t →
      NonnegativeState (ofFullSpace (γ t)) := by
  have hin (t : ℝ) := nonnegative_state_field_inward k
    (ofFullSpace (clampFullSpace B (γ t))) hk
    (clampFullSpace_nonnegative B (γ t))
  have hs (i : Fin (n+1)) :
      ∀ t : ℝ, 0 ≤ t → 0 ≤ (γ t).1 i := by
    let g : ℝ → ℝ := fun t => (γ t).1 i
    have hgd (t : ℝ) :
        HasDerivAt g
          ((fullFieldEuclid k (clampFullSpace B (γ t))).1 i) t := by
      simpa [g] using
        (hasDerivAt_pi.mp ((hγ t).hasFDerivAt.fst.hasDerivAt)) i
    apply nonnegative_of_deriv_nonneg_when_negative
    · intro t
      rw [(hgd t).deriv]
      exact hgd t
    · intro t ht
      rw [(hgd t).deriv]
      have hzero :
          (ofFullSpace (clampFullSpace B (γ t))).S i = 0 := by
        exact clampSpecies_eq_zero_of_neg B ((γ t).1 i) hB ht
      exact (hin t).1 i hzero
    · exact h0.1 i
  have he : ∀ t : ℝ, 0 ≤ t → 0 ≤ (γ t).2.1.1 := by
    let g : ℝ → ℝ := fun t => (γ t).2.1.1
    have hgd (t : ℝ) :
        HasDerivAt g
          (fullFieldEuclid k (clampFullSpace B (γ t))).2.1.1 t := by
      simpa [g] using
        (hγ t).hasFDerivAt.snd.fst.fst.hasDerivAt
    apply nonnegative_of_deriv_nonneg_when_negative
    · intro t
      rw [(hgd t).deriv]
      exact hgd t
    · intro t ht
      rw [(hgd t).deriv]
      have hzero :
          (ofFullSpace (clampFullSpace B (γ t))).E = 0 :=
        clampSpecies_eq_zero_of_neg B ((γ t).2.1.1) hB ht
      exact (hin t).2.1 hzero
    · exact h0.2.1
  have hf : ∀ t : ℝ, 0 ≤ t → 0 ≤ (γ t).2.1.2 := by
    let g : ℝ → ℝ := fun t => (γ t).2.1.2
    have hgd (t : ℝ) :
        HasDerivAt g
          (fullFieldEuclid k (clampFullSpace B (γ t))).2.1.2 t := by
      simpa [g] using
        (hγ t).hasFDerivAt.snd.fst.snd.hasDerivAt
    apply nonnegative_of_deriv_nonneg_when_negative
    · intro t
      rw [(hgd t).deriv]
      exact hgd t
    · intro t ht
      rw [(hgd t).deriv]
      have hzero :
          (ofFullSpace (clampFullSpace B (γ t))).F = 0 :=
        clampSpecies_eq_zero_of_neg B ((γ t).2.1.2) hB ht
      exact (hin t).2.2.1 hzero
    · exact h0.2.2.1
  have hc (i : Fin n) :
      ∀ t : ℝ, 0 ≤ t → 0 ≤ (γ t).2.2.1 i := by
    let g : ℝ → ℝ := fun t => (γ t).2.2.1 i
    have hgd (t : ℝ) :
        HasDerivAt g
          ((fullFieldEuclid k (clampFullSpace B (γ t))).2.2.1 i) t := by
      simpa [g] using
        (hasDerivAt_pi.mp
          ((hγ t).hasFDerivAt.snd.snd.fst.hasDerivAt)) i
    apply nonnegative_of_deriv_nonneg_when_negative
    · intro t
      rw [(hgd t).deriv]
      exact hgd t
    · intro t ht
      rw [(hgd t).deriv]
      have hzero :
          (ofFullSpace (clampFullSpace B (γ t))).C i = 0 :=
        clampSpecies_eq_zero_of_neg B ((γ t).2.2.1 i) hB ht
      exact (hin t).2.2.2.1 i hzero
    · exact h0.2.2.2.1 i
  have hd (i : Fin n) :
      ∀ t : ℝ, 0 ≤ t → 0 ≤ (γ t).2.2.2 i := by
    let g : ℝ → ℝ := fun t => (γ t).2.2.2 i
    have hgd (t : ℝ) :
        HasDerivAt g
          ((fullFieldEuclid k (clampFullSpace B (γ t))).2.2.2 i) t := by
      simpa [g] using
        (hasDerivAt_pi.mp
          ((hγ t).hasFDerivAt.snd.snd.snd.hasDerivAt)) i
    apply nonnegative_of_deriv_nonneg_when_negative
    · intro t
      rw [(hgd t).deriv]
      exact hgd t
    · intro t ht
      rw [(hgd t).deriv]
      have hzero :
          (ofFullSpace (clampFullSpace B (γ t))).D i = 0 :=
        clampSpecies_eq_zero_of_neg B ((γ t).2.2.2 i) hB ht
      exact (hin t).2.2.2.2 i hzero
    · exact h0.2.2.2.2 i
  intro t ht
  exact ⟨fun i => hs i t ht, he t ht, hf t ht,
    fun i => hc i t ht, fun i => hd i t ht⟩

end
end PhosphorylationStableCapacity
