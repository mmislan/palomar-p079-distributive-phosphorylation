module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCompleteLaw
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.HurwitzNonlinearStability
public import proofs.PhosphorylationStableCapacity.ClassPolytopeTopology

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Polynomial

/-- The sign and transverse gap from the same analytic split branch give
the literal class-Jacobian sink/saddle classification for the paper's
fixed-binding system. -/
theorem paperFixedBinding_completePoint_sink_or_saddle
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε α K δ : ℝ)
    (ω : Fin (m+1) → ℝ)
    (lam : Fin (2*(m+1)+1) → ℝ → ℝ)
    (hα : 0 < α)
    (hpoint : PaperFixedBindingCompletePoint m ξ r τ ε α K δ ω lam)
    (j : Fin (2*(m+1)+1)) :
    (Even j.val →
      IsLinearlyStable (2*r) 2 (2*(r+1))
        (paperFixedBindingSplitRates m ξ r δ ε (Fin.lastCases τ ω))
        (toCoordinateSpace
          (chart (arbitrarySplitFiniteState (m+1) ξ r δ j)))) ∧
    (Odd j.val →
      IsOneUnstableSaddle (2*r) 2 (2*(r+1))
        (paperFixedBindingSplitRates m ξ r δ ε (Fin.lastCases τ ω))
        (toCoordinateSpace
          (chart (arbitrarySplitFiniteState (m+1) ξ r δ j)))) := by
  let k := paperFixedBindingSplitRates m ξ r δ ε (Fin.lastCases τ ω)
  let s := arbitrarySplitFiniteState (m+1) ξ r δ j
  let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k
    (toCoordinateSpace (chart s))
  obtain ⟨_, _, _, _, hj⟩ := hpoint
  obtain ⟨_, _, _, _, _, _, hroot, hsimple, hmargin,
    _, _, hneg, hpos⟩ := hj j
  constructor
  · intro heven
    change IsHurwitz J
    intro z hz
    rcases hmargin z
        (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hz) with heq | hleft
    · rw [heq]
      simpa using hneg heven
    · linarith
  · intro hodd
    change ∃ x : ℝ, 0 < x ∧ J.charpoly.IsRoot x ∧
      ((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ, z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
        z.re < 0 ∨ z = (x : ℂ)
    refine ⟨lam j δ, hpos hodd, hroot, hsimple, ?_⟩
    intro z hz
    rcases hmargin z hz with heq | hleft
    · exact Or.inr heq
    · exact Or.inl (by linarith)

/-- Even members of the very same fixed-binding family are nonlinear
class sinks, with no separate existential construction. -/
theorem paperFixedBinding_completePoint_even_nonlinear_sink
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε α K δ : ℝ)
    (ω : Fin (m+1) → ℝ)
    (lam : Fin (2*(m+1)+1) → ℝ → ℝ)
    (hr : 0 < r) (hα : 0 < α)
    (hpoint : PaperFixedBindingCompletePoint m ξ r τ ε α K δ ω lam)
    (j : Fin (2*(m+1)+1)) (heven : Even j.val) :
    IsLinearlyStable (2*r) 2 (2*(r+1))
      (paperFixedBindingSplitRates m ξ r δ ε (Fin.lastCases τ ω))
      (toCoordinateSpace
        (chart (arbitrarySplitFiniteState (m+1) ξ r δ j))) ∧
    IsLocallyAsymptoticallyStableClass (2*r) 2 (2*(r+1))
      (paperFixedBindingSplitRates m ξ r δ ε (Fin.lastCases τ ω))
      (toCoordinateSpace
        (chart (arbitrarySplitFiniteState (m+1) ξ r δ j))) := by
  let k := paperFixedBindingSplitRates m ξ r δ ε (Fin.lastCases τ ω)
  let s := arbitrarySplitFiniteState (m+1) ξ r δ j
  let u := toCoordinateSpace (chart s)
  have hstable :=
    (paperFixedBinding_completePoint_sink_or_saddle
      m ξ r τ ε α K δ ω lam hα hpoint j).1 heven
  obtain ⟨hk, _, _, _, hj⟩ := hpoint
  obtain ⟨hs, heq, hET, hFT, hST, _⟩ := hj j
  have hclass : InClass (2*r) 2 (2*(r+1)) s :=
    ⟨hET, hFT, hST⟩
  have hback :
      unChart (2*r) 2 (2*(r+1)) (ofCoordinateSpace u) = s := by
    rw [of_toCoordinateSpace]
    exact unChart_chart_of_inClass (2*r) 2 (2*(r+1)) s hclass
  have hfield :
      restrictedFieldEuclid (2*r) 2 (2*(r+1)) k u = 0 := by
    apply (restrictedFieldEuclid_eq_zero_iff
      (2*r) 2 (2*(r+1)) k u).2
    rw [hback]
    exact heq
  have hu : u ∈ classPolytopeStrict (m+2) (2*r) 2 (2*(r+1)) := by
    exact positive_state_mem_classPolytopeStrict
      (2*r) 2 (2*(r+1)) s hs hclass
  exact ⟨hstable,
    isLinearlyStable_locally_asymptotically_stable
      (by omega : 1 ≤ m+2)
      (2*r) 2 (2*(r+1))
      (mul_pos (by norm_num : (0 : ℝ) < 2) hr)
      k hk u hu hfield hstable⟩

end
end PhosphorylationStableCapacity
