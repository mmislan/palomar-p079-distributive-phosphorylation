module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingRouthCertifiedAdmission435
public import proofs.PhosphorylationStableCapacity.PaperOrderedRouthDesignTermination435

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Polynomial Matrix

/-- Complete literal physical, rational, equilibrium, current and spectral
configuration at one actual four-loop output a,b,c,d. This proposition keeps
the exact arithmetic construction and all its witnesses visible. -/
def PaperOrderedRouthCertifiedConfiguration
    (m : ℕ) (ξ : ℕ → ℚ) (a b c d : ℕ) : Prop :=
    let r : ℝ := (((2 : ℚ)^a : ℚ) : ℝ)
    let t : ℝ := (((1/2 : ℚ)^b : ℚ) : ℝ)
    let ε : ℝ := (((1/2 : ℚ)^c : ℚ) : ℝ)
    let δ : ℝ := (((1/2 : ℚ)^d : ℚ) : ℝ)
    let x := coalescedFiniteState (m+1) r
    let τ : ℝ := t/x.D (Fin.last (m+1))
    let θ : Fin (m+1) → ℝ := fun i => 1/x.D i.castSucc
    let w : Fin (m+2) → ℝ := Fin.lastCases (motive := fun _ => ℝ) τ θ
    let k₀ := relaxRates (paperFixedBindingRates (coalescedAllScaledRates m r w)) ε
    let k := paperFixedBindingSplitRates m (fun i => (ξ i : ℝ)) r δ ε w
    let f := arbitrarySplitFiniteState (m+1) (fun i => (ξ i : ℝ)) r δ
    (3*(m+2 : ℝ))/2 ≤ r ∧
      SimpleNeutralHurwitzComplement
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k₀
          (fromLoadedCoord (loadedCoordOfState x))) ∧
      (∀ i : Fin (m+1), k₀.gamma i.castSucc*x.D i.castSucc = 1) ∧
      k₀.gamma (Fin.last (m+1))*x.D (Fin.last (m+1)) = t ∧
      k.Positive ∧ RationalRates k ∧
      (∀ j : Fin (2*(m+1)+1), (f j).Positive ∧ RationalState (f j) ∧
        Equilibrium k (f j) ∧ InClass (2*r) 2 (2*(r+1)) (f j)) ∧
      Function.Injective f ∧
      {s : State (m+2) | s.Positive ∧ Equilibrium k s ∧ InClass (2*r) 2 (2*(r+1)) s} =
        Set.range f ∧
      {s : State (m+2) | s.Positive ∧ Equilibrium k s ∧ InClass (2*r) 2 (2*(r+1)) s}.ncard =
        2*(m+1)+1 ∧
      (∀ j : Fin (2*(m+1)+1), ∀ i : Fin (m+2),
        k.c i*(f j).C i = k.gamma i*(f j).D i ∧
        0 < k.gamma i*(f j).D i ∧ k.gamma i*(f j).D i = w i*(f j).D i) ∧
      ∀ j : Fin (2*(m+1)+1),
        (Even j.val →
          IsLinearlyStable (2*r) 2 (2*(r+1)) k (toCoordinateSpace (chart (f j))) ∧
          IsLocallyAsymptoticallyStableClass (2*r) 2 (2*(r+1)) k
            (toCoordinateSpace (chart (f j)))) ∧
        (Odd j.val → IsOneUnstableSaddle (2*r) 2 (2*(r+1)) k
          (toCoordinateSpace (chart (f j))))

/-- EVERY accepted output of the concrete original four loops yields the
complete configuration. The producer is finite rational arithmetic; its
characteristic casts are proved and no spectral premises are supplied. -/
theorem paperOrderedRouthDesign_certified_configuration
    (m : ℕ) (ξ : ℕ → ℚ) (hξ : StrictMono ξ) (a b c d : ℕ)
    (haccepted : OrderedDesignAccepted
      (orderedRationalPhysicalPrefixTest m (paperRationalPrefixDiagonalAccepts m))
      (paperOrderedSlowRouthAccepts m) (paperOrderedCoalescedRouthAccepts m ξ)
      (orderedRationalPhysicalSplitTest m ξ (paperOrderedSplitRouthAccepts m ξ))
      a b c d) : PaperOrderedRouthCertifiedConfiguration m ξ a b c d := by
  have haccepted' : OrderedDesignAccepted
      (orderedRationalPhysicalPrefixTest m (paperRationalPrefixDiagonalAccepts m))
      (paperOrderedSlowRouthAccepts m)
      (rationalRouthFamilyCoalescedAccepts m (paperOrderedRouthPolynomial m ξ))
      (orderedRationalPhysicalSplitTest m ξ
        (rationalRouthFamilySplitAccepts m (paperOrderedRouthPolynomial m ξ)))
      a b c d := by
    have hcoalesced :
        rationalRouthFamilyCoalescedAccepts m (paperOrderedRouthPolynomial m ξ) =
          paperOrderedCoalescedRouthAccepts m ξ := by
      funext a b c
      rfl
    have hsplit :
        rationalRouthFamilySplitAccepts m (paperOrderedRouthPolynomial m ξ) =
          paperOrderedSplitRouthAccepts m ξ := by
      funext a b c d
      rfl
    rw [hcoalesced, hsplit]
    exact haccepted
  exact orderedRationalRouthDesign_certified_same_family m ξ hξ
    (paperRationalPrefixDiagonalAccepts m) (paperOrderedSlowRouthAccepts m)
    (paperOrderedRouthPolynomial m ξ) (paperOrderedRouthPolynomial_cast m ξ)
    a b c d haccepted'

/-- Complete FIRST-SUCCESS design for every size and strictly ordered
rational offset sequence. The same earliest a,b,c,d satisfy the original
four arithmetic tests AND the whole physical/spectral configuration. -/
theorem paperOrderedRouthDesign_first_acceptance_certified
    (m : ℕ) (ξ : ℕ → ℚ) (hξ : StrictMono ξ) :
    ∃ a b c d : ℕ,
      OrderedDesignAccepted
        (orderedRationalPhysicalPrefixTest m (paperRationalPrefixDiagonalAccepts m))
        (paperOrderedSlowRouthAccepts m) (paperOrderedCoalescedRouthAccepts m ξ)
        (orderedRationalPhysicalSplitTest m ξ (paperOrderedSplitRouthAccepts m ξ))
        a b c d ∧ PaperOrderedRouthCertifiedConfiguration m ξ a b c d := by
  obtain ⟨a, b, c, d, haccepted⟩ := paperOrderedRouthDesign_first_acceptance m ξ hξ
  exact ⟨a, b, c, d, haccepted,
    paperOrderedRouthDesign_certified_configuration m ξ hξ a b c d haccepted⟩

end
end PhosphorylationStableCapacity
