module
public import proofs.PhosphorylationStableCapacity.LocalRouthAlternation435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingPrefactorDifferentiability
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitGenericPrefactorZero435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitRootGapParity
public import proofs.PhosphorylationStableCapacity.SimpleNeutralPositiveCoefficient435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCoalescence435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Filter
open scoped Topology

/-- The polynomial actually tested in the paper's final ordered loop. -/
def paperFixedBindingRouthPolynomial
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε δ : ℝ)
    (ω : Fin (m+1) → ℝ) (j : Fin (2*(m+1)+1)) : ℝ[X] :=
  (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
    (paperFixedBindingSplitRates m ξ r δ ε (Fin.lastCases τ ω))
    (toCoordinateSpace (chart
      (arbitrarySplitFiniteState (m+1) ξ r δ j)))).charpoly

/-- The exact constant-term sign required by both branches of the local
Routh test, proved from the positive physical prefactor and root gap.
The odd branch is included and uses the same literal kinetic family. -/
theorem paperFixedBinding_routh_constant_alternates
    (m : ℕ) (ξ : ℕ → ℝ) (hξ : StrictMono ξ)
    (r τ ε : ℝ) (ω : Fin (m+1) → ℝ)
    (hω : ∀ i, 0 < ω i) (hr : 1 < r)
    (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : (coalescedAllScaledRates m r (Fin.lastCases τ ω)).Positive)
    (hk₀ : (relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε).Positive)
    (hx₀ : (coalescedFiniteState (m+1) r).Positive)
    (heq₀ : Equilibrium (relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
      (coalescedFiniteState (m+1) r))
    (hET₀ : totalE (coalescedFiniteState (m+1) r) = 2*r)
    (hFT₀ : totalF (coalescedFiniteState (m+1) r) = 2) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j : Fin (2*(m+1)+1),
        (Even j.val → 0 < (paperFixedBindingRouthPolynomial m ξ r τ ε δ ω j).coeff 0) ∧
        (Odd j.val → (paperFixedBindingRouthPolynomial m ξ r τ ε δ ω j).coeff 0 < 0) := by
  apply Filter.eventually_all.mpr
  intro j
  let w : Fin (m+2) → ℝ := Fin.lastCases τ ω
  let k : ℝ → Rates (m+2) := fun δ => paperFixedBindingSplitRates m ξ r δ ε w
  let c : ℝ → ℝ := fun δ => arbitrarySplitGenericPhysicalPrefactor m ξ r δ (k δ) j
  have hkzero : k 0 = relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r w)) ε := by
    simp [k, paperFixedBindingSplitRates, coalescedAllScaledRates,
      arbitrarySplitFiniteRates_zero_eq_coalesced]
  have hc₀ : 0 < c 0 := by
    apply arbitrarySplitGenericPhysicalPrefactor_zero_pos m ξ r (k 0) j hr hD₀
    · rw [hkzero]
      exact hk₀
    · exact hx₀
    · rw [hkzero]
      exact heq₀
    · exact hET₀
    · exact hFT₀
  have hc : ContinuousAt c 0 :=
    (paperFixedBindingSplit_genericPrefactor_differentiableAt
      m ξ r τ ε ω hr hD₀ hB₀ hbase j).continuousAt
  have hcpos : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < c δ :=
    (hc.eventually (Ioi_mem_nhds hc₀)).filter_mono nhdsWithin_le_nhds
  have hconv := (arbitrarySplit_conversion_positive_near_zero
    (m+1) ξ r (ne_of_gt (lt_trans zero_lt_one hr)) hD₀ hB₀)
  have hy := (offsetSplitRoot_gt_one_eventually (m+1) ξ).filter_mono
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hv : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      0 < r-ratio (offsetSplitRoot ξ δ j.val) := by
    have hcont : ContinuousAt (fun δ : ℝ => r-ratio (offsetSplitRoot ξ δ j.val)) 0 := by
      unfold ratio offsetSplitRoot
      fun_prop
    have hzero : 0 < r-ratio (offsetSplitRoot ξ 0 j.val) := by
      norm_num [ratio, offsetSplitRoot]
      linarith
    exact (hcont.eventually (Ioi_mem_nhds hzero)).filter_mono nhdsWithin_le_nhds
  have hw : ∀ i : Fin (m+2), 0 < w i := by
    intro i
    cases i using Fin.lastCases with
    | last => simpa [w] using hτ
    | cast i => simpa [w] using hω i
  filter_upwards [hcpos, hconv, hy, hv, self_mem_nhdsWithin]
    with δ hcpos hconv hy hv hδ
  have hyj := hy j.val (by omega)
  obtain ⟨hk, _, heq, hclass⟩ := paperFixedBindingSplit_source
    m ξ r δ ε w hw hε hε1 hconv.1 hconv.2 j hyj
  have hconstant := arbitrarySplitGeneric_charpoly_constant_root_gap
    m ξ r δ (k δ) hk hconv.1 hconv.2 j hyj hv heq
      hclass.1 hclass.2.1 hclass.2.2
  have hgap := arbitrary_offset_root_gap_alternates (m+1) ξ hξ j
  constructor
  · intro heven
    change 0 < (restrictedJacobianMatrix (2*r) 2 (2*(r+1)) (k δ)
      (toCoordinateSpace (chart (arbitrarySplitFiniteState (m+1) ξ r δ j)))).charpoly.coeff 0
    rw [hconstant]
    exact mul_pos hcpos (mul_pos (pow_pos hδ _) (hgap.1 heven))
  · intro hodd
    change (restrictedJacobianMatrix (2*r) 2 (2*(r+1)) (k δ)
      (toCoordinateSpace (chart (arbitrarySplitFiniteState (m+1) ξ r δ j)))).charpoly.coeff 0 < 0
    rw [hconstant]
    exact mul_neg_of_pos_of_neg hcpos
      (mul_neg_of_pos_of_neg (pow_pos hδ _) (hgap.2 hodd))

/-- Local Routh arithmetic completeness for the actual fixed-binding
family, under the exact coalesced-deflation Hurwitz-minor premise. This
isolates the classical Routh necessity input from all network inputs;
no odd-spectrum premise has been replaced by a Hurwitz-only checker. -/
theorem paperFixedBinding_routh_pattern_has_halving_index
    (m : ℕ) (ξ : ℕ → ℝ) (hξ : StrictMono ξ)
    (r τ ε : ℝ) (ω : Fin (m+1) → ℝ)
    (hω : ∀ i, 0 < ω i) (hr : 1 < r)
    (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : (coalescedAllScaledRates m r (Fin.lastCases τ ω)).Positive)
    (hk₀ : (relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε).Positive)
    (hx₀ : (coalescedFiniteState (m+1) r).Positive)
    (heq₀ : Equilibrium (relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
      (coalescedFiniteState (m+1) r))
    (hET₀ : totalE (coalescedFiniteState (m+1) r) = 2*r)
    (hFT₀ : totalF (coalescedFiniteState (m+1) r) = 2)
    (hspec : SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
        (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r)))))
    (hq : let p₀ := (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
        (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r)))).charpoly
      ∀ k : Fin (3*(m+2)-1),
        0 < routhHurwitzMinor (3*(m+2)-1) (k.val+1) p₀.divX) :
    ∃ b : ℕ, ∀ j : Fin (2*(m+1)+1),
      (∀ k : Fin (3*(m+2)-1),
        0 < routhHurwitzMinor (3*(m+2)) (k.val+1)
          (paperFixedBindingRouthPolynomial m ξ r τ ε ((1/2 : ℝ)^b) ω j)) ∧
      (if decide (Odd j.val) then
        (paperFixedBindingRouthPolynomial m ξ r τ ε ((1/2 : ℝ)^b) ω j).coeff 0 < 0
      else 0 < (paperFixedBindingRouthPolynomial m ξ r τ ε ((1/2 : ℝ)^b) ω j).coeff 0) := by
  let J₀ := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
    (relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
    (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r)))
  let q : ℝ[X] := J₀.charpoly.divX
  have hpzero : J₀.charpoly.coeff 0 = 0 :=
    simpleNeutral_real_charpoly_coeff_zero J₀ hspec
  have hfactor : J₀.charpoly = Polynomial.X*q := by
    have h := (Polynomial.X_mul_divX_add J₀.charpoly).symm
    simpa [q, hpzero] using h
  let P : Fin (2*(m+1)+1) → ℝ → ℝ[X] :=
    fun j δ => paperFixedBindingRouthPolynomial m ξ r τ ε δ ω j
  have hzero : ∀ j, P j 0 = Polynomial.X*q := by
    intro j
    have h := congrArg Matrix.charpoly
      (paperFixedBindingSplit_restrictedJacobianMatrix_zero_eq_coalesced
        m ξ r ε (Fin.lastCases τ ω) j)
    change P j 0 = J₀.charpoly at h
    exact h.trans hfactor
  have hcoeff : ∀ j n, ContinuousAt (fun δ => (P j δ).coeff n) 0 := by
    intro j n
    exact (paperFixedBindingSplit_charpoly_coeff_differentiableAt
      m ξ r τ ε ω (ne_of_gt (lt_trans zero_lt_one hr)) hD₀ hB₀ hbase j n).continuousAt
  have hconstant := paperFixedBinding_routh_constant_alternates
    m ξ hξ r τ ε ω hω hr hτ hε hε1 hD₀ hB₀ hbase
      hk₀ hx₀ heq₀ hET₀ hFT₀
  have hsign : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j, if decide (Odd j.val) then (P j δ).coeff 0 < 0 else 0 < (P j δ).coeff 0 := by
    filter_upwards [hconstant] with δ hδ j
    by_cases hj : Odd j.val
    · simpa [hj] using (hδ j).2 hj
    · have heven : Even j.val := Nat.not_odd_iff_even.mp hj
      simpa [hj] using (hδ j).1 heven
  have hd : (3*(m+2)-1)+1 = 3*(m+2) := by omega
  obtain ⟨b, hb⟩ := localRouthPattern_has_halving_index
    (3*(m+2)-1) P q (fun j => decide (Odd j.val)) hzero hcoeff hq hsign
  exact ⟨b, by simpa only [hd, P] using hb⟩

end
end PhosphorylationStableCapacity
