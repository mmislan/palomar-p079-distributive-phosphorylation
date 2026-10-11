module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCompactQuantitativeCore435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCompactPhysicalBounds435
public import proofs.PhosphorylationStableCapacity.CompactQuantitativeSlowMode435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Matrix Polynomial
open scoped Topology

/-- The actual-network numerator and characteristic secant estimates
force one relative O(δ) constant over the compact current family.
The selected spectral certificate is carried through unchanged. -/
theorem paperFixedBinding_compact_relative_from_actual_core
    (m : ℕ) (ξ : ℕ → ℝ) (r ε : ℝ)
    (K : Set (Fin (m+2) → ℝ)) (hK : IsCompact K)
    (hKpos : ∀ w ∈ K, ∀ i, 0 < w i)
    (hr : 1 < r) (hε : 0 < ε)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase0 : (coalescedFiniteRates (m+1) r).Positive)
    (hsource : ∀ᶠ δ : ℝ in 𝓝 0,
      (arbitrarySplitFiniteRates (m+1) ξ r δ).Positive)
    (j : Fin (2*(m+1)+1))
    (hstate0 :
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).S 0 *
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).E *
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).F ≠ 0)
    (S : (Fin (m+2) → ℝ) → ℝ → ℝ → Prop)
    (gap pmin : ℝ) (hgap : gap ≠ 0) (hpmin : 0 < pmin)
    (hp1 : ∀ w ∈ K,
      pmin ≤
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (paperFixedBindingSplitRates m ξ r 0 ε w)
          (toCoordinateSpace (chart
            (arbitrarySplitFiniteState (m+1) ξ r 0 j)))).charpoly.derivative.eval 0)
    (hcpos : ∀ w ∈ K,
      0 < arbitrarySplitGenericPhysicalPrefactor m ξ r 0
        (paperFixedBindingSplitRates m ξ r 0 ε w) j)
    (hconst : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ w ∈ K,
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (paperFixedBindingSplitRates m ξ r δ ε w)
          (toCoordinateSpace (chart
            (arbitrarySplitFiniteState (m+1) ξ r δ j)))).charpoly.eval 0 =
        arbitrarySplitGenericPhysicalPrefactor m ξ r δ
          (paperFixedBindingSplitRates m ξ r δ ε w) j *
            δ^(2*(m+1))*gap)
    (hslow : ∀ ρ : ℝ, 0 < ρ →
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        ∀ w ∈ K, ∃ lam : ℝ,
          |lam| < ρ ∧
          (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r δ ε w)
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r δ j)))).charpoly.IsRoot lam ∧
          S w δ lam) :
    ∃ Q : ℝ, 0 < Q ∧
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        ∀ w ∈ K, ∃ lam : ℝ,
          let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r δ ε w)
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r δ j)))
          let J₀ := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r 0 ε w)
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r 0 j)))
          J.charpoly.IsRoot lam ∧ S w δ lam ∧
          |lam / (-(arbitrarySplitGenericPhysicalPrefactor m ξ r 0
              (paperFixedBindingSplitRates m ξ r 0 ε w) j /
                J₀.charpoly.derivative.eval 0) *
              δ^(2*(m+1))*gap)-1| ≤ Q*|δ| := by
  let J (w : Fin (m+2) → ℝ) (δ : ℝ) :=
    restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (paperFixedBindingSplitRates m ξ r δ ε w)
      (toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j)))
  let P (w : Fin (m+2) → ℝ) (δ : ℝ) : ℝ[X] := (J w δ).charpoly
  let c (w : Fin (m+2) → ℝ) (δ : ℝ) :=
    arbitrarySplitGenericPhysicalPrefactor m ξ r δ
      (paperFixedBindingSplitRates m ξ r δ ε w) j
  obtain ⟨A, η₀, C, hA, hη₀, hC, hnum, hrect⟩ :=
    paperFixedBinding_compact_actual_quantitative_core
      m ξ r ε K hK hKpos hr hε hD₀ hB₀
      hbase0 hsource j hstate0
  have hbase :
      (arbitrarySplitFiniteRates (m+1) ξ r 0).Positive := by
    simpa only [arbitrarySplitFiniteRates_zero_eq_coalesced] using hbase0
  obtain ⟨cmin, cmax, hcmin, hcmax, hcbounds⟩ :=
    paperFixedBinding_compact_physicalPrefactor_zero_bounds
      m ξ r ε K hK hKpos hbase j hcpos
  let η := min (η₀/2) (1/2)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hrect' : ∀ w ∈ K, ∀ δ x : ℝ,
      |δ| < η → |x| < η →
        |(constantTermSecant (P w δ)).eval x -
          (P w 0).derivative.eval 0| ≤ C*(|δ|+|x|) := by
    intro w hw δ x hδ hx
    apply hrect w hw δ x
    · have hle : η ≤ η₀/2 := min_le_left ..
      linarith
    · have hle : η ≤ 1/2 := min_le_right ..
      linarith
  obtain ⟨Q, hQ, hlaw⟩ :=
    quantitative_slow_mode_compact_family_of_factored_constant_term
      K P c S (2*(m+1)) gap cmin cmax pmin η A C
      hgap (by omega) hcmin hcmax hpmin hη hA hC
      (fun w hw => hcbounds w hw)
      (fun w hw => hp1 w hw) hnum hrect' hconst hslow
  refine ⟨Q, hQ, ?_⟩
  filter_upwards [hlaw] with δ hδ w hw
  simpa only [J, P, c] using hδ w hw

end

end PhosphorylationStableCapacity
