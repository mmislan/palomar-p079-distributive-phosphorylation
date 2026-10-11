module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCompactPhysicalPrefactor435
public import proofs.PhosphorylationStableCapacity.CompactPositiveScalarBounds435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness
open scoped Topology

/-- The literal coalesced physical numerator varies continuously with
the paper's positive current factors. The explicit physical product,
not an abstract eigenvalue coefficient, supplies this continuity. -/
theorem paperFixedBinding_physicalPrefactor_zero_continuousOn
    (m : ℕ) (ξ : ℕ → ℝ) (r ε : ℝ)
    (K : Set (Fin (m+2) → ℝ))
    (hKpos : ∀ w ∈ K, ∀ i, 0 < w i)
    (hbase0 : (arbitrarySplitFiniteRates (m+1) ξ r 0).Positive)
    (j : Fin (2*(m+1)+1)) :
    ContinuousOn (fun w : Fin (m+2) → ℝ =>
      arbitrarySplitGenericPhysicalPrefactor m ξ r 0
        (paperFixedBindingSplitRates m ξ r 0 ε w) j) K := by
  classical
  let base := arbitrarySplitFiniteRates (m+1) ξ r 0
  let F (w : Fin (m+2) → ℝ) : ℝ :=
    arbitrarySplitGeometricFactor m ξ r j 0 *
      ∏ i : Fin (m+2),
        ((1+w i*base.c i)*(1+w i)*(base.alpha i/2)*w i)/ε^2
  have hcont : Continuous F := by
    dsimp [F]
    apply Continuous.mul continuous_const
    apply continuous_finsetProd
    intro i hi
    fun_prop
  apply hcont.continuousOn.congr
  intro w hw
  have hproduct := paperFixedBinding_split_relaxed_rateProduct_product
    m ξ r 0 ε w (hKpos w hw) hbase0
  have hfactor :=
    arbitrarySplitGenericPhysicalPrefactor_eq_geometric_mul_rateProduct
      m ξ r 0 (paperFixedBindingSplitRates m ξ r 0 ε w) j
  dsimp only [F, base]
  exact hfactor.trans
    (congrArg (fun v : ℝ => arbitrarySplitGeometricFactor m ξ r j 0 * v)
      hproduct)

/-- Both uniform bounds required by the compact quantitative law:
the physical numerator is bounded away from zero and bounded above
on the same compact fixed-binding family. -/
theorem paperFixedBinding_compact_physicalPrefactor_zero_bounds
    (m : ℕ) (ξ : ℕ → ℝ) (r ε : ℝ)
    (K : Set (Fin (m+2) → ℝ)) (hK : IsCompact K)
    (hKpos : ∀ w ∈ K, ∀ i, 0 < w i)
    (hbase0 : (arbitrarySplitFiniteRates (m+1) ξ r 0).Positive)
    (j : Fin (2*(m+1)+1))
    (hpos : ∀ w ∈ K,
      0 < arbitrarySplitGenericPhysicalPrefactor m ξ r 0
        (paperFixedBindingSplitRates m ξ r 0 ε w) j) :
    ∃ cmin cmax : ℝ, 0 < cmin ∧ 0 ≤ cmax ∧
      ∀ w ∈ K,
        cmin ≤ arbitrarySplitGenericPhysicalPrefactor m ξ r 0
          (paperFixedBindingSplitRates m ξ r 0 ε w) j ∧
        |arbitrarySplitGenericPhysicalPrefactor m ξ r 0
          (paperFixedBindingSplitRates m ξ r 0 ε w) j| ≤ cmax := by
  let c (w : Fin (m+2) → ℝ) :=
    arbitrarySplitGenericPhysicalPrefactor m ξ r 0
      (paperFixedBindingSplitRates m ξ r 0 ε w) j
  have hc : ContinuousOn c K :=
    paperFixedBinding_physicalPrefactor_zero_continuousOn
      m ξ r ε K hKpos hbase0 j
  obtain ⟨cmin, hcmin, hmin⟩ :=
    compact_continuous_positive_lower K hK c hc hpos
  obtain ⟨cmax, hcmax, hmax⟩ :=
    compact_finite_scalar_abs_upper K hK (fun (_ : Unit) w => c w)
      (fun _ => hc)
  exact ⟨cmin, cmax, hcmin, hcmax.le,
    fun w hw => ⟨hmin w hw, hmax w hw ()⟩⟩

end

end PhosphorylationStableCapacity
