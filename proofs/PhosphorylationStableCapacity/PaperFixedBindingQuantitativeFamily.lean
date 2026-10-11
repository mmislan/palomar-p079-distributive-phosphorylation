module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingPrefactorDifferentiability
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingPrintedCoefficient
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingSplitCount435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCoalescence435
public import proofs.PhosphorylationStableCapacity.SplitQuantitativeSlowModeFamily
public import proofs.PhosphorylationStableCapacity.SplitUniformTransverseGap
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitRootGapNonzero

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Polynomial Matrix
open scoped Topology

/-- Pointwise literal-paper splitting law. The same `bᵢ=βᵢ=1`
rates, actual class Jacobian, physical determinant coefficient and
selected simple slow mode appear in every clause. -/
theorem paperFixedBinding_quantitative_slow_mode_family
    (m : ℕ) (ξ : ℕ → ℝ) (hξ : StrictMono ξ)
    (r τ ε : ℝ) (ω : Fin (m+1) → ℝ)
    (hω : ∀ i, 0 < ω i)
    (hr : 1 < r) (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : (coalescedAllScaledRates m r
      (Fin.lastCases τ ω)).Positive)
    (hk₀ : (relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε).Positive)
    (hx₀ : (coalescedFiniteState (m+1) r).Positive)
    (heq₀ : Equilibrium
      (relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
      (coalescedFiniteState (m+1) r))
    (hET₀ : totalE (coalescedFiniteState (m+1) r) = 2*r)
    (hFT₀ : totalF (coalescedFiniteState (m+1) r) = 2)
    (hspec : SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
        (fromLoadedCoord (loadedCoordOfState
          (coalescedFiniteState (m+1) r)))))
    (j : Fin (2*(m+1)+1)) :
    ∃ α K : ℝ, 0 < α ∧ 0 < K ∧
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        ∃ lam : ℝ,
          let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r δ ε
              (Fin.lastCases τ ω))
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r δ j)))
          J.charpoly.IsRoot lam ∧
          ((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
            (lam : ℂ) ≠ 0 ∧
          (∀ z : ℂ, z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
            z = (lam : ℂ) ∨ z.re ≤ -α) ∧
          |lam / (-paperFixedBindingPrintedCoefficient m r τ ε ω *
              δ^(2*(m+1)) *
              (∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
                (ξ j.val-ξ i))) - 1| ≤ K*|δ| := by
  let w : Fin (m+2) → ℝ := Fin.lastCases τ ω
  let k : ℝ → Rates (m+2) := fun δ =>
    paperFixedBindingSplitRates m ξ r δ ε w
  let J : ℝ → Matrix (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2)))
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) ℝ := fun δ =>
    restrictedJacobianMatrix (2*r) 2 (2*(r+1)) (k δ)
      (toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j)))
  let P : ℝ → ℝ[X] := fun δ => (J δ).charpoly
  let c : ℝ → ℝ := fun δ =>
    arbitrarySplitGenericPhysicalPrefactor m ξ r δ (k δ) j
  let gap : ℝ := ∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
    (ξ j.val-ξ i)
  let p₁ : ℝ := (P 0).derivative.eval 0
  have hkzero : k 0 =
      relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r w)) ε := by
    simp [k, paperFixedBindingSplitRates, coalescedAllScaledRates,
      arbitrarySplitFiniteRates_zero_eq_coalesced]
  have hw : ∀ i : Fin (m+2), 0 < w i := by
    intro i
    cases i using Fin.lastCases with
    | last => simpa [w] using hτ
    | cast i => simpa [w] using hω i
  have hJdiff : DifferentiableAt ℝ J 0 :=
    restrictedJacobianMatrix_parameter_differentiableAt
      (m+2) (2*r) 2 (2*(r+1)) k
      (fun δ => toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j)))
      (paperFixedBindingSplit_rateVector_differentiableAt
        m ξ r τ ε ω (by linarith) hD₀ hB₀ hbase)
      (arbitrarySplitState_coordinate_differentiableAt
        m ξ r (by linarith) hD₀ j)
  have hJzero : J 0 =
      restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r w)) ε)
        (fromLoadedCoord (loadedCoordOfState
          (coalescedFiniteState (m+1) r))) := by
    simpa only [J, k, w] using
      paperFixedBindingSplit_restrictedJacobianMatrix_zero_eq_coalesced
        m ξ r ε w j
  have hsource : SimpleNeutralHurwitzComplement (J 0) := by
    rw [hJzero]
    exact hspec
  obtain ⟨α, hα, hslowRaw⟩ :=
    continuousNeutralMatrix_slowMode_uniform_gap_any_radius
      J hJdiff.continuousAt hsource
  let S : ℝ → ℝ → Prop := fun δ lam =>
    (((J δ).map (algebraMap ℝ ℂ)).charpoly).derivative.eval
      (lam : ℂ) ≠ 0 ∧
    ∀ z : ℂ, z ∈ spectrum ℂ ((J δ).map (algebraMap ℝ ℂ)) →
      z = (lam : ℂ) ∨ z.re ≤ -α
  have hp₁eq : p₁ = (J 0).charpoly.coeff 1 := by
    change (J 0).charpoly.derivative.eval 0 = _
    rw [← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_derivative]
    simp
  have hp₁ : 0 < p₁ := by
    rw [hp₁eq]
    exact simpleNeutral_real_charpoly_coeff_one_pos (J 0) hsource
  have hc₀ : 0 < c 0 := by
    change 0 < arbitrarySplitGenericPhysicalPrefactor m ξ r 0 (k 0) j
    have hk : (k 0).Positive := by
      rw [hkzero]
      simpa only [w] using hk₀
    have heq : Equilibrium (k 0)
        (coalescedFiniteState (m+1) r) := by
      rw [hkzero]
      simpa only [w] using heq₀
    exact arbitrarySplitGenericPhysicalPrefactor_zero_pos
      m ξ r (k 0) j hr hD₀ hk hx₀ heq hET₀ hFT₀
  have hgap : gap ≠ 0 :=
    arbitrarySplit_root_gap_ne_zero (m+1) ξ hξ j
  have hcard : Fintype.card
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) = 3*(m+2) := by
    simp [Fintype.card_sum, Fintype.card_fin]
    omega
  have hdegree (δ : ℝ) :
      (constantTermSecant (P δ)).natDegree < 3*(m+2)+1 := by
    apply constantTermSecant_degree_lt
    change (J δ).charpoly.natDegree < 3*(m+2)+1
    rw [(J δ).charpoly_natDegree_eq_dim, hcard]
    omega
  have hcoeff (q : ℕ) :
      DifferentiableAt ℝ (fun δ => (P δ).coeff q) 0 :=
    paperFixedBindingSplit_charpoly_coeff_differentiableAt
      m ξ r τ ε ω (by linarith) hD₀ hB₀ hbase j q
  have hc : DifferentiableAt ℝ c 0 :=
    paperFixedBindingSplit_genericPrefactor_differentiableAt
      m ξ r τ ε ω hr hD₀ hB₀ hbase j
  have hconv := arbitrarySplit_conversion_positive_near_zero
    (m+1) ξ r (by linarith : r ≠ 0) hD₀ hB₀
  have hy : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      1 < offsetSplitRoot ξ δ j.val := by
    have h := offsetSplitRoot_gt_one_eventually (m+1) ξ
    filter_upwards [h.filter_mono nhdsWithin_le_nhds] with δ hd
    exact hd j.val (by omega)
  have hv : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      0 < r-ratio (offsetSplitRoot ξ δ j.val) := by
    have hcont : ContinuousAt
        (fun δ : ℝ => r-ratio (offsetSplitRoot ξ δ j.val)) 0 := by
      unfold ratio offsetSplitRoot
      fun_prop
    have hzero : 0 < r-ratio (offsetSplitRoot ξ 0 j.val) := by
      norm_num [ratio, offsetSplitRoot]
      linarith
    exact (hcont.eventually (Ioi_mem_nhds hzero)).filter_mono
      nhdsWithin_le_nhds
  have hconst : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      (P δ).eval 0 = c δ*δ^(2*(m+1))*gap := by
    filter_upwards [hconv, hy, hv] with δ hconv hy hv
    obtain ⟨hk, _, heq, hclass⟩ :=
      paperFixedBindingSplit_source m ξ r δ ε w hw hε hε1
        hconv.1 hconv.2 j hy
    have hphysical := arbitrarySplitGeneric_charpoly_constant_root_gap
      m ξ r δ (k δ) hk hconv.1 hconv.2 j hy hv heq
      hclass.1 hclass.2.1 hclass.2.2
    change (J δ).charpoly.eval 0 = c δ*δ^(2*(m+1))*gap
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact hphysical.trans (by dsimp [c, gap]; ring)
  have hslow (η : ℝ) (hη : 0 < η) :
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        ∃ lam : ℝ, |lam| < η ∧ (P δ).IsRoot lam ∧ S δ lam := by
    filter_upwards [(hslowRaw η hη).filter_mono nhdsWithin_le_nhds]
      with δ hδ
    exact hδ
  obtain ⟨K, hK, hmain⟩ :=
    quantitative_slow_mode_family_of_factored_constant_term
      P c S (2*(m+1)) (3*(m+2)+1) gap (c 0) p₁
      hgap hc₀ hp₁ hdegree hcoeff hc rfl rfl
      hconst hslow (by omega)
  refine ⟨α, K, hα, hK, ?_⟩
  filter_upwards [hmain] with δ hδ
  obtain ⟨lam, hroot, hS, hbound⟩ := hδ
  have hbound' :
      |lam / (-(c 0 / (J 0).charpoly.coeff 1) *
        δ^(2*(m+1)) * gap) - 1| ≤ K*|δ| := by
    simpa only [hp₁eq] using hbound
  have hcoef := paperFixedBindingPrintedCoefficient_eq_physical_ratio
    m ξ r τ ε ω j hr hD₀ hk₀ hx₀ heq₀ hET₀ hFT₀
  have hcoef' : c 0 / (J 0).charpoly.coeff 1 =
      paperFixedBindingPrintedCoefficient m r τ ε ω := by
    change arbitrarySplitGenericPhysicalPrefactor m ξ r 0 (k 0) j /
      (J 0).charpoly.coeff 1 = _
    rw [hkzero, hJzero]
    simpa only [w] using hcoef
  rw [hcoef'] at hbound'
  exact ⟨lam, hroot, hS.1, hS.2,
    by simpa only [J, k, w, gap] using hbound'⟩

end
end PhosphorylationStableCapacity
