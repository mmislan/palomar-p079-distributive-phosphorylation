module
public import proofs.PhosphorylationStableCapacity.PaperCoalescedRationalDiagonal435
public import proofs.PhosphorylationStableCapacity.CoalescedAllEdgeKernel
public import proofs.PhosphorylationStableCapacity.CoalescedKernelLastNonzero
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingOrderedSearch435
public import proofs.PhosphorylationStableCapacity.PaperCoalescedPhysicalData435
public import proofs.PhosphorylationStableCapacity.PaperPointwiseSchurDerivative435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingRouthMinorAdmission435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial Matrix Filter PhosphorylationSharpness
open scoped Topology

/-- Physical coefficient admission gives the literal positive source and
its exact totals pointwise, with no eventual lower bound replacing r. -/
theorem coalescedFiniteState_source_of_dense_positive
    (m : ℕ) (r : ℝ)
    (hD : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB : DensePositive (coalescedRawB (m+1) r) (m+1)) :
    (coalescedFiniteRates (m+1) r).Positive ∧
      (coalescedFiniteState (m+1) r).Positive ∧
      Equilibrium (coalescedFiniteRates (m+1) r) (coalescedFiniteState (m+1) r) ∧
      totalE (coalescedFiniteState (m+1) r) = 2*r ∧
      totalF (coalescedFiniteState (m+1) r) = 2 ∧
      totalS (coalescedFiniteState (m+1) r) = 2*(r+1) := by
  have hsource : (3-1 : ℝ)*(coalescedPair (m+1)).1.eval (ratio 3)-
      2*(coalescedPair (m+1)).2.eval (ratio 3) = 0 := by
    have hval := coalescedPair_eval_one (m+1)
    norm_num [ratio, hval.1, hval.2]
  have hrel := conversion_root (coalescedPair (m+1)).1
    (coalescedPair (m+1)).2 r 3 hsource
  have hresult := source_from_coefficients (coalescedRawB (m+1) r)
    (coalescedRawD (m+1) r) hB hD r 3 (by norm_num)
      (by simpa [coalescedRawB, coalescedRawD] using hrel)
  have hk : (coalescedFiniteRates (m+1) r).Positive := by
    unfold coalescedFiniteRates
    exact realize_positive _ _ _
      (fun i => (dense_inventory_product hD).1 i (by omega))
      (fun i => hB.1 i (by omega)) (fun i => hD.1 i (by omega))
  exact ⟨hk, by simpa only [coalescedFiniteState] using hresult.1,
    by simpa only [coalescedFiniteRates, coalescedFiniteState] using hresult.2.1,
    by simpa only [coalescedFiniteState] using hresult.2.2.1,
    by simpa only [coalescedFiniteState] using hresult.2.2.2.1,
    by simpa only [coalescedFiniteState] using hresult.2.2.2.2⟩

theorem coalescedFiniteState_component_totals_of_dense_positive
    (m : ℕ) (r : ℝ)
    (hD : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB : DensePositive (coalescedRawB (m+1) r) (m+1)) :
    (∑ i, (coalescedFiniteState (m+1) r).C i) = 2*r-1 ∧
      (∑ i, (coalescedFiniteState (m+1) r).D i) = 1 ∧
      (∑ i, (coalescedFiniteState (m+1) r).S i) = 2 := by
  obtain ⟨_, _, _, hE, hF, hS⟩ :=
    coalescedFiniteState_source_of_dense_positive m r hD hB
  obtain ⟨hfreeE, hfreeF⟩ := coalescedFiniteState_EF (m+1) r
  unfold totalE at hE
  unfold totalF at hF
  unfold totalS at hS
  rw [hfreeE] at hE
  rw [hfreeF] at hF
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The pointwise admitted source supplies every exact physical datum
used by the full fixed-binding derivative and Schur identities. -/
theorem paperCoalescedPhysicalData_of_dense_positive
    (m : ℕ) (r : ℝ) (hr : 1 < r)
    (hD : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB : DensePositive (coalescedRawB (m+1) r) (m+1)) :
    PaperCoalescedPhysicalData m r := by
  obtain ⟨hk, hx, heq, hET, hFT, hST⟩ :=
    coalescedFiniteState_source_of_dense_positive m r hD hB
  obtain ⟨hC, hY, _⟩ := coalescedFiniteState_component_totals_of_dense_positive m r hD hB
  exact ⟨hk, hx, heq, hET, hFT, hST, hC, hY,
    ne_of_gt (lt_trans zero_lt_one hr), coalescedFullMass_det_ne_zero m r hx hC hY⟩

theorem orderedRationalPrefixAdmits_physicalData
    (m : ℕ) (r : ℚ) (h : orderedRationalPrefixAdmits m r = true) :
    PaperCoalescedPhysicalData m (r : ℝ) := by
  obtain ⟨hr, _, hD, hB⟩ := (orderedRationalPrefixAdmits_iff m r).mp h
  exact paperCoalescedPhysicalData_of_dense_positive m r hr hD hB

/-- All four literal mass/current moments at every physically admitted
source. The support assumptions are those actually checked by admission. -/
theorem coalescedLiteralMoments_of_dense_positive
    (m : ℕ) (r : ℝ) (hr : r ≠ 0)
    (hD : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB : DensePositive (coalescedRawB (m+1) r) (m+1)) :
    ((∑ k : Fin (m+3), coalescedLiteralFeedbackWeight m r k) =
      coalescedSourceH0 r ∧
      (∑ k : Fin (m+3), coalescedLiteralFeedbackWeight m r k*(k.val : ℝ)) =
      coalescedSourceH1 m r) ∧
    ((∑ k : Fin (m+3), coalescedLiteralMassTotalWeight m r k) =
      coalescedSourceT0 r ∧
      (∑ k : Fin (m+3), coalescedLiteralMassTotalWeight m r k*(k.val : ℝ)) =
      coalescedSourceT1 m r) := by
  have ht := coalescedFiniteState_component_totals_of_dense_positive m r hD hB
  have hD0 : (coalescedRawD (m+1) r).eval 1 ≠ 0 :=
    ne_of_gt (hD.eval_pos (by norm_num))
  have hdegD : (coalescedRawD (m+1) r).natDegree ≤ m+1 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hD.2
  have hdegB : (coalescedRawB (m+1) r).natDegree ≤ m+1 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hB.2
  have hC : (∑ k : Fin (m+3), coalescedFiniteCLevel m r k*(k.val : ℝ)) =
      (derivative (coalescedRawB (m+1) r)).eval 1/
        (coalescedRawD (m+1) r).eval 1 := by
    rw [coalescedFiniteCLevel_firstMoment_eq]
    exact coalescedFiniteState_C_firstMoment m r hdegB
  have hY : (∑ k : Fin (m+3), coalescedFiniteYLevel m r k*(k.val : ℝ)) =
      ((coalescedRawD (m+1) r).eval 1+
        (derivative (coalescedRawD (m+1) r)).eval 1)/
        (coalescedRawD (m+1) r).eval 1 := by
    rw [coalescedFiniteYLevel_firstMoment_eq]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    simp only [mul_one]
    rw [coalescedFiniteState_D_firstMoment m r hdegD, ht.2.1]
    field_simp [hD0]
    ring
  have hlin : (1+X : ℝ[X]).natDegree ≤ 1 := by
    calc
      _ ≤ max (1 : ℝ[X]).natDegree X.natDegree := Polynomial.natDegree_add_le _ _
      _ = 1 := by simp [Polynomial.natDegree_X]
  have hinventory : ((1+X)*coalescedRawD (m+1) r).natDegree ≤ m+2 := by
    calc
      _ ≤ (1+X : ℝ[X]).natDegree+(coalescedRawD (m+1) r).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ m+2 := by omega
  have hS : (∑ k : Fin (m+3), (coalescedFiniteState (m+1) r).S k*(k.val : ℝ)) =
      ((coalescedRawD (m+1) r).eval 1+
        2*(derivative (coalescedRawD (m+1) r)).eval 1)/
        (coalescedRawD (m+1) r).eval 1 := by
    rw [coalescedFiniteState_S_firstMoment m r hinventory,
      coalescedInventory_deriv_eval_one]
  exact ⟨⟨coalescedLiteralFeedback_H0 m r hr ht.1 ht.2.1,
    coalescedLiteralFeedback_H1 m r hr hY hC⟩,
    ⟨coalescedLiteralMass_T0 m r hr ht.1 ht.2.1 ht.2.2,
      coalescedLiteralMass_T1 m r hr hD0 hS hC hY⟩⟩

/-- The exact source zero mode is present at every admitted parameter,
before the spectral prefix test is used to normalize its last coordinate. -/
theorem coalescedFullLoadedMatrix_nontrivial_kernel_of_dense_positive
    (m : ℕ) (r : ℝ) (hr : 1 < r)
    (hD : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB : DensePositive (coalescedRawB (m+1) r) (m+1)) :
    ∃ z : Fin (m+2) → ℝ, z ≠ 0 ∧ (coalescedFullLoadedMatrix m r).mulVec z = 0 := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_trans zero_lt_one hr)
  have ht := coalescedFiniteState_component_totals_of_dense_positive m r hD hB
  obtain ⟨hfeedback, hmass⟩ := coalescedLiteralMoments_of_dense_positive m r hr0 hD hB
  let σ := coalescedAffineZeroTangent m r
  have hf : (∑ k : Fin (m+3), coalescedLiteralFeedbackWeight m r k*σ k) =
      coalescedSourceH0 r := by
    change (∑ k : Fin (m+3), coalescedLiteralFeedbackWeight m r k*
      ((1-coalescedSourceH1 m r)+coalescedSourceH0 r*(k.val : ℝ))) = _
    rw [affine_weighted_sum, hfeedback.1, hfeedback.2]
    ring
  have hcurrent (i : Fin (m+2)) :
      (coalescedCurrentJacobianMatrix m r).mulVec σ i = 0 := by
    rw [coalescedCurrentJacobianMatrix_mulVec]
    change (coalescedFiniteState (m+1) r).D i*
      (σ i.castSucc-σ i.succ+∑ k : Fin (m+3),
        coalescedLiteralFeedbackWeight m r k*σ k) = 0
    rw [hf]
    simp only [σ, coalescedAffineZeroTangent, Fin.val_castSucc, Fin.val_succ]
    push_cast
    ring
  have htotal : (∑ i : Fin (m+3), (coalescedFullMass m r).mulVec σ i) = 0 := by
    rw [coalescedFullMass_total_action m r σ hr0 ht.1 ht.2.1]
    have hm : (∑ k : Fin (m+3), (coalescedFiniteState (m+1) r).S k*σ k)+
        (∑ k : Fin (m+3), coalescedFiniteCLevel m r k*σ k)/(2*r)+
        (∑ k : Fin (m+3), coalescedFiniteYLevel m r k*σ k)/2 =
        ∑ k : Fin (m+3), coalescedLiteralMassTotalWeight m r k*σ k := by
      unfold coalescedLiteralMassTotalWeight
      simp_rw [add_mul, div_mul_eq_mul_div]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.sum_div, ← Finset.sum_div]
    rw [hm]
    change (∑ k : Fin (m+3), coalescedLiteralMassTotalWeight m r k*
      ((1-coalescedSourceH1 m r)+coalescedSourceH0 r*(k.val : ℝ))) = 0
    rw [affine_weighted_sum, hmass.1, hmass.2]
    have hdet := coalescedSourceMomentDet_zero m r hr0
      (ne_of_gt (hD.eval_pos (by norm_num)))
    nlinarith [hdet]
  have hdet : (coalescedFullMass m r).det ≠ 0 :=
    coalescedFullMass_det_ne_zero m r
      (coalescedFiniteState_source_of_dense_positive m r hD hB).2.1 ht.1 ht.2.1
  let q := (coalescedFullMass m r).mulVec σ
  obtain ⟨z, hz⟩ := pathIncidence_transpose_zero_sum_range
    (m := m+2) (by omega) q htotal
  have hQ : (coalescedFullEdgeForcingMatrix m).mulVec z = q := by
    rw [coalescedFullEdgeForcing_eq_incidence]
    funext k
    exact hz k
  have hrecover : (coalescedFullMass m r)⁻¹.mulVec q = σ := by
    dsimp [q]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have hznonzero : z ≠ 0 := by
    intro hz0
    have hq0 : q = 0 := by rw [← hQ, hz0]; simp
    have hσ0 : σ = 0 := by rw [← hrecover, hq0]; simp
    exact coalescedAffineZeroTangent_ne_zero m r hr hσ0
  refine ⟨z, hznonzero, ?_⟩
  funext i
  change (coalescedCurrentJacobianMatrix m r*(coalescedFullMass m r)⁻¹*
    coalescedFullEdgeForcingMatrix m).mulVec z i = 0
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQ, hrecover]
  exact hcurrent i

/-- An accepted loaded prefix supplies the missing normalization at the
same physical source parameter. A weighted prefix may be used directly. -/
theorem coalescedFullLoadedMatrix_normalized_kernel_of_accepted_prefix
    (m : ℕ) (r : ℝ) (hr : 1 < r)
    (hD : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB : DensePositive (coalescedRawB (m+1) r) (m+1))
    (ω : Fin (m+1) → ℝ)
    (hprefix : IsHurwitz (coalescedPrefixLoadedMatrix m r*Matrix.diagonal ω)) :
    ∃ u : Fin (m+2) → ℝ, u (Fin.last (m+1)) = 1 ∧
      (coalescedFullLoadedMatrix m r).mulVec u = 0 := by
  obtain ⟨z, hz, hKz⟩ :=
    coalescedFullLoadedMatrix_nontrivial_kernel_of_dense_positive m r hr hD hB
  have hweighted := isHurwitz_det_ne_zero hprefix
  rw [Matrix.det_mul] at hweighted
  have hdet : (coalescedPrefixLoadedMatrix m r).det ≠ 0 :=
    (mul_ne_zero_iff.mp hweighted).1
  have hdet' : Matrix.det (fun i j : Fin (m+1) =>
      coalescedFullLoadedMatrix m r i.castSucc j.castSucc) ≠ 0 := by
    simpa only [coalescedFullLoadedMatrix_prefix] using hdet
  have hlast := kernel_last_ne_zero_of_prefix_det_ne_zero (m+1)
    (coalescedFullLoadedMatrix m r) hdet' z hz hKz
  let u := (z (Fin.last (m+1)))⁻¹ • z
  refine ⟨u, ?_, ?_⟩
  · simp [u, smul_eq_mul, hlast]
  · dsimp [u]
    rw [Matrix.mulVec_smul, hKz, smul_zero]

/-- Every physically admitted, accepted prefix leads to a small-final-rate
Hurwitz complement, retaining that same r and every prefix weight. -/
theorem acceptedPhysicalPrefix_eventually_slow_deflation
    (m : ℕ) (r : ℝ) (hr : 1 < r)
    (hD : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB : DensePositive (coalescedRawB (m+1) r) (m+1))
    (ω : Fin (m+1) → ℝ) (hω : ∀ i, 0 < ω i)
    (hprefix : IsHurwitz (coalescedPrefixLoadedMatrix m r*Matrix.diagonal ω)) :
    ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), ∃ q : ℝ[X],
      (coalescedFullLoadedMatrix m r*Matrix.diagonal (Fin.lastCases τ ω)).charpoly =
        q*X ∧ q.eval 0 ≠ 0 ∧
      ∀ z : ℂ, (q.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0 := by
  have hkernel := coalescedFullLoadedMatrix_normalized_kernel_of_accepted_prefix
    m r hr hD hB ω hprefix
  have hslow := acceptedPrefix_eventually_slow_deflation m r ω hω hprefix hkernel
  simpa only [coalescedAllCurrentMatrix_eq_prefix_then_final] using hslow

/-- Positive rescaling preserves approach to zero from the right. -/
theorem tendsto_div_positive_right (d : ℝ) (hd : 0 < d) :
    Tendsto (fun t : ℝ => t/d) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [id_eq, zero_div] using
      ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))).div_const d).mono_left
        nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact div_pos ht hd

/-- The small parameter is the actual final current t. Its frozen
catalytic factor is t divided by the same positive source complex. -/
theorem acceptedPhysicalPrefix_eventually_actual_current_simpleNeutral
    (m : ℕ) (r : ℝ) (hr : 1 < r)
    (hD : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hprefix : IsHurwitz (coalescedPrefixLoadedMatrix m r*
      Matrix.diagonal (fun i : Fin (m+1) =>
        1/(coalescedFiniteState (m+1) r).D i.castSucc))) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      SimpleNeutralHurwitzComplement (coalescedFullLoadedMatrix m r*
        Matrix.diagonal (Fin.lastCases
          (t/(coalescedFiniteState (m+1) r).D (Fin.last (m+1)))
          (fun i : Fin (m+1) => 1/(coalescedFiniteState (m+1) r).D i.castSucc))) := by
  have hx := (coalescedFiniteState_source_of_dense_positive m r hD hB).2.1
  have hω : ∀ i : Fin (m+1), 0 < 1/(coalescedFiniteState (m+1) r).D i.castSucc := by
    intro i
    exact div_pos zero_lt_one (hx.2.2.2.2 i.castSucc)
  have hslow := acceptedPhysicalPrefix_eventually_slow_deflation
    m r hr hD hB _ hω hprefix
  have ht := (tendsto_div_positive_right _ (hx.2.2.2.2 (Fin.last (m+1)))).eventually hslow
  filter_upwards [ht] with t hspec
  obtain ⟨q, hchar, hq0, hqleft⟩ := hspec
  refine ⟨q.map (algebraMap ℝ ℂ), ?_, ?_, hqleft⟩
  · rw [Matrix.charpoly_map, hchar, Polynomial.map_mul, Polynomial.map_X, mul_comm]
  · simpa only [Polynomial.eval_zero_map, Complex.coe_algebraMap] using
      (show ((q.eval 0 : ℝ) : ℂ) ≠ 0 by exact_mod_cast hq0)

/-- The specified-P acceptance certifies every positive catalytic prefix
weight on loaded coordinates, using its explicit diagonal certificate. -/
theorem paperRationalPrefixDiagonal_accepted_loaded_all_weights
    (m a : ℕ)
    (hadmit : orderedRationalPrefixAdmits m ((2 : ℚ)^a) = true)
    (haccept : paperRationalPrefixDiagonalAccepts m a = true)
    (ω : Fin (m+1) → ℝ) (hω : ∀ i, 0 < ω i) :
    IsHurwitz (coalescedPrefixLoadedMatrix m ((2 : ℝ)^a)*Matrix.diagonal ω) := by
  let r : ℝ := (2 : ℝ)^a
  let L := coalescedPrefixLoadedMatrix m r
  let P := (paperRationalDiagonalP m).map (algebraMap ℚ ℝ)
  let PL := P*Matrix.diagonal (fun i : Fin (m+1) =>
    1/(coalescedFiniteState (m+1) r).D i.castSucc)
  obtain ⟨hQ, hPL, hidentity, _⟩ :=
    paperRationalPrefixDiagonal_accepted_loaded_certificate m a hadmit haccept
  let p : Fin (m+1) → ℝ := fun i =>
    ((pathH (coalescedPathWeights m))⁻¹.mulVec (coalescedPathEdgeFeedback m)) i/
      pathVectorFin (coalescedPathWeights m) i
  let pL : Fin (m+1) → ℝ := fun i => p i/(coalescedFiniteState (m+1) r).D i.castSucc
  have hPeq : P = Matrix.diagonal p := paperRationalDiagonalP_cast m
  have hPLeq : PL = Matrix.diagonal pL := by
    dsimp only [PL]
    rw [hPeq, Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    simp only [pL, div_eq_mul_inv, one_mul]
  have hpL : ∀ i, 0 < pL i := Matrix.posDef_diagonal_iff.mp (hPLeq ▸ hPL)
  have hnegative : (-(L.transpose*Matrix.diagonal pL+Matrix.diagonal pL*L)).PosDef := by
    rw [← hPLeq, hidentity, neg_neg]
    exact hQ
  exact (diagonal_lyapunov_all_positive_currents L pL ω hpL hω hnegative).2.2

/-- Universal predecessor implication for the exact physically guarded
specified-P first loop. It retains unit actual prefix currents and the
same frozen source complexes when the final actual current tends to zero. -/
theorem paperRationalPrefixDiagonal_accepted_eventually_slow_actual_current
    (m a : ℕ)
    (hadmit : orderedRationalPrefixAdmits m ((2 : ℚ)^a) = true)
    (haccept : paperRationalPrefixDiagonalAccepts m a = true) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      SimpleNeutralHurwitzComplement (coalescedFullLoadedMatrix m ((2 : ℝ)^a)*
        Matrix.diagonal (Fin.lastCases
          (t/(coalescedFiniteState (m+1) ((2 : ℝ)^a)).D (Fin.last (m+1)))
          (fun i : Fin (m+1) => 1/(coalescedFiniteState (m+1) ((2 : ℝ)^a)).D i.castSucc))) := by
  obtain ⟨hr, _, hD, hB⟩ := (orderedRationalPrefixAdmits_iff m ((2 : ℚ)^a)).mp hadmit
  have hr' : 1 < (2 : ℝ)^a := by simpa only [Rat.cast_pow, Rat.cast_ofNat] using hr
  have hD' : DensePositive (coalescedRawD (m+1) ((2 : ℝ)^a)) (m+1) := by
    simpa only [Rat.cast_pow, Rat.cast_ofNat] using hD
  have hB' : DensePositive (coalescedRawB (m+1) ((2 : ℝ)^a)) (m+1) := by
    simpa only [Rat.cast_pow, Rat.cast_ofNat] using hB
  have hx := (coalescedFiniteState_source_of_dense_positive m _ hD' hB').2.1
  have hω : ∀ i : Fin (m+1), 0 < 1/(coalescedFiniteState (m+1) ((2 : ℝ)^a)).D i.castSucc :=
    fun i => div_pos zero_lt_one (hx.2.2.2.2 i.castSucc)
  exact acceptedPhysicalPrefix_eventually_actual_current_simpleNeutral
    m _ hr' hD' hB'
    (paperRationalPrefixDiagonal_accepted_loaded_all_weights m a hadmit haccept _ hω)

/-- EVERY accepted slow design at a physically admitted r gives a simple
neutral actual fixed-binding class Jacobian for all sufficiently small
positive binding scales. All catalytic weights are kept exactly fixed. -/
theorem paperAcceptedSlow_eventually_fixedBinding_simpleNeutral
    (m : ℕ) (r : ℝ) (hr : 1 < r)
    (hD : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB : DensePositive (coalescedRawB (m+1) r) (m+1))
    (w : Fin (m+2) → ℝ) (hw : ∀ i, 0 < w i)
    (hslow : SimpleNeutralHurwitzComplement
      (coalescedFullLoadedMatrix m r*Matrix.diagonal w)) :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      SimpleNeutralHurwitzComplement
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (relaxRates (paperFixedBindingRates (coalescedAllScaledRates m r w)) ε)
          (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r)))) := by
  have hdata := paperCoalescedPhysicalData_of_dense_positive m r hr hD hB
  let s := coalescedFiniteState (m+1) r
  let u := loadedCoordOfState s
  let k₀ := coalescedAllScaledRates m r w
  let k := paperFixedBindingRates k₀
  let x := stateFromLoaded (2*r) 2 (2*(r+1)) u
  have hchart : x = s := stateFromLoaded_loadedCoordOfState (2*r) 2 (2*(r+1)) s
    ⟨hdata.totalE_eq, hdata.totalF_eq, hdata.totalS_eq⟩
  have hk₀ : k₀.Positive := edgeScaledRates_positive w _ hw hdata.ratesPositive
  have heq₀ : Equilibrium k₀ s := by
    apply edgeScaledRates_equilibrium
    · intro i
      have h := hdata.stateEquilibrium.2.2.2.1 i
      change kinaseNet (coalescedFiniteRates (m+1) r) s i-
        (coalescedFiniteRates (m+1) r).c i*s.C i = 0 at h
      exact sub_eq_zero.mp h
    · intro i
      have h := hdata.stateEquilibrium.2.2.2.2 i
      change phosphataseNet (coalescedFiniteRates (m+1) r) s i-
        (coalescedFiniteRates (m+1) r).gamma i*s.D i = 0 at h
      exact sub_eq_zero.mp h
    · intro i
      exact realize_reconstruct_catalytic_balance
        (fun j : Fin (m+3) => ((1+X)*coalescedRawD (m+1) r).coeff j)
        (fun j : Fin (m+2) => (coalescedRawB (m+1) r).coeff j)
        (fun j : Fin (m+2) => (coalescedRawD (m+1) r).coeff j)
        (ratio 3) (rootS 3 ((coalescedRawD (m+1) r).eval (ratio 3)))
        (rootF 3) i (ne_of_gt (hB.1 i (by omega)))
  have hpos : x.Positive := by
    rw [hchart]
    exact hdata.statePositive
  have hk : k.Positive := paperFixedBindingRates_positive k₀ hk₀
  have heq : Equilibrium k x := by
    rw [hchart]
    exact paperFixedBindingRates_preserves_equilibrium k₀ s hk₀ heq₀
  have hρ (j : Fin (m+2)) : 0 < k.a j*x.S j.castSucc*x.E :=
    mul_pos (mul_pos (hk j).1 (hpos.1 j.castSucc)) hpos.2.1
  have hσ (j : Fin (m+2)) : 0 < k.alpha j*x.S j.succ*x.F :=
    mul_pos (mul_pos (hk j).2.2.2.1 (hpos.1 j.succ)) hpos.2.2.1
  let M := coalescedFullLoadedMatrix m r*Matrix.diagonal w
  let q := M.charpoly.divX
  have hzero : M.charpoly.coeff 0 = 0 := simpleNeutral_real_charpoly_coeff_zero M hslow
  have hfactor : M.charpoly = q*X := by
    have hf := Polynomial.X_mul_divX_add M.charpoly
    simpa only [hzero, Polynomial.C_0, add_zero, mul_comm] using hf.symm
  obtain ⟨_hmonic, hleft⟩ := simpleNeutral_real_charpoly_divX_hurwitz M hslow
  have hqzero : q.eval 0 ≠ 0 := by
    intro hz
    have hc : (q.map (algebraMap ℝ ℂ)).eval (0 : ℂ) = 0 := by
      rw [Polynomial.eval_zero_map, hz, map_zero]
    have h := hleft 0 hc
    norm_num at h
  have hSchur :
      (schurLinear (loadedBlockA (2*r) 2 (2*(r+1)) k u).toLinearMap
        (loadedBlockB (2*r) 2 (2*(r+1)) k u).toLinearMap
        (loadedBlockC (2*r) 2 (2*(r+1)) k u).toLinearMap
        (fastBindingEquiv x hpos (fun j => k.a j*x.S j.castSucc*x.E)
          (fun j => k.alpha j*x.S j.succ*x.F) hρ hσ)).charpoly = q*X := by
    calc
      _ = M.charpoly := paperPointwise_fixedBindingSchur_charpoly m r hdata w hw
        hpos heq hρ hσ
      _ = q*X := hfactor
  have hspec := loadedRestrictedJacobian_eventually_simple_zero_hurwitz_complement
    (2*r) 2 (2*(r+1)) k u hpos heq hρ hσ q hSchur hqzero hleft
  filter_upwards [hspec.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with ε hε hεpos
  exact hε hεpos

theorem orderedRationalPrefixAdmits_acceptedSlow_eventually_fixedBinding_simpleNeutral
    (m : ℕ) (r : ℚ) (hadmit : orderedRationalPrefixAdmits m r = true)
    (w : Fin (m+2) → ℝ) (hw : ∀ i, 0 < w i)
    (hslow : SimpleNeutralHurwitzComplement
      (coalescedFullLoadedMatrix m (r : ℝ)*Matrix.diagonal w)) :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      SimpleNeutralHurwitzComplement
        (restrictedJacobianMatrix (2*(r : ℝ)) 2 (2*((r : ℝ)+1))
          (relaxRates (paperFixedBindingRates (coalescedAllScaledRates m (r : ℝ) w)) ε)
          (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) (r : ℝ))))) := by
  obtain ⟨hr, _, hD, hB⟩ := (orderedRationalPrefixAdmits_iff m r).mp hadmit
  exact paperAcceptedSlow_eventually_fixedBinding_simpleNeutral m r hr hD hB w hw hslow

end
end PhosphorylationStableCapacity
