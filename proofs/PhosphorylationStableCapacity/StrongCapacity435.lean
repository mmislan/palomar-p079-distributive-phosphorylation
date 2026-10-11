module
public import proofs.PhosphorylationStableCapacity.ExactCapacity435
public import proofs.PhosphorylationStableCapacity.SplitStableAttainment
public import proofs.PhosphorylationStableCapacity.SourceJacobianAugmentedOrientation

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Filter
open scoped Topology

/-- The attaining states are equilibria, Hurwitz sinks, and nonlinear
attractors for the very same rates and totals. -/
def HyperbolicNonlinearClassAttains (n count : ℕ) : Prop :=
  ∃ (k : Rates n) (ET FT ST : ℝ) (u : Fin count → CoordinateSpace n),
    k.Positive ∧ 0 < ET ∧ 0 < FT ∧ 0 < ST ∧ Function.Injective u ∧
      ∀ j, (unChart ET FT ST (ofCoordinateSpace (u j))).Positive ∧
        restrictedFieldEuclid ET FT ST k (u j) = 0 ∧
        IsLinearlyStable ET FT ST k (u j) ∧
        IsLocallyAsymptoticallyStableClass ET FT ST k (u j)

/-- A single positive system has the full prescribed split equilibrium
family, and every even-indexed member is a hyperbolic nonlinear sink. -/
def FullFamilyWithHyperbolicSinks (n : ℕ) : Prop :=
  ∃ (k : Rates n) (ET FT ST : ℝ)
      (u : Fin (2*n-1) → CoordinateSpace n),
    k.Positive ∧ 0 < ET ∧ 0 < FT ∧ 0 < ST ∧ Function.Injective u ∧
      (∀ j, (unChart ET FT ST (ofCoordinateSpace (u j))).Positive ∧
        restrictedFieldEuclid ET FT ST k (u j) = 0) ∧
      ∀ i : Fin n, ∃ j : Fin (2*n-1), j.val = 2*i.val ∧
        IsLinearlyStable ET FT ST k (u j) ∧
        IsLocallyAsymptoticallyStableClass ET FT ST k (u j)

theorem all_size_hyperbolic_nonlinear_attainment
    (n : ℕ) (hn : 1 ≤ n) :
    HyperbolicNonlinearClassAttains n n := by
  obtain ⟨k, ET, FT, ST, u, hk, hET, hFT, hST, hinj, hstates⟩ :=
    all_size_linearly_stable_attainment n hn
  refine ⟨k, ET, FT, ST, u, hk, hET, hFT, hST, hinj, ?_⟩
  intro j
  refine ⟨(hstates j).1, (hstates j).2.1, (hstates j).2.2, ?_⟩
  have hx : u j ∈ classPolytopeStrict n ET FT ST := by
    have hp := positive_state_mem_classPolytopeStrict
      ET FT ST (unChart ET FT ST (ofCoordinateSpace (u j)))
      (hstates j).1 (unChart_inClass ET FT ST _)
    simpa only [chart_unChart, to_ofCoordinateSpace] using hp
  exact isLinearlyStable_locally_asymptotically_stable
    hn ET FT ST hET k hk (u j) hx
    (hstates j).2.1 (hstates j).2.2

/-- The earlier exact ceiling remains universal, including nonhyperbolic
attractors; its attaining witnesses additionally have Hurwitz Jacobians. -/
def ExactCapacityWithHyperbolicAttainment (n : ℕ) : Prop :=
  HyperbolicNonlinearClassAttains n n ∧
    ∀ (ET FT ST : ℝ), 0 < ET → 0 < FT → 0 < ST →
      ∀ (k : Rates n), k.Positive →
        (locallyStablePositiveStates ET FT ST k).Finite ∧
        (locallyStablePositiveStates ET FT ST k).ncard ≤ n

theorem all_size_exact_capacity_with_hyperbolic_attainment_435
    (n : ℕ) (hn : 1 ≤ n) :
    ExactCapacityWithHyperbolicAttainment n :=
  ⟨all_size_hyperbolic_nonlinear_attainment n hn,
    (all_size_exact_capacity_finite_435 n hn).2⟩

theorem split_even_hurwitz_with_full_family
    (m : ℕ) (r τ δ ε : ℝ)
    (hr : 0 < r) (hτ : 0 < τ) (hε : 0 < ε) (hδ : 0 < δ)
    (hD : DensePositive (splitRawD (m+1) r δ) (m+1))
    (hB : DensePositive (splitRawB (m+1) r δ) (m+1))
    (hv : ∀ j : Fin (2*(m+1)+1),
      0 < r-ratio (splitRoot δ j.val))
    (ρ : Fin (2*(m+1)+1) → ℝ)
    (hcert : ∀ j, SplitSlowModeCertificate m r τ δ ε j (ρ j))
    (i : Fin (m+2)) :
    IsLinearlyStable (2*r) 2 (2*(r+1))
      (splitRetunedRates m r τ δ ε)
      (toCoordinateSpace (chart
        (splitFiniteState (m+1) r δ (splitEvenIndex m i)))) := by
  let j := splitEvenIndex m i
  let x := splitFiniteState (m+1) r δ j
  let k := splitFiniteRates (m+1) r δ
  obtain ⟨hk, hx, heq, hET, hFT, hST⟩ :=
    splitFiniteState_source_of_conversion_positive
      (m+1) r δ hδ.le hD hB j
  have heven : Even j.val := by simp [j, splitEvenIndex]
  have haug : 0 < (-1 : ℝ)^(m+2) *
      (sourceAugmentedCurrentMatrix k x).det := by
    simpa only [k, x, j, Nat.add_assoc] using
      split_even_source_augmented_current_det_pos
        (m+1) r δ j hr hδ hD hB (hv j) heven
  have hsrc : 0 < (-1 : ℝ)^(m+2) *
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k
        (toCoordinateSpace (chart x))).det := by
    have h := (equilibrium_restricted_jacobian_parity_det_pos_iff_augmented
      k x hk hx heq).2 haug
    change totalE x = 2*r at hET
    change totalF x = 2 at hFT
    change totalS x = 2*(r+1) at hST
    rw [hET, hFT, hST] at h
    simpa only [show m+1+1 = m+2 by omega] using h
  have hpow : (-1 : ℝ)^Fintype.card
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) =
      (-1 : ℝ)^(m+2) := by
    have hcard : Fintype.card
        (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) =
        (m+2) + 2*(m+2) := by simp; omega
    rw [hcard, pow_add, pow_mul]
    norm_num
  have hret : 0 < (-1 : ℝ)^Fintype.card
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) *
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (splitRetunedRates m r τ δ ε)
        (toCoordinateSpace (chart x))).det := by
    apply (splitRetunedJacobian_parity_det_sign
      m r τ δ ε j hτ hε).2
    simpa only [hpow] using hsrc
  exact (splitSlowModeCertificate_hurwitz_iff_det_positive
    m r τ δ ε j (ρ j) (hcert j)).2 hret

/-- For every chain with at least two sites, the same positive rates and
totals admit all `2n-1` prescribed equilibria. The `n` even-indexed
members of that very family are Hurwitz and nonlinear attractors. -/
theorem all_size_full_family_with_hyperbolic_sinks
    (n : ℕ) (hn : 2 ≤ n) : FullFamilyWithHyperbolicSinks n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m+2 := ⟨n-2, by omega⟩
  obtain ⟨hp, hq⟩ := coalescedPair_dense (m+1)
  have hconv := conversion_eventually_positive hp hq
  have hr1 : ∀ᶠ r : ℝ in atTop, 1 < r := eventually_gt_atTop 1
  obtain ⟨r, ⟨hspec, hconv⟩, hr1⟩ :=
    (((coalescedSpectral_splitFamily_simpleSlow_eventually m).and hconv).and hr1).exists
  have hτpos : ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), 0 < τ :=
    self_mem_nhdsWithin
  obtain ⟨τ, hspec, hτ⟩ := (hspec.and hτpos).exists
  have hεpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε :=
    self_mem_nhdsWithin
  have hεle : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 := by
    have hnear : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ε < 1 :=
      Iio_mem_nhds (by norm_num)
    exact (hnear.filter_mono nhdsWithin_le_nhds).mono
      (fun _ h => h.le)
  obtain ⟨ε, ⟨hspec, hε⟩, hεle⟩ :=
    ((hspec.filter_mono nhdsWithin_le_nhds).and hεpos |>.and hεle).exists
  obtain ⟨ρ, _, hδspec⟩ := hspec hε hεle
  have hδconv := split_conversion_positive_near_zero (m+1) r
    (by linarith : r ≠ 0) hconv.1 hconv.2
  have hδhv := split_root_ratios_below_source_eventually
    (m+1) r hr1
  have hδpos : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ :=
    self_mem_nhdsWithin
  obtain ⟨δ, ⟨⟨hspec, hconv⟩, hv⟩, hδ⟩ :=
    (((hδspec.and hδconv).and hδhv).and hδpos).exists
  let k := splitRetunedRates m r τ δ ε
  let z := splitFiniteState (m+1) r δ
  let u : Fin (2*(m+1)+1) → CoordinateSpace (m+2) :=
    fun j => toCoordinateSpace (chart (z j))
  have hfamily := hspec.1.2.2
  have hback (j : Fin (2*(m+1)+1)) :
      unChart (2*r) 2 (2*(r+1)) (ofCoordinateSpace (u j)) = z j := by
    rw [show ofCoordinateSpace (u j) = chart (z j) by
      simp only [u, of_toCoordinateSpace]]
    exact unChart_chart_of_inClass (2*r) 2 (2*(r+1)) (z j)
      ⟨(hfamily j).2.2.1, (hfamily j).2.2.2.1,
        (hfamily j).2.2.2.2⟩
  have heq (j : Fin (2*(m+1)+1)) :
      restrictedFieldEuclid (2*r) 2 (2*(r+1)) k (u j) = 0 := by
    apply (restrictedFieldEuclid_eq_zero_iff
      (2*r) 2 (2*(r+1)) k (u j)).2
    rw [hback]
    exact (hfamily j).2.1
  have hstable (i : Fin (m+2)) :
      IsLinearlyStable (2*r) 2 (2*(r+1)) k
        (u (splitEvenIndex m i)) := by
    exact split_even_hurwitz_with_full_family m r τ δ ε
      (by linarith) hτ hε hδ hconv.1 hconv.2 hv ρ hspec.2 i
  unfold FullFamilyWithHyperbolicSinks
  refine ⟨k, 2*r, 2, 2*(r+1), u, hspec.1.1,
    by positivity, by norm_num, by positivity, ?_, ?_, ?_⟩
  · intro a b hab
    apply hspec.1.2.1
    change z a = z b
    rw [← hback a, ← hback b, hab]
  · intro j
    exact ⟨by rw [hback]; exact (hfamily j).1, heq j⟩
  · intro i
    refine ⟨splitEvenIndex m i, rfl, hstable i, ?_⟩
    have hx : u (splitEvenIndex m i) ∈
        classPolytopeStrict (m+2) (2*r) 2 (2*(r+1)) := by
      have hp := positive_state_mem_classPolytopeStrict
        (2*r) 2 (2*(r+1))
        (unChart (2*r) 2 (2*(r+1))
          (ofCoordinateSpace (u (splitEvenIndex m i))))
        (by rw [hback]; exact (hfamily (splitEvenIndex m i)).1)
        (unChart_inClass (2*r) 2 (2*(r+1)) _)
      simpa only [chart_unChart, to_ofCoordinateSpace] using hp
    exact isLinearlyStable_locally_asymptotically_stable
      (by omega : 1 ≤ m+2) (2*r) 2 (2*(r+1))
      (by positivity) k hspec.1.1 (u (splitEvenIndex m i)) hx
      (heq (splitEvenIndex m i)) (hstable i)

end
end PhosphorylationStableCapacity
