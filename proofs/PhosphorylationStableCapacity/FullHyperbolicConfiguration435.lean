module
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.ExactSplitEquilibriumCount

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Filter
open scoped Topology

/-- One system has the full prescribed split family: every even state is a
Hurwitz nonlinear sink and every odd state has one unstable direction. -/
def FullFamilyWithSinksAndSaddles (n : ℕ) : Prop :=
  ∃ (k : Rates n) (ET FT ST : ℝ)
      (u : Fin (2*n-1) → CoordinateSpace n),
    k.Positive ∧ 0 < ET ∧ 0 < FT ∧ 0 < ST ∧ Function.Injective u ∧
      (∀ j, (unChart ET FT ST (ofCoordinateSpace (u j))).Positive ∧
        restrictedFieldEuclid ET FT ST k (u j) = 0) ∧
      (∀ i : Fin n, ∃ j : Fin (2*n-1), j.val = 2*i.val ∧
        IsLinearlyStable ET FT ST k (u j) ∧
        IsLocallyAsymptoticallyStableClass ET FT ST k (u j)) ∧
      (∀ j : Fin (2*n-1), Odd j.val →
        IsOneUnstableSaddle ET FT ST k (u j)) ∧
      {x : State n | x.Positive ∧ Equilibrium k x ∧
        InClass ET FT ST x} =
          Set.range (fun j : Fin (2*n-1) =>
            unChart ET FT ST (ofCoordinateSpace (u j))) ∧
      {x : State n | x.Positive ∧ Equilibrium k x ∧
        InClass ET FT ST x}.ncard = 2*n-1

/-- All the sink and saddle claims use the same positive rates, totals,
and indexed equilibria. -/
theorem all_size_full_family_with_sinks_and_saddles
    (n : ℕ) (hn : 2 ≤ n) : FullFamilyWithSinksAndSaddles n := by
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
  have hexact := splitRetuned_positive_equilibria_exact_family
    m r τ δ ε (by linarith) hτ hδ hε hεle hconv.1 hconv.2
  have hcard := splitRetuned_positive_equilibria_ncard
    m r τ δ ε (by linarith) hτ hδ hε hεle hconv.1 hconv.2
  unfold FullFamilyWithSinksAndSaddles
  refine ⟨k, 2*r, 2, 2*(r+1), u, hspec.1.1,
    by positivity, by norm_num, by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro j hj
    exact split_odd_is_one_unstable_saddle m r τ δ ε
      (by linarith) hτ hε hδ hconv.1 hconv.2 hv ρ hspec.2 j hj
  · rw [hexact]
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, hback j⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, (hback j).symm⟩
  · simpa only [k, show 2*(m+2)-1 = 2*(m+1)+1 by omega]
      using hcard

end
end PhosphorylationStableCapacity
