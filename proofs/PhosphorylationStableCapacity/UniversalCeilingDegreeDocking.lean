module
public import proofs.PhosphorylationStableCapacity.FiniteStableStateEnumeration
public import proofs.PhosphorylationStableCapacity.FiniteLocalDegreeSelection
public import proofs.PhosphorylationStableCapacity.ExactNonlinearCapacityTarget
public import proofs.PhosphorylationStableCapacity.SignedNegativeFieldIndex

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
attribute [local instance] Classical.propDecidable

open PhosphorylationSharpness

/-- The remaining topological input, stated on exactly the regular
perturbation and enclosing balls already constructed for P079. The
same index convention must give total degree `+1` and local degree
`+1` around each old attractor. This is a contract, not a theorem. -/
def AttractorDegreeSumPrinciple : Prop :=
  ∀ {n : ℕ} (_hn : 0 < n) (ET FT ST : ℝ)
    (_hET : 0 < ET) (_hFT : 0 < FT) (_hST : 0 < ST)
    (k k' : Rates n) (_hk : k.Positive) (_hk' : k'.Positive)
    (xs : Fin (n + 1) → CoordinateSpace n)
    (_hxs : ∀ i, IsLocallyAsymptoticallyStableClass ET FT ST k (xs i))
    (r : Fin (n + 1) → ℝ) (_hr : ∀ i, 0 < r i)
    (_hinside : ∀ i, Metric.closedBall (xs i) (r i) ⊆
      classPolytopeStrict n ET FT ST)
    (_hinward : ∀ i, ∃ T : ℝ, 0 < T ∧
      ∀ z : classPolytope n ET FT ST,
        dist z.1 (xs i) ≤ r i →
          dist (physicalForwardCurve ET FT ST _hET k _hk z T) (xs i) < r i)
    (_hnoReturn : ∀ i, ∀ z : classPolytope n ET FT ST,
      dist z.1 (xs i) = r i → ∀ t : ℝ, 0 < t →
        physicalForwardCurve ET FT ST _hET k _hk z t ≠ z.1)
    (E : Set (State n))
    (_hE : E = {z | z.Positive ∧ Equilibrium k' z ∧ InClass ET FT ST z})
    (hfinite : E.Finite)
    (_hregular : ∀ z ∈ E,
      (restrictedJacobianMatrix ET FT ST k'
        (toCoordinateSpace (chart z))).det ≠ 0)
    (_hboundary : ∀ i : Fin (n + 1), ∀ t : ℝ,
      t ∈ Set.Icc (0 : ℝ) 1 →
      ∀ y : CoordinateSpace n, dist y (xs i) = r i →
        restrictedFieldEuclid ET FT ST
          (ratesFromVector
            (rateVector k + t • (rateVector k' - rateVector k))) y ≠ 0),
    (∑ z ∈ hfinite.toFinset,
      signedNegativeFieldIndex ET FT ST k' z) = 1 ∧
      (∀ i, (∑ z ∈ hfinite.toFinset.filter
        (fun z => toCoordinateSpace (chart z) ∈
          Metric.closedBall (xs i) (r i)),
        signedNegativeFieldIndex ET FT ST k' z) = 1)

/-- All remaining model-specific finite assembly follows from the
signed total and local degree sums. In particular the stable-state
ceiling does not require hyperbolicity of the original attractors. -/
theorem universal_ceiling_of_attractor_degree_sums
    (hdegree : AttractorDegreeSumPrinciple) :
    UniversalNonlinearStableCeiling := by
  classical
  intro n hn ET FT ST hET hFT hST k hk
  by_contra hceiling
  have hn' : 0 < n := by omega
  have hmore : n < (locallyStablePositiveStates ET FT ST k).ncard :=
    Nat.lt_of_not_ge hceiling
  obtain ⟨states, hstates_inj, hstates⟩ :=
    stable_state_ceiling_violation_has_n_succ_attractors
      hn' ET FT ST hET hFT k hk hmore
  let xs : Fin (n + 1) → CoordinateSpace n :=
    fun i => toCoordinateSpace (chart (states i))
  obtain ⟨hxs_inj, hxs_stable, hxs_strict⟩ :=
    stable_state_family_chart_data ET FT ST k states hstates_inj hstates
  obtain ⟨r, hr, hballs_disjoint, hinside, hinward, hnoReturn,
    w, hwpos, hreg, hboundary⟩ :=
    nearby_regular_rates_with_disjoint_attractor_boundaries
      hn' ET FT ST hET hFT k hk xs hxs_inj hxs_stable hxs_strict
  let k' : Rates n := ratesAdd k (selectedRates w)
  let E : Set (State n) :=
    {z | z.Positive ∧ Equilibrium k' z ∧ InClass ET FT ST z}
  have hfinite : E.Finite := hreg.1
  have hbudget : E.ncard ≤ 2 * n := hreg.2.1
  have hregular : ∀ z ∈ E,
      (restrictedJacobianMatrix ET FT ST k'
        (toCoordinateSpace (chart z))).det ≠ 0 := hreg.2.2
  obtain ⟨htotal, hlocal⟩ :=
    hdegree hn' ET FT ST hET hFT hST k k' hk hwpos
      xs hxs_stable r hr hinside hinward hnoReturn
      E rfl hfinite hregular hboundary
  let B : Fin (n + 1) → Set (State n) :=
    fun i => {z | toCoordinateSpace (chart z) ∈
      Metric.closedBall (xs i) (r i)}
  have hdec : ∀ i, DecidablePred (B i) :=
    fun _ _ => Classical.propDecidable _
  have hBdisjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    exact (Set.disjoint_left.mp (hballs_disjoint i j hij)) hzi hzj
  have hcard : hfinite.toFinset.card ≤ 2 * n := by
    simpa only [Set.ncard_eq_toFinset_card E hfinite] using hbudget
  exact @no_n_succ_disjoint_local_degree_one_regions
    (State n) (inferInstance)
    hfinite.toFinset (signedNegativeFieldIndex ET FT ST k') n B hdec hBdisjoint
    (by intro z _hz; exact
      signedNegativeFieldIndex_eq_one_or_neg_one ET FT ST k' z)
    htotal hcard (by
      intro i
      have hfilter :
          @Finset.filter (State n) (B i) (hdec i) hfinite.toFinset =
            hfinite.toFinset.filter (fun z =>
              toCoordinateSpace (chart z) ∈ Metric.closedBall (xs i) (r i)) := by
        exact @Finset.filter_congr_decidable (State n) hfinite.toFinset
          (B i) (hdec i) (fun _ => Classical.propDecidable _)
      rw [hfilter]
      exact hlocal i)

/-- Conditional exact-capacity endpoint, explicitly exposing the
unproved degree principle rather than treating its contract as evidence. -/
theorem all_size_exact_capacity_of_attractor_degree_sums
    (hdegree : AttractorDegreeSumPrinciple)
    (n : ℕ) (hn : 1 ≤ n) :
    ExactNonlinearStableCapacity n :=
  all_size_exact_nonlinear_capacity_of_universal_ceiling
    (universal_ceiling_of_attractor_degree_sums hdegree) n hn

end
end PhosphorylationStableCapacity
