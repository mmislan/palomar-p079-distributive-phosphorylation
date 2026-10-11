module
public import proofs.PhosphorylationStableCapacity.UniversalCeilingDegreeDocking
public import proofs.PhosphorylationStableCapacity.RatioResidualSignedIndex

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
attribute [local instance] Classical.propDecidable
open PhosphorylationSharpness

/-- The sole remaining topological input: under the regular perturbation,
each isolating ball around an old attractor has signed index one. -/
def LocalAttractorIndexPrinciple : Prop :=
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
      ∀ i, (∑ z ∈ hfinite.toFinset.filter
        (fun z => toCoordinateSpace (chart z) ∈
          Metric.closedBall (xs i) (r i)),
        signedNegativeFieldIndex ET FT ST k' z) = 1

/-- The global signed sum is already supplied by the scalar residual
crossing theorem and determinant orientation. -/
theorem attractorDegreeSumPrinciple_of_local
    (hlocal : LocalAttractorIndexPrinciple) :
    AttractorDegreeSumPrinciple := by
  intro n hn ET FT ST hET hFT hST k k' hk hk'
    xs hxs r hr hinside hinward hnoReturn
    E hE hfinite hregular hboundary
  constructor
  · exact positive_equilibria_signedNegativeFieldIndex_sum_one_of_regular
      hn k' hk' ET FT ST hET hFT hST E hE hfinite hregular
  · exact hlocal hn ET FT ST hET hFT hST k k' hk hk'
      xs hxs r hr hinside hinward hnoReturn
      E hE hfinite hregular hboundary

theorem universal_ceiling_of_local_attractor_indices
    (hlocal : LocalAttractorIndexPrinciple) :
    UniversalNonlinearStableCeiling :=
  universal_ceiling_of_attractor_degree_sums
    (attractorDegreeSumPrinciple_of_local hlocal)

theorem all_size_exact_capacity_of_local_attractor_indices
    (hlocal : LocalAttractorIndexPrinciple)
    (n : ℕ) (hn : 1 ≤ n) :
    ExactNonlinearStableCapacity n :=
  all_size_exact_capacity_of_attractor_degree_sums
    (attractorDegreeSumPrinciple_of_local hlocal) n hn

end
end PhosphorylationStableCapacity
