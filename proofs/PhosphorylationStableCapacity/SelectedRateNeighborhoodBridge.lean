module
public import proofs.PhosphorylationStableCapacity.AttractorRateBoundaryPersistence
public import proofs.PhosphorylationStableCapacity.RateRegularBudget

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness

/-- The three selected rate coordinates used by Sard's theorem vary
continuously in the full six-array rate-vector topology. -/
theorem continuous_selected_perturbed_rateVector {n : ℕ}
    (k : Rates n) :
    Continuous (fun w : CoordinateSpace n =>
      rateVector (ratesAdd k (selectedRates w))) := by
  classical
  apply continuous_pi
  intro j
  apply continuous_pi
  intro i
  fin_cases j <;> simp [rateVector, ratesAdd, selectedRates] <;> fun_prop

/-- Zero selected-rate perturbation is exactly the original literal
rate list, including the three arrays that are held fixed. -/
theorem selected_perturbed_rateVector_zero {n : ℕ} (k : Rates n) :
    rateVector (ratesAdd k (selectedRates (0 : CoordinateSpace n))) =
      rateVector k := by
  congr 1
  cases k
  simp [ratesAdd, selectedRates]

/-- One positive regular perturbation can be selected inside the exact
rate neighborhood that preserves a local attractor's zero-free
boundary throughout the rate homotopy. The regular equilibrium count
is the full model-specific `2n` budget. -/
theorem nearby_regular_rates_preserve_attractor_boundary {n : ℕ}
    (hn : 0 < n) (ET FT ST : ℝ) (hET : 0 < ET) (hFT : 0 < FT)
    (k : Rates n) (hk : k.Positive) (x : CoordinateSpace n)
    (hx : IsLocallyAsymptoticallyStableClass ET FT ST k x) :
    ∃ r : ℝ, 0 < r ∧
      ∃ w : CoordinateSpace n,
        (ratesAdd k (selectedRates w)).Positive ∧
        (let E : Set (State n) :=
          {z | z.Positive ∧
            Equilibrium (ratesAdd k (selectedRates w)) z ∧
            InClass ET FT ST z}
         E.Finite ∧ E.ncard ≤ 2 * n ∧
           ∀ z ∈ E,
             (restrictedJacobianMatrix ET FT ST
               (ratesAdd k (selectedRates w))
               (toCoordinateSpace (chart z))).det ≠ 0) ∧
        ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
          ∀ y : CoordinateSpace n, dist y x = r →
            restrictedFieldEuclid ET FT ST
              (ratesFromVector
                (rateVector k + t •
                  (rateVector (ratesAdd k (selectedRates w)) -
                    rateVector k))) y ≠ 0 := by
  obtain ⟨r, δ, hr, hδ, hboundary⟩ :=
    local_attractor_boundary_zero_free_rate_homotopy ET FT ST k x hx
  let U : Set (CoordinateSpace n) :=
    (fun w => rateVector (ratesAdd k (selectedRates w))) ⁻¹'
      Metric.ball (rateVector k) δ
  have hU : IsOpen U :=
    Metric.isOpen_ball.preimage (continuous_selected_perturbed_rateVector k)
  have hzero : (0 : CoordinateSpace n) ∈ U := by
    change rateVector (ratesAdd k (selectedRates (0 : CoordinateSpace n))) ∈
      Metric.ball (rateVector k) δ
    rw [selected_perturbed_rateVector_zero]
    exact Metric.mem_ball_self hδ
  obtain ⟨w, hwU, hwpos, hreg⟩ :=
    nearby_positive_rates_finite_regular_budget hn ET FT ST hET hFT
      k hk hU hzero
  refine ⟨r, hr, w, hwpos, hreg, ?_⟩
  exact hboundary _ (Metric.mem_ball.mp hwU)

/-- A single regular rate perturbation simultaneously respects the
zero-free rate homotopies around any finite family of local attractors.
The radii are individual; no disjointness or index claim is asserted. -/
theorem nearby_regular_rates_preserve_finite_attractor_boundaries
    {n m : ℕ} (hn : 0 < n) (ET FT ST : ℝ)
    (hET : 0 < ET) (hFT : 0 < FT)
    (k : Rates n) (hk : k.Positive)
    (xs : Fin m → CoordinateSpace n)
    (hxs : ∀ i, IsLocallyAsymptoticallyStableClass ET FT ST k (xs i))
    (R : Fin m → ℝ) (hR : ∀ i, 0 < R i) :
    ∃ r : Fin m → ℝ, (∀ i, 0 < r i ∧ r i < R i) ∧
      ∃ w : CoordinateSpace n,
        (ratesAdd k (selectedRates w)).Positive ∧
        (let E : Set (State n) :=
          {z | z.Positive ∧
            Equilibrium (ratesAdd k (selectedRates w)) z ∧
            InClass ET FT ST z}
         E.Finite ∧ E.ncard ≤ 2 * n ∧
           ∀ z ∈ E,
             (restrictedJacobianMatrix ET FT ST
               (ratesAdd k (selectedRates w))
               (toCoordinateSpace (chart z))).det ≠ 0) ∧
        ∀ i : Fin m, ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
          ∀ y : CoordinateSpace n, dist y (xs i) = r i →
            restrictedFieldEuclid ET FT ST
              (ratesFromVector
                (rateVector k + t •
                  (rateVector (ratesAdd k (selectedRates w)) -
                    rateVector k))) y ≠ 0 := by
  classical
  choose r δ hr hrR hδ hboundary using
    (fun i => local_attractor_boundary_zero_free_rate_homotopy_below
      ET FT ST k (xs i) (hxs i) (R i) (hR i))
  let U : Set (CoordinateSpace n) :=
    ⋂ i : Fin m,
      (fun w => rateVector (ratesAdd k (selectedRates w))) ⁻¹'
        Metric.ball (rateVector k) (δ i)
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    exact Metric.isOpen_ball.preimage
      (continuous_selected_perturbed_rateVector k)
  have hzero : (0 : CoordinateSpace n) ∈ U := by
    apply Set.mem_iInter.mpr
    intro i
    change rateVector (ratesAdd k (selectedRates (0 : CoordinateSpace n))) ∈
      Metric.ball (rateVector k) (δ i)
    rw [selected_perturbed_rateVector_zero]
    exact Metric.mem_ball_self (hδ i)
  obtain ⟨w, hwU, hwpos, hreg⟩ :=
    nearby_positive_rates_finite_regular_budget hn ET FT ST hET hFT
      k hk hU hzero
  refine ⟨r, (fun i => ⟨hr i, hrR i⟩), w, hwpos, hreg, ?_⟩
  intro i t ht y hy
  exact hboundary i _
    (Metric.mem_ball.mp (Set.mem_iInter.mp hwU i)) t ht y hy

end
end PhosphorylationStableCapacity
