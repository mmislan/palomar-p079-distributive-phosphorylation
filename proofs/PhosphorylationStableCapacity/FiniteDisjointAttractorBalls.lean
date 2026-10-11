module
public import proofs.PhosphorylationStableCapacity.SelectedRateNeighborhoodBridge
public import proofs.PhosphorylationStableCapacity.ClassUniformAttraction
public import proofs.PhosphorylationStableCapacity.ClassNoPeriodicInBasin
public import Mathlib.Topology.MetricSpace.Infsep

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness

/-- A finite family of distinct class states has one positive radius
bound such that any smaller closed balls around them are disjoint. -/
theorem finite_distinct_centers_small_balls_disjoint {n : ℕ}
    (hn : 0 < n) (xs : Fin (n + 1) → CoordinateSpace n)
    (hxs : Function.Injective xs) :
    ∃ R : ℝ, 0 < R ∧
      ∀ r : Fin (n + 1) → ℝ,
        (∀ i, 0 < r i ∧ r i < R) →
        ∀ i j, i ≠ j →
          Disjoint (Metric.closedBall (xs i) (r i))
            (Metric.closedBall (xs j) (r j)) := by
  classical
  let S : Set (CoordinateSpace n) := Set.range xs
  have hfinite : S.Finite := Set.finite_range xs
  let i₀ : Fin (n + 1) := ⟨0, by omega⟩
  let i₁ : Fin (n + 1) := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [i₀, i₁] at hv
  have hnon : S.Nontrivial :=
    ⟨xs i₀, ⟨i₀, rfl⟩, xs i₁, ⟨i₁, rfl⟩, hxs.ne hi⟩
  have hsep : 0 < S.infsep :=
    (hfinite.infsep_pos_iff_nontrivial).mpr hnon
  refine ⟨S.infsep / 3, by positivity, ?_⟩
  intro r hr i j hij
  apply Set.disjoint_left.mpr
  intro y hyi hyj
  have hpair : S.infsep ≤ dist (xs i) (xs j) :=
    Set.infsep_le_dist_of_mem ⟨i, rfl⟩ ⟨j, rfl⟩
      (hxs.ne hij)
  have hiy : dist (xs i) y ≤ r i := by
    simpa [dist_comm] using (Metric.mem_closedBall.mp hyi)
  have hyj' : dist y (xs j) ≤ r j := Metric.mem_closedBall.mp hyj
  have htri := dist_triangle (xs i) y (xs j)
  have hri := (hr i).2
  have hrj := (hr j).2
  linarith

/-- At `n+1` distinct local attractors, one positive regular rate
perturbation has at most `2n` positive equilibria while the literal
rate homotopy stays zero-free on pairwise disjoint enclosing spheres.
No degree, local index, or interior persistence is asserted here. -/
theorem nearby_regular_rates_with_disjoint_attractor_boundaries
    {n : ℕ} (hn : 0 < n) (ET FT ST : ℝ)
    (hET : 0 < ET) (hFT : 0 < FT)
    (k : Rates n) (hk : k.Positive)
    (xs : Fin (n + 1) → CoordinateSpace n)
    (hinj : Function.Injective xs)
    (hxs : ∀ i, IsLocallyAsymptoticallyStableClass ET FT ST k (xs i))
    (hstrict : ∀ i, xs i ∈ classPolytopeStrict n ET FT ST) :
    ∃ r : Fin (n + 1) → ℝ,
      (∀ i, 0 < r i) ∧
      (∀ i j, i ≠ j →
        Disjoint (Metric.closedBall (xs i) (r i))
          (Metric.closedBall (xs j) (r j))) ∧
      (∀ i, Metric.closedBall (xs i) (r i) ⊆
        classPolytopeStrict n ET FT ST) ∧
      (∀ i, ∃ T : ℝ, 0 < T ∧
        ∀ z : classPolytope n ET FT ST,
          dist z.1 (xs i) ≤ r i →
            dist (physicalForwardCurve ET FT ST hET k hk z T) (xs i) < r i) ∧
      (∀ i, ∀ z : classPolytope n ET FT ST,
        dist z.1 (xs i) = r i → ∀ t : ℝ, 0 < t →
          physicalForwardCurve ET FT ST hET k hk z t ≠ z.1) ∧
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
        ∀ i : Fin (n + 1), ∀ t : ℝ,
          t ∈ Set.Icc (0 : ℝ) 1 →
          ∀ y : CoordinateSpace n, dist y (xs i) = r i →
            restrictedFieldEuclid ET FT ST
              (ratesFromVector
                (rateVector k + t •
                  (rateVector (ratesAdd k (selectedRates w)) -
                    rateVector k))) y ≠ 0 := by
  obtain ⟨R, hR, hdisj⟩ :=
    finite_distinct_centers_small_balls_disjoint hn xs hinj
  have hopen : IsOpen (classPolytopeStrict n ET FT ST) :=
    classPolytopeStrict_isOpen n ET FT ST
  choose ε hε hball using
    (fun i => Metric.isOpen_iff.mp hopen (xs i) (hstrict i))
  have hxmem : ∀ i, xs i ∈ classPolytope n ET FT ST :=
    fun i => (classPolytopeStrict_subset n ET FT ST) (hstrict i)
  choose r₀ hr₀ huniform using
    (fun i => local_attractor_uniform_on_closedBall
      ET FT ST hET k hk (xs i) (hxs i) (hxmem i))
  choose δ hδ hnoreturn using
    (fun i => local_attractor_no_positive_time_return
      ET FT ST hET k hk (xs i) (hxs i))
  let R' : Fin (n + 1) → ℝ :=
    fun i => min R (min (ε i / 2) (min (r₀ i) (δ i)))
  have hR' : ∀ i, 0 < R' i := by
    intro i
    exact lt_min hR (lt_min (by linarith [hε i])
      (lt_min (hr₀ i) (hδ i)))
  obtain ⟨r, hr, w, hwpos, hreg, hboundary⟩ :=
    nearby_regular_rates_preserve_finite_attractor_boundaries
      hn ET FT ST hET hFT k hk xs hxs R' hR'
  have hrsep : ∀ i, 0 < r i ∧ r i < R := by
    intro i
    exact ⟨(hr i).1, lt_of_lt_of_le (hr i).2 (min_le_left _ _)⟩
  have hinside : ∀ i, Metric.closedBall (xs i) (r i) ⊆
      classPolytopeStrict n ET FT ST := by
    intro i y hy
    apply hball i
    apply Metric.mem_ball.mpr
    have hdist : dist y (xs i) ≤ r i := Metric.mem_closedBall.mp hy
    have hri : r i < ε i / 2 :=
      lt_of_lt_of_le (lt_of_lt_of_le (hr i).2 (min_le_right _ _))
        (min_le_left _ _)
    linarith [hε i]
  have hinward : ∀ i, ∃ T : ℝ, 0 < T ∧
      ∀ z : classPolytope n ET FT ST,
        dist z.1 (xs i) ≤ r i →
          dist (physicalForwardCurve ET FT ST hET k hk z T) (xs i) < r i := by
    intro i
    obtain ⟨T₀, hT₀, hbound⟩ := huniform i (r i) (hr i).1
    let T := max 1 T₀
    refine ⟨T, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
    intro z hz
    have hRr₀ : R' i ≤ r₀ i := by
      dsimp [R']
      exact (min_le_right R _).trans
        ((min_le_right (ε i / 2) _).trans (min_le_left (r₀ i) (δ i)))
    have hrle : r i ≤ r₀ i :=
      le_of_lt ((hr i).2.trans_le hRr₀)
    have hz₀ : z ∈ Metric.closedBall
        (⟨xs i, hxmem i⟩ : classPolytope n ET FT ST) (r₀ i) :=
      Metric.mem_closedBall.mpr (by
        simpa only [Subtype.dist_eq] using hz.trans hrle)
    exact hbound z hz₀ T (le_max_right _ _)
  have hnoReturn : ∀ i, ∀ z : classPolytope n ET FT ST,
      dist z.1 (xs i) = r i → ∀ t : ℝ, 0 < t →
        physicalForwardCurve ET FT ST hET k hk z t ≠ z.1 := by
    intro i z hz t ht hfix
    have hRδ : R' i ≤ δ i := by
      dsimp [R']
      exact (min_le_right R _).trans
        ((min_le_right (ε i / 2) _).trans (min_le_right (r₀ i) (δ i)))
    have hrδ : r i < δ i := (hr i).2.trans_le hRδ
    have hzx := hnoreturn i z (by rw [hz]; exact hrδ) t ht hfix
    rw [hzx, dist_self] at hz
    exact (ne_of_gt (hr i).1) hz.symm
  exact ⟨r, (fun i => (hr i).1), hdisj r hrsep, hinside,
    hinward, hnoReturn,
    w, hwpos, hreg, hboundary⟩

end
end PhosphorylationStableCapacity
