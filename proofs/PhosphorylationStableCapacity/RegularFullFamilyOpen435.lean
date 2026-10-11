module
public import proofs.PhosphorylationStableCapacity.OpenParameterPersistence
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter
open scoped Topology Matrix.Norms.L2Operator

/-- Physical state positivity and nonsingularity of the actual class
Jacobian form an open condition jointly in every rate, total and state
coordinate. Nonsingularity excludes zero eigenvalues only. -/
theorem isOpen_capacityParameterRegularPositive (n : ℕ) :
    IsOpen {q : CapacityParameter n × CoordinateSpace n |
      (unChart q.1.2.1 q.1.2.2.1 q.1.2.2.2
        (ofCoordinateSpace q.2)).Positive ∧
      (restrictedJacobianMatrix q.1.2.1 q.1.2.2.1 q.1.2.2.2
        (ratesFromVector q.1.1) q.2).det ≠ 0} := by
  have hdet : Continuous (fun q : CapacityParameter n × CoordinateSpace n =>
      (restrictedJacobianMatrix q.1.2.1 q.1.2.2.1 q.1.2.2.2
        (ratesFromVector q.1.1) q.2).det) :=
    (continuous_capacityParameterJacobianMatrix n).matrix_det
  exact (isOpen_capacityParameterStatePositive n).inter
    (isOpen_ne.preimage hdet)

/-- A full regular family at a specified physical parameter persists on
one open neighborhood of that very parameter. Every continued family is
positive, distinct, regular and exhaustive, with the exact maximal count.
No hyperbolicity or sink/saddle premise is required. -/
theorem capacity_open_full_regular_family_of_base
    (n : ℕ) (hn : 0 < n) (p₀ : CapacityParameter n)
    (u₀ : Fin (2*n-1) → CoordinateSpace n)
    (hparam : (ratesFromVector p₀.1).Positive ∧
      0 < p₀.2.1 ∧ 0 < p₀.2.2.1 ∧ 0 < p₀.2.2.2)
    (hinj : Function.Injective u₀)
    (hstates : ∀ j,
      (unChart p₀.2.1 p₀.2.2.1 p₀.2.2.2
        (ofCoordinateSpace (u₀ j))).Positive ∧
      capacityParameterField (p₀, u₀ j) = 0 ∧
      (restrictedJacobianMatrix p₀.2.1 p₀.2.2.1 p₀.2.2.2
        (ratesFromVector p₀.1) (u₀ j)).det ≠ 0) :
    ∃ s : Set (CapacityParameter n), IsOpen s ∧ p₀ ∈ s ∧
      ∀ p ∈ s,
        ((ratesFromVector p.1).Positive ∧
          0 < p.2.1 ∧ 0 < p.2.2.1 ∧ 0 < p.2.2.2) ∧
        ∃ u : Fin (2*n-1) → CoordinateSpace n,
          Function.Injective u ∧
          (∀ j,
            (unChart p.2.1 p.2.2.1 p.2.2.2
              (ofCoordinateSpace (u j))).Positive ∧
            capacityParameterField (p, u j) = 0 ∧
            (restrictedJacobianMatrix p.2.1 p.2.2.1 p.2.2.2
              (ratesFromVector p.1) (u j)).det ≠ 0) ∧
          {z : State n | z.Positive ∧ Equilibrium (ratesFromVector p.1) z ∧
            InClass p.2.1 p.2.2.1 p.2.2.2 z} =
              Set.range (fun j => unChart p.2.1 p.2.2.1 p.2.2.2
                (ofCoordinateSpace (u j))) ∧
          {z : State n | z.Positive ∧ Equilibrium (ratesFromVector p.1) z ∧
            InClass p.2.1 p.2.2.1 p.2.2.2 z}.ncard = 2*n-1 := by
  classical
  let good : Fin (2*n-1) → Set (CapacityParameter n × CoordinateSpace n) :=
    fun _ => {q |
      (unChart q.1.2.1 q.1.2.2.1 q.1.2.2.2
        (ofCoordinateSpace q.2)).Positive ∧
      (restrictedJacobianMatrix q.1.2.1 q.1.2.2.1 q.1.2.2.2
        (ratesFromVector q.1.1) q.2).det ≠ 0}
  have hgood (j : Fin (2*n-1)) : IsOpen (good j) :=
    isOpen_capacityParameterRegularPositive n
  have hbase : Function.Injective u₀ ∧ ∀ j,
      capacityParameterField (p₀, u₀ j) = 0 ∧ (p₀, u₀ j) ∈ good j ∧
      (fderiv ℝ (capacityParameterField (n := n)) (p₀, u₀ j) ∘L
        ContinuousLinearMap.inr ℝ (CapacityParameter n) (CoordinateSpace n)).IsInvertible := by
    refine ⟨hinj, ?_⟩
    intro j
    exact ⟨(hstates j).2.1, ⟨(hstates j).1, (hstates j).2.2⟩,
      capacity_parameter_field_regular_of_det_ne_zero p₀ (u₀ j) (hstates j).2.2⟩
  obtain ⟨s, hsopen, hp₀, hs⟩ :=
    finite_regular_family_open_persistence (2*n-1)
      (capacityParameterField (n := n)) good p₀ u₀
      (contDiff_capacityParameterField n) hgood hbase
  let t : Set (CapacityParameter n) :=
    s ∩ {p | (ratesFromVector p.1).Positive ∧
      0 < p.2.1 ∧ 0 < p.2.2.1 ∧ 0 < p.2.2.2}
  refine ⟨t, hsopen.inter (isOpen_capacityParameterPositive n),
    ⟨hp₀, hparam⟩, ?_⟩
  intro p hp
  obtain ⟨u, huinj, hu⟩ := hs p hp.1
  have hstates' : ∀ j,
      (unChart p.2.1 p.2.2.1 p.2.2.2
        (ofCoordinateSpace (u j))).Positive ∧
      capacityParameterField (p, u j) = 0 :=
    fun j => ⟨(hu j).2.1, (hu j).1⟩
  have hex := capacity_exact_count_of_full_positive_family n hn p hp.2 u huinj hstates'
  exact ⟨hp.2, u, huinj,
    fun j => ⟨(hu j).2.1, (hu j).1, (hu j).2.2⟩, hex⟩

end

end PhosphorylationStableCapacity
