module
/-
Copyright (c) 2026 Michael Mislan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

This module is compiled in the separately authorized Lean 4.35 degree
environment. It is not part of the frozen Lean 4.30 project.
-/

public import DifferentialGeometry.Topology.LocalDegree.ClosedBall
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.ProperSpace

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace PhosphorylationStableCapacity.Topology435

noncomputable section

open Set Metric

abbrev CoordinateSpace435 (n : ℕ) :=
  (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)

/-- Every positive-site coordinate space has a linear Euclidean chart
of its full finite dimension. -/
theorem exists_coordinate_chart (n : ℕ) (hn : 0 < n) :
    ∃ d : ℕ, Nonempty
      (CoordinateSpace435 n ≃L[ℝ]
        EuclideanSpace ℝ (Fin (d + 1))) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let E := CoordinateSpace435 n
  haveI : Nontrivial E := inferInstance
  have hpos : 0 < Module.finrank ℝ E := Module.finrank_pos
  let d := Module.finrank ℝ E - 1
  have hdim : Module.finrank ℝ E = d + 1 :=
    (Nat.sub_add_cancel hpos).symm
  have heq : Module.finrank ℝ E =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (d + 1))) := by
    simpa using hdim
  exact ⟨d, ⟨ContinuousLinearEquiv.ofFinrankEq heq⟩⟩

/-- The product-norm ball lies strictly inside some Euclidean ball
after applying the chosen chart. -/
theorem exists_coordinate_enclosure (n : ℕ) (hn : 0 < n)
    (a : CoordinateSpace435 n) (r : ℝ) (_hr : 0 < r) :
    ∃ (d : ℕ) (A : CoordinateSpace435 n ≃L[ℝ]
        EuclideanSpace ℝ (Fin (d + 1))) (R : ℝ),
      0 < R ∧
      ∀ x : closedBall a r, A x.val ∈ ball (A a) R := by
  obtain ⟨d, ⟨A⟩⟩ := exists_coordinate_chart n hn
  have hcompact : IsCompact (A '' closedBall a r) :=
    (isCompact_closedBall a r).image A.continuous
  obtain ⟨R, hR, hcover⟩ := hcompact.isBounded.subset_ball_lt 0 (A a)
  exact ⟨d, A, R, hR, fun x => hcover ⟨x.val, x.property, rfl⟩⟩

end

end PhosphorylationStableCapacity.Topology435
