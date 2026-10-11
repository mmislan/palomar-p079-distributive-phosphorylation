module
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter
open scoped Topology BigOperators

/-- Finitely many near-zero first-order estimates, each uniform in a
parameter set, combine into one coefficient bound and one common
signed interval. -/
theorem finite_uniform_first_order_bounds_on_interval
    {α : Type*} (K : Set α) (N : ℕ)
    (f : Fin N → α → ℝ → ℝ)
    (hper : ∀ k : Fin N,
      ∃ C : ℝ, 0 < C ∧
        ∀ᶠ δ : ℝ in 𝓝 0,
          ∀ a ∈ K, |f k a δ-f k a 0| ≤ C*|δ|) :
    ∃ η A : ℝ, 0 < η ∧ 0 < A ∧
      ∀ δ : ℝ, |δ| < η →
        ∀ a ∈ K, ∀ k : Fin N,
          |f k a δ-f k a 0| ≤ A*|δ| := by
  classical
  choose C hC hEv using hper
  let A := (∑ k : Fin N, C k)+1
  have hA : 0 < A := by
    dsimp [A]
    have hsum : 0 ≤ ∑ k : Fin N, C k :=
      Finset.sum_nonneg (fun k hk => (hC k).le)
    linarith
  have hCbound (k : Fin N) : C k ≤ A := by
    have hle : C k ≤ ∑ i : Fin N, C i :=
      Finset.single_le_sum
        (fun i hi => (hC i).le) (Finset.mem_univ k)
    dsimp [A]
    linarith
  have hAll : ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ k : Fin N, ∀ a ∈ K,
        |f k a δ-f k a 0| ≤ C k*|δ| :=
    Filter.eventually_all.mpr hEv
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hAll
  refine ⟨η, A, hη, hA, ?_⟩
  intro δ hδ a ha k
  have hmem : δ ∈ Metric.ball (0 : ℝ) η := by
    simpa [Metric.mem_ball, Real.dist_eq] using hδ
  exact (hball hmem k a ha).trans
    (mul_le_mul_of_nonneg_right (hCbound k) (abs_nonneg δ))

end

end PhosphorylationStableCapacity
