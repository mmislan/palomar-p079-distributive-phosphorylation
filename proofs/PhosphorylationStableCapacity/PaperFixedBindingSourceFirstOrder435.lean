module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitStateDifferentiability
public import proofs.PhosphorylationStableCapacity.SplitFirstOrderBound

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter
open scoped Topology

/-- A single signed split-parameter tube and one first-order constant
control every source association and conversion coefficient that enters
the literal frozen-binding physical determinant product. -/
theorem paperFixedBinding_source_alpha_c_finite_first_order
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1)) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      (∀ i : Fin (m+2),
        |(arbitrarySplitFiniteRates (m+1) ξ r 0).c i| ≤ B ∧
        |(arbitrarySplitFiniteRates (m+1) ξ r 0).alpha i| ≤ B) ∧
      (∀ᶠ δ : ℝ in 𝓝 0,
        |δ| ≤ 1 ∧ ∀ i : Fin (m+2),
          |(arbitrarySplitFiniteRates (m+1) ξ r δ).c i -
            (arbitrarySplitFiniteRates (m+1) ξ r 0).c i| ≤ A*|δ| ∧
          |(arbitrarySplitFiniteRates (m+1) ξ r δ).alpha i -
            (arbitrarySplitFiniteRates (m+1) ξ r 0).alpha i| ≤ A*|δ|) := by
  classical
  let base (δ : ℝ) := arbitrarySplitFiniteRates (m+1) ξ r δ
  have hdiff := arbitrarySplitFiniteRates_components_differentiableAt
    (m+1) ξ r hr hD₀ hB₀
  have hper (i : Fin (m+2)) : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ δ : ℝ in 𝓝 0,
        |(base δ).c i-(base 0).c i| ≤ C*|δ| ∧
        |(base δ).alpha i-(base 0).alpha i| ≤ C*|δ| := by
    obtain ⟨_, _, hc, hα, _, _⟩ := hdiff i
    obtain ⟨Cc, hCc, hce⟩ :=
      differentiableAt_first_order_abs_bound
        (fun δ => (base δ).c i) hc
    obtain ⟨Ca, hCa, hae⟩ :=
      differentiableAt_first_order_abs_bound
        (fun δ => (base δ).alpha i) hα
    refine ⟨Cc+Ca+1, by positivity, ?_⟩
    filter_upwards [hce, hae] with δ hcδ haδ
    constructor
    · exact hcδ.trans (mul_le_mul_of_nonneg_right
        (by linarith : Cc ≤ Cc+Ca+1) (abs_nonneg δ))
    · exact haδ.trans (mul_le_mul_of_nonneg_right
        (by linarith : Ca ≤ Cc+Ca+1) (abs_nonneg δ))
  choose C hC hEvent using hper
  let A := (∑ i : Fin (m+2), C i)+1
  let B := (∑ i : Fin (m+2),
    (|(base 0).c i|+|(base 0).alpha i|))+1
  have hA : 0 < A := by
    dsimp [A]
    have hsum : 0 ≤ ∑ i : Fin (m+2), C i :=
      Finset.sum_nonneg (fun i hi => (hC i).le)
    linarith
  have hB : 0 < B := by
    dsimp [B]
    have hsum : 0 ≤ ∑ i : Fin (m+2),
        (|(base 0).c i|+|(base 0).alpha i|) := by
      exact Finset.sum_nonneg (fun i hi =>
        add_nonneg (abs_nonneg _) (abs_nonneg _))
    linarith
  have hCbound (i : Fin (m+2)) : C i ≤ A := by
    have hsingle : C i ≤ ∑ j : Fin (m+2), C j :=
      Finset.single_le_sum (fun j hj => (hC j).le) (Finset.mem_univ i)
    dsimp [A]
    linarith
  have hbase (i : Fin (m+2)) :
      |(base 0).c i| ≤ B ∧ |(base 0).alpha i| ≤ B := by
    have hsingle : |(base 0).c i|+|(base 0).alpha i| ≤
        ∑ j : Fin (m+2),
          (|(base 0).c j|+|(base 0).alpha j|) :=
      Finset.single_le_sum (fun j hj =>
        add_nonneg (abs_nonneg ((base 0).c j))
          (abs_nonneg ((base 0).alpha j))) (Finset.mem_univ i)
    dsimp [B]
    constructor <;> linarith [abs_nonneg ((base 0).c i),
      abs_nonneg ((base 0).alpha i)]
  have hsmall : ∀ᶠ δ : ℝ in 𝓝 0, |δ| ≤ 1 := by
    have hball : ∀ᶠ δ : ℝ in 𝓝 0,
        δ ∈ Metric.ball (0 : ℝ) 1 :=
      Metric.ball_mem_nhds 0 (by norm_num)
    filter_upwards [hball] with δ hd
    exact le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hd)
  refine ⟨A, B, hA, hB, ?_, ?_⟩
  · intro i
    exact hbase i
  · have hAll : ∀ᶠ δ : ℝ in 𝓝 0,
        ∀ i : Fin (m+2),
          |(base δ).c i-(base 0).c i| ≤ C i*|δ| ∧
          |(base δ).alpha i-(base 0).alpha i| ≤ C i*|δ| :=
      Filter.eventually_all.mpr hEvent
    filter_upwards [hsmall, hAll] with δ hd he
    refine ⟨hd, ?_⟩
    intro i
    exact ⟨(he i).1.trans (mul_le_mul_of_nonneg_right
        (hCbound i) (abs_nonneg δ)),
      (he i).2.trans (mul_le_mul_of_nonneg_right
        (hCbound i) (abs_nonneg δ))⟩

end

end PhosphorylationStableCapacity
