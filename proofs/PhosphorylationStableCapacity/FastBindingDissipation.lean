module
public import proofs.PhosphorylationStableCapacity.FastBindingAffinity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

def fastBindingLinear {n : ℕ} (x : State n)
    (ρ σ : Fin n → ℝ) (v : FastSpace n) : FastSpace n :=
  (fun i => -ρ i * fastAffinityC x v i,
    fun i => -σ i * fastAffinityD x v i)

theorem weightedSquareMul_nonneg {ι : Type*} [Fintype ι]
    (w v : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ ∑ i, w i * v i ^ 2 := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))

theorem weightedSquareMul_pos {ι : Type*} [Fintype ι]
    (w v : ι → ℝ) (hw : ∀ i, 0 < w i) (hv : v ≠ 0) :
    0 < ∑ i, w i * v i ^ 2 := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_pos'
    (fun j _ => mul_nonneg (hw j).le (sq_nonneg _))
    ⟨i, Finset.mem_univ i, mul_pos (hw i) (sq_pos_of_ne_zero hi)⟩

/-- A nonzero fast perturbation has a nonzero binding affinity. -/
theorem fastAffinities_nonzero {n : ℕ} (x : State n)
    (hx : x.Positive) (v : FastSpace n) (hv : v ≠ 0) :
    (fun i => fastAffinityC x v i) ≠ 0 ∨
      (fun i => fastAffinityD x v i) ≠ 0 := by
  by_contra h
  push Not at h
  have hpos := fastBindingEnergy_pos x hx v hv
  rw [fastBindingEnergy_eq_affinity_pairing] at hpos
  simp [h.1, h.2] at hpos

/-- The binding fast operator dissipates the strictly positive concentration
metric in every nonzero complex direction. -/
theorem fastBindingLinear_dissipative {n : ℕ} (x : State n)
    (hx : x.Positive) (ρ σ : Fin n → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    (v : FastSpace n) (hv : v ≠ 0) :
    (∑ i, fastAffinityC x v i * (fastBindingLinear x ρ σ v).1 i) +
      (∑ i, fastAffinityD x v i * (fastBindingLinear x ρ σ v).2 i) < 0 := by
  have hC0 := weightedSquareMul_nonneg ρ (fastAffinityC x v)
    (fun i => (hρ i).le)
  have hD0 := weightedSquareMul_nonneg σ (fastAffinityD x v)
    (fun i => (hσ i).le)
  have hstrict :
      0 < (∑ i, ρ i * fastAffinityC x v i ^ 2) +
        (∑ i, σ i * fastAffinityD x v i ^ 2) := by
    rcases fastAffinities_nonzero x hx v hv with hC | hD
    · exact add_pos_of_pos_of_nonneg
        (weightedSquareMul_pos ρ (fastAffinityC x v) hρ hC) hD0
    · exact add_pos_of_nonneg_of_pos hC0
        (weightedSquareMul_pos σ (fastAffinityD x v) hσ hD)
  simp only [fastBindingLinear]
  have hC :
      (∑ i, fastAffinityC x v i * (-ρ i * fastAffinityC x v i)) =
        -(∑ i, ρ i * fastAffinityC x v i ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hD :
      (∑ i, fastAffinityD x v i * (-σ i * fastAffinityD x v i)) =
        -(∑ i, σ i * fastAffinityD x v i ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hC, hD]
  simpa only [neg_add] using (neg_lt_zero.mpr hstrict)

/-- Strict dissipation rules out every nonzero fast kernel vector. -/
theorem fastBindingLinear_kernel_zero {n : ℕ} (x : State n)
    (hx : x.Positive) (ρ σ : Fin n → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    (v : FastSpace n) (hv : fastBindingLinear x ρ σ v = 0) :
    v = 0 := by
  by_contra hne
  have hneg := fastBindingLinear_dissipative x hx ρ σ hρ hσ v hne
  rw [hv] at hneg
  simp at hneg

end
end PhosphorylationStableCapacity
