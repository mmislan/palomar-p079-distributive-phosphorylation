module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open Filter
open scoped Topology

private theorem abs_finset_prod_le_pow
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, |f i| ≤ B) :
    |∏ i ∈ s, f i| ≤ B ^ s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hfi : |f i| ≤ B := hf i (Finset.mem_insert_self i s)
      have hrest : ∀ j ∈ s, |f j| ≤ B := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have hprod := ih hrest
      rw [Finset.prod_insert hi, abs_mul, Finset.card_insert_of_notMem hi,
        pow_succ]
      simpa only [mul_comm] using
        mul_le_mul hfi hprod (abs_nonneg _) hB

/-- If every factor is uniformly bounded and has one shared
first-order scalar perturbation bound, its finite product has a
single first-order bound valid throughout the same parameter tube.
This elementary lemma avoids a separate parameterized implicit
function theorem in the compact current calculation. -/
theorem uniform_finite_product_first_order
    {α ι : Type*} [DecidableEq ι]
    (s : Finset ι) (K : Set α) (f : ι → α → ℝ → ℝ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hfirst : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ),
      ∀ ω ∈ K, ∀ i ∈ s,
        |f i ω δ - f i ω 0| ≤ A*|δ|)
    (hbound : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ),
      ∀ ω ∈ K, ∀ i ∈ s,
        |f i ω δ| ≤ B ∧ |f i ω 0| ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ),
        ∀ ω ∈ K,
          |(∏ i ∈ s, f i ω δ) - (∏ i ∈ s, f i ω 0)| ≤
            C*|δ| := by
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, by norm_num, Filter.Eventually.of_forall ?_⟩
      intro δ ω hω
      simp
  | @insert i s hi ih =>
      have hfirstRest : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ),
          ∀ ω ∈ K, ∀ j ∈ s,
            |f j ω δ - f j ω 0| ≤ A*|δ| := by
        filter_upwards [hfirst] with δ hδ ω hω j hj
        exact hδ ω hω j (Finset.mem_insert_of_mem hj)
      have hboundRest : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ),
          ∀ ω ∈ K, ∀ j ∈ s,
            |f j ω δ| ≤ B ∧ |f j ω 0| ≤ B := by
        filter_upwards [hbound] with δ hδ ω hω j hj
        exact hδ ω hω j (Finset.mem_insert_of_mem hj)
      obtain ⟨C, hC, hrest⟩ := ih hfirstRest hboundRest
      let C' := A*B^s.card+B*C
      have hC' : 0 < C' := by
        have hfirstTerm : 0 ≤ A*B^s.card :=
          mul_nonneg hA (pow_nonneg (by linarith) _)
        have hsecondTerm : 0 < B*C := mul_pos (by linarith) hC
        dsimp [C']
        linarith
      refine ⟨C', hC', ?_⟩
      filter_upwards [hfirst, hbound, hrest]
        with δ hδ hδbound hδrest ω hω
      have hfi := hδ ω hω i (Finset.mem_insert_self i s)
      have hfiBound := (hδbound ω hω i (Finset.mem_insert_self i s)).2
      have hprodBound : |∏ j ∈ s, f j ω δ| ≤ B^s.card :=
        abs_finset_prod_le_pow s (fun j => f j ω δ) B (by linarith)
          (fun j hj => (hδbound ω hω j
            (Finset.mem_insert_of_mem hj)).1)
      have hrestBound := hδrest ω hω
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      calc
        |f i ω δ * (∏ j ∈ s, f j ω δ) -
            f i ω 0 * (∏ j ∈ s, f j ω 0)| =
            |(f i ω δ-f i ω 0)*(∏ j ∈ s, f j ω δ) +
              f i ω 0*((∏ j ∈ s, f j ω δ)-
                (∏ j ∈ s, f j ω 0))| := by congr 1; ring
        _ ≤ |f i ω δ-f i ω 0| *|∏ j ∈ s, f j ω δ| +
              |f i ω 0| *|(∏ j ∈ s, f j ω δ)-
                (∏ j ∈ s, f j ω 0)| := by
              simpa only [abs_mul] using abs_add_le
                ((f i ω δ-f i ω 0)*(∏ j ∈ s, f j ω δ))
                (f i ω 0*((∏ j ∈ s, f j ω δ)-
                  (∏ j ∈ s, f j ω 0)))
        _ ≤ (A*|δ|)*B^s.card+B*(C*|δ|) := by
              apply add_le_add
              · exact mul_le_mul hfi hprodBound (abs_nonneg _)
                  (mul_nonneg hA (abs_nonneg _))
              · exact mul_le_mul hfiBound hrestBound (abs_nonneg _)
                  (by linarith)
        _ = C'*|δ| := by dsimp [C']; ring

end

end PhosphorylationStableCapacity
