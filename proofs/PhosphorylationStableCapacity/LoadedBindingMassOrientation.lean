module
public import proofs.PhosphorylationStableCapacity.LoadedBindingPositive
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The bound-complex quadratic correction stays nonnegative when the
enzyme total is any positive free concentration plus its complexes. -/
theorem binding_complex_quadratic_nonneg_general {ι : Type*} [Fintype ι]
    (C σ : ι → ℝ) (ET e : ℝ)
    (hC : ∀ i, 0 ≤ C i) (he : 0 < e)
    (hET : ET = e + ∑ i, C i) :
    0 ≤ (∑ i, C i * σ i ^ 2) -
      (∑ i, C i * σ i) ^ 2 / ET := by
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => hC i)
  have hETpos : 0 < ET := by rw [hET]; linarith
  have hsq : 0 ≤ ∑ i, C i * σ i ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hC i) (sq_nonneg _))
  have hcs := weighted_binding_cauchy C σ hC
  apply sub_nonneg.mpr
  apply (div_le_iff₀ hETpos).mpr
  rw [hET]
  nlinarith

theorem loadedBindingMass_quadratic_pos_general {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (S C Y σ : ι → ℝ) (ET FT E F : ℝ)
    (hS : ∀ i, 0 < S i)
    (hC : ∀ i, 0 ≤ C i)
    (hY : ∀ i, 0 ≤ Y i)
    (hE : 0 < E) (hF : 0 < F)
    (hET : ET = E + ∑ i, C i)
    (hFT : FT = F + ∑ i, Y i)
    (hσ : σ ≠ 0) :
    0 < ∑ i, σ i * (loadedBindingMass S C Y ET FT).mulVec σ i := by
  have hex : ∃ i, σ i ≠ 0 := by
    by_contra h
    push Not at h
    apply hσ
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  have hSsum : 0 < ∑ j, S j * σ j ^ 2 :=
    Finset.sum_pos' (fun j _ => mul_nonneg (hS j).le (sq_nonneg _))
      ⟨i, Finset.mem_univ i, mul_pos (hS i) (sq_pos_of_ne_zero hi)⟩
  have hCnon := binding_complex_quadratic_nonneg_general C σ ET E
    hC hE hET
  have hYnon := binding_complex_quadratic_nonneg_general Y σ FT F
    hY hF hFT
  rw [loadedBindingMass_quadratic]
  linarith

theorem loadedBindingMass_isHermitian {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (S C Y : ι → ℝ) (ET FT : ℝ) :
    (loadedBindingMass S C Y ET FT).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [loadedBindingMass]
  · simp [loadedBindingMass, hij, Ne.symm hij, mul_comm]

/-- The full binding inventory mass matrix preserves orientation at
every positive physical state with its actual enzyme totals. -/
theorem loadedBindingMass_det_pos_general {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (S C Y : ι → ℝ) (ET FT E F : ℝ)
    (hS : ∀ i, 0 < S i)
    (hC : ∀ i, 0 ≤ C i)
    (hY : ∀ i, 0 ≤ Y i)
    (hE : 0 < E) (hF : 0 < F)
    (hET : ET = E + ∑ i, C i)
    (hFT : FT = F + ∑ i, Y i) :
    0 < (loadedBindingMass S C Y ET FT).det := by
  have hpos : (loadedBindingMass S C Y ET FT).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
      (loadedBindingMass_isHermitian S C Y ET FT)
    intro σ hσ
    simpa only [dotProduct, star_trivial] using
      loadedBindingMass_quadratic_pos_general S C Y σ ET FT E F
        hS hC hY hE hF hET hFT hσ
  exact hpos.det_pos

/-- Attach each literal kinase and phosphatase complex to its substrate
level, using zero at the absent endpoint. -/
def sourceLevelC {n : ℕ} (x : State n) (j : Fin (n+1)) : ℝ :=
  ∑ i : Fin n, if i.castSucc = j then x.C i else 0

def sourceLevelD {n : ℕ} (x : State n) (j : Fin (n+1)) : ℝ :=
  ∑ i : Fin n, if i.succ = j then x.D i else 0

theorem sourceLevelC_sum {n : ℕ} (x : State n) :
    (∑ j, sourceLevelC x j) = ∑ i, x.C i := by
  simp [sourceLevelC, Finset.sum_comm]

theorem sourceLevelD_sum {n : ℕ} (x : State n) :
    (∑ j, sourceLevelD x j) = ∑ i, x.D i := by
  simp [sourceLevelD, Finset.sum_comm]

theorem sourceLevelC_nonneg {n : ℕ} (x : State n)
    (hC : ∀ i, 0 ≤ x.C i) (j : Fin (n+1)) :
    0 ≤ sourceLevelC x j := by
  unfold sourceLevelC
  exact Finset.sum_nonneg (fun i _ => by
    by_cases h : i.castSucc = j
    · simpa [h] using hC i
    · simp [h])

theorem sourceLevelD_nonneg {n : ℕ} (x : State n)
    (hD : ∀ i, 0 ≤ x.D i) (j : Fin (n+1)) :
    0 ≤ sourceLevelD x j := by
  unfold sourceLevelD
  exact Finset.sum_nonneg (fun i _ => by
    by_cases h : i.succ = j
    · simpa [h] using hD i
    · simp [h])

/-- The binding mass matrix built from the actual literal species has
positive orientation at every positive state. -/
theorem source_loadedBindingMass_det_pos {n : ℕ} (x : State n)
    (hx : x.Positive) :
    0 < (loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
      (totalE x) (totalF x)).det := by
  apply loadedBindingMass_det_pos_general
    x.S (sourceLevelC x) (sourceLevelD x)
    (totalE x) (totalF x) x.E x.F
  · exact hx.1
  · intro i
    exact sourceLevelC_nonneg x (fun j => (hx.2.2.2.1 j).le) i
  · intro i
    exact sourceLevelD_nonneg x (fun j => (hx.2.2.2.2 j).le) i
  · exact hx.2.1
  · exact hx.2.2.1
  · simp [totalE, sourceLevelC_sum]
  · simp [totalF, sourceLevelD_sum]

end
end PhosphorylationStableCapacity
