module
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import proofs.PhosphorylationStableCapacity.SplitRootFamily

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Filter
open scoped Topology

/-- Prescribed splitting offsets, with no positivity or ordering restriction. -/
def offsetSplitRoot (ξ : ℕ → ℝ) (δ : ℝ) (j : ℕ) : ℝ :=
  3 + δ * ξ j

/-- The paper's paired-root recurrence for arbitrary real offsets. -/
def arbitrarySplitPair : ℕ → (ℕ → ℝ) → ℝ → ℝ[X] × ℝ[X]
  | 0, ξ, δ => (1, C ((offsetSplitRoot ξ δ 0 - 1) / 2))
  | m + 1, ξ, δ =>
      let pq := arbitrarySplitPair m ξ δ
      (nextN (offsetSplitRoot ξ δ (2*m+1))
        (offsetSplitRoot ξ δ (2*m+2)) pq.1 pq.2,
       nextJ (offsetSplitRoot ξ δ (2*m+1))
        (offsetSplitRoot ξ δ (2*m+2)) pq.1 pq.2)

def arbitrarySplitScalarProduct : ℕ → (ℕ → ℝ) → ℝ → ℝ → ℝ
  | 0, ξ, δ, x => x - offsetSplitRoot ξ δ 0
  | m+1, ξ, δ, x =>
      (x-offsetSplitRoot ξ δ (2*m+1)) *
        (x-offsetSplitRoot ξ δ (2*m+2)) *
          arbitrarySplitScalarProduct m ξ δ x

/-- The arbitrary-offset family still has the same coalesced limiting
source. The choice of offsets changes only its unfolding. -/
theorem arbitrarySplitPair_zero_eq_coalesced (m : ℕ) (ξ : ℕ → ℝ) :
    arbitrarySplitPair m ξ 0 = coalescedPair m := by
  induction m with
  | zero =>
      norm_num [arbitrarySplitPair, coalescedPair, offsetSplitRoot]
  | succ m ih =>
      simp [arbitrarySplitPair, coalescedPair, offsetSplitRoot, ih]

/-- The existing stable construction is the evenly spaced specialization
of the arbitrary-offset recurrence. -/
theorem arbitrarySplitPair_nat_offsets_eq_splitPair (m : ℕ) (δ : ℝ) :
    arbitrarySplitPair m (fun j => (j : ℝ)) δ = splitPair m δ := by
  induction m with
  | zero =>
      norm_num [arbitrarySplitPair, splitPair, offsetSplitRoot]
  | succ m ih =>
      simp [arbitrarySplitPair, splitPair, offsetSplitRoot, splitRoot, ih]

/-- The source coefficients are positive whenever the finitely many
prescribed roots lie above the physical threshold one. -/
theorem arbitrarySplitPair_dense (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j) :
    DensePositive (arbitrarySplitPair m ξ δ).1 m ∧
      DensePositive (arbitrarySplitPair m ξ δ).2 m := by
  induction m with
  | zero =>
      have hx := hroot 0 (by omega)
      constructor
      · simpa [arbitrarySplitPair] using dense_constant 1 (by norm_num)
      · simpa [arbitrarySplitPair] using
          dense_constant ((offsetSplitRoot ξ δ 0-1)/2) (by linarith)
  | succ m ih =>
      have hold : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j := by
        intro j hj
        exact hroot j (by omega)
      have ha := hroot (2*m+1) (by omega)
      have hb := hroot (2*m+2) (by omega)
      exact next_dense (ih hold).1 (ih hold).2 ha hb

/-- Arbitrary finite offsets still put all prescribed roots above one
for sufficiently small splitting parameters of either sign. -/
theorem offsetSplitRoot_gt_one_eventually
    (m : ℕ) (ξ : ℕ → ℝ) :
    ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j := by
  have hfin : ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ j : Fin (2*m+1), 1 < offsetSplitRoot ξ δ j.val :=
    Filter.eventually_all.mpr (fun j => by
      have hc : ContinuousAt (fun δ : ℝ => offsetSplitRoot ξ δ j.val) 0 := by
        unfold offsetSplitRoot
        fun_prop
      exact hc.eventually (Ioi_mem_nhds (by
        norm_num [offsetSplitRoot])))
  filter_upwards [hfin] with δ hδ j hj
  exact hδ ⟨j, by omega⟩

theorem arbitrarySplitPair_dense_eventually
    (m : ℕ) (ξ : ℕ → ℝ) :
    ∀ᶠ δ : ℝ in 𝓝 0,
      DensePositive (arbitrarySplitPair m ξ δ).1 m ∧
        DensePositive (arbitrarySplitPair m ξ δ).2 m := by
  filter_upwards [offsetSplitRoot_gt_one_eventually m ξ] with δ hroot
  exact arbitrarySplitPair_dense m ξ δ hroot

/-- Exact prescribed-root product identity for arbitrary offsets. -/
theorem arbitrarySplitPair_scalar_identity
    (m : ℕ) (ξ : ℕ → ℝ) (δ x : ℝ) :
    (x-1)*(arbitrarySplitPair m ξ δ).1.eval (ratio x) -
      2*(arbitrarySplitPair m ξ δ).2.eval (ratio x) =
        arbitrarySplitScalarProduct m ξ δ x := by
  induction m with
  | zero =>
      simp [arbitrarySplitScalarProduct, arbitrarySplitPair]
      ring
  | succ m ih =>
      change (x-1)*(nextN _ _ _ _).eval (ratio x) -
        2*(nextJ _ _ _ _).eval (ratio x) = _
      rw [next_identity, ih]
      rfl

/-- The recursive scalar residual is the complete finite root product. -/
theorem arbitrarySplitScalarProduct_eq_prod_range
    (m : ℕ) (ξ : ℕ → ℝ) (δ x : ℝ) :
    arbitrarySplitScalarProduct m ξ δ x =
      ∏ j ∈ Finset.range (2*m+1), (x-offsetSplitRoot ξ δ j) := by
  induction m with
  | zero =>
      simp [arbitrarySplitScalarProduct]
  | succ m ih =>
      rw [arbitrarySplitScalarProduct, ih]
      have hsize : 2*(m+1)+1 = (2*m+1+1)+1 := by omega
      rw [hsize]
      conv_rhs =>
        rw [Finset.prod_range_succ]
        rw [Finset.prod_range_succ]
      ring

/-- The exact derivative includes the arbitrary root gaps and the
universal splitting exponent. -/
theorem arbitrarySplitScalarProduct_deriv_at_root
    (m j : ℕ) (ξ : ℕ → ℝ) (δ : ℝ) (hj : j < 2*m+1) :
    deriv (fun x => arbitrarySplitScalarProduct m ξ δ x)
      (offsetSplitRoot ξ δ j) =
    δ ^ (2*m) *
      ∏ i ∈ (Finset.range (2*m+1)).erase j, (ξ j - ξ i) := by
  classical
  have heq : (fun x => arbitrarySplitScalarProduct m ξ δ x) =
      fun x => ∏ i ∈ Finset.range (2*m+1),
        (x-offsetSplitRoot ξ δ i) := by
    funext x
    exact arbitrarySplitScalarProduct_eq_prod_range m ξ δ x
  rw [heq, deriv_fun_finsetProd]
  · simp only [deriv_sub_const, deriv_id'', smul_eq_mul, mul_one]
    have hsingle :
        (∑ i ∈ Finset.range (2*m+1),
          ∏ l ∈ (Finset.range (2*m+1)).erase i,
            (offsetSplitRoot ξ δ j-offsetSplitRoot ξ δ l)) =
        ∏ l ∈ (Finset.range (2*m+1)).erase j,
          (offsetSplitRoot ξ δ j-offsetSplitRoot ξ δ l) := by
      apply Finset.sum_eq_single j
      · intro i hi hij
        have hjmem : j ∈ (Finset.range (2*m+1)).erase i :=
          Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_range.mpr hj⟩
        rw [Finset.prod_eq_zero hjmem]
        simp
      · intro hnot
        exact (hnot (Finset.mem_range.mpr hj)).elim
    rw [hsingle]
    have hgap (i : ℕ) :
        offsetSplitRoot ξ δ j-offsetSplitRoot ξ δ i =
          δ*(ξ j-ξ i) := by
      unfold offsetSplitRoot
      ring
    simp_rw [hgap]
    rw [Finset.prod_mul_distrib]
    simp [Finset.card_erase_of_mem, Finset.mem_range.mpr hj]
  · intro i hi
    fun_prop

end
end PhosphorylationStableCapacity
