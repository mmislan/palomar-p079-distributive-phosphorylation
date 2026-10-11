module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingRealization435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitSource

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness

/-- For the paper's fixed reversible binding choice, the physical
determinant's rate product is an explicit polynomial in each edge
factor and the source binding ratio. This separates the current
parameters from the varying source coefficients. -/
theorem paperFixedBinding_rateProduct_edge_factor {n : ℕ}
    (w : Fin n → ℝ) (k : Rates n)
    (hw : ∀ i, 0 < w i) (hk : k.Positive) (i : Fin n) :
    let K := paperFixedBindingRates (edgeScaledRates w k)
    (K.b i+K.c i)*K.alpha i*K.gamma i =
      (1+w i*k.c i)*(1+w i*k.gamma i)*
        sourceBindingQ k i.succ*(w i*k.gamma i) := by
  have hQ := congrFun (sourceBindingRatios_edgeScaledRates w k hw hk).2 i.succ
  dsimp only
  change (1+w i*k.c i)*
    ((1+w i*k.gamma i)*sourceBindingQ (edgeScaledRates w k) i.succ)*
      (w i*k.gamma i) = _
  rw [hQ]
  ring

/-- Fast binding relaxation contributes exactly two inverse powers
of the relaxation scale per edge to the physical determinant factor. -/
theorem relaxRates_rateProduct_site {n : ℕ}
    (k : Rates n) (ε : ℝ) (i : Fin n) :
    ((relaxRates k ε).b i+(relaxRates k ε).c i)*
      (relaxRates k ε).alpha i*(relaxRates k ε).gamma i =
        ((k.b i+k.c i)*k.alpha i*k.gamma i)/ε^2 := by
  simp only [relaxRates]
  ring

theorem paperFixedBinding_relaxed_rateProduct_edge_factor {n : ℕ}
    (w : Fin n → ℝ) (k : Rates n) (ε : ℝ)
    (hw : ∀ i, 0 < w i) (hk : k.Positive) (i : Fin n) :
    let K := relaxRates (paperFixedBindingRates (edgeScaledRates w k)) ε
    (K.b i+K.c i)*K.alpha i*K.gamma i =
      ((1+w i*k.c i)*(1+w i*k.gamma i)*
        sourceBindingQ k i.succ*(w i*k.gamma i))/ε^2 := by
  dsimp only
  rw [relaxRates_rateProduct_site,
    paperFixedBinding_rateProduct_edge_factor w k hw hk i]

/-- In the split source `gamma_i=1`, so the entire rate product is a
finite polynomial in the positive edge factors times source ratios.
The same identity applies after the paper realization and before
fast binding relaxation. -/
theorem paperFixedBinding_split_rateProduct_factor
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (w : Fin (m+2) → ℝ)
    (hw : ∀ i, 0 < w i)
    (hk : (arbitrarySplitFiniteRates (m+1) ξ r δ).Positive) :
    let base := arbitrarySplitFiniteRates (m+1) ξ r δ
    let K := paperFixedBindingRates (edgeScaledRates w base)
    (∏ i : Fin (m+2), (K.b i+K.c i)*K.alpha i*K.gamma i) =
      ∏ i : Fin (m+2),
        (1+w i*base.c i)*(1+w i)*sourceBindingQ base i.succ*w i := by
  dsimp only
  apply Finset.prod_congr rfl
  intro i _
  rw [paperFixedBinding_rateProduct_edge_factor w
    (arbitrarySplitFiniteRates (m+1) ξ r δ) hw hk i]
  have hgamma :
      (arbitrarySplitFiniteRates (m+1) ξ r δ).gamma i = 1 := by
    rfl
  rw [hgamma]
  ring

/-- The source realization has unit phosphatase reverse and catalytic
constants, so its binding ratio is half its association rate. -/
theorem arbitrarySplitFiniteRates_bindingQ_eq_half_alpha
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (i : Fin (m+2)) :
    sourceBindingQ (arbitrarySplitFiniteRates (m+1) ξ r δ) i.succ =
      (arbitrarySplitFiniteRates (m+1) ξ r δ).alpha i / 2 := by
  rw [sourceBindingQ_succ]
  norm_num [arbitrarySplitFiniteRates, realize]

/-- The completely explicit factor used for compact first-order
control of the manuscript's physical determinant coefficient. -/
theorem paperFixedBinding_split_relaxed_rateProduct_site
    (m : ℕ) (ξ : ℕ → ℝ) (r δ ε : ℝ)
    (w : Fin (m+2) → ℝ)
    (hw : ∀ i, 0 < w i)
    (hk : (arbitrarySplitFiniteRates (m+1) ξ r δ).Positive)
    (i : Fin (m+2)) :
    let base := arbitrarySplitFiniteRates (m+1) ξ r δ
    let K := relaxRates (paperFixedBindingRates (edgeScaledRates w base)) ε
    (K.b i+K.c i)*K.alpha i*K.gamma i =
      ((1+w i*base.c i)*(1+w i)*(base.alpha i/2)*w i)/ε^2 := by
  dsimp only
  rw [paperFixedBinding_relaxed_rateProduct_edge_factor w
    (arbitrarySplitFiniteRates (m+1) ξ r δ) ε hw hk i,
    arbitrarySplitFiniteRates_bindingQ_eq_half_alpha]
  have hgamma :
      (arbitrarySplitFiniteRates (m+1) ξ r δ).gamma i = 1 := rfl
  rw [hgamma]
  ring

theorem paperFixedBinding_split_relaxed_rateProduct_product
    (m : ℕ) (ξ : ℕ → ℝ) (r δ ε : ℝ)
    (w : Fin (m+2) → ℝ)
    (hw : ∀ i, 0 < w i)
    (hk : (arbitrarySplitFiniteRates (m+1) ξ r δ).Positive) :
    let base := arbitrarySplitFiniteRates (m+1) ξ r δ
    let K := relaxRates (paperFixedBindingRates (edgeScaledRates w base)) ε
    (∏ i : Fin (m+2), (K.b i+K.c i)*K.alpha i*K.gamma i) =
      ∏ i : Fin (m+2),
        ((1+w i*base.c i)*(1+w i)*(base.alpha i/2)*w i)/ε^2 := by
  dsimp only
  apply Finset.prod_congr rfl
  intro i _
  exact paperFixedBinding_split_relaxed_rateProduct_site
    m ξ r δ ε w hw hk i

end

end PhosphorylationStableCapacity
