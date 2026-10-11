module
public import proofs.PhosphorylationStableCapacity.AnalyticSlowModeIdentification

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix Polynomial

/-- The root, simplicity, and transverse margin carried together in
the compact split law. -/
def SimpleTransverseRoot
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (α x : ℝ) : Prop :=
  J.charpoly.IsRoot x ∧
    ((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
    ∀ z : ℂ, z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
      z = (x : ℂ) ∨ z.re ≤ -α

/-- Select the unique near-neutral root from a signed spectral
certificate. The default value is used only outside the certified
parameter neighborhood and never in a theorem's split-law interval. -/
def selectedTransverseRoot
    {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : β → ℝ → Matrix ι ι ℝ) (α : ℝ)
    (b : β) (δ : ℝ) : ℝ := by
  classical
  exact if h : ∃ x : ℝ, SimpleTransverseRoot (J b δ) α x then
    Classical.choose h
  else 0

theorem selectedTransverseRoot_spec
    {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : β → ℝ → Matrix ι ι ℝ) (α : ℝ)
    (b : β) (δ : ℝ)
    (h : ∃ x : ℝ, SimpleTransverseRoot (J b δ) α x) :
    SimpleTransverseRoot (J b δ) α
      (selectedTransverseRoot J α b δ) := by
  classical
  simp only [selectedTransverseRoot, dite_eq_left h]
  exact Classical.choose_spec h

/-- Any characteristic root to the right of the transverse margin
coincides with the selected root. This is the uniform identification
step that carries a quantitative estimate onto the analytic branch. -/
theorem near_root_eq_selectedTransverseRoot
    {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : β → ℝ → Matrix ι ι ℝ) (α : ℝ)
    (b : β) (δ x : ℝ)
    (hcert : ∃ y : ℝ, SimpleTransverseRoot (J b δ) α y)
    (hx : (J b δ).charpoly.IsRoot x)
    (hnear : -α < x) :
    x = selectedTransverseRoot J α b δ := by
  exact near_real_root_eq_selected_transverse_mode
    (J b δ) α (selectedTransverseRoot J α b δ) x hnear hx
      (selectedTransverseRoot_spec J α b δ hcert).2.2

end

end PhosphorylationStableCapacity
