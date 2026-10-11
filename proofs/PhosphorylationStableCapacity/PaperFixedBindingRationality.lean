module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingSplitCount435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitRationalSource

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness

private theorem rationalReal_one_fixed : RationalReal (1 : ℝ) :=
  ⟨1, by norm_num⟩

private theorem rationalReal_add_fixed {x y : ℝ}
    (hx : RationalReal x) (hy : RationalReal y) : RationalReal (x+y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a+b, by norm_num⟩

private theorem rationalReal_sub_fixed {x y : ℝ}
    (hx : RationalReal x) (hy : RationalReal y) : RationalReal (x-y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a-b, by norm_num⟩

private theorem rationalReal_mul_fixed {x y : ℝ}
    (hx : RationalReal x) (hy : RationalReal y) : RationalReal (x*y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a*b, by norm_num⟩

private theorem rationalReal_div_fixed {x y : ℝ}
    (hx : RationalReal x) (hy : RationalReal y) : RationalReal (x/y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a/b, by norm_num⟩

/-- The exact `bᵢ=βᵢ=1` transformation preserves rationality of every
physical rate constant. -/
theorem paperFixedBindingRates_rational {n : ℕ} {k : Rates n}
    (hk : RationalRates k) : RationalRates (paperFixedBindingRates k) := by
  intro i
  obtain ⟨ha, hb, hc, hα, hβ, hγ⟩ := hk i
  change RationalReal ((1+k.c i)*sourceBindingP k i.castSucc) ∧
    RationalReal (1 : ℝ) ∧ RationalReal (k.c i) ∧
    RationalReal ((1+k.gamma i)*sourceBindingQ k i.succ) ∧
    RationalReal (1 : ℝ) ∧ RationalReal (k.gamma i)
  have hP : RationalReal (sourceBindingP k i.castSucc) := by
    simpa only [sourceBindingP_castSucc] using
      rationalReal_div_fixed ha (rationalReal_add_fixed hb hc)
  have hQ : RationalReal (sourceBindingQ k i.succ) := by
    simpa only [sourceBindingQ_succ] using
      rationalReal_div_fixed hα (rationalReal_add_fixed hβ hγ)
  exact ⟨rationalReal_mul_fixed
      (rationalReal_add_fixed rationalReal_one_fixed hc) hP,
    rationalReal_one_fixed, hc,
    rationalReal_mul_fixed
      (rationalReal_add_fixed rationalReal_one_fixed hγ) hQ,
    rationalReal_one_fixed, hγ⟩

/-- Positive edge scaling and binding relaxation preserve rationality;
no positivity hypothesis is needed for this algebraic statement. -/
theorem paperFixedBindingSplitRates_rational_of_base
    {n : ℕ} (k : Rates n) (w : Fin n → ℝ) (ε : ℝ)
    (hk : RationalRates k) (hw : ∀ i, RationalReal (w i))
    (hε : RationalReal ε) :
    RationalRates (relaxRates
      (paperFixedBindingRates (edgeScaledRates w k)) ε) := by
  have hscaled : RationalRates (edgeScaledRates w k) := by
    intro i
    obtain ⟨ha, hb, hc, hα, hβ, hγ⟩ := hk i
    exact ⟨rationalReal_mul_fixed (hw i) ha,
      rationalReal_mul_fixed (hw i) hb,
      rationalReal_mul_fixed (hw i) hc,
      rationalReal_mul_fixed (hw i) hα,
      rationalReal_mul_fixed (hw i) hβ,
      rationalReal_mul_fixed (hw i) hγ⟩
  have hfixed := paperFixedBindingRates_rational hscaled
  intro i
  obtain ⟨ha, hb, hc, hα, hβ, hγ⟩ := hfixed i
  exact ⟨rationalReal_div_fixed ha hε,
    rationalReal_sub_fixed
      (rationalReal_div_fixed (rationalReal_add_fixed hb hc) hε) hc,
    hc, rationalReal_div_fixed hα hε,
    rationalReal_sub_fixed
      (rationalReal_div_fixed (rationalReal_add_fixed hβ hγ) hε) hγ,
    hγ⟩

/-- Every rational prescribed-offset family has one rational fixed-binding
rate vector and rational labelled physical states. -/
theorem paperFixedBindingSplit_rational_offsets
    (m : ℕ) (ξ : ℕ → ℝ) {r δ ε : ℝ} (w : Fin (m+2) → ℝ)
    (hr : RationalReal r) (hδ : RationalReal δ)
    (hε : RationalReal ε) (hξ : ∀ j, RationalReal (ξ j))
    (hw : ∀ i, RationalReal (w i)) :
    RationalRates (paperFixedBindingSplitRates m ξ r δ ε w) ∧
      ∀ j : Fin (2*(m+1)+1),
        RationalState (arbitrarySplitFiniteState (m+1) ξ r δ j) := by
  obtain ⟨hk, hstate⟩ :=
    arbitrarySplitFiniteSource_rational (m+1) ξ hr hδ hξ
  constructor
  · change RationalRates (relaxRates (paperFixedBindingRates
      (edgeScaledRates w (arbitrarySplitFiniteRates (m+1) ξ r δ))) ε)
    exact paperFixedBindingSplitRates_rational_of_base _ w ε hk hw hε
  · exact hstate

/-- In the evenly spaced rational-offset instance of the manuscript's
fixed-binding family, rational source and edge parameters yield one
rational positive-rate candidate and rational labelled states. -/
theorem paperFixedBindingSplit_nat_offsets_rational
    (m : ℕ) {r δ ε : ℝ} (w : Fin (m+2) → ℝ)
    (hr : RationalReal r) (hδ : RationalReal δ)
    (hε : RationalReal ε)
    (hw : ∀ i, RationalReal (w i)) :
    RationalRates (paperFixedBindingSplitRates m
      (fun j : ℕ => (j : ℝ)) r δ ε w) ∧
      ∀ j : Fin (2*(m+1)+1),
        RationalState (arbitrarySplitFiniteState (m+1)
          (fun j : ℕ => (j : ℝ)) r δ j) := by
  exact paperFixedBindingSplit_rational_offsets m (fun j : ℕ => (j : ℝ))
    w hr hδ hε (fun j => ⟨j, by norm_cast⟩) hw

/-- At rational source parameter, every coordinate of the coalesced
state—and hence each frozen unit-current catalytic scale `1/Yᵢ(X₀)`—
is rational. -/
theorem coalescedFiniteState_rational_of_rational_source
    (m : ℕ) {r : ℝ} (hr : RationalReal r) :
    RationalState (coalescedFiniteState (m+1) r) := by
  have hzero : RationalReal (0 : ℝ) := ⟨0, by norm_num⟩
  have h := (arbitrarySplitFiniteSource_rational (m+1)
    (fun j : ℕ => (j : ℝ)) hr hzero (fun j => ⟨j, by norm_cast⟩)).2
    (0 : Fin (2*(m+1)+1))
  rw [arbitrarySplitFiniteState_zero_eq_coalesced] at h
  exact h

/-- The literal paper family with actual unit prefix currents has
rational rates and rational labelled equilibria whenever its four
selected scalar parameters are rational. -/
theorem paperFixedBindingSplit_nat_offsets_actual_unit_current_rational
    (m : ℕ) {r τ δ ε : ℝ}
    (hr : RationalReal r) (hτ : RationalReal τ)
    (hδ : RationalReal δ) (hε : RationalReal ε) :
    let x₀ := coalescedFiniteState (m+1) r
    let θ : Fin (m+1) → ℝ := fun i => 1 / x₀.D i.castSucc
    RationalRates (paperFixedBindingSplitRates m
      (fun j : ℕ => (j : ℝ)) r δ ε (Fin.lastCases τ θ)) ∧
      ∀ j : Fin (2*(m+1)+1),
        RationalState (arbitrarySplitFiniteState (m+1)
          (fun j : ℕ => (j : ℝ)) r δ j) := by
  let x₀ := coalescedFiniteState (m+1) r
  let θ : Fin (m+1) → ℝ := fun i => 1 / x₀.D i.castSucc
  let w : Fin (m+2) → ℝ := Fin.lastCases τ θ
  have hx : RationalState x₀ := coalescedFiniteState_rational_of_rational_source m hr
  have hθ (i : Fin (m+1)) : RationalReal (θ i) :=
    rationalReal_div_fixed rationalReal_one_fixed (hx.2.2.2.2 i.castSucc)
  have hw : ∀ i : Fin (m+2), RationalReal (w i) := by
    intro i
    refine Fin.lastCases (motive := fun i => RationalReal (w i)) ?_ ?_ i
    · simpa only [w, Fin.lastCases_last] using hτ
    · intro j
      simpa only [w, Fin.lastCases_castSucc] using hθ j
  change RationalRates (paperFixedBindingSplitRates m
      (fun j : ℕ => (j : ℝ)) r δ ε w) ∧
    ∀ j : Fin (2*(m+1)+1),
      RationalState (arbitrarySplitFiniteState (m+1)
        (fun j : ℕ => (j : ℝ)) r δ j)
  exact paperFixedBindingSplit_nat_offsets_rational m w hr hδ hε hw

/-- Rationality is expressed in the paper's actual final current `t`,
with frozen final catalytic scale `t/Y_last(X₀)`. -/
theorem paperFixedBindingSplit_nat_offsets_actual_currents_rational
    (m : ℕ) {r t δ ε : ℝ}
    (hr : RationalReal r) (ht : RationalReal t)
    (hδ : RationalReal δ) (hε : RationalReal ε) :
    let x₀ := coalescedFiniteState (m+1) r
    let τ := t / x₀.D (Fin.last (m+1))
    let θ : Fin (m+1) → ℝ := fun i => 1 / x₀.D i.castSucc
    RationalRates (paperFixedBindingSplitRates m
      (fun j : ℕ => (j : ℝ)) r δ ε (Fin.lastCases τ θ)) ∧
      ∀ j : Fin (2*(m+1)+1),
        RationalState (arbitrarySplitFiniteState (m+1)
          (fun j : ℕ => (j : ℝ)) r δ j) := by
  let x₀ := coalescedFiniteState (m+1) r
  have hx := coalescedFiniteState_rational_of_rational_source m hr
  have hτ : RationalReal (t / x₀.D (Fin.last (m+1))) :=
    rationalReal_div_fixed ht (hx.2.2.2.2 (Fin.last (m+1)))
  exact paperFixedBindingSplit_nat_offsets_actual_unit_current_rational
    m hr hτ hδ hε

end
end PhosphorylationStableCapacity
