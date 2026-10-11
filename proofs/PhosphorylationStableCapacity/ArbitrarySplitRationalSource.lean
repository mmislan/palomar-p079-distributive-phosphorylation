module
public import proofs.PhosphorylationStableCapacity.RationalSplitWitnessAlgebra
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitSource
public import proofs.PhosphorylationStableCapacity.KineticFreedom

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Polynomial

private theorem rationalReal_nat (n : ℕ) : RationalReal (n : ℝ) :=
  ⟨n, by norm_cast⟩

private theorem rationalReal_one : RationalReal (1 : ℝ) :=
  ⟨1, by norm_num⟩

private theorem rationalReal_add {x y : ℝ}
    (hx : RationalReal x) (hy : RationalReal y) : RationalReal (x+y) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨a+b, by push_cast; rfl⟩

private theorem rationalReal_sub {x y : ℝ}
    (hx : RationalReal x) (hy : RationalReal y) : RationalReal (x-y) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨a-b, by push_cast; rfl⟩

private theorem rationalReal_mul {x y : ℝ}
    (hx : RationalReal x) (hy : RationalReal y) : RationalReal (x*y) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨a*b, by push_cast; rfl⟩

private theorem rationalReal_div {x y : ℝ}
    (hx : RationalReal x) (hy : RationalReal y) : RationalReal (x/y) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨a/b, by push_cast; rfl⟩

private theorem rationalReal_pow {x : ℝ}
    (hx : RationalReal x) (n : ℕ) : RationalReal (x^n) := by
  rcases hx with ⟨a, rfl⟩
  exact ⟨a^n, by push_cast; rfl⟩

private theorem rationalPoly_C {x : ℝ}
    (hx : RationalReal x) : RationalPoly (C x) := by
  rcases hx with ⟨a, rfl⟩
  exact ⟨C a, by simp⟩

private theorem rationalPoly_X : RationalPoly (X : ℝ[X]) :=
  ⟨X, by simp⟩

private theorem rationalPoly_add {p q : ℝ[X]}
    (hp : RationalPoly p) (hq : RationalPoly q) : RationalPoly (p+q) := by
  rcases hp with ⟨p, rfl⟩
  rcases hq with ⟨q, rfl⟩
  exact ⟨p+q, by simp⟩

private theorem rationalPoly_sub {p q : ℝ[X]}
    (hp : RationalPoly p) (hq : RationalPoly q) : RationalPoly (p-q) := by
  rcases hp with ⟨p, rfl⟩
  rcases hq with ⟨q, rfl⟩
  exact ⟨p-q, by simp⟩

private theorem rationalPoly_mul {p q : ℝ[X]}
    (hp : RationalPoly p) (hq : RationalPoly q) : RationalPoly (p*q) := by
  rcases hp with ⟨p, rfl⟩
  rcases hq with ⟨q, rfl⟩
  exact ⟨p*q, by simp⟩

private theorem rationalPoly_coeff {p : ℝ[X]}
    (hp : RationalPoly p) (i : ℕ) : RationalReal (p.coeff i) := by
  rcases hp with ⟨p, rfl⟩
  exact ⟨p.coeff i, by simp⟩

private theorem rationalPoly_eval {p : ℝ[X]} {x : ℝ}
    (hp : RationalPoly p) (hx : RationalReal x) :
    RationalReal (p.eval x) := by
  rcases hp with ⟨p, rfl⟩
  rcases hx with ⟨x, rfl⟩
  refine ⟨p.eval x, ?_⟩
  have hcast (q : ℚ) : (algebraMap ℚ ℝ) q = (q : ℝ) := by
    norm_cast
  simpa only [eval_map_algebraMap, hcast] using
    (eval_map_apply (f := algebraMap ℚ ℝ) (p := p) x).symm

private theorem rationalPoly_divByMonic_X_sub_C {p : ℝ[X]} {r : ℝ}
    (hp : RationalPoly p) (hr : RationalReal r) :
    RationalPoly (p /ₘ (X-C r)) := by
  rcases hp with ⟨p, rfl⟩
  rcases hr with ⟨r, rfl⟩
  refine ⟨p /ₘ (X-C r), ?_⟩
  rw [map_divByMonic (algebraMap ℚ ℝ) (monic_X_sub_C r)]
  simp

private theorem rationalPoly_nextN {a b : ℝ} {p q : ℝ[X]}
    (ha : RationalReal a) (hb : RationalReal b)
    (hp : RationalPoly p) (hq : RationalPoly q) :
    RationalPoly (nextN a b p q) := by
  unfold nextN
  apply rationalPoly_add
  · apply rationalPoly_add
    · exact rationalPoly_mul
        (rationalPoly_C (rationalReal_mul
          (rationalReal_add ha rationalReal_one)
          (rationalReal_add hb rationalReal_one))) hp
    · exact rationalPoly_mul (rationalPoly_C (rationalReal_nat 8))
        (rationalPoly_mul rationalPoly_X hp)
  · exact rationalPoly_mul
      (rationalPoly_C (rationalReal_mul (rationalReal_nat 2)
        (rationalReal_add ha hb))) hq

private theorem rationalPoly_nextJ {a b : ℝ} {p q : ℝ[X]}
    (ha : RationalReal a) (hb : RationalReal b)
    (hp : RationalPoly p) (hq : RationalPoly q) :
    RationalPoly (nextJ a b p q) := by
  unfold nextJ
  apply rationalPoly_add
  · apply rationalPoly_add
    · exact rationalPoly_mul
        (rationalPoly_C (rationalReal_mul
          (rationalReal_sub ha rationalReal_one)
          (rationalReal_sub hb rationalReal_one))) hq
    · exact rationalPoly_mul (rationalPoly_C (rationalReal_nat 8))
        (rationalPoly_mul rationalPoly_X hq)
  · exact rationalPoly_mul
      (rationalPoly_C (rationalReal_mul (rationalReal_nat 4)
        (rationalReal_add ha hb)))
      (rationalPoly_mul rationalPoly_X hp)

private theorem conversionNumerator_rational {p q : ℝ[X]} {r : ℝ}
    (hp : RationalPoly p) (hq : RationalPoly q)
    (hr : RationalReal r) :
    RationalPoly (conversionNumerator p q r) := by
  unfold conversionNumerator
  apply rationalPoly_sub
  · exact rationalPoly_mul
      (rationalPoly_C (rationalPoly_eval hq hr))
      (rationalPoly_mul rationalPoly_X hp)
  · exact rationalPoly_mul
      (rationalPoly_C (rationalReal_mul hr (rationalPoly_eval hp hr))) hq

private theorem quotient_rational {p q : ℝ[X]} {r : ℝ}
    (hp : RationalPoly p) (hq : RationalPoly q)
    (hr : RationalReal r) : RationalPoly (quotient p q r) := by
  unfold quotient
  exact rationalPoly_divByMonic_X_sub_C
    (conversionNumerator_rational hp hq hr) hr

private theorem rawD_rational {p q : ℝ[X]} {r : ℝ}
    (hp : RationalPoly p) (hq : RationalPoly q)
    (hr : RationalReal r) : RationalPoly (rawD p q r) := by
  unfold rawD
  exact rationalPoly_mul (rationalPoly_C (rationalReal_nat 4))
    (quotient_rational hp hq hr)

private theorem rawB_rational {p q : ℝ[X]} {r : ℝ}
    (hp : RationalPoly p) (hq : RationalPoly q)
    (hr : RationalReal r) : RationalPoly (rawB p q r) := by
  unfold rawB
  apply rationalPoly_sub
  · apply rationalPoly_add
    · exact rationalPoly_mul (rationalPoly_C hr)
        (rawD_rational hp hq hr)
    · exact rationalPoly_mul
        (rationalPoly_C
          (rationalReal_sub
            (rationalReal_mul (rationalReal_mul
              (rationalReal_nat 4) hr) (rationalPoly_eval hp hr))
            (rationalReal_mul (rationalReal_nat 2)
              (rationalPoly_eval hq hr)))) hp
  · exact rationalPoly_mul
      (rationalPoly_C (rationalReal_mul (rationalReal_nat 2)
        (rationalPoly_eval hq hr))) hq

private theorem realize_rational {n : ℕ}
    {t : Fin (n+1) → ℝ} {B D : Fin n → ℝ}
    (ht : ∀ i, RationalReal (t i))
    (hB : ∀ i, RationalReal (B i))
    (hD : ∀ i, RationalReal (D i)) :
    RationalRates (realize t B D) := by
  intro i
  change RationalReal (2*D i/t i.castSucc) ∧
    RationalReal (D i/B i) ∧ RationalReal (D i/B i) ∧
    RationalReal (2*D i/t i.succ) ∧
    RationalReal 1 ∧ RationalReal 1
  exact ⟨rationalReal_div
      (rationalReal_mul (rationalReal_nat 2) (hD i)) (ht _),
    rationalReal_div (hD i) (hB i),
    rationalReal_div (hD i) (hB i),
    rationalReal_div
      (rationalReal_mul (rationalReal_nat 2) (hD i)) (ht _),
    rationalReal_one, rationalReal_one⟩

private theorem reconstruct_rational {n : ℕ}
    {t : Fin (n+1) → ℝ} {B D : Fin n → ℝ} {u s f : ℝ}
    (ht : ∀ i, RationalReal (t i))
    (hB : ∀ i, RationalReal (B i))
    (hD : ∀ i, RationalReal (D i))
    (hu : RationalReal u) (hs : RationalReal s) (hf : RationalReal f) :
    RationalState (reconstruct t B D u s f) := by
  refine ⟨?_, rationalReal_mul hu hf, hf, ?_, ?_⟩
  · intro i
    exact rationalReal_mul
      (rationalReal_mul (ht i) (rationalReal_pow hu i.val)) hs
  · intro i
    exact rationalReal_mul
      (rationalReal_mul
        (rationalReal_mul (hB i)
          (rationalReal_pow hu (i.val+1))) hs) hf
  · intro i
    exact rationalReal_mul
      (rationalReal_mul
        (rationalReal_mul (hD i)
          (rationalReal_pow hu (i.val+1))) hs) hf

private theorem ratio_rational {x : ℝ} (hx : RationalReal x) :
    RationalReal (ratio x) := by
  unfold ratio
  exact rationalReal_div
    (rationalReal_sub (rationalReal_pow hx 2) rationalReal_one)
    (rationalReal_nat 8)

private theorem rootS_rational {x d : ℝ}
    (hx : RationalReal x) (hd : RationalReal d) :
    RationalReal (rootS x d) := by
  unfold rootS
  exact rationalReal_div (rationalReal_sub hx rationalReal_one)
    (rationalReal_mul
      (rationalReal_mul (rationalReal_nat 2) (ratio_rational hx)) hd)

private theorem rootF_rational {x : ℝ} (hx : RationalReal x) :
    RationalReal (rootF x) := by
  unfold rootF
  exact rationalReal_div (rationalReal_nat 4)
    (rationalReal_add hx rationalReal_one)

/-- Every rational offset tuple, with arbitrary signs and centering, gives
rational coefficients in the literal paired-root recurrence. -/
theorem arbitrarySplitPair_rational (m : ℕ) (ξ : ℕ → ℝ)
    {δ : ℝ} (hξ : ∀ j, RationalReal (ξ j)) (hδ : RationalReal δ) :
    RationalPoly (arbitrarySplitPair m ξ δ).1 ∧
      RationalPoly (arbitrarySplitPair m ξ δ).2 := by
  have hroot (j : ℕ) : RationalReal (offsetSplitRoot ξ δ j) :=
    rationalReal_add (rationalReal_nat 3) (rationalReal_mul hδ (hξ j))
  induction m with
  | zero =>
      exact ⟨⟨1, by simp [arbitrarySplitPair]⟩,
        rationalPoly_C (rationalReal_div
          (rationalReal_sub (hroot 0) rationalReal_one) (rationalReal_nat 2))⟩
  | succ m ih =>
      simp only [arbitrarySplitPair]
      exact ⟨rationalPoly_nextN (hroot (2*m+1)) (hroot (2*m+2)) ih.1 ih.2,
        rationalPoly_nextJ (hroot (2*m+1)) (hroot (2*m+2)) ih.1 ih.2⟩

/-- The exact monic conversion preserves rationality for arbitrary offsets. -/
theorem arbitrarySplitRaw_polynomials_rational (m : ℕ) (ξ : ℕ → ℝ)
    {r δ : ℝ} (hr : RationalReal r) (hδ : RationalReal δ)
    (hξ : ∀ j, RationalReal (ξ j)) :
    RationalPoly (arbitrarySplitRawD m ξ r δ) ∧
      RationalPoly (arbitrarySplitRawB m ξ r δ) := by
  obtain ⟨hp, hq⟩ := arbitrarySplitPair_rational m ξ hξ hδ
  exact ⟨rawD_rational hp hq hr, rawB_rational hp hq hr⟩

/-- One common rational rate vector and every reconstructed rational state,
for arbitrary rational offsets. No ordering or positivity premise is needed
for this algebraic assertion. -/
theorem arbitrarySplitFiniteSource_rational (m : ℕ) (ξ : ℕ → ℝ)
    {r δ : ℝ} (hr : RationalReal r) (hδ : RationalReal δ)
    (hξ : ∀ j, RationalReal (ξ j)) :
    RationalRates (arbitrarySplitFiniteRates m ξ r δ) ∧
      ∀ j : Fin (2*m+1), RationalState (arbitrarySplitFiniteState m ξ r δ j) := by
  obtain ⟨hD, hB⟩ := arbitrarySplitRaw_polynomials_rational m ξ hr hδ hξ
  have ht (i : Fin (m+2)) :
      RationalReal (((1+X)*arbitrarySplitRawD m ξ r δ).coeff i) :=
    rationalPoly_coeff (rationalPoly_mul
      (rationalPoly_add (rationalPoly_C rationalReal_one) rationalPoly_X) hD) i
  have hBcoeff (i : Fin (m+1)) :
      RationalReal ((arbitrarySplitRawB m ξ r δ).coeff i) := rationalPoly_coeff hB i
  have hDcoeff (i : Fin (m+1)) :
      RationalReal ((arbitrarySplitRawD m ξ r δ).coeff i) := rationalPoly_coeff hD i
  constructor
  · exact realize_rational ht hBcoeff hDcoeff
  · intro j
    have hx : RationalReal (offsetSplitRoot ξ δ j.val) :=
      rationalReal_add (rationalReal_nat 3) (rationalReal_mul hδ (hξ j.val))
    have hu := ratio_rational hx
    exact reconstruct_rational ht hBcoeff hDcoeff hu
      (rootS_rational hx (rationalPoly_eval hD hu)) (rootF_rational hx)

/-- Common rational catalytic retuning preserves every rate coordinate. -/
theorem retune_rational {n : ℕ} (k : Rates n) (l b β : Fin n → ℝ)
    (hk : RationalRates k) (hl : ∀ i, RationalReal (l i))
    (hb : ∀ i, RationalReal (b i)) (hβ : ∀ i, RationalReal (β i)) :
    RationalRates (retune k l b β) := by
  intro i
  obtain ⟨ha, hb0, hc, hα, hβ0, hγ⟩ := hk i
  exact ⟨rationalReal_div
      (rationalReal_mul (rationalReal_add (hb i) (rationalReal_mul (hl i) hc)) ha)
      (rationalReal_add hb0 hc), hb i, rationalReal_mul (hl i) hc,
    rationalReal_div
      (rationalReal_mul (rationalReal_add (hβ i) (rationalReal_mul (hl i) hγ)) hα)
      (rationalReal_add hβ0 hγ), hβ i, rationalReal_mul (hl i) hγ⟩

end
end PhosphorylationStableCapacity
