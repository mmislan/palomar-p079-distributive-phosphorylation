module
public import proofs.PhosphorylationStableCapacity.RationalSplitWitness

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Polynomial

/-- A real number lies in the image of the canonical rational embedding. -/
def RationalReal (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

/-- A real polynomial is the image of a rational-coefficient polynomial. -/
def RationalPoly (p : ℝ[X]) : Prop :=
  ∃ q : ℚ[X], q.map (algebraMap ℚ ℝ) = p

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

/-- Rational splitting parameters give rational coefficients in both
polynomials of the paired-root source recurrence. -/
theorem splitPair_rational (m : ℕ) {δ : ℝ} (hδ : RationalReal δ) :
    RationalPoly (splitPair m δ).1 ∧
      RationalPoly (splitPair m δ).2 := by
  induction m with
  | zero =>
      exact ⟨⟨1, by simp [splitPair]⟩, ⟨1, by simp [splitPair]⟩⟩
  | succ m ih =>
      have hroot (j : ℕ) : RationalReal (splitRoot δ j) := by
        exact rationalReal_add (rationalReal_nat 3)
          (rationalReal_mul hδ (rationalReal_nat j))
      simp only [splitPair]
      exact ⟨rationalPoly_nextN (hroot (2*m+1)) (hroot (2*m+2)) ih.1 ih.2,
        rationalPoly_nextJ (hroot (2*m+1)) (hroot (2*m+2)) ih.1 ih.2⟩

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

/-- The conversion step preserves rational polynomial coefficients. -/
theorem splitRaw_polynomials_rational (m : ℕ) {r δ : ℝ}
    (hr : RationalReal r) (hδ : RationalReal δ) :
    RationalPoly (splitRawD m r δ) ∧
      RationalPoly (splitRawB m r δ) := by
  obtain ⟨hp, hq⟩ := splitPair_rational m hδ
  exact ⟨rawD_rational hp hq hr, rawB_rational hp hq hr⟩

/-- Every coordinate of a rate list is rational. -/
def RationalRates {n : ℕ} (k : Rates n) : Prop :=
  ∀ i, RationalReal (k.a i) ∧ RationalReal (k.b i) ∧
    RationalReal (k.c i) ∧ RationalReal (k.alpha i) ∧
    RationalReal (k.beta i) ∧ RationalReal (k.gamma i)

/-- Every coordinate of a literal state is rational. -/
def RationalState {n : ℕ} (x : State n) : Prop :=
  (∀ i, RationalReal (x.S i)) ∧ RationalReal x.E ∧
    RationalReal x.F ∧ (∀ i, RationalReal (x.C i)) ∧
    (∀ i, RationalReal (x.D i))

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

/-- The literal split source is rational at rational `r` and `δ`:
both its common rates and every reconstructed equilibrium coordinate. -/
theorem splitFiniteSource_rational (m : ℕ) {r δ : ℝ}
    (hr : RationalReal r) (hδ : RationalReal δ) :
    RationalRates (splitFiniteRates m r δ) ∧
      ∀ j : Fin (2*m+1), RationalState (splitFiniteState m r δ j) := by
  obtain ⟨hD, hB⟩ := splitRaw_polynomials_rational m hr hδ
  have ht (i : Fin (m+2)) :
      RationalReal (((1 + X) * splitRawD m r δ).coeff i) :=
    rationalPoly_coeff
      (rationalPoly_mul
        (rationalPoly_add (rationalPoly_C rationalReal_one)
          rationalPoly_X) hD) i
  have hBcoeff (i : Fin (m+1)) :
      RationalReal ((splitRawB m r δ).coeff i) :=
    rationalPoly_coeff hB i
  have hDcoeff (i : Fin (m+1)) :
      RationalReal ((splitRawD m r δ).coeff i) :=
    rationalPoly_coeff hD i
  constructor
  · exact realize_rational ht hBcoeff hDcoeff
  · intro j
    have hx : RationalReal (splitRoot δ j.val) :=
      rationalReal_add (rationalReal_nat 3)
        (rationalReal_mul hδ (rationalReal_nat j.val))
    have hu := ratio_rational hx
    have hd := rationalPoly_eval hD hu
    exact reconstruct_rational ht hBcoeff hDcoeff hu
      (rootS_rational hx hd) (rootF_rational hx)

private theorem edgeScaledRates_rational {n : ℕ}
    {w : Fin n → ℝ} {k : Rates n}
    (hw : ∀ i, RationalReal (w i))
    (hk : RationalRates k) : RationalRates (edgeScaledRates w k) := by
  intro i
  obtain ⟨ha, hb, hc, hα, hβ, hγ⟩ := hk i
  exact ⟨rationalReal_mul (hw i) ha,
    rationalReal_mul (hw i) hb,
    rationalReal_mul (hw i) hc,
    rationalReal_mul (hw i) hα,
    rationalReal_mul (hw i) hβ,
    rationalReal_mul (hw i) hγ⟩

private theorem relaxRates_rational {n : ℕ}
    {k : Rates n} {ε : ℝ}
    (hk : RationalRates k) (hε : RationalReal ε) :
    RationalRates (relaxRates k ε) := by
  intro i
  obtain ⟨ha, hb, hc, hα, hβ, hγ⟩ := hk i
  exact ⟨rationalReal_div ha hε,
    rationalReal_sub (rationalReal_div (rationalReal_add hb hc) hε) hc,
    hc, rationalReal_div hα hε,
    rationalReal_sub (rationalReal_div (rationalReal_add hβ hγ) hε) hγ,
    hγ⟩

/-- The final-edge retuning and binding relaxation retain rational rates.
The equilibrium states themselves do not depend on `τ` or `ε`. -/
theorem splitRetunedSource_rational (m : ℕ) {r τ δ ε : ℝ}
    (hr : RationalReal r) (hτ : RationalReal τ)
    (hδ : RationalReal δ) (hε : RationalReal ε) :
    RationalRates (splitRetunedRates m r τ δ ε) ∧
      ∀ j : Fin (2*(m+1)+1),
        RationalState (splitFiniteState (m+1) r δ j) := by
  obtain ⟨hk, hz⟩ := splitFiniteSource_rational (m+1) hr hδ
  have hw (i : Fin (m+2)) :
      RationalReal (coalescedFinalCurrentWeights m τ i) := by
    by_cases hi : i = Fin.last (m+1)
    · simpa [coalescedFinalCurrentWeights, hi] using hτ
    · simpa [coalescedFinalCurrentWeights, hi] using rationalReal_one
  exact ⟨relaxRates_rational (edgeScaledRates_rational hw hk) hε, hz⟩

/-- Rational parameter choices preserve the same full split-family
admissibility and every simple-slow spectral certificate; all literal
rates and all `2m+3` equilibrium states have rational coordinates. -/
theorem rational_split_family_with_spectral_certificates (m : ℕ) :
    ∃ r τ δ ε : ℚ,
      (1 : ℝ) < (r : ℝ) ∧
      0 < (τ : ℝ) ∧ 0 < (δ : ℝ) ∧
      0 < (ε : ℝ) ∧ (ε : ℝ) ≤ 1 ∧
      DensePositive (splitRawD (m+1) (r : ℝ) (δ : ℝ)) (m+1) ∧
      DensePositive (splitRawB (m+1) (r : ℝ) (δ : ℝ)) (m+1) ∧
      (∀ j : Fin (2*(m+1)+1),
        0 < (r : ℝ)-ratio (splitRoot (δ : ℝ) j.val)) ∧
      RationalRates (splitRetunedRates m (r : ℝ) (τ : ℝ)
        (δ : ℝ) (ε : ℝ)) ∧
      (∀ j : Fin (2*(m+1)+1),
        RationalState (splitFiniteState (m+1) (r : ℝ) (δ : ℝ) j)) ∧
      ∃ ρ : Fin (2*(m+1)+1) → ℝ,
        SplitRetunedFamilyAdmissible m (r : ℝ) (τ : ℝ) (δ : ℝ) (ε : ℝ) ∧
        ∀ j, SplitSlowModeCertificate m (r : ℝ) (τ : ℝ)
          (δ : ℝ) (ε : ℝ) j (ρ j) := by
  obtain ⟨r, τ, δ, ε, hr, hτ, hδ, hε, hε1, hD, hB, hv,
    ρ, hadm, hcert⟩ := rational_split_spectral_parameters m
  obtain ⟨hk, hz⟩ := splitRetunedSource_rational m
    (⟨r, rfl⟩ : RationalReal (r : ℝ))
    (⟨τ, rfl⟩ : RationalReal (τ : ℝ))
    (⟨δ, rfl⟩ : RationalReal (δ : ℝ))
    (⟨ε, rfl⟩ : RationalReal (ε : ℝ))
  exact ⟨r, τ, δ, ε, hr, hτ, hδ, hε, hε1, hD, hB, hv,
    hk, hz, ρ, hadm, hcert⟩

end
end PhosphorylationStableCapacity
