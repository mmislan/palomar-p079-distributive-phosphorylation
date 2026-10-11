module
public import proofs.PhosphorylationStableCapacity.SourceBindingCurrentBridge
public import proofs.PhosphorylationStableCapacity.RelaxationRates
public import proofs.PhosphorylationStableCapacity.LoadedReducedField
public import proofs.PhosphorylationStableCapacity.LoadedFastField
public import proofs.PhosphorylationStableCapacity.SourceCurrentSchur
public import proofs.PhosphorylationStableCapacity.LoadedFieldDifferentiability

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness

/-- The paper's `bᵢ=βᵢ=1` freedom choice. The source association/outflow
ratios and catalytic coefficients are kept exactly, so the literal
binding manifold and its catalytic current map agree with the given
positive realization. -/
def paperFixedBindingRates {n : ℕ} (k : Rates n) : Rates n where
  a i := (1 + k.c i) * sourceBindingP k i.castSucc
  b _ := 1
  c := k.c
  alpha i := (1 + k.gamma i) * sourceBindingQ k i.succ
  beta _ := 1
  gamma := k.gamma

theorem paperFixedBindingRates_positive {n : ℕ}
    (k : Rates n) (hk : k.Positive) :
    (paperFixedBindingRates k).Positive := by
  intro i
  obtain ⟨hp, hq⟩ := sourceBindingRatios_positive k hk i
  rcases hk i with ⟨_, _, hc, _, _, hg⟩
  dsimp [paperFixedBindingRates]
  exact ⟨mul_pos (by linarith) hp, by norm_num, hc,
    mul_pos (by linarith) hq, by norm_num, hg⟩

theorem paperFixedBindingRates_ratios {n : ℕ}
    (k : Rates n) (hk : k.Positive) :
    sourceBindingP (paperFixedBindingRates k) = sourceBindingP k ∧
      sourceBindingQ (paperFixedBindingRates k) = sourceBindingQ k := by
  constructor
  · funext j
    cases j using Fin.lastCases with
    | last => simp [sourceBindingP]
    | cast i =>
        have hc : 1 + k.c i ≠ 0 := ne_of_gt (by linarith [(hk i).2.2.1])
        simp only [sourceBindingP_castSucc, paperFixedBindingRates]
        field_simp [hc]
  · funext j
    cases j using Fin.cases with
    | zero => simp [sourceBindingQ]
    | succ i =>
        have hg : 1 + k.gamma i ≠ 0 :=
          ne_of_gt (by linarith [(hk i).2.2.2.2.2])
        change ((1 + k.gamma i) * sourceBindingQ k i.succ) /
          (1 + k.gamma i) = sourceBindingQ k i.succ
        field_simp [hg]

/-- Positive edge-current scaling does not alter the reversible-binding
association/outflow ratios. -/
theorem sourceBindingRatios_edgeScaledRates {n : ℕ}
    (w : Fin n → ℝ) (k : Rates n)
    (hw : ∀ i, 0 < w i) (hk : k.Positive) :
    sourceBindingP (edgeScaledRates w k) = sourceBindingP k ∧
      sourceBindingQ (edgeScaledRates w k) = sourceBindingQ k := by
  constructor
  · funext j
    cases j using Fin.lastCases with
    | last => simp [sourceBindingP]
    | cast i =>
        have hw0 : w i ≠ 0 := ne_of_gt (hw i)
        have hb : k.b i + k.c i ≠ 0 :=
          ne_of_gt (add_pos (hk i).2.1 (hk i).2.2.1)
        have hsum : w i*k.b i+w i*k.c i ≠ 0 := by
          rw [← mul_add]
          exact mul_ne_zero hw0 hb
        simp only [sourceBindingP_castSucc]
        change (w i*k.a i)/(w i*k.b i+w i*k.c i) =
          k.a i/(k.b i+k.c i)
        field_simp [hw0, hb, hsum]
  · funext j
    cases j using Fin.cases with
    | zero => simp [sourceBindingQ]
    | succ i =>
        have hw0 : w i ≠ 0 := ne_of_gt (hw i)
        have hb : k.beta i + k.gamma i ≠ 0 :=
          ne_of_gt (add_pos (hk i).2.2.2.2.1 (hk i).2.2.2.2.2)
        have hsum : w i*k.beta i+w i*k.gamma i ≠ 0 := by
          rw [← mul_add]
          exact mul_ne_zero hw0 hb
        change (w i*k.alpha i)/(w i*k.beta i+w i*k.gamma i) =
          k.alpha i/(k.beta i+k.gamma i)
        field_simp [hw0, hb, hsum]

/-- Once the matching binding ratios are supplied, the entire nonlinear
reduced slow field is identical at every substrate point, not only its
linearization at the coalesced equilibrium. -/
theorem paperFixedBindingRates_reducedField {n : ℕ}
    (ET FT : ℝ) (p q : Fin (n+1) → ℝ)
    (k : Rates n) (S : Fin (n+1) → ℝ) (j : Fin (n+1)) :
    bindingReducedSlowField ET FT p q (paperFixedBindingRates k) S j =
      bindingReducedSlowField ET FT p q k S j := by
  rw [bindingReducedSlowField_eq_current_sum,
    bindingReducedSlowField_eq_current_sum]
  rfl

/-- At every loaded state the slow rows agree exactly. -/
theorem paperFixedBindingRates_loadedSlowField {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    (loadedRestrictedField ET FT ST (paperFixedBindingRates k) u).1 =
      (loadedRestrictedField ET FT ST k u).1 := by
  rw [loadedRestrictedField_slow_eq_incidence_current,
    loadedRestrictedField_slow_eq_incidence_current]
  rfl

/-- Each fast kinase row changes by one positive rate-dependent scalar. -/
theorem paperFixedBindingRates_loadedFastC {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (hk : k.Positive)
    (u : CoordinateSpace n) (i : Fin n) :
    (loadedRestrictedField ET FT ST (paperFixedBindingRates k) u).2.1 i =
      ((1 + k.c i) / (k.b i + k.c i)) *
        (loadedRestrictedField ET FT ST k u).2.1 i := by
  have hden : k.b i + k.c i ≠ 0 :=
    ne_of_gt (add_pos (hk i).2.1 (hk i).2.2.1)
  rw [loadedFastField_C, loadedFastField_C]
  simp only [paperFixedBindingRates, sourceBindingP_castSucc]
  field_simp [hden]

/-- Each fast phosphatase row changes by one positive rate-dependent scalar. -/
theorem paperFixedBindingRates_loadedFastD {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (hk : k.Positive)
    (u : CoordinateSpace n) (i : Fin n) :
    (loadedRestrictedField ET FT ST (paperFixedBindingRates k) u).2.2 i =
      ((1 + k.gamma i) / (k.beta i + k.gamma i)) *
        (loadedRestrictedField ET FT ST k u).2.2 i := by
  have hden : k.beta i + k.gamma i ≠ 0 :=
    ne_of_gt (add_pos (hk i).2.2.2.2.1 (hk i).2.2.2.2.2)
  rw [loadedFastField_D, loadedFastField_D]
  simp only [paperFixedBindingRates, sourceBindingQ_succ]
  field_simp [hden]

/-- A fixed output map that rescales only the reversible-binding rows. -/
def paperFixedBindingOutputLinear {n : ℕ}
    (k : Rates n) : CoordinateSpace n →ₗ[ℝ] CoordinateSpace n where
  toFun v :=
    (v.1,
      (fun i => (1 + k.c i) / (k.b i + k.c i) * v.2.1 i,
       fun i => (1 + k.gamma i) / (k.beta i + k.gamma i) * v.2.2 i))
  map_add' v w := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> funext i <;> simp [mul_add]
  map_smul' a v := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> funext i <;> simp [smul_eq_mul] <;> ring

def paperFixedBindingOutputCLM {n : ℕ} (k : Rates n) :
    CoordinateSpace n →L[ℝ] CoordinateSpace n :=
  (paperFixedBindingOutputLinear k).toContinuousLinearMap

theorem paperFixedBindingRates_loadedField_eq_output {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (hk : k.Positive)
    (u : CoordinateSpace n) :
    loadedRestrictedField ET FT ST (paperFixedBindingRates k) u =
      paperFixedBindingOutputCLM k
        (loadedRestrictedField ET FT ST k u) := by
  apply Prod.ext
  · exact paperFixedBindingRates_loadedSlowField ET FT ST k u
  · apply Prod.ext <;> funext i
    · exact paperFixedBindingRates_loadedFastC ET FT ST k hk u i
    · exact paperFixedBindingRates_loadedFastD ET FT ST k hk u i

theorem paperFixedBindingRates_loadedFderiv_eq_comp {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (hk : k.Positive)
    (u : CoordinateSpace n) :
    fderiv ℝ (loadedRestrictedField ET FT ST (paperFixedBindingRates k)) u =
      (paperFixedBindingOutputCLM k).comp
        (fderiv ℝ (loadedRestrictedField ET FT ST k) u) := by
  have hfun : loadedRestrictedField ET FT ST (paperFixedBindingRates k) =
      (paperFixedBindingOutputCLM k) ∘
        loadedRestrictedField ET FT ST k := by
    funext v
    exact paperFixedBindingRates_loadedField_eq_output ET FT ST k hk v
  have hdiff :=
    (differentiable_loadedRestrictedField ET FT ST k).differentiableAt
      (x := u)
  rw [hfun]
  change fderiv ℝ
    ((paperFixedBindingOutputCLM k) ∘ loadedRestrictedField ET FT ST k) u = _
  rw [fderiv_comp u (paperFixedBindingOutputCLM k).differentiableAt hdiff]
  rw [ContinuousLinearMap.fderiv]

/-- The paper choice and the original realization have exactly the
same loaded Jacobian action whenever the original fast action vanishes. -/
theorem paperFixedBindingRates_loadedFderiv_fastZero {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (hk : k.Positive)
    (u v : CoordinateSpace n) (s : Fin n → ℝ)
    (h : fderiv ℝ (loadedRestrictedField ET FT ST k) u v =
      (s, (0, 0))) :
    fderiv ℝ (loadedRestrictedField ET FT ST
      (paperFixedBindingRates k)) u v = (s, (0, 0)) := by
  rw [paperFixedBindingRates_loadedFderiv_eq_comp ET FT ST k hk u]
  change paperFixedBindingOutputCLM k
    (fderiv ℝ (loadedRestrictedField ET FT ST k) u v) = _
  rw [h]
  simp [paperFixedBindingOutputCLM, paperFixedBindingOutputLinear]
  funext i
  simp

/-- The fixed-binding choice keeps every positive equilibrium of the
initial literal kinetics at the same physical concentrations and totals. -/
theorem paperFixedBindingRates_preserves_equilibrium {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (heq : Equilibrium k x) :
    Equilibrium (paperFixedBindingRates k) x := by
  obtain ⟨hp, hq⟩ := sourceBindingRatios_rate_identities k hk
  obtain ⟨hC, hD⟩ :=
    equilibrium_binding_complex_formulas k (sourceBindingP k)
      (sourceBindingQ k) x hk heq hp hq
  apply equilibrium_of_currents
  · intro i
    have hi := hC i
    dsimp [kinaseNet, paperFixedBindingRates]
    rw [hi]
    ring
  · intro i
    have hi := hD i
    dsimp [phosphataseNet, paperFixedBindingRates]
    rw [hi]
    ring
  · intro i
    change k.c i * x.C i = k.gamma i * x.D i
    exact equilibrium_catalytic_balance k x heq i

/-- Binding relaxation of the paper realization preserves the same
equilibrium and the same irreversible catalytic current. -/
theorem paperFixedBindingRates_relaxed_equilibrium {n : ℕ}
    (k : Rates n) (x : State n) (ε : ℝ)
    (hk : k.Positive) (heq : Equilibrium k x) (hε : ε ≠ 0) :
    Equilibrium (relaxRates (paperFixedBindingRates k) ε) x :=
  relaxRates_preserves_equilibrium _ _ hε
    (paperFixedBindingRates_preserves_equilibrium k x hk heq)

end

end PhosphorylationStableCapacity
