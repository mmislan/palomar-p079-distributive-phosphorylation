module
public import proofs.PhosphorylationStableCapacity.RouthPositiveRealRoot435
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial Filter
open scoped Topology BigOperators

private theorem positiveRootContinuityReal_eval_map (p : ℝ[X]) (u : ℝ) :
    (p.map (algebraMap ℝ ℂ)).eval (u : ℂ) =
      ((p.eval u : ℝ) : ℂ) := by
  simpa only [Complex.coe_algebraMap] using
    (Polynomial.eval_map_apply (p := p) (f := algebraMap ℝ ℂ) u)

/-- Finite coefficient convergence gives evaluation convergence at every
fixed real argument. Degrees are bounded, so no polynomial topology or root
labelling theorem is needed. -/
theorem bounded_degree_real_polynomial_eval_tendsto
    {T : Type*} (l : Filter T) (P : T → ℝ[X]) (p : ℝ[X]) (d : ℕ)
    (hdegree : ∀ t, (P t).natDegree ≤ d) (hpdegree : p.natDegree ≤ d)
    (hcoeff : ∀ i ≤ d, Tendsto (fun t => (P t).coeff i) l (𝓝 (p.coeff i)))
    (x : ℝ) : Tendsto (fun t => (P t).eval x) l (𝓝 (p.eval x)) := by
  classical
  have hsum := tendsto_finsetSum (Finset.range (d+1))
    (fun i hi => (hcoeff i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).mul
      (tendsto_const_nhds : Tendsto (fun _ : T => x^i) l (𝓝 (x^i))))
  have heq : (fun t => (P t).eval x) =
      (fun t => ∑ i ∈ Finset.range (d+1), (P t).coeff i*x^i) := by
    funext t
    exact (P t).eval_eq_sum_range' (Nat.lt_succ_iff.mpr (hdegree t)) x
  rw [heq, p.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hpdegree) x]
  exact hsum

/-- Fixed strict sign brackets persist in parameter neighborhoods. IVT
and uniqueness then place the same selected positive root between them. -/
theorem selected_positive_root_eventually_between
    {T : Type*} [TopologicalSpace T] (P : T → ℝ[X]) (d : ℕ)
    (hdegree : ∀ t, (P t).natDegree ≤ d)
    (hcoeff : ∀ i ≤ d, Continuous (fun t => (P t).coeff i))
    (u : T → ℝ)
    (hunique : ∀ t, ∀ v : ℝ, 0 < v → (P t).eval v = 0 → v = u t)
    (a : T) (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    (hleft : (P a).eval b < 0) (hright : 0 < (P a).eval c) :
    ∀ᶠ t in 𝓝 a, b < u t ∧ u t < c := by
  have hlim (x : ℝ) : Tendsto (fun t => (P t).eval x) (𝓝 a) (𝓝 ((P a).eval x)) :=
    bounded_degree_real_polynomial_eval_tendsto (𝓝 a) P (P a) d hdegree (hdegree a)
      (fun i hi => (hcoeff i hi).tendsto a) x
  have hleft' := (hlim b).eventually (Iio_mem_nhds hleft)
  have hright' := (hlim c).eventually (Ioi_mem_nhds hright)
  filter_upwards [hleft', hright'] with t htleft htright
  obtain ⟨v, hv, hvroot⟩ := intermediate_value_Icc hbc.le
    (P t).continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Icc ((P t).eval b) ((P t).eval c) from
        ⟨htleft.le, htright.le⟩)
  have hvpos : 0 < v := hb.trans_le hv.1
  have hvneleft : v ≠ b := by
    intro heq
    exact htleft.ne (heq ▸ hvroot)
  have hvneright : v ≠ c := by
    intro heq
    exact htright.ne' (heq ▸ hvroot)
  have hveq := hunique t v hvpos hvroot
  rw [← hveq]
  exact ⟨lt_of_le_of_ne hv.1 hvneleft.symm,
    lt_of_le_of_ne hv.2 hvneright⟩

/-- Arbitrarily narrow positive sign brackets prove continuity of the
unique positive real root, using only finite coefficient continuity. -/
theorem selected_positive_root_continuousAt_of_brackets
    {T : Type*} [TopologicalSpace T] (P : T → ℝ[X]) (d : ℕ)
    (hdegree : ∀ t, (P t).natDegree ≤ d)
    (hcoeff : ∀ i ≤ d, Continuous (fun t => (P t).coeff i))
    (u : T → ℝ) (hupos : ∀ t, 0 < u t)
    (hunique : ∀ t, ∀ v : ℝ, 0 < v → (P t).eval v = 0 → v = u t)
    (a : T)
    (hbrackets : ∀ b c : ℝ, 0 < b → b < u a → u a < c →
      (P a).eval b < 0 ∧ 0 < (P a).eval c) : ContinuousAt u a := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨b', hmax, hb'u⟩ := exists_between
      (max_lt_iff.mpr ⟨hb, hupos a⟩ : max b 0 < u a)
    have hb'b : b < b' := (le_max_left b 0).trans_lt hmax
    have hb' : 0 < b' := (le_max_right b 0).trans_lt hmax
    let c : ℝ := u a+1
    have huc : u a < c := by dsimp [c]; linarith
    have hsign := hbrackets b' c hb' hb'u huc
    filter_upwards [selected_positive_root_eventually_between
      P d hdegree hcoeff u hunique a b' c hb' (hb'u.trans huc) hsign.1 hsign.2]
      with t ht
    exact hb'b.trans ht.1
  · intro c hc
    obtain ⟨c', huc', hc'c⟩ := exists_between hc
    let b : ℝ := u a/2
    have hb : 0 < b := by dsimp [b]; linarith [hupos a]
    have hbu : b < u a := by dsimp [b]; linarith [hupos a]
    have hsign := hbrackets b c' hb hbu huc'
    filter_upwards [selected_positive_root_eventually_between
      P d hdegree hcoeff u hunique a b c' hb (hbu.trans huc') hsign.1 hsign.2]
      with t ht
    exact ht.2.trans hc'c

/-- The coefficient-transition proof supplies the strict brackets around
its root: normalized evaluation is strictly increasing and the root is zero. -/
theorem signedCoefficientTransition_positive_root_brackets
    (p : ℝ[X]) (cut : ℕ) (h : SignedCoefficientTransition p cut)
    (u : ℝ) (hu : 0 < u) (hroot : p.eval u = 0)
    (b c : ℝ) (hb : 0 < b) (hbu : b < u) (huc : u < c) :
    p.eval b < 0 ∧ 0 < p.eval c := by
  have hmono := signedCoefficientTransition_normalized_strictMonoOn p cut h
  have hc : 0 < c := hu.trans huc
  have hleft := hmono hb hu hbu
  have hright := hmono hu hc huc
  dsimp only at hleft hright
  rw [hroot, zero_div] at hleft hright
  refine ⟨?_, (div_pos_iff_of_pos_right (pow_pos hc cut)).mp hright⟩
  simpa only [zero_mul] using (div_lt_iff₀ (pow_pos hb cut)).mp hleft

/-- In a continuous bounded-degree family with one coefficient transition,
the actual selected positive root is continuous. No bracket or continuous
root hypothesis remains in this endpoint. -/
theorem signedCoefficientTransition_positive_root_continuous
    {T : Type*} [TopologicalSpace T] (P : T → ℝ[X]) (d : ℕ)
    (hdegree : ∀ t, (P t).natDegree ≤ d)
    (hcoeff : ∀ i ≤ d, Continuous (fun t => (P t).coeff i))
    (cut : T → ℕ) (htransition : ∀ t, SignedCoefficientTransition (P t) (cut t))
    (u : T → ℝ) (hupos : ∀ t, 0 < u t) (hroot : ∀ t, (P t).eval (u t) = 0) :
    Continuous u := by
  have hunique (t : T) (v : ℝ) (hv : 0 < v) (hvro : (P t).eval v = 0) :
      v = u t := signedCoefficientTransition_positive_root_unique
    (P t) (cut t) (htransition t) v (u t) hv (hupos t) hvro (hroot t)
  apply continuous_iff_continuousAt.mpr
  intro a
  exact selected_positive_root_continuousAt_of_brackets P d hdegree hcoeff u hupos
    hunique a (signedCoefficientTransition_positive_root_brackets
      (P a) (cut a) (htransition a) (u a) (hupos a) (hroot a))

/-- Construct the actual continuous positive root from the already-proved
existence, uniqueness and simplicity endpoint. The same function has the
real root identity and strictly positive derivative at every parameter. -/
theorem signedCoefficientTransition_continuous_simple_positive_root_exists
    {T : Type*} [TopologicalSpace T] (P : T → ℝ[X]) (d : ℕ)
    (hdegree : ∀ t, (P t).natDegree ≤ d)
    (hcoeff : ∀ i ≤ d, Continuous (fun t => (P t).coeff i))
    (cut : T → ℕ) (htransition : ∀ t, SignedCoefficientTransition (P t) (cut t))
    (hleading : ∀ t, 0 < (P t).leadingCoeff) :
    ∃ u : T → ℝ, Continuous u ∧ ∀ t, 0 < u t ∧ (P t).eval (u t) = 0 ∧
      0 < (P t).derivative.eval (u t) ∧
      ∀ v : ℝ, 0 < v → (P t).eval v = 0 → v = u t := by
  choose u hu hroot hderiv hunique using
    (fun t => signedCoefficientTransition_unique_simple_positive_root
      (P t) (cut t) (htransition t) (hleading t))
  exact ⟨u, signedCoefficientTransition_positive_root_continuous
    P d hdegree hcoeff cut htransition u hu hroot,
      fun t => ⟨hu t, hroot t, hderiv t, hunique t⟩⟩

/-- The same continuous selected root supplies the complex root and
simplicity identities consumed by the signed-family topology theorem. -/
theorem signedCoefficientTransition_continuous_simple_positive_complex_root_exists
    {T : Type*} [TopologicalSpace T] (P : T → ℝ[X]) (d : ℕ)
    (hdegree : ∀ t, (P t).natDegree ≤ d)
    (hcoeff : ∀ i ≤ d, Continuous (fun t => (P t).coeff i))
    (cut : T → ℕ) (htransition : ∀ t, SignedCoefficientTransition (P t) (cut t))
    (hleading : ∀ t, 0 < (P t).leadingCoeff) :
    ∃ u : T → ℝ, Continuous u ∧ ∀ t, 0 < u t ∧
      ((P t).map (algebraMap ℝ ℂ)).eval (u t : ℂ) = 0 ∧
      ((P t).map (algebraMap ℝ ℂ)).derivative.eval (u t : ℂ) ≠ 0 ∧
      ∀ v : ℝ, 0 < v → ((P t).map (algebraMap ℝ ℂ)).eval (v : ℂ) = 0 → v = u t := by
  obtain ⟨u, hu, hroots⟩ :=
    signedCoefficientTransition_continuous_simple_positive_root_exists
      P d hdegree hcoeff cut htransition hleading
  refine ⟨u, hu, ?_⟩
  intro t
  obtain ⟨hupos, hroot, hderiv, hunique⟩ := hroots t
  refine ⟨hupos, ?_, ?_, ?_⟩
  · simpa only [positiveRootContinuityReal_eval_map, Complex.ofReal_eq_zero] using hroot
  · have hnonzero : (((P t).derivative.eval (u t) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hderiv.ne'
    simpa only [Polynomial.derivative_map, positiveRootContinuityReal_eval_map] using hnonzero
  · intro v hv hvroot
    apply hunique v hv
    have hcast : (((P t).eval v : ℝ) : ℂ) = 0 := by
      simpa only [positiveRootContinuityReal_eval_map] using hvroot
    exact_mod_cast hcast

/-- At a neutral endpoint, IVT on [0,b] and uniqueness suffice to show
that the positive root tends to zero. Only signs at fixed, arbitrarily
small positive endpoints are used; simplicity at the neutral endpoint
and an implicit-function theorem are unnecessary. -/
theorem selected_positive_root_tendsto_zero_of_fixed_brackets
    {T : Type*} (l : Filter T) (P : T → ℝ[X]) (p : ℝ[X]) (u : T → ℝ)
    (heval : ∀ x : ℝ, Tendsto (fun t => (P t).eval x) l (𝓝 (p.eval x)))
    (hupos : ∀ᶠ t in l, 0 < u t)
    (hnegative : ∀ᶠ t in l, (P t).eval 0 < 0)
    (hunique : ∀ᶠ t in l, ∀ v : ℝ, 0 < v → (P t).eval v = 0 → v = u t)
    (hbrackets : ∀ c : ℝ, 0 < c → ∃ b : ℝ, 0 < b ∧ b < c ∧ 0 < p.eval b) :
    Tendsto u l (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [hupos] with t ht
    exact hb.trans ht
  · intro c hc
    obtain ⟨b, hb, hbc, hpb⟩ := hbrackets c hc
    have hright := (heval b).eventually (Ioi_mem_nhds hpb)
    filter_upwards [hnegative, hunique, hright] with t htzero htunique htb
    obtain ⟨v, hv, hvroot⟩ := intermediate_value_Icc hb.le
      (P t).continuous.continuousOn
        (show (0 : ℝ) ∈ Set.Icc ((P t).eval 0) ((P t).eval b) from
          ⟨htzero.le, htb.le⟩)
    have hvne : v ≠ 0 := by
      intro heq
      exact htzero.ne (heq ▸ hvroot)
    have hvpos : 0 < v := lt_of_le_of_ne hv.1 hvne.symm
    have hveq := htunique v hvpos hvroot
    rw [← hveq]
    exact hv.2.trans_lt hbc

/-- The neutral-endpoint convergence theorem with its evaluation limits
derived directly from the finite coefficient family. -/
theorem bounded_degree_selected_positive_root_tendsto_zero
    {T : Type*} (l : Filter T) (P : T → ℝ[X]) (p : ℝ[X]) (d : ℕ)
    (hdegree : ∀ t, (P t).natDegree ≤ d) (hpdegree : p.natDegree ≤ d)
    (hcoeff : ∀ i ≤ d, Tendsto (fun t => (P t).coeff i) l (𝓝 (p.coeff i)))
    (u : T → ℝ) (hupos : ∀ᶠ t in l, 0 < u t)
    (hnegative : ∀ᶠ t in l, (P t).eval 0 < 0)
    (hunique : ∀ᶠ t in l, ∀ v : ℝ, 0 < v → (P t).eval v = 0 → v = u t)
    (hbrackets : ∀ c : ℝ, 0 < c → ∃ b : ℝ, 0 < b ∧ b < c ∧ 0 < p.eval b) :
    Tendsto u l (𝓝 0) :=
  selected_positive_root_tendsto_zero_of_fixed_brackets l P p u
    (bounded_degree_real_polynomial_eval_tendsto l P p d hdegree hpdegree hcoeff)
    hupos hnegative hunique hbrackets

end
end PhosphorylationStableCapacity
