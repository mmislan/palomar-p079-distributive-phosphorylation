module
public import proofs.PhosphorylationStableCapacity.AllCurrentFiniteSlowSpectrum435
public import proofs.PhosphorylationStableCapacity.DyadicEventuallySelection
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCompleteLaw

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix Filter Polynomial
open scoped Topology

/-- First success means that every earlier test has finished and rejected.
No simultaneous enumeration or change of the paper's loop order is hidden
in this predicate. -/
def FirstAcceptedIndex (test : ℕ → Bool) (k : ℕ) : Prop :=
  test k = true ∧ ∀ i < k, test i = false

/-- A loop with one successful finite test has a first successful test. -/
theorem firstAcceptedIndex_exists (test : ℕ → Bool)
    (hsuccess : ∃ k, test k = true) :
    ∃ k, FirstAcceptedIndex test k := by
  refine ⟨Nat.find hsuccess, Nat.find_spec hsuccess, ?_⟩
  intro i hi
  have hnot := Nat.find_min hsuccess hi
  cases hval : test i with
  | false => rfl
  | true => exact False.elim (hnot hval)

/-- The actual four nested loops: each later test uses precisely the
parameters returned by the previous first-success loop. -/
def OrderedDesignAccepted
    («prefix» : ℕ → Bool) (slow : ℕ → ℕ → Bool)
    (coalesced : ℕ → ℕ → ℕ → Bool)
    (split : ℕ → ℕ → ℕ → ℕ → Bool)
    (a b c d : ℕ) : Prop :=
  FirstAcceptedIndex «prefix» a ∧ FirstAcceptedIndex (slow a) b ∧
    FirstAcceptedIndex (coalesced a b) c ∧
    FirstAcceptedIndex (split a b c) d

/-- Structural termination of the original ordered first-success loops.
The successor obligations are universal over accepted earlier choices;
a single favorable existential quadruple does not meet these premises. -/
theorem orderedDesign_first_acceptance
    («prefix» : ℕ → Bool) (slow : ℕ → ℕ → Bool)
    (coalesced : ℕ → ℕ → ℕ → Bool)
    (split : ℕ → ℕ → ℕ → ℕ → Bool)
    (hprefix : ∃ a, «prefix» a = true)
    (hslow : ∀ a, «prefix» a = true → ∃ b, slow a b = true)
    (hcoalesced : ∀ a b, «prefix» a = true → slow a b = true →
      ∃ c, coalesced a b c = true)
    (hsplit : ∀ a b c, «prefix» a = true → slow a b = true →
      coalesced a b c = true → ∃ d, split a b c d = true) :
    ∃ a b c d, OrderedDesignAccepted «prefix» slow coalesced split a b c d := by
  obtain ⟨a, ha⟩ := firstAcceptedIndex_exists «prefix» hprefix
  obtain ⟨b, hb⟩ := firstAcceptedIndex_exists (slow a) (hslow a ha.1)
  obtain ⟨c, hc⟩ := firstAcceptedIndex_exists (coalesced a b)
    (hcoalesced a b ha.1 hb.1)
  obtain ⟨d, hd⟩ := firstAcceptedIndex_exists (split a b c)
    (hsplit a b c ha.1 hb.1 hc.1)
  exact ⟨a, b, c, d, ha, hb, hc, hd⟩

/-- Geometric admission can be tested before accepting a prefix spectrum.
It preserves the doubling sequence and prevents a first spectral success
from silently discarding the source-parameter lower bound. -/
def rationalPrefixAdmission (m a : ℕ) (spectral : ℕ → Bool) : Bool :=
  decide ((3*((m+2 : ℕ) : ℚ))/2 ≤ (2 : ℚ)^a ∧
    1 < (2 : ℚ)^a ∧ spectral a = true)

theorem rationalPrefixAdmission_sound (m a : ℕ) (spectral : ℕ → Bool)
    (h : rationalPrefixAdmission m a spectral = true) :
    (3*(m+2 : ℝ))/2 ≤ (2 : ℝ)^a ∧
      1 < (2 : ℝ)^a ∧ spectral a = true := by
  simp only [rationalPrefixAdmission, decide_eq_true_eq] at h
  refine ⟨?_, by exact_mod_cast h.2.1, h.2.2⟩
  simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_pow, Nat.cast_add, Nat.cast_ofNat] using
    (Rat.cast_le (K := ℝ)).mpr h.1

/-- Admission itself terminates whenever the prefix spectral test accepts
all sufficiently large doubling indices. -/
theorem rationalPrefixAdmission_first_acceptance (m : ℕ)
    (spectral : ℕ → Bool)
    (hspectral : ∀ᶠ a : ℕ in atTop, spectral a = true) :
    ∃ a, FirstAcceptedIndex (fun a => rationalPrefixAdmission m a spectral) a := by
  have ht : Tendsto (fun a : ℕ => (2 : ℚ)^a) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hbound := ht.eventually (eventually_ge_atTop
    ((3*((m+2 : ℕ) : ℚ))/2))
  have hone := ht.eventually (eventually_gt_atTop (1 : ℚ))
  apply firstAcceptedIndex_exists
  obtain ⟨a, ha, hlarge, hgreater⟩ :=
    (hspectral.and (hbound.and hone)).exists
  refine ⟨a, ?_⟩
  simp only [rationalPrefixAdmission, decide_eq_true_eq]
  exact ⟨hlarge, hgreater, ha⟩

/-- If doubling starts at an admitted source value, every tested value
retains the paper's geometric lower bound. This is an admission invariant,
not a consequence of a Hurwitz test alone. -/
theorem doubling_from_admitted_start (m a₀ : ℕ)
    (hbound : (3*(m+2 : ℝ))/2 ≤ (2 : ℝ)^a₀)
    (hgreater : 1 < (2 : ℝ)^a₀) (k : ℕ) :
    (3*(m+2 : ℝ))/2 ≤ (2 : ℝ)^(a₀+k) ∧
      1 < (2 : ℝ)^(a₀+k) := by
  have hmono : (2 : ℝ)^a₀ ≤ (2 : ℝ)^(a₀+k) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  exact ⟨hbound.trans hmono, hgreater.trans_le hmono⟩

/-- At an accepted physical source parameter, prefix Hurwitz stability is
sufficient for the next (small final-current) stage. Thus the implication
is not restricted to one parameter chosen by an eventual-existence proof.
The normalized kernel is a source-geometry premise, not a spectral test. -/
theorem acceptedPrefix_eventually_slow_deflation
    (m : ℕ) (r : ℝ) (ω : Fin (m+1) → ℝ)
    (hω : ∀ i, 0 < ω i)
    (hprefix : IsHurwitz
      (coalescedPrefixLoadedMatrix m r * Matrix.diagonal ω))
    (hkernel : ∃ u : Fin (m+2) → ℝ,
      u (Fin.last (m+1)) = 1 ∧
        (coalescedFullLoadedMatrix m r).mulVec u = 0) :
    ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
      ∃ q : ℝ[X],
        (coalescedPrefixWeightedLoadedMatrix m r ω *
          Matrix.diagonal (coalescedFinalCurrentWeights m τ)).charpoly =
          q * Polynomial.X ∧ q.eval 0 ≠ 0 ∧
        ∀ z : ℂ, (q.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0 := by
  obtain ⟨u, hulast, hKu⟩ := hkernel
  obtain ⟨v, hvlast, hKv⟩ :=
    coalescedPrefixWeightedLoadedMatrix_kernel m r ω hω u hulast hKu
  have hp : IsHurwitz
      (fun i j : Fin (m+1) =>
        coalescedPrefixWeightedLoadedMatrix m r ω i.castSucc j.castSucc) := by
    have hmatrix : (fun i j : Fin (m+1) =>
        coalescedPrefixWeightedLoadedMatrix m r ω i.castSucc j.castSucc) =
        coalescedPrefixLoadedMatrix m r * Matrix.diagonal ω := by
      ext i j
      exact coalescedPrefixWeightedLoadedMatrix_prefix m r ω i j
    rw [hmatrix]
    exact hprefix
  have hτ := rankOneShearComplement_eventually_hurwitz_of_hurwitz
    (fun i j : Fin (m+1) =>
      coalescedPrefixWeightedLoadedMatrix m r ω i.castSucc j.castSucc)
    (fun i => v i.castSucc)
    (fun j => coalescedPrefixWeightedLoadedMatrix m r ω
      (Fin.last (m+1)) j.castSucc) hp
  filter_upwards [hτ.filter_mono nhdsWithin_le_nhds] with τ hτ
  let q := (finalEdgeShearComplement (m+1)
    (coalescedPrefixWeightedLoadedMatrix m r ω) v τ).charpoly
  refine ⟨q, ?_, ?_, ?_⟩
  · exact finalEdgeWeightedMatrix_charpoly_factor (m+1)
      (coalescedPrefixWeightedLoadedMatrix m r ω) v hvlast hKv τ
  · exact isHurwitz_charpoly_eval_zero_ne_zero (by
      simpa only [finalEdgeShearComplement] using hτ)
  · intro z hz
    apply hτ z
    rw [Matrix.charpoly_map]
    exact hz

/-- Once a common coalesced design has been accepted, a complete exact
spectral checker accepts a first dyadic member of that same literal family.
Its completeness hypothesis covers odd saddles as well as even sinks;
it cannot be replaced by completeness for Hurwitz matrices alone. -/
theorem paperFixedBinding_split_checker_first_acceptance
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε α K : ℝ)
    (ω : Fin (m+1) → ℝ)
    (lam : Fin (2*(m+1)+1) → ℝ → ℝ)
    (test : ℕ → Bool)
    (hfamily : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      PaperFixedBindingCompletePoint m ξ r τ ε α K δ ω lam)
    (hcomplete : ∀ d,
      PaperFixedBindingCompletePoint m ξ r τ ε α K ((1/2 : ℝ)^d) ω lam →
      test d = true) :
    ∃ d, FirstAcceptedIndex test d := by
  obtain ⟨d, hd⟩ := eventually_right_has_halving_index _ hfamily
  exact firstAcceptedIndex_exists test ⟨d, hcomplete d hd⟩

/-- Every output of the ordered dyadic procedure is strictly positive;
no denominator positivity is obtained by replacing these inequalities
with nonzero assumptions. -/
theorem orderedDesign_parameter_positive (a b c d : ℕ) :
    0 < (2 : ℝ)^a ∧ 0 < (1/2 : ℝ)^b ∧
      0 < (1/2 : ℝ)^c ∧ 0 < (1/2 : ℝ)^d ∧
      (1/2 : ℝ)^c ≤ 1 := by
  refine ⟨pow_pos (by norm_num) a, pow_pos (by norm_num) b,
    pow_pos (by norm_num) c, pow_pos (by norm_num) d, ?_⟩
  exact pow_le_one₀ (by norm_num) (by norm_num)

end
end PhosphorylationStableCapacity
