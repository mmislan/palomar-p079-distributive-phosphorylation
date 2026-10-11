module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingOrderedSearch435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingRationality

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Polynomial Filter
open scoped Topology BigOperators

noncomputable section

/-- Rational producers for exactly the paper's prescribed root recurrence. -/
def orderedRationalNextN (a b : ℚ) (p q : ℚ[X]) : ℚ[X] :=
  C ((a+1)*(b+1))*p + C 8*(X*p) + C (2*(a+b))*q

def orderedRationalNextJ (a b : ℚ) (p q : ℚ[X]) : ℚ[X] :=
  C ((a-1)*(b-1))*q + C 8*(X*q) + C (4*(a+b))*(X*p)

def orderedRationalPair : ℕ → (ℕ → ℚ) → ℚ → ℚ[X] × ℚ[X]
  | 0, ξ, δ => (1, C ((3+δ*ξ 0-1)/2))
  | n+1, ξ, δ =>
      let pq := orderedRationalPair n ξ δ
      (orderedRationalNextN (3+δ*ξ (2*n+1)) (3+δ*ξ (2*n+2)) pq.1 pq.2,
       orderedRationalNextJ (3+δ*ξ (2*n+1)) (3+δ*ξ (2*n+2)) pq.1 pq.2)

def orderedRationalRawD (n : ℕ) (ξ : ℕ → ℚ) (r δ : ℚ) : ℚ[X] :=
  let pq := orderedRationalPair n ξ δ
  C 4*((C (pq.2.eval r)*(X*pq.1)-C (r*pq.1.eval r)*pq.2) /ₘ (X-C r))

def orderedRationalRawB (n : ℕ) (ξ : ℕ → ℚ) (r δ : ℚ) : ℚ[X] :=
  let pq := orderedRationalPair n ξ δ
  C r*orderedRationalRawD n ξ r δ +
    C (4*r*pq.1.eval r-2*pq.2.eval r)*pq.1-C (2*pq.2.eval r)*pq.2

/-- Finite coefficient checks include the support bound. They decide
DensePositive exactly after embedding into the real numbers. -/
def orderedRationalDenseAccepts (n : ℕ) (p : ℚ[X]) : Bool :=
  decide ((∀ i : Fin (n+1), 0 < p.coeff i.val) ∧ p.natDegree ≤ n)

/-- Admission of a large-source candidate; the spectrum test stays an
independent finite test. Coefficient guards are redundant under the
manuscript's positivity theorem but make physical admission explicit. -/
def orderedRationalPrefixAdmits (m : ℕ) (r : ℚ) : Bool :=
  (decide (1 < r ∧ (3*((m+2 : ℕ) : ℚ))/2 ≤ r) &&
    orderedRationalDenseAccepts (m+1)
      (orderedRationalRawD (m+1) (fun j => (j : ℚ)) r 0)) &&
    orderedRationalDenseAccepts (m+1)
      (orderedRationalRawB (m+1) (fun j => (j : ℚ)) r 0)

/-- A distance is physically eligible before its original Routh tests
are performed. All operations are finite rational arithmetic. -/
def orderedRationalSplitAdmits (m : ℕ) (ξ : ℕ → ℚ) (r δ ε : ℚ) : Bool :=
  (decide (0 < r ∧ 0 < δ ∧ 0 < ε ∧ ε ≤ 1 ∧
    ∀ j : Fin (2*(m+1)+1), 1 < 3+δ*ξ j.val) &&
    orderedRationalDenseAccepts (m+1) (orderedRationalRawD (m+1) ξ r δ)) &&
    orderedRationalDenseAccepts (m+1) (orderedRationalRawB (m+1) ξ r δ)

/-- A conservative rational initialization domain for natural offsets.
It makes the manuscript's root geometry persist under every halving. -/
def orderedRationalNatGeometryAdmits (m : ℕ) (r δ : ℚ) : Bool :=
  decide ((3*((m+2 : ℕ) : ℚ))/2 ≤ r ∧ 0 < δ ∧
    δ*((m+2 : ℕ) : ℚ)*((2*(m+1)+1 : ℕ) : ℚ) ≤ 1)

/-- The original prefix spectral test, with physical admission before
acceptance. The doubling order is unchanged. -/
def orderedRationalPhysicalPrefixTest (m : ℕ) (spectral : ℕ → Bool)
    (a : ℕ) : Bool :=
  orderedRationalPrefixAdmits m ((2 : ℚ)^a) && spectral a

/-- The original simultaneous odd/even spectral test, with physical
admission before acceptance. Its actual distance and binding scale are
the original halving sequences. -/
def orderedRationalPhysicalSplitTest (m : ℕ) (ξ : ℕ → ℚ)
    (spectral : ℕ → ℕ → ℕ → ℕ → Bool) (a b c d : ℕ) : Bool :=
  orderedRationalSplitAdmits m ξ
    ((2 : ℚ)^a) ((1/2 : ℚ)^d) ((1/2 : ℚ)^c) && spectral a b c d

private theorem orderedRationalReal_div {x y : ℝ}
    (hx : RationalReal x) (hy : RationalReal y) : RationalReal (x/y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a/b, by norm_num⟩

private theorem orderedRational_eval_cast (p : ℚ[X]) (r : ℚ) :
    (p.map (algebraMap ℚ ℝ)).eval (r : ℝ) = ((p.eval r : ℚ) : ℝ) := by
  simpa using (Polynomial.eval_map_apply (p := p) (f := algebraMap ℚ ℝ) r)

theorem orderedRationalPair_cast (n : ℕ) (ξ : ℕ → ℚ) (δ : ℚ) :
    ((orderedRationalPair n ξ δ).1.map (algebraMap ℚ ℝ) =
      (arbitrarySplitPair n (fun j => (ξ j : ℝ)) (δ : ℝ)).1) ∧
    ((orderedRationalPair n ξ δ).2.map (algebraMap ℚ ℝ) =
      (arbitrarySplitPair n (fun j => (ξ j : ℝ)) (δ : ℝ)).2) := by
  induction n with
  | zero => simp [orderedRationalPair, arbitrarySplitPair, offsetSplitRoot]
  | succ n ih =>
    simp [orderedRationalPair, arbitrarySplitPair, orderedRationalNextN,
      orderedRationalNextJ, nextN, nextJ, offsetSplitRoot,
      Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, ih.1, ih.2]

theorem orderedRationalRawD_cast (n : ℕ) (ξ : ℕ → ℚ) (r δ : ℚ) :
    (orderedRationalRawD n ξ r δ).map (algebraMap ℚ ℝ) =
      arbitrarySplitRawD n (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ) := by
  have hpair := orderedRationalPair_cast n ξ δ
  have hevP : (((orderedRationalPair n ξ δ).1.eval r : ℚ) : ℝ) =
      (arbitrarySplitPair n (fun j => (ξ j : ℝ)) (δ : ℝ)).1.eval (r : ℝ) := by
    rw [← orderedRational_eval_cast, hpair.1]
  have hevQ : (((orderedRationalPair n ξ δ).2.eval r : ℚ) : ℝ) =
      (arbitrarySplitPair n (fun j => (ξ j : ℝ)) (δ : ℝ)).2.eval (r : ℝ) := by
    rw [← orderedRational_eval_cast, hpair.2]
  unfold orderedRationalRawD arbitrarySplitRawD rawD quotient conversionNumerator
  rw [Polynomial.map_mul, Polynomial.map_divByMonic
    (algebraMap ℚ ℝ) (monic_X_sub_C r)]
  simp [Polynomial.map_sub, Polynomial.map_mul, hpair.1, hpair.2,
    hevP, hevQ]

theorem orderedRationalRawB_cast (n : ℕ) (ξ : ℕ → ℚ) (r δ : ℚ) :
    (orderedRationalRawB n ξ r δ).map (algebraMap ℚ ℝ) =
      arbitrarySplitRawB n (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ) := by
  have hpair := orderedRationalPair_cast n ξ δ
  have hevP : (((orderedRationalPair n ξ δ).1.eval r : ℚ) : ℝ) =
      (arbitrarySplitPair n (fun j => (ξ j : ℝ)) (δ : ℝ)).1.eval (r : ℝ) := by
    rw [← orderedRational_eval_cast, hpair.1]
  have hevQ : (((orderedRationalPair n ξ δ).2.eval r : ℚ) : ℝ) =
      (arbitrarySplitPair n (fun j => (ξ j : ℝ)) (δ : ℝ)).2.eval (r : ℝ) := by
    rw [← orderedRational_eval_cast, hpair.2]
  unfold orderedRationalRawB arbitrarySplitRawB rawB
  simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    orderedRationalRawD_cast, arbitrarySplitRawD, hpair.1, hpair.2, hevP, hevQ]

theorem orderedRationalDenseAccepts_iff (n : ℕ) (p : ℚ[X]) :
    orderedRationalDenseAccepts n p = true ↔
      DensePositive (p.map (algebraMap ℚ ℝ)) n := by
  simp only [orderedRationalDenseAccepts, decide_eq_true_eq]
  constructor
  · rintro ⟨hpositive, hdegree⟩
    constructor
    · intro i hi
      have h := hpositive ⟨i, by omega⟩
      simp only [Polynomial.coeff_map]
      change (0 : ℝ) < (p.coeff i : ℝ)
      exact (Rat.cast_pos (K := ℝ)).mpr h
    · intro i hi
      have h := Polynomial.natDegree_le_iff_coeff_eq_zero.mp hdegree i hi
      simp [Polynomial.coeff_map, h]
  · intro h
    constructor
    · intro i
      have hi := h.1 i.val (by omega)
      simp only [Polynomial.coeff_map] at hi
      change (0 : ℝ) < (p.coeff i.val : ℝ) at hi
      exact (Rat.cast_pos (K := ℝ)).mp hi
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro i hi
      have heq := h.2 i hi
      simp only [Polynomial.coeff_map] at heq
      change (p.coeff i : ℝ) = 0 at heq
      exact Rat.cast_eq_zero.mp heq

theorem orderedRationalPrefixAdmits_iff (m : ℕ) (r : ℚ) :
    orderedRationalPrefixAdmits m r = true ↔
      1 < (r : ℝ) ∧ (3*(m+2 : ℝ))/2 ≤ (r : ℝ) ∧
        DensePositive (coalescedRawD (m+1) (r : ℝ)) (m+1) ∧
        DensePositive (coalescedRawB (m+1) (r : ℝ)) (m+1) := by
  simp only [orderedRationalPrefixAdmits, Bool.and_eq_true, decide_eq_true_eq,
    orderedRationalDenseAccepts_iff, orderedRationalRawD_cast, orderedRationalRawB_cast]
  have hD : arbitrarySplitRawD (m+1) (fun j => ((j : ℚ) : ℝ)) (r : ℝ) 0 =
      coalescedRawD (m+1) (r : ℝ) := by
    simp [arbitrarySplitRawD, coalescedRawD, arbitrarySplitPair_zero_eq_coalesced]
  have hB : arbitrarySplitRawB (m+1) (fun j => ((j : ℚ) : ℝ)) (r : ℝ) 0 =
      coalescedRawB (m+1) (r : ℝ) := by
    simp [arbitrarySplitRawB, coalescedRawB, arbitrarySplitPair_zero_eq_coalesced]
  simp only [Rat.cast_zero]
  rw [hD, hB]
  constructor
  · rintro ⟨⟨⟨hr, hbound⟩, hd⟩, hb⟩
    refine ⟨by exact_mod_cast hr, ?_, hd, hb⟩
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_ofNat, Nat.cast_add, Nat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hbound
  · rintro ⟨hr, hbound, hd, hb⟩
    refine ⟨⟨⟨by exact_mod_cast hr, ?_⟩, hd⟩, hb⟩
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_ofNat, Nat.cast_add, Nat.cast_ofNat] using hbound

theorem orderedRationalSplitAdmits_iff (m : ℕ) (ξ : ℕ → ℚ) (r δ ε : ℚ) :
    orderedRationalSplitAdmits m ξ r δ ε = true ↔
      0 < (r : ℝ) ∧ 0 < (δ : ℝ) ∧ 0 < (ε : ℝ) ∧ (ε : ℝ) ≤ 1 ∧
      (∀ j : Fin (2*(m+1)+1), 1 < offsetSplitRoot (fun j => (ξ j : ℝ)) (δ : ℝ) j.val) ∧
      DensePositive (arbitrarySplitRawD (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ)) (m+1) ∧
      DensePositive (arbitrarySplitRawB (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ)) (m+1) := by
  simp only [orderedRationalSplitAdmits, Bool.and_eq_true, decide_eq_true_eq,
    orderedRationalDenseAccepts_iff, orderedRationalRawD_cast, orderedRationalRawB_cast]
  constructor
  · rintro ⟨⟨⟨hr, hδ, hε, hε1, hroots⟩, hd⟩, hb⟩
    refine ⟨by exact_mod_cast hr, by exact_mod_cast hδ,
      by exact_mod_cast hε, by exact_mod_cast hε1, ?_, hd, hb⟩
    intro j
    have hj := hroots j
    dsimp [offsetSplitRoot]
    exact_mod_cast hj
  · rintro ⟨hr, hδ, hε, hε1, hroots, hd, hb⟩
    refine ⟨⟨⟨by exact_mod_cast hr, by exact_mod_cast hδ,
      by exact_mod_cast hε, by exact_mod_cast hε1, ?_⟩, hd⟩, hb⟩
    intro j
    have hj := hroots j
    dsimp [offsetSplitRoot] at hj
    exact_mod_cast hj

/-- Every admitted distance has the same positive rates and every
prescribed positive equilibrium at the original common totals. The
frozen edge factors are carried intact from the coalesced choice. -/
theorem orderedRationalSplitAdmits_physical
    (m : ℕ) (ξ : ℕ → ℚ) (r δ ε : ℚ) (w : Fin (m+2) → ℝ)
    (hw : ∀ i, 0 < w i) (h : orderedRationalSplitAdmits m ξ r δ ε = true) :
    (paperFixedBindingSplitRates m (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ) (ε : ℝ) w).Positive ∧
    ∀ j : Fin (2*(m+1)+1),
      (arbitrarySplitFiniteState (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ) j).Positive ∧
      Equilibrium
        (paperFixedBindingSplitRates m (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ) (ε : ℝ) w)
        (arbitrarySplitFiniteState (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ) j) ∧
      InClass (2*(r : ℝ)) 2 (2*((r : ℝ)+1))
        (arbitrarySplitFiniteState (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ) j) := by
  obtain ⟨_, _, hε, hε1, hroots, hd, hb⟩ := (orderedRationalSplitAdmits_iff m ξ r δ ε).mp h
  have hsource (j : Fin (2*(m+1)+1)) := paperFixedBindingSplit_source
    m (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ) (ε : ℝ) w hw hε hε1 hd hb j (hroots j)
  exact ⟨(hsource 0).1, fun j => (hsource j).2⟩

/-- At every admitted source parameter the coalesced state is positive.
Thus all reciprocal complexes used to freeze the literal unit currents
are positive, regardless of which spectral candidate succeeds first. -/
theorem orderedRationalPrefixAdmits_coalesced_positive
    (m : ℕ) (r : ℚ) (h : orderedRationalPrefixAdmits m r = true) :
    (coalescedFiniteState (m+1) (r : ℝ)).Positive := by
  obtain ⟨_, _, hd, hb⟩ := (orderedRationalPrefixAdmits_iff m r).mp h
  have hd' : DensePositive (arbitrarySplitRawD (m+1) (fun j => (j : ℝ)) (r : ℝ) 0) (m+1) := by
    simpa [arbitrarySplitRawD, coalescedRawD, arbitrarySplitPair_zero_eq_coalesced] using hd
  have hb' : DensePositive (arbitrarySplitRawB (m+1) (fun j => (j : ℝ)) (r : ℝ) 0) (m+1) := by
    simpa [arbitrarySplitRawB, coalescedRawB, arbitrarySplitPair_zero_eq_coalesced] using hb
  have hx := (arbitrarySplitFiniteState_source_of_conversion_positive
    (m+1) (fun j => (j : ℝ)) (r : ℝ) 0 hd' hb'
      (0 : Fin (2*(m+1)+1)) (by norm_num [offsetSplitRoot])).2.1
  simpa only [arbitrarySplitFiniteState_zero_eq_coalesced] using hx

/-- Every positive actual final current and unit prefix current produces
the same positive frozen edge factors at an admitted coalesced state. -/
theorem orderedRationalPrefixAdmits_frozen_factors_positive
    (m : ℕ) (r : ℚ) (h : orderedRationalPrefixAdmits m r = true)
    (t : ℝ) (ht : 0 < t) :
    let s₀ := coalescedFiniteState (m+1) (r : ℝ)
    ∀ i : Fin (m+2), 0 < (Fin.lastCases (motive := fun _ => ℝ)
      (t/s₀.D (Fin.last (m+1))) (fun j => 1/s₀.D j.castSucc)) i := by
  have hx := orderedRationalPrefixAdmits_coalesced_positive m r h
  intro s₀ i
  cases i using Fin.lastCases with
  | last => simpa using div_pos ht (hx.2.2.2.2 (Fin.last (m+1)))
  | cast j => simpa using div_pos (by norm_num : (0 : ℝ) < 1) (hx.2.2.2.2 j.castSucc)

/-- The exact halving sequence tends to zero through positive values. -/
private theorem ordered_halving_tendsto_right :
    Tendsto (fun b : ℕ => (1/2 : ℝ)^b) atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : (1/2 : ℝ) < 1)
  · exact Filter.Eventually.of_forall (fun b => pow_pos (by norm_num : (0 : ℝ) < 1/2) b)

/-- The physical guard eventually accepts along the actual halving
sequence, for every already admitted coalesced source parameter. -/
theorem orderedRationalSplitAdmits_eventually_halving
    (m : ℕ) (ξ : ℕ → ℚ) (r ε : ℚ)
    (hprefix : orderedRationalPrefixAdmits m r = true)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ b : ℕ in atTop,
      orderedRationalSplitAdmits m ξ r ((1/2 : ℚ)^b) ε = true := by
  obtain ⟨hr, _, hd, hb⟩ := (orderedRationalPrefixAdmits_iff m r).mp hprefix
  have hconv := arbitrarySplit_conversion_positive_near_zero
    (m+1) (fun j => (ξ j : ℝ)) (r : ℝ)
      (ne_of_gt (lt_trans zero_lt_one hr)) hd hb
  have hroots : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j ≤ 2*(m+1), 1 < offsetSplitRoot (fun j => (ξ j : ℝ)) δ j :=
    (offsetSplitRoot_gt_one_eventually (m+1)
      (fun j => (ξ j : ℝ))).filter_mono nhdsWithin_le_nhds
  have hsmall := ordered_halving_tendsto_right.eventually (hconv.and hroots)
  filter_upwards [hsmall] with b hgood
  apply (orderedRationalSplitAdmits_iff m ξ r ((1/2 : ℚ)^b) ε).mpr
  refine ⟨lt_trans zero_lt_one hr, ?_, by exact_mod_cast hε,
    by exact_mod_cast hε1, ?_, ?_, ?_⟩
  · exact_mod_cast (pow_pos (by norm_num : (0 : ℚ) < 1/2) b)
  · intro j
    have hj := hgood.2 j.val (by omega)
    simpa using hj
  · simpa using hgood.1.1
  · simpa using hgood.1.2

/-- A finite physical guard preserves termination of a spectral test
which eventually accepts along the very same halving sequence. -/
theorem orderedRational_admitted_split_first_acceptance
    (m : ℕ) (ξ : ℕ → ℚ) (r ε : ℚ)
    (hprefix : orderedRationalPrefixAdmits m r = true)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (spectral : ℕ → Bool)
    (hspectral : ∀ᶠ b : ℕ in atTop, spectral b = true) :
    ∃ d, FirstAcceptedIndex
      (fun b => orderedRationalSplitAdmits m ξ r ((1/2 : ℚ)^b) ε && spectral b) d := by
  have hadmit := orderedRationalSplitAdmits_eventually_halving m ξ r ε hprefix hε hε1
  obtain ⟨d, hd, hs⟩ := (hadmit.and hspectral).exists
  apply firstAcceptedIndex_exists
  exact ⟨d, Bool.and_eq_true_iff.mpr ⟨hd, hs⟩⟩

/-- Physical admissibility of every first accepted split, with precisely
the coalesced state, actual current, and frozen factors selected earlier.
It does not conjoin a second independently constructed kinetic witness. -/
theorem orderedRational_first_accepted_split_physical
    (m : ℕ) (ξ : ℕ → ℚ) (r ε : ℚ) (t : ℝ)
    (hprefix : orderedRationalPrefixAdmits m r = true) (ht : 0 < t)
    (spectral : ℕ → Bool) (d : ℕ)
    (hfirst : FirstAcceptedIndex
      (fun b => orderedRationalSplitAdmits m ξ r ((1/2 : ℚ)^b) ε && spectral b) d) :
    let s₀ := coalescedFiniteState (m+1) (r : ℝ)
    let w  := Fin.lastCases (motive := fun _ => ℝ) (t/s₀.D (Fin.last (m+1))) (fun j => 1/s₀.D j.castSucc)
    let δ : ℝ := ((1/2 : ℚ)^d : ℚ)
    (paperFixedBindingSplitRates m (fun j => (ξ j : ℝ)) (r : ℝ) δ (ε : ℝ) w).Positive ∧
    ∀ j : Fin (2*(m+1)+1),
      (arbitrarySplitFiniteState (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) δ j).Positive ∧
      Equilibrium (paperFixedBindingSplitRates m (fun j => (ξ j : ℝ)) (r : ℝ) δ (ε : ℝ) w)
        (arbitrarySplitFiniteState (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) δ j) ∧
      InClass (2*(r : ℝ)) 2 (2*((r : ℝ)+1))
        (arbitrarySplitFiniteState (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) δ j) := by
  have hadmit := (Bool.and_eq_true_iff.mp hfirst.1).1
  exact orderedRationalSplitAdmits_physical m ξ r ((1/2 : ℚ)^d) ε _
    (orderedRationalPrefixAdmits_frozen_factors_positive m r hprefix t ht) hadmit

/-- Prefix coefficient admission eventually succeeds along the very
same doubling sequence as the manuscript's first spectral loop. -/
theorem orderedRationalPrefixAdmits_eventually_doubling (m : ℕ) :
    ∀ᶠ a : ℕ in atTop, orderedRationalPrefixAdmits m ((2 : ℚ)^a) = true := by
  obtain ⟨hp, hq⟩ := coalescedPair_dense (m+1)
  have hconv := conversion_eventually_positive hp hq
  have ht : Tendsto (fun a : ℕ => (2 : ℝ)^a) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hphysical := ht.eventually
    (hconv.and ((eventually_gt_atTop (1 : ℝ)).and
      (eventually_ge_atTop ((3*(m+2 : ℝ))/2))))
  filter_upwards [hphysical] with a ha
  apply (orderedRationalPrefixAdmits_iff m ((2 : ℚ)^a)).mpr
  rcases ha with ⟨⟨hd, hb⟩, hr, hbound⟩
  refine ⟨by simpa using hr, by simpa using hbound, ?_, ?_⟩
  · simpa [coalescedRawD] using hd
  · simpa [coalescedRawB] using hb

/-- A first spectral success with the explicit coefficient guard is
physically admitted and adequate; the guard does not rely on any inferred
positivity from a spectrum alone. -/
theorem orderedRational_admitted_prefix_first_acceptance
    (m : ℕ) (spectral : ℕ → Bool)
    (hspectral : ∀ᶠ a : ℕ in atTop, spectral a = true) :
    ∃ a, FirstAcceptedIndex
      (fun a => orderedRationalPrefixAdmits m ((2 : ℚ)^a) && spectral a) a := by
  obtain ⟨a, ha, hs⟩ :=
    ((orderedRationalPrefixAdmits_eventually_doubling m).and hspectral).exists
  apply firstAcceptedIndex_exists
  exact ⟨a, by simp [ha, hs]⟩

/-- Positivity, equilibrium, and actual unit-prefix/final-t currents hold
for every positive t and every 0<epsilon<=1 at an admitted r. Thus neither
later spectral first success can spoil the coalesced physical witness. -/
theorem orderedRationalPrefixAdmits_coalesced_actual_currents
    (m : ℕ) (r : ℚ) (hprefix : orderedRationalPrefixAdmits m r = true)
    (t ε : ℝ) (ht : 0 < t) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let s₀ := coalescedFiniteState (m+1) (r : ℝ)
    let w  := Fin.lastCases (motive := fun _ => ℝ) (t/s₀.D (Fin.last (m+1))) (fun j => 1/s₀.D j.castSucc)
    let k := paperFixedBindingSplitRates m (fun j => (j : ℝ)) (r : ℝ) 0 ε w
    k.Positive ∧ s₀.Positive ∧ Equilibrium k s₀ ∧
      InClass (2*(r : ℝ)) 2 (2*((r : ℝ)+1)) s₀ ∧
      (∀ i : Fin (m+1), k.gamma i.castSucc*s₀.D i.castSucc = 1) ∧
      k.gamma (Fin.last (m+1))*s₀.D (Fin.last (m+1)) = t := by
  let s₀ := coalescedFiniteState (m+1) (r : ℝ)
  let w : Fin (m+2) → ℝ := Fin.lastCases (motive := fun _ => ℝ)
    (t/s₀.D (Fin.last (m+1))) (fun j => 1/s₀.D j.castSucc)
  let k := paperFixedBindingSplitRates m (fun j => (j : ℝ)) (r : ℝ) 0 ε w
  have hw := orderedRationalPrefixAdmits_frozen_factors_positive m r hprefix t ht
  obtain ⟨_, _, hd, hb⟩ := (orderedRationalPrefixAdmits_iff m r).mp hprefix
  have hd' : DensePositive (arbitrarySplitRawD (m+1) (fun j => (j : ℝ)) (r : ℝ) 0) (m+1) := by
    simpa [arbitrarySplitRawD, coalescedRawD, arbitrarySplitPair_zero_eq_coalesced] using hd
  have hb' : DensePositive (arbitrarySplitRawB (m+1) (fun j => (j : ℝ)) (r : ℝ) 0) (m+1) := by
    simpa [arbitrarySplitRawB, coalescedRawB, arbitrarySplitPair_zero_eq_coalesced] using hb
  have hsource := paperFixedBindingSplit_source m (fun j => (j : ℝ)) (r : ℝ) 0 ε w
    hw hε hε1 hd' hb' (0 : Fin (2*(m+1)+1)) (by norm_num [offsetSplitRoot])
  have hstatezero : arbitrarySplitFiniteState (m+1) (fun j => (j : ℝ)) (r : ℝ) 0
      (0 : Fin (2*(m+1)+1)) = s₀ := arbitrarySplitFiniteState_zero_eq_coalesced _ _ _ _
  rw [hstatezero] at hsource
  have hgamma (i : Fin (m+2)) : k.gamma i = w i := by
    simp [k, paperFixedBindingSplitRates, paperFixedBindingRates,
      relaxRates, edgeScaledRates, arbitrarySplitFiniteRates, realize]
  refine ⟨hsource.1, hsource.2.1, hsource.2.2.1, hsource.2.2.2, ?_, ?_⟩
  · intro i
    rw [hgamma]
    simp only [w, Fin.lastCases_castSucc]
    change (1/s₀.D i.castSucc)*s₀.D i.castSucc = 1
    exact div_mul_cancel₀ 1 (ne_of_gt (hsource.2.1.2.2.2.2 i.castSucc))
  · rw [hgamma]
    simp only [w, Fin.lastCases_last]
    change (t/s₀.D (Fin.last (m+1)))*s₀.D (Fin.last (m+1)) = t
    exact div_mul_cancel₀ t (ne_of_gt (hsource.2.1.2.2.2.2 (Fin.last (m+1))))

/-- A conservative natural-offset initialization satisfies all root
geometry inequalities by rational arithmetic. In particular it avoids
using a square-root comparison as a numerical check. -/
theorem orderedRationalNatGeometryAdmits_sound
    (m : ℕ) (r δ : ℚ) (h : orderedRationalNatGeometryAdmits m r δ = true) :
    (∀ j : Fin (2*(m+1)+1),
      1 < 3+δ*(j.val : ℚ) ∧ (3+δ*(j.val : ℚ))^2 < 1+8*r) ∧
    (∑ j : Fin (2*(m+1)+1), (3+δ*(j.val : ℚ))) < 4*r := by
  simp only [orderedRationalNatGeometryAdmits, decide_eq_true_eq] at h
  rcases h with ⟨hr, hδ, hsmall⟩
  let n : ℚ := (m+2 : ℕ)
  let L : ℚ := (2*(m+1)+1 : ℕ)
  have hn : 2 ≤ n := by dsimp [n]; exact_mod_cast (by omega : 2 ≤ m+2)
  have hL : L = 2*n-1 := by dsimp [n, L]; push_cast; ring
  have hLpos : 0 < L := by linarith
  have hsmall' : δ*n*L ≤ 1 := hsmall
  have hr' : 3*n/2 ≤ r := hr
  have hden : L-1 ≤ n*L := by
    have hp := mul_nonneg (by linarith : 0 ≤ n-1) hLpos.le
    nlinarith
  have hmax : δ*(L-1) ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hden hδ.le
    nlinarith
  have hjbound (j : Fin (2*(m+1)+1)) : (j.val : ℚ) ≤ L-1 := by
    dsimp [L]
    have hj : (j.val : ℚ)+1 ≤ ((2*(m+1)+1 : ℕ) : ℚ) := by
      exact_mod_cast (by omega : j.val+1 ≤ 2*(m+1)+1)
    linarith
  have hrootbounds (j : Fin (2*(m+1)+1)) :
      3 ≤ 3+δ*(j.val : ℚ) ∧ 3+δ*(j.val : ℚ) ≤ 4 := by
    have hj := hjbound j
    have hmul := mul_le_mul_of_nonneg_left hj hδ.le
    have hj0 : 0 ≤ (j.val : ℚ) := Nat.cast_nonneg _
    have hprod := mul_nonneg hδ.le hj0
    constructor <;> linarith
  constructor
  · intro j
    obtain ⟨hjlow, hjhigh⟩ := hrootbounds j
    constructor
    · linarith
    · have hsquare := mul_nonneg (sub_nonneg.mpr hjhigh) (by linarith : 0 ≤ 4+(3+δ*(j.val : ℚ)))
      nlinarith
  · have hindices : (∑ j : Fin (2*(m+1)+1), (j.val : ℚ)) ≤ L*(L-1) := by
      calc
        (∑ j : Fin (2*(m+1)+1), (j.val : ℚ)) ≤
            ∑ _j : Fin (2*(m+1)+1), (L-1) :=
          Finset.sum_le_sum (fun j _ => hjbound j)
        _ = L*(L-1) := by simp [L, nsmul_eq_mul]
    have hdeltaindices := mul_le_mul_of_nonneg_left hindices hδ.le
    have hcompare : L-1 ≤ 2*n := by linarith
    have hmult := mul_le_mul_of_nonneg_left hcompare (mul_pos hδ hLpos).le
    have hgeom : 3*L+δ*(∑ j : Fin (2*(m+1)+1), (j.val : ℚ)) < 4*r := by
      nlinarith
    simpa [Finset.sum_add_distrib, ← Finset.mul_sum, L, nsmul_eq_mul, mul_comm] using hgeom

/-- The admitted geometry is monotone under halving. -/
theorem orderedRationalNatGeometryAdmits_half
    (m : ℕ) (r δ : ℚ) (h : orderedRationalNatGeometryAdmits m r δ = true) :
    orderedRationalNatGeometryAdmits m r (δ/2) = true := by
  simp only [orderedRationalNatGeometryAdmits, decide_eq_true_eq] at h ⊢
  rcases h with ⟨hr, hδ, hsmall⟩
  refine ⟨hr, div_pos hδ (by norm_num), ?_⟩
  have heq : (δ/2)*((m+2 : ℕ) : ℚ)*((2*(m+1)+1 : ℕ) : ℚ) =
      (δ*((m+2 : ℕ) : ℚ)*((2*(m+1)+1 : ℕ) : ℚ))/2 := by ring
  rw [heq]
  linarith

/-- The conservative geometry guard has a dyadic initialization at every
adequate source value, and every subsequent halving remains in its domain. -/
theorem orderedRationalNatGeometryAdmits_dyadic_initialization
    (m : ℕ) (r : ℚ) (hr : (3*((m+2 : ℕ) : ℚ))/2 ≤ r) :
    ∃ d₀ : ℕ, ∀ b : ℕ,
      orderedRationalNatGeometryAdmits m r ((1/2 : ℚ)^(d₀+b)) = true := by
  let D : ℚ := ((m+2 : ℕ) : ℚ)*((2*(m+1)+1 : ℕ) : ℚ)
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨d₀, hd₀⟩ := exists_pow_lt_of_lt_one
    (div_pos (by norm_num : (0 : ℚ) < 1) hD) (by norm_num : (1/2 : ℚ) < 1)
  have hmul := mul_le_mul_of_nonneg_right hd₀.le hD.le
  have hcancel : (1/D)*D = 1 := div_mul_cancel₀ 1 (ne_of_gt hD)
  rw [hcancel] at hmul
  have hinit : orderedRationalNatGeometryAdmits m r ((1/2 : ℚ)^d₀) = true := by
    simp only [orderedRationalNatGeometryAdmits, decide_eq_true_eq]
    refine ⟨hr, pow_pos (by norm_num) _, ?_⟩
    simpa [D, mul_assoc] using hmul
  refine ⟨d₀, ?_⟩
  intro b
  induction b with
  | zero => simpa using hinit
  | succ b ih =>
    have hhalf := orderedRationalNatGeometryAdmits_half m r ((1/2 : ℚ)^(d₀+b)) ih
    have heq : (1/2 : ℚ)^(d₀+(b+1)) = ((1/2 : ℚ)^(d₀+b))/2 := by
      rw [show d₀+(b+1) = (d₀+b)+1 by omega, pow_succ]
      ring
    simpa only [heq] using hhalf

/-- Physical admission gives the exact whole positive equilibrium set,
for ordered rational offsets and the same frozen unit-current factors. -/
theorem orderedRationalSplitAdmits_exact_actual_family
    (m : ℕ) (ξ : ℕ → ℚ) (hξ : StrictMono ξ) (r δ ε : ℚ) (t : ℝ)
    (hprefix : orderedRationalPrefixAdmits m r = true) (ht : 0 < t)
    (hsplit : orderedRationalSplitAdmits m ξ r δ ε = true) :
    let s₀ := coalescedFiniteState (m+1) (r : ℝ)
    let θ : Fin (m+1) → ℝ := fun j => 1/s₀.D j.castSucc
    let τ := t/s₀.D (Fin.last (m+1))
    let k := paperFixedBindingSplitRates m (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ) (ε : ℝ)
      (Fin.lastCases (motive := fun _ => ℝ) τ θ)
    {s : State (m+2) | s.Positive ∧ Equilibrium k s ∧
      InClass (2*(r : ℝ)) 2 (2*((r : ℝ)+1)) s} =
      Set.range (arbitrarySplitFiniteState (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ)) := by
  have hx := orderedRationalPrefixAdmits_coalesced_positive m r hprefix
  obtain ⟨hr, hδ, hε, hε1, hroots, hd, hb⟩ :=
    (orderedRationalSplitAdmits_iff m ξ r δ ε).mp hsplit
  have hξR : StrictMono (fun j => (ξ j : ℝ)) := by
    intro i j hij
    exact (Rat.cast_lt (K := ℝ)).mpr (hξ hij)
  exact paperFixedBindingSplit_positive_equilibria_exact_family
    m (fun j => (ξ j : ℝ)) hξR (r : ℝ)
    (t/(coalescedFiniteState (m+1) (r : ℝ)).D (Fin.last (m+1)))
    (δ : ℝ) (ε : ℝ) (fun j => 1/(coalescedFiniteState (m+1) (r : ℝ)).D j.castSucc)
    hr (div_pos ht (hx.2.2.2.2 _))
    (fun j => div_pos (by norm_num) (hx.2.2.2.2 _)) hδ hε hε1 hd hb hroots

/-- Rationality of each physically admitted rational-offset first success
uses the very same source/current/distance/binding values. -/
theorem orderedRational_first_accepted_split_rational
    (m : ℕ) (ξ : ℕ → ℚ) (r t ε : ℚ) (spectral : ℕ → Bool) (d : ℕ)
    (hprefix : orderedRationalPrefixAdmits m r = true) (ht : 0 < t)
    (hfirst : FirstAcceptedIndex
      (fun b => orderedRationalSplitAdmits m ξ r ((1/2 : ℚ)^b) ε && spectral b) d) :
    let s₀ := coalescedFiniteState (m+1) (r : ℝ)
    let w  := Fin.lastCases (motive := fun _ => ℝ) ((t : ℝ)/s₀.D (Fin.last (m+1))) (fun j => 1/s₀.D j.castSucc)
    let δ : ℝ := ((1/2 : ℚ)^d : ℚ)
    let k := paperFixedBindingSplitRates m (fun j => (ξ j : ℝ)) (r : ℝ) δ (ε : ℝ) w
    k.Positive ∧ RationalRates k ∧
      ∀ j : Fin (2*(m+1)+1),
        (arbitrarySplitFiniteState (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) δ j).Positive ∧
        RationalState (arbitrarySplitFiniteState (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) δ j) ∧
        Equilibrium k (arbitrarySplitFiniteState (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) δ j) ∧
        InClass (2*(r : ℝ)) 2 (2*((r : ℝ)+1))
          (arbitrarySplitFiniteState (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) δ j) := by
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hphysical := orderedRational_first_accepted_split_physical
    m ξ r ε (t : ℝ) hprefix htR spectral d hfirst
  have hrRat : RationalReal (r : ℝ) := ⟨r, rfl⟩
  have htRat : RationalReal (t : ℝ) := ⟨t, rfl⟩
  have hδRat : RationalReal (((1/2 : ℚ)^d : ℚ) : ℝ) := ⟨(1/2 : ℚ)^d, rfl⟩
  have hεRat : RationalReal (ε : ℝ) := ⟨ε, rfl⟩
  let s₀ := coalescedFiniteState (m+1) (r : ℝ)
  let w : Fin (m+2) → ℝ := Fin.lastCases (motive := fun _ => ℝ)
    ((t : ℝ)/s₀.D (Fin.last (m+1))) (fun j => 1/s₀.D j.castSucc)
  have hs₀ := coalescedFiniteState_rational_of_rational_source m hrRat
  have hwRat (i : Fin (m+2)) : RationalReal (w i) := by
    cases i using Fin.lastCases with
    | last => simpa [w] using orderedRationalReal_div htRat (hs₀.2.2.2.2 (Fin.last (m+1)))
    | cast j => simpa [w] using orderedRationalReal_div (show RationalReal (1 : ℝ) from ⟨1, by norm_num⟩) (hs₀.2.2.2.2 j.castSucc)
  obtain ⟨hkRat, hstatesRat⟩ := paperFixedBindingSplit_rational_offsets
    m (fun j => (ξ j : ℝ)) w hrRat hδRat hεRat (fun j => ⟨ξ j, rfl⟩) hwRat
  refine ⟨?_, hkRat, ?_⟩
  · simpa using hphysical.1
  · intro j
    obtain ⟨hs, heq, hclass⟩ := hphysical.2 j
    exact ⟨by simpa using hs, hstatesRat j, by simpa using heq, by simpa using hclass⟩

/-- Physical admission closes all domain obligations in the literal
four-loop order. The remaining premises concern only the original finite
spectral tests, universally at every accepted predecessor. In particular,
no favorable existential quadruple or dovetailed search is substituted
for the manuscript's first-success algorithm. -/
theorem orderedRationalPhysicalDesign_first_acceptance
    (m : ℕ) (ξ : ℕ → ℚ) («prefix» : ℕ → Bool) (slow : ℕ → ℕ → Bool)
    (coalesced : ℕ → ℕ → ℕ → Bool)
    (split : ℕ → ℕ → ℕ → ℕ → Bool)
    (hprefix : ∀ᶠ a : ℕ in atTop, «prefix» a = true)
    (hslow : ∀ a, orderedRationalPhysicalPrefixTest m «prefix» a = true →
      ∃ b, slow a b = true)
    (hcoalesced : ∀ a b, orderedRationalPhysicalPrefixTest m «prefix» a = true →
      slow a b = true → ∃ c, coalesced a b c = true)
    (hsplit : ∀ a b c, orderedRationalPhysicalPrefixTest m «prefix» a = true →
      slow a b = true → coalesced a b c = true →
      ∀ᶠ d : ℕ in atTop, split a b c d = true) :
    ∃ a b c d, OrderedDesignAccepted
      (orderedRationalPhysicalPrefixTest m «prefix») slow coalesced
      (orderedRationalPhysicalSplitTest m ξ split) a b c d := by
  obtain ⟨a, ha⟩ := orderedRational_admitted_prefix_first_acceptance m «prefix» hprefix
  apply orderedDesign_first_acceptance
    (orderedRationalPhysicalPrefixTest m «prefix») slow coalesced
    (orderedRationalPhysicalSplitTest m ξ split)
    ⟨a, ha.1⟩ hslow hcoalesced
  intro a b c hp hs hc
  have hpAdmit := (Bool.and_eq_true_iff.mp hp).1
  obtain ⟨d, hd⟩ := orderedRational_admitted_split_first_acceptance
    m ξ ((2 : ℚ)^a) ((1/2 : ℚ)^c) hpAdmit
    (pow_pos (by norm_num) c)
    (pow_le_one₀ (by norm_num) (by norm_num))
    (split a b c) (hsplit a b c hp hs hc)
  exact ⟨d, hd.1⟩

/-- Every actual first-success result of the guarded ordered design has
positive rational rates, positive rational states, and exactly the
prescribed whole family at the common totals. The same earlier coalesced
state freezes unit «prefix» currents and final current t; no witness is
rechosen after the odd/even spectral test succeeds. -/
theorem orderedRationalPhysicalDesign_rational_exact_family
    (m : ℕ) (ξ : ℕ → ℚ) (hξ : StrictMono ξ)
    («prefix» : ℕ → Bool) (slow : ℕ → ℕ → Bool)
    (coalesced : ℕ → ℕ → ℕ → Bool)
    (split : ℕ → ℕ → ℕ → ℕ → Bool) (a b c d : ℕ)
    (haccepted : OrderedDesignAccepted
      (orderedRationalPhysicalPrefixTest m «prefix») slow coalesced
      (orderedRationalPhysicalSplitTest m ξ split) a b c d) :
    let r : ℝ := ((2 : ℚ)^a : ℚ)
    let t : ℝ := ((1/2 : ℚ)^b : ℚ)
    let ε : ℝ := ((1/2 : ℚ)^c : ℚ)
    let δ : ℝ := ((1/2 : ℚ)^d : ℚ)
    let s₀ := coalescedFiniteState (m+1) r
    let w  := Fin.lastCases (motive := fun _ => ℝ) (t/s₀.D (Fin.last (m+1))) (fun j => 1/s₀.D j.castSucc)
    let k := paperFixedBindingSplitRates m (fun j => (ξ j : ℝ)) r δ ε w
    (3*(m+2 : ℝ))/2 ≤ r ∧ k.Positive ∧ RationalRates k ∧
      (∀ j : Fin (2*(m+1)+1),
        (arbitrarySplitFiniteState (m+1) (fun j => (ξ j : ℝ)) r δ j).Positive ∧
        RationalState (arbitrarySplitFiniteState (m+1) (fun j => (ξ j : ℝ)) r δ j) ∧
        Equilibrium k (arbitrarySplitFiniteState (m+1) (fun j => (ξ j : ℝ)) r δ j) ∧
        InClass (2*r) 2 (2*(r+1))
          (arbitrarySplitFiniteState (m+1) (fun j => (ξ j : ℝ)) r δ j)) ∧
      {s : State (m+2) | s.Positive ∧ Equilibrium k s ∧ InClass (2*r) 2 (2*(r+1)) s} =
        Set.range (arbitrarySplitFiniteState (m+1) (fun j => (ξ j : ℝ)) r δ) := by
  have hp := (Bool.and_eq_true_iff.mp haccepted.1.1).1
  have hsplit := (Bool.and_eq_true_iff.mp haccepted.2.2.2.1).1
  have ht : 0 < (1/2 : ℚ)^b := pow_pos (by norm_num) b
  have hr := (orderedRationalPrefixAdmits_iff m ((2 : ℚ)^a)).mp hp
  have hphysical := orderedRational_first_accepted_split_rational
    m ξ ((2 : ℚ)^a) ((1/2 : ℚ)^b) ((1/2 : ℚ)^c)
    (split a b c) d hp ht haccepted.2.2.2
  have hfamily := orderedRationalSplitAdmits_exact_actual_family
    m ξ hξ
    ((2 : ℚ)^a) ((1/2 : ℚ)^d) ((1/2 : ℚ)^c) (((1/2 : ℚ)^b : ℚ) : ℝ)
    hp (by exact_mod_cast ht) hsplit
  exact ⟨hr.2.1, hphysical.1, hphysical.2.1, hphysical.2.2, hfamily⟩

end
end PhosphorylationStableCapacity
