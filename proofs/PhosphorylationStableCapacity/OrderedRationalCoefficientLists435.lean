module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingOrderedAdmissibility435
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity
open Polynomial
open scoped BigOperators

/-- Padded ascending coefficient access; no Polynomial operation occurs in this producer. -/
def orderedListCoeff (l : List ℚ) (i : ℕ) : ℚ := l.getD i 0

def orderedListShiftCoeff (l : List ℚ) (i : ℕ) : ℚ :=
  if i = 0 then 0 else orderedListCoeff l (i-1)

def orderedListNextN (n : ℕ) (a b : ℚ) (p q : List ℚ) : List ℚ :=
  List.ofFn fun i : Fin (n+2) =>
    (a+1)*(b+1)*orderedListCoeff p i.val +
      8*orderedListShiftCoeff p i.val + 2*(a+b)*orderedListCoeff q i.val

def orderedListNextJ (n : ℕ) (a b : ℚ) (p q : List ℚ) : List ℚ :=
  List.ofFn fun i : Fin (n+2) =>
    (a-1)*(b-1)*orderedListCoeff q i.val +
      8*orderedListShiftCoeff q i.val + 4*(a+b)*orderedListShiftCoeff p i.val

/-- The actual finite recurrence, including the constant base pair. -/
def orderedListPair : ℕ → (ℕ → ℚ) → ℚ → List ℚ × List ℚ
  | 0, ξ, δ => ([1], [(3+δ*ξ 0-1)/2])
  | n+1, ξ, δ =>
      let pq := orderedListPair n ξ δ
      (orderedListNextN n (3+δ*ξ (2*n+1)) (3+δ*ξ (2*n+2)) pq.1 pq.2,
       orderedListNextJ n (3+δ*ξ (2*n+1)) (3+δ*ξ (2*n+2)) pq.1 pq.2)

/-- Horner evaluation of ascending coefficients. -/
def orderedListHorner (l : List ℚ) (r : ℚ) : ℚ :=
  l.foldr (fun c b => c+r*b) 0

/-- The fixed-length synthetic-division formula, valid also when r=0. -/
def orderedListRawD (n : ℕ) (ξ : ℕ → ℚ) (r δ : ℚ) : List ℚ :=
  let pq := orderedListPair n ξ δ
  let pr := orderedListHorner pq.1 r
  let qr := orderedListHorner pq.2 r
  List.ofFn fun i : Fin (n+1) =>
    4 * ∑ j ∈ Finset.Icc (i.val+1) (n+1),
      r^(j-(i.val+1)) *
        (qr*orderedListShiftCoeff pq.1 j-r*pr*orderedListCoeff pq.2 j)

def orderedListRawB (n : ℕ) (ξ : ℕ → ℚ) (r δ : ℚ) : List ℚ :=
  let pq := orderedListPair n ξ δ
  let pr := orderedListHorner pq.1 r
  let qr := orderedListHorner pq.2 r
  let d := orderedListRawD n ξ r δ
  List.ofFn fun i : Fin (n+1) =>
    r*orderedListCoeff d i.val + (4*r*pr-2*qr)*orderedListCoeff pq.1 i.val -
      2*qr*orderedListCoeff pq.2 i.val

def orderedListDenseAccepts (l : List ℚ) : Bool :=
  l.all (fun c => decide (0 < c))

def orderedListPrefixAdmits (m : ℕ) (r : ℚ) : Bool :=
  (decide (1 < r ∧ (3*((m+2 : ℕ) : ℚ))/2 ≤ r) &&
    orderedListDenseAccepts (orderedListRawD (m+1) (fun j => (j : ℚ)) r 0)) &&
    orderedListDenseAccepts (orderedListRawB (m+1) (fun j => (j : ℚ)) r 0)

def orderedListSplitAdmits (m : ℕ) (ξ : ℕ → ℚ) (r δ ε : ℚ) : Bool :=
  (decide (0 < r ∧ 0 < δ ∧ 0 < ε ∧ ε ≤ 1 ∧
    ∀ j : Fin (2*(m+1)+1), 1 < 3+δ*ξ j.val) &&
    orderedListDenseAccepts (orderedListRawD (m+1) ξ r δ)) &&
    orderedListDenseAccepts (orderedListRawB (m+1) ξ r δ)

noncomputable section

/-- Complete coefficient correspondence includes the padded zero tail. -/
def OrderedListRepresents (n : ℕ) (l : List ℚ) (p : ℚ[X]) : Prop :=
  l.length = n+1 ∧ ∀ i, orderedListCoeff l i = p.coeff i

private theorem orderedListCoeff_ofFn {N : ℕ} (f : Fin N → ℚ) (i : ℕ) :
    orderedListCoeff (List.ofFn f) i = if h : i < N then f ⟨i,h⟩ else 0 := by
  by_cases hi : i < N <;>
    simp [orderedListCoeff, List.getD_eq_getElem?_getD, hi]

private theorem orderedListCoeff_outside (l : List ℚ) (i : ℕ) (hi : l.length ≤ i) :
    orderedListCoeff l i = 0 :=
  List.getD_eq_default l 0 hi

theorem OrderedListRepresents.degree_le {n : ℕ} {l : List ℚ} {p : ℚ[X]}
    (h : OrderedListRepresents n l p) : p.natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [← h.2 i]
  exact orderedListCoeff_outside l i (by rw [h.1]; omega)

private theorem orderedListRepresents_ofFn {n : ℕ} (f : Fin (n+1) → ℚ) (p : ℚ[X])
    (hdegree : p.natDegree ≤ n) (hcoeff : ∀ i, f i = p.coeff i.val) :
    OrderedListRepresents n (List.ofFn f) p := by
  refine ⟨List.length_ofFn, ?_⟩
  intro i
  rw [orderedListCoeff_ofFn]
  split_ifs with hi
  · exact hcoeff ⟨i,hi⟩
  · symm
    exact coeff_eq_zero_of_natDegree_lt (by omega)

private theorem orderedListShiftCoeff_correct {n : ℕ} {l : List ℚ} {p : ℚ[X]}
    (h : OrderedListRepresents n l p) (i : ℕ) :
    orderedListShiftCoeff l i = (X*p).coeff i := by
  cases i with
  | zero => simp [orderedListShiftCoeff]
  | succ i => simpa [orderedListShiftCoeff] using h.2 i

private theorem orderedListNext_correct {n : ℕ} {l k : List ℚ} {p q : ℚ[X]}
    (hp : OrderedListRepresents n l p) (hq : OrderedListRepresents n k q) (a b : ℚ) :
    OrderedListRepresents (n+1) (orderedListNextN n a b l k) (orderedRationalNextN a b p q) ∧
    OrderedListRepresents (n+1) (orderedListNextJ n a b l k) (orderedRationalNextJ a b p q) := by
  have hzero (i : ℕ) (hi : n < i) : p.coeff i = 0 ∧ q.coeff i = 0 :=
    ⟨coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp.degree_le hi),
     coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq.degree_le hi)⟩
  have hdegreeN : (orderedRationalNextN a b p q).natDegree ≤ n+1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    cases i with
    | zero => omega
    | succ i =>
      have hz := hzero i (by omega)
      have hz' := hzero (i+1) (by omega)
      simp only [orderedRationalNextN, coeff_add, coeff_C_mul, coeff_X_mul,
        hz.1, hz'.1, hz'.2, mul_zero, add_zero]
  have hdegreeJ : (orderedRationalNextJ a b p q).natDegree ≤ n+1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    cases i with
    | zero => omega
    | succ i =>
      have hz := hzero i (by omega)
      have hz' := hzero (i+1) (by omega)
      simp only [orderedRationalNextJ, coeff_add, coeff_C_mul, coeff_X_mul,
        hz.1, hz.2, hz'.2, mul_zero, add_zero]
  constructor
  · apply orderedListRepresents_ofFn _ _ hdegreeN
    intro i
    simp only [orderedRationalNextN, coeff_add, coeff_C_mul,
      hp.2, hq.2, orderedListShiftCoeff_correct hp]
  · apply orderedListRepresents_ofFn _ _ hdegreeJ
    intro i
    simp only [orderedRationalNextJ, coeff_add, coeff_C_mul,
      hq.2, orderedListShiftCoeff_correct hp, orderedListShiftCoeff_correct hq]

/-- One structural induction proves every degree and every rational input. -/
theorem orderedListPair_correct (n : ℕ) (ξ : ℕ → ℚ) (δ : ℚ) :
    OrderedListRepresents n (orderedListPair n ξ δ).1 (orderedRationalPair n ξ δ).1 ∧
    OrderedListRepresents n (orderedListPair n ξ δ).2 (orderedRationalPair n ξ δ).2 := by
  induction n with
  | zero =>
    constructor
    · refine ⟨rfl, ?_⟩
      intro i
      cases i <;> simp [orderedListPair, orderedRationalPair, orderedListCoeff, coeff_one]
    · refine ⟨rfl, ?_⟩
      intro i
      cases i <;> simp [orderedListPair, orderedRationalPair, orderedListCoeff]
  | succ n ih =>
    exact orderedListNext_correct ih.1 ih.2 _ _

private def orderedListPolynomial : List ℚ → ℚ[X]
  | [] => 0
  | c::l => C c+X*orderedListPolynomial l

private theorem orderedListPolynomial_coeff (l : List ℚ) (i : ℕ) :
    (orderedListPolynomial l).coeff i = orderedListCoeff l i := by
  induction l generalizing i with
  | nil => simp [orderedListPolynomial, orderedListCoeff]
  | cons c l ih =>
    cases i with
    | zero => simp [orderedListPolynomial, orderedListCoeff]
    | succ i => simp [orderedListPolynomial, orderedListCoeff, coeff_X_mul, ih]

private theorem orderedListPolynomial_eval (l : List ℚ) (r : ℚ) :
    (orderedListPolynomial l).eval r = orderedListHorner l r := by
  induction l with
  | nil => simp [orderedListPolynomial, orderedListHorner]
  | cons c l ih => simp [orderedListPolynomial, orderedListHorner, ih]

theorem OrderedListRepresents.horner_eq {n : ℕ} {l : List ℚ} {p : ℚ[X]}
    (h : OrderedListRepresents n l p) (r : ℚ) : orderedListHorner l r = p.eval r := by
  have heq : orderedListPolynomial l = p := by
    ext i
    rw [orderedListPolynomial_coeff, h.2 i]
  rw [← orderedListPolynomial_eval, heq]

private theorem ordered_bounded_divByMonic_coeff (p : ℚ[X]) (r : ℚ) (n i : ℕ)
    (hdegree : p.natDegree ≤ n+1) :
    (p /ₘ (X-C r)).coeff i =
      ∑ j ∈ Finset.Icc (i+1) (n+1), r^(j-(i+1))*p.coeff j := by
  rw [coeff_divByMonic_X_sub_C]
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro j hj hjnot
    have hjdegree : p.natDegree < j := by
      simp only [Finset.mem_Icc] at hj hjnot
      omega
    rw [coeff_eq_zero_of_natDegree_lt hjdegree, mul_zero]

private theorem ordered_conversion_numerator_degree (p q : ℚ[X]) (r : ℚ) (n : ℕ)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (C (q.eval r)*(X*p)-C (r*p.eval r)*q).natDegree ≤ n+1 := by
  have hxp : (X*p).natDegree ≤ n+1 :=
    natDegree_mul_le.trans (by rw [natDegree_X]; omega)
  exact (natDegree_sub_le _ _).trans
    (max_le ((natDegree_C_mul_le _ _).trans hxp)
      ((natDegree_C_mul_le _ _).trans (by omega)))

/-- Synthetic division is correct without dividing by r, including r=0. -/
theorem orderedListRawD_correct (n : ℕ) (ξ : ℕ → ℚ) (r δ : ℚ) :
    OrderedListRepresents n (orderedListRawD n ξ r δ) (orderedRationalRawD n ξ r δ) := by
  obtain ⟨hp,hq⟩ := orderedListPair_correct n ξ δ
  have hnum := ordered_conversion_numerator_degree _ _ r n hp.degree_le hq.degree_le
  have hdegree : (orderedRationalRawD n ξ r δ).natDegree ≤ n := by
    dsimp only [orderedRationalRawD]
    apply (natDegree_C_mul_le _ _).trans
    rw [natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C]
    omega
  apply orderedListRepresents_ofFn _ _ hdegree
  intro i
  rw [hp.horner_eq, hq.horner_eq]
  dsimp only [orderedRationalRawD]
  rw [coeff_C_mul, ordered_bounded_divByMonic_coeff _ r n i.val hnum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [orderedListShiftCoeff_correct hp, hq.2]
  simp only [coeff_sub, coeff_C_mul]

/-- B is computed at the same source, distance, pair and D coefficients. -/
theorem orderedListRawB_correct (n : ℕ) (ξ : ℕ → ℚ) (r δ : ℚ) :
    OrderedListRepresents n (orderedListRawB n ξ r δ) (orderedRationalRawB n ξ r δ) := by
  obtain ⟨hp,hq⟩ := orderedListPair_correct n ξ δ
  have hd := orderedListRawD_correct n ξ r δ
  have hdegree : (orderedRationalRawB n ξ r δ).natDegree ≤ n := by
    dsimp only [orderedRationalRawB]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · apply (natDegree_add_le _ _).trans
      exact max_le ((natDegree_C_mul_le _ _).trans hd.degree_le)
        ((natDegree_C_mul_le _ _).trans hp.degree_le)
    · exact (natDegree_C_mul_le _ _).trans hq.degree_le
  apply orderedListRepresents_ofFn _ _ hdegree
  intro i
  rw [hp.horner_eq, hq.horner_eq, hd.2, hp.2, hq.2]
  simp only [orderedRationalRawB, coeff_sub, coeff_add, coeff_C_mul]

/-- The finite list fold agrees with the exact semantic degree/support guard. -/
theorem orderedListDenseAccepts_eq {n : ℕ} {l : List ℚ} {p : ℚ[X]}
    (h : OrderedListRepresents n l p) :
    orderedListDenseAccepts l = orderedRationalDenseAccepts n p := by
  apply Bool.eq_iff_iff.mpr
  simp only [orderedListDenseAccepts, List.all_eq_true, decide_eq_true_eq,
    orderedRationalDenseAccepts]
  constructor
  · intro hall
    refine ⟨?_, h.degree_le⟩
    intro i
    rw [← h.2 i.val]
    have hi : i.val < l.length := by rw [h.1]; exact i.is_lt
    have hmem : orderedListCoeff l i.val ∈ l := by
      unfold orderedListCoeff
      rw [List.getD_eq_getElem l 0 hi]
      exact List.getElem_mem hi
    exact hall _ hmem
  · rintro ⟨hpos,_⟩ c hc
    obtain ⟨i,hi,hc⟩ := List.mem_iff_getElem.mp hc
    have hi' : i < n+1 := by simpa only [h.1] using hi
    have hp := hpos ⟨i,hi'⟩
    simpa only [← h.2 i, orderedListCoeff, List.getD_eq_getElem l 0 hi, hc] using hp

theorem orderedListPrefixAdmits_eq (m : ℕ) (r : ℚ) :
    orderedListPrefixAdmits m r = orderedRationalPrefixAdmits m r := by
  rw [orderedListPrefixAdmits, orderedRationalPrefixAdmits,
    orderedListDenseAccepts_eq (orderedListRawD_correct _ _ _ _),
    orderedListDenseAccepts_eq (orderedListRawB_correct _ _ _ _)]

theorem orderedListSplitAdmits_eq (m : ℕ) (ξ : ℕ → ℚ) (r δ ε : ℚ) :
    orderedListSplitAdmits m ξ r δ ε = orderedRationalSplitAdmits m ξ r δ ε := by
  rw [orderedListSplitAdmits, orderedRationalSplitAdmits,
    orderedListDenseAccepts_eq (orderedListRawD_correct _ _ _ _),
    orderedListDenseAccepts_eq (orderedListRawB_correct _ _ _ _)]

end
end PhosphorylationStableCapacity
