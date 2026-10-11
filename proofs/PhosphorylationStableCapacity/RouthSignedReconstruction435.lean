module
public import proofs.PhosphorylationStableCapacity.RouthNeutralCheckerSoundness435
public import proofs.PhosphorylationStableCapacity.RouthPositiveRealRoot435
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial
open scoped Topology

noncomputable section

/-- Literal inverse Routh step at a fixed declared target degree. -/
def routhReconstruct (d : ℕ) (q : ℝ[X]) (c : ℝ) : ℝ[X] :=
  q + Polynomial.C c*Polynomial.X*routhSameParity (d-1) q

/-- A fixed-degree terminal-constant family, with the positive Routh
ratios held fixed and only the terminal linear constant varied. -/
def routhTerminalFamily (a : ℝ) : List ℝ → ℝ → ℝ[X]
  | [], lam => Polynomial.C a*Polynomial.X + Polynomial.C lam
  | c :: cs, lam => routhReconstruct (cs.length+2) (routhTerminalFamily a cs lam) c

theorem routhSameParity_coeff (d n : ℕ) (p : ℝ[X]) :
    (routhSameParity d p).coeff n =
      if d % 2 = n % 2 then p.coeff n else 0 := by
  simp only [routhSameParity, Polynomial.coeff_sub, routhOppositeParity_coeff]
  split_ifs <;> simp

theorem routhReconstruct_coeff_zero (d : ℕ) (q : ℝ[X]) (c : ℝ) :
    (routhReconstruct d q c).coeff 0 = q.coeff 0 := by
  simp [routhReconstruct, mul_assoc]

theorem routhReconstruct_coeff_succ (d n : ℕ) (q : ℝ[X]) (c : ℝ) :
    (routhReconstruct d q c).coeff (n+1) =
      q.coeff (n+1)+c*(if (d-1) % 2 = n % 2 then q.coeff n else 0) := by
  simp [routhReconstruct, mul_assoc, Polynomial.coeff_X_mul, routhSameParity_coeff]

theorem routhReconstruct_oppositeParity
    (d : ℕ) (hd : 0 < d) (q : ℝ[X]) (c : ℝ) :
    routhOppositeParity d (routhReconstruct d q c) = routhSameParity (d-1) q := by
  ext n
  rw [routhOppositeParity_coeff, routhSameParity_coeff]
  cases n with
  | zero =>
      rw [routhReconstruct_coeff_zero]
      by_cases heven : d % 2 = 0 % 2
      · have hnext : ¬ ((d-1) % 2 = 0 % 2) := by omega
        simp [heven, hnext]
      · have hnext : (d-1) % 2 = 0 % 2 := by omega
        simp [heven, hnext]
  | succ n =>
      rw [routhReconstruct_coeff_succ]
      by_cases heven : d % 2 = (n+1) % 2
      · have hnext : ¬ ((d-1) % 2 = (n+1) % 2) := by omega
        simp [heven, hnext]
      · have hnext : (d-1) % 2 = (n+1) % 2 := by omega
        have hprev : ¬ ((d-1) % 2 = n % 2) := by omega
        simp only [ite_eq_right heven, ite_eq_left hnext, ite_eq_right hprev,
          mul_zero, add_zero]

theorem routhReconstruct_homotopy_endpoint
    (d : ℕ) (hd : 0 < d) (q : ℝ[X]) (c : ℝ) :
    routhPolynomialHomotopy d (routhReconstruct d q c) c = q := by
  rw [routhPolynomialHomotopy, routhReconstruct_oppositeParity d hd q c,
    routhReconstruct]
  ring

theorem routhReconstruct_natDegree_le
    (d : ℕ) (hd : 0 < d) (q : ℝ[X]) (hdegree : q.natDegree = d-1) (c : ℝ) :
    (routhReconstruct d q c).natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
      rw [routhReconstruct_coeff_succ]
      have hN : q.coeff (n+1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have hnq : q.coeff n = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [hN, hnq]

theorem routhReconstruct_top_coeff
    (d : ℕ) (hd : 0 < d) (q : ℝ[X]) (hdegree : q.natDegree = d-1) (c : ℝ) :
    (routhReconstruct d q c).coeff d = c*q.leadingCoeff := by
  have hEq : d-1+1 = d := by omega
  have hzero : q.coeff d = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hlead : q.coeff (d-1) = q.leadingCoeff := by
    rw [← hdegree, Polynomial.coeff_natDegree]
  have h := routhReconstruct_coeff_succ d (d-1) q c
  simpa only [hEq, ite_true, hzero, zero_add, hlead] using h

theorem routhReconstruct_next_coeff
    (d : ℕ) (hd : 0 < d) (q : ℝ[X]) (hdegree : q.natDegree = d-1) (c : ℝ) :
    (routhReconstruct d q c).coeff (d-1) = q.leadingCoeff := by
  have hlead : q.coeff (d-1) = q.leadingCoeff := by
    rw [← hdegree, Polynomial.coeff_natDegree]
  by_cases hd1 : d = 1
  · subst d
    simpa only [Nat.sub_self, routhReconstruct_coeff_zero] using hlead
  · have hEq : d-2+1 = d-1 := by omega
    have hpar : ¬ ((d-1) % 2 = (d-2) % 2) := by omega
    have h := routhReconstruct_coeff_succ d (d-2) q c
    simpa only [hEq, ite_eq_right hpar, mul_zero, add_zero, hlead] using h

theorem routhReconstruct_degree_leading_pivot
    (d : ℕ) (hd : 0 < d) (q : ℝ[X]) (hdegree : q.natDegree = d-1)
    (hleading : 0 < q.leadingCoeff) (c : ℝ) (hc : 0 < c) :
    (routhReconstruct d q c).natDegree = d ∧
      (routhReconstruct d q c).leadingCoeff = c*q.leadingCoeff ∧
      routhDescendingCoeff d (routhReconstruct d q c) 1 = q.leadingCoeff := by
  have htop := routhReconstruct_top_coeff d hd q hdegree c
  have hdeg : (routhReconstruct d q c).natDegree = d :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (routhReconstruct_natDegree_le d hd q hdegree c)
      (by rw [htop]; exact (mul_pos hc hleading).ne')
  refine ⟨hdeg, ?_, ?_⟩
  · rw [← Polynomial.coeff_natDegree, hdeg, htop]
  · have hbound : (0 : ℤ) ≤ 1 ∧ (1 : ℤ) ≤ (d : ℤ) := by omega
    simp only [routhDescendingCoeff, ite_eq_left hbound]
    change (routhReconstruct d q c).coeff (d-1) = q.leadingCoeff
    exact routhReconstruct_next_coeff d hd q hdegree c

/-- Exact reconstruction followed by the actual finite reduction returns
the original polynomial, including the terminal degree-one case. -/
theorem routhReducedPolynomial_reconstruct
    (d : ℕ) (hd : 0 < d) (q : ℝ[X]) (hdegree : q.natDegree = d-1)
    (hleading : 0 < q.leadingCoeff) (c : ℝ) (hc : 0 < c) :
    routhReducedPolynomial d (routhReconstruct d q c) = q := by
  obtain ⟨hdegreeP, _hleadingP, hpivot⟩ :=
    routhReconstruct_degree_leading_pivot d hd q hdegree hleading c hc
  have hnonzero : routhDescendingCoeff d (routhReconstruct d q c) 1 ≠ 0 := by
    rw [hpivot]
    exact hleading.ne'
  have ha0 : routhDescendingCoeff d (routhReconstruct d q c) 0 = c*q.leadingCoeff := by
    simp [routhDescendingCoeff, routhReconstruct_top_coeff d hd q hdegree c]
  have hratio : routhDescendingCoeff d (routhReconstruct d q c) 0 /
      routhDescendingCoeff d (routhReconstruct d q c) 1 = c := by
    rw [ha0, hpivot]
    field_simp [hleading.ne']
  rw [routhReducedPolynomial_eq_homotopy d hd _ hdegreeP.le hnonzero, hratio]
  exact routhReconstruct_homotopy_endpoint d hd q c

/-- The exact actual reduction also reconstructs its input at its own
leading ratio. This direction does not assume a signed root criterion. -/
theorem routhReconstruct_reducedPolynomial
    (d : ℕ) (hd : 0 < d) (p : ℝ[X]) (hdegree : p.natDegree ≤ d)
    (hpivot : routhDescendingCoeff d p 1 ≠ 0) :
    routhReconstruct d (routhReducedPolynomial d p)
      (routhDescendingCoeff d p 0 / routhDescendingCoeff d p 1) = p := by
  let c := routhDescendingCoeff d p 0 / routhDescendingCoeff d p 1
  have hq : routhReducedPolynomial d p = routhPolynomialHomotopy d p c :=
    routhReducedPolynomial_eq_homotopy d hd p hdegree hpivot
  rw [routhReconstruct, hq, routhSameParity_next_homotopy d hd p c,
    routhPolynomialHomotopy]
  ring

/-- All proper Routh minors remain positive independently of the terminal
constant. Leading coefficient, declared degree and constant are exact. -/
theorem routhTerminalFamily_structure
    (a : ℝ) (ha : 0 < a) (cs : List ℝ) (hcs : ∀ c ∈ cs, 0 < c) (lam : ℝ) :
    (routhTerminalFamily a cs lam).natDegree = cs.length+1 ∧
      (routhTerminalFamily a cs lam).leadingCoeff = a*cs.prod ∧
      (routhTerminalFamily a cs lam).coeff 0 = lam ∧
      ∀ k : ℕ, k ≤ cs.length →
        0 < routhHurwitzMinor (cs.length+1) k (routhTerminalFamily a cs lam) := by
  induction cs with
  | nil =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [routhTerminalFamily, List.length_nil, Nat.zero_add] using
          (Polynomial.natDegree_linear (a := a) (b := lam) ha.ne')
      · simpa only [routhTerminalFamily, List.prod_nil, mul_one] using
          (Polynomial.leadingCoeff_linear (a := a) (b := lam) ha.ne')
      · simp [routhTerminalFamily]
      · intro k hk
        have hkzero : k = 0 := by simpa using hk
        subst k
        simp [routhHurwitzMinor]
  | cons c cs ih =>
      have hc : 0 < c := hcs c (by simp)
      have hrest : ∀ u ∈ cs, 0 < u := fun u hu => hcs u (by simp [hu])
      obtain ⟨hqdegree, hqleading, hqconstant, hqproper⟩ := ih hrest
      let q := routhTerminalFamily a cs lam
      have hqleadpos : 0 < q.leadingCoeff := by
        rw [hqleading]
        exact mul_pos ha (List.prod_pos hrest)
      have hdegree : q.natDegree = (cs.length+2)-1 := by
        change (routhTerminalFamily a cs lam).natDegree = (cs.length+2)-1
        omega
      obtain ⟨hPdegree, hPleading, hpivot⟩ := routhReconstruct_degree_leading_pivot
        (cs.length+2) (by omega) q hdegree hqleadpos c hc
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [routhTerminalFamily, List.length_cons, Nat.add_assoc] using hPdegree
      · change (routhReconstruct (cs.length+2) q c).leadingCoeff = a*(c::cs).prod
        rw [hPleading, hqleading, List.prod_cons]
        ring
      · simpa only [routhTerminalFamily, routhReconstruct_coeff_zero] using hqconstant
      · intro k hk
        cases k with
        | zero => simp [routhHurwitzMinor]
        | succ k =>
            have hpivotpos : 0 < routhDescendingCoeff (cs.length+2)
                (routhReconstruct (cs.length+2) q c) 1 := by
              rw [hpivot]
              exact hqleadpos
            change 0 < routhHurwitzMinor (cs.length+2) (k+1)
              (routhReconstruct (cs.length+2) q c)
            rw [routhHurwitzMinor_reduction (cs.length+2) (by omega) _ hpivotpos.ne' k,
              routhReducedPolynomial_reconstruct (cs.length+2) (by omega) q
                hdegree hqleadpos c hc, hpivot]
            apply mul_pos hqleadpos
            rw [show cs.length+2-1 = cs.length+1 by omega]
            exact hqproper k (by simpa only [List.length_cons] using Nat.le_of_succ_le_succ hk)

theorem routhTerminalFamily_coeff_continuous (a : ℝ) (cs : List ℝ) (i : ℕ) :
    Continuous (fun lam : ℝ => (routhTerminalFamily a cs lam).coeff i) := by
  induction cs generalizing i with
  | nil =>
      cases i with
      | zero =>
          simp only [routhTerminalFamily, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_zero, mul_zero,
            Polynomial.coeff_C_zero, zero_add]
          change Continuous (id : ℝ → ℝ)
          exact continuous_id
      | succ i =>
          simp only [routhTerminalFamily, Polynomial.coeff_add,
            Polynomial.coeff_C_succ, add_zero]
          exact continuous_const
  | cons c cs ih =>
      cases i with
      | zero =>
          simpa only [routhTerminalFamily, routhReconstruct_coeff_zero] using ih 0
      | succ i =>
          simp only [routhTerminalFamily, routhReconstruct_coeff_succ]
          split_ifs
          · exact (ih (i+1)).add (continuous_const.mul (ih i))
          · simpa only [mul_zero, add_zero] using ih (i+1)

/-- At terminal constant zero, the actual deflation has all positive
minors and positive leading coefficient. The zero root is therefore
simple and every complementary root is genuinely Hurwitz. -/
theorem routhTerminalFamily_zero_hurwitz_deflation
    (a : ℝ) (ha : 0 < a) (cs : List ℝ) (hcs : ∀ c ∈ cs, 0 < c) :
    0 < (routhTerminalFamily a cs 0).divX.leadingCoeff ∧
      0 < (routhTerminalFamily a cs 0).divX.coeff 0 ∧
      (∀ z : ℂ, (((routhTerminalFamily a cs 0).divX).map
        (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0) := by
  obtain ⟨hdegree, hleading, hconstant, hproper⟩ :=
    routhTerminalFamily_structure a ha cs hcs 0
  let p := routhTerminalFamily a cs 0
  let q := p.divX
  have hfactor : p = Polynomial.X*q := by
    have h := Polynomial.X_mul_divX_add p
    have hc : p.coeff 0 = 0 := hconstant
    simpa only [hc, Polynomial.C_0, add_zero, q] using h.symm
  have hqdegree : q.natDegree = cs.length := by
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hdegree]
    omega
  have hlead : 0 < p.leadingCoeff := by
    rw [hleading]
    exact mul_pos ha (List.prod_pos hcs)
  have hqlead : 0 < q.leadingCoeff := by
    have heq : p.leadingCoeff = q.leadingCoeff := by
      rw [hfactor, mul_comm, Polynomial.leadingCoeff_mul_X]
    rw [← heq]
    exact hlead
  have hqminors : ∀ k : ℕ, k ≤ q.natDegree →
      0 < routhHurwitzMinor q.natDegree k q := by
    intro k hk
    rw [hqdegree] at hk ⊢
    have h := hproper k hk
    change 0 < routhHurwitzMinor (cs.length+1) k p at h
    rw [hfactor, routhHurwitzMinor_X_mul] at h
    exact h
  have hstable := hurwitzPolynomial_of_all_routh_minors_positive q hqlead hqminors
  have hqconstant : 0 < q.coeff 0 := hurwitzPolynomial_constantCoeff_pos q hqlead hstable
  exact ⟨hqlead, hqconstant, hstable⟩

/-- A nonnegative inverse-Routh weight preserves a single ascending
coefficient sign transition; only the boundary coefficient can change cut. -/
theorem signedCoefficientTransition_reconstruct
    (d : ℕ) (q : ℝ[X]) (c : ℝ) (hc : 0 ≤ c)
    (cut : ℕ) (h : SignedCoefficientTransition q cut) :
    ∃ newCut : ℕ, SignedCoefficientTransition (routhReconstruct d q c) newCut := by
  obtain ⟨hcut, hconstant, hbelow, habove⟩ := h
  have hconstantP : (routhReconstruct d q c).coeff 0 < 0 := by
    rw [routhReconstruct_coeff_zero]
    exact hconstant
  have hbelowP (i : ℕ) (hi : i < cut) : (routhReconstruct d q c).coeff i ≤ 0 := by
    cases i with
    | zero => rw [routhReconstruct_coeff_zero]; exact hbelow 0 hi
    | succ i =>
        rw [routhReconstruct_coeff_succ]
        split_ifs
        · exact add_nonpos (hbelow (i+1) hi)
            (mul_nonpos_of_nonneg_of_nonpos hc (hbelow i (by omega)))
        · simpa only [mul_zero, add_zero] using hbelow (i+1) hi
  have haboveP (i : ℕ) (hi : cut+1 ≤ i) : 0 ≤ (routhReconstruct d q c).coeff i := by
    cases i with
    | zero => omega
    | succ i =>
        rw [routhReconstruct_coeff_succ]
        split_ifs
        · exact add_nonneg (habove (i+1) (by omega))
            (mul_nonneg hc (habove i (by omega)))
        · simpa only [mul_zero, add_zero] using habove (i+1) (by omega)
  by_cases hboundary : 0 ≤ (routhReconstruct d q c).coeff cut
  · refine ⟨cut, hcut, hconstantP, hbelowP, ?_⟩
    intro i hi
    by_cases heq : i = cut
    · simpa only [heq] using hboundary
    · exact haboveP i (by omega)
  · refine ⟨cut+1, by omega, hconstantP, ?_, haboveP⟩
    intro i hi
    by_cases heq : i = cut
    · rw [heq]
      exact (lt_of_not_ge hboundary).le
    · exact hbelowP i (by omega)

theorem routhTerminalFamily_signed_transition
    (a : ℝ) (ha : 0 < a) (cs : List ℝ) (hcs : ∀ c ∈ cs, 0 < c)
    (lam : ℝ) (hlam : lam < 0) :
    ∃ cut : ℕ, SignedCoefficientTransition (routhTerminalFamily a cs lam) cut := by
  induction cs with
  | nil =>
      refine ⟨1, by norm_num, ?_, ?_, ?_⟩
      · simpa [routhTerminalFamily] using hlam
      · intro i hi
        have hi0 : i = 0 := by omega
        subst i
        simpa [routhTerminalFamily] using hlam.le
      · intro i hi
        by_cases hi1 : i = 1
        · subst i
          simpa [routhTerminalFamily] using ha.le
        · have hi0 : i ≠ 0 := by omega
          simp [routhTerminalFamily, Polynomial.coeff_C, Polynomial.coeff_X, hi0, Ne.symm hi1]
  | cons c cs ih =>
      have hc : 0 < c := hcs c (by simp)
      have hrest : ∀ u ∈ cs, 0 < u := fun u hu => hcs u (by simp [hu])
      obtain ⟨cut, hcut⟩ := ih hrest
      exact signedCoefficientTransition_reconstruct (cs.length+2)
        (routhTerminalFamily a cs lam) c hc.le cut hcut

/-- Every terminal family excludes imaginary-axis roots when its actual
constant is nonzero. This algebraic boundary-root implication even permits
arbitrary real reconstruction weights; stability is not an input. -/
theorem routhTerminalFamily_no_imaginary_axis_roots
    (a : ℝ) (cs : List ℝ) (lam : ℝ) (hlam : lam ≠ 0)
    (z : ℂ) (hz : z.re = 0) :
    ((routhTerminalFamily a cs lam).map (algebraMap ℝ ℂ)).eval z ≠ 0 := by
  induction cs with
  | nil =>
      intro hroot
      have h := congrArg Complex.re hroot
      apply hlam
      simpa [routhTerminalFamily, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_X, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Complex.mul_re, hz] using h
  | cons c cs ih =>
      intro hroot
      have h := routhPolynomialHomotopy_imaginary_root_of_original
        (cs.length+2) (routhReconstruct (cs.length+2) (routhTerminalFamily a cs lam) c)
        c z hz hroot
      rw [routhReconstruct_homotopy_endpoint (cs.length+2) (by omega)
        (routhTerminalFamily a cs lam) c] at h
      exact ih h

/-- Every nonconstant positive-leading polynomial with positive proper
Hurwitz minors is an actual terminal-constant reconstruction family.
The terminal constant is exactly the original p(0), with common positive
ratios and degree retained throughout the entire reduction chain. -/
theorem routh_positive_proper_minors_terminal_decomposition
    (p : ℝ[X]) (hdegree : 0 < p.natDegree) (hleading : 0 < p.leadingCoeff)
    (hproper : ∀ k : Fin (p.natDegree-1),
      0 < routhHurwitzMinor p.natDegree (k.val+1) p) :
    ∃ a : ℝ, ∃ cs : List ℝ, 0 < a ∧ (∀ c ∈ cs, 0 < c) ∧
      cs.length+1 = p.natDegree ∧ routhTerminalFamily a cs (p.coeff 0) = p := by
  have hproperNat : ∀ k : ℕ, k < p.natDegree →
      0 < routhHurwitzMinor p.natDegree k p := by
    intro k hk
    cases k with
    | zero => simp [routhHurwitzMinor]
    | succ k => exact hproper ⟨k, by omega⟩
  suffices h : ∀ d : ℕ, 0 < d → ∀ q : ℝ[X], q.natDegree = d →
      0 < q.leadingCoeff →
      (∀ k : ℕ, k < d → 0 < routhHurwitzMinor d k q) →
      ∃ a : ℝ, ∃ cs : List ℝ, 0 < a ∧ (∀ c ∈ cs, 0 < c) ∧
        cs.length+1 = d ∧ routhTerminalFamily a cs (q.coeff 0) = q from
    h p.natDegree hdegree p rfl hleading hproperNat
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
      intro hd p hdegree hlead hproper
      by_cases hd1 : d = 1
      · have hpdegree : p.natDegree = 1 := hdegree.trans hd1
        refine ⟨p.leadingCoeff, [], hlead, by simp, ?_, ?_⟩
        · simpa only [List.length_nil, Nat.zero_add] using hd1.symm
        · have hp := Polynomial.eq_X_add_C_of_natDegree_le_one hpdegree.le
          have hcoeff : p.coeff 1 = p.leadingCoeff := by
            rw [← hpdegree, Polynomial.coeff_natDegree]
          rw [hcoeff] at hp
          simpa only [routhTerminalFamily] using hp.symm
      · have hd2 : 2 ≤ d := by omega
        have hpivot : 0 < routhDescendingCoeff d p 1 := by
          have hfirst := hproper 1 (by omega)
          simpa [routhHurwitzMinor, Matrix.det_fin_one, routhHurwitzMatrix] using hfirst
        let q := routhReducedPolynomial d p
        have hqdegree : q.natDegree = d-1 :=
          routhReducedPolynomial_natDegree d hd p hpivot.ne'
        have hqleading : 0 < q.leadingCoeff := by
          rw [routhReducedPolynomial_leadingCoeff d hd p hpivot.ne']
          exact hpivot
        have hqproper : ∀ k : ℕ, k < d-1 → 0 < routhHurwitzMinor (d-1) k q := by
          intro k hk
          have hparent := hproper (k+1) (by omega)
          rw [routhHurwitzMinor_reduction d hd p hpivot.ne' k] at hparent
          exact (mul_pos_iff_of_pos_left hpivot).mp hparent
        obtain ⟨a, cs, ha, hcs, hlength, hfamily⟩ :=
          ih (d-1) (by omega) (by omega) q hqdegree hqleading hqproper
        let c := routhDescendingCoeff d p 0 / routhDescendingCoeff d p 1
        have ha0 : 0 < routhDescendingCoeff d p 0 := by
          have heq : routhDescendingCoeff d p 0 = p.leadingCoeff := by
            simp [routhDescendingCoeff, Polynomial.leadingCoeff, hdegree]
          rw [heq]
          exact hlead
        have hc : 0 < c := div_pos ha0 hpivot
        have hqhom : q = routhPolynomialHomotopy d p c :=
          routhReducedPolynomial_eq_homotopy d hd p hdegree.le hpivot.ne'
        have hqconstant : q.coeff 0 = p.coeff 0 := by
          rw [hqhom]
          exact routhPolynomialHomotopy_coeff_zero d p c
        refine ⟨a, c::cs, ha, ?_, ?_, ?_⟩
        · intro u hu
          rcases List.mem_cons.mp hu with heq | hu
          · simpa only [heq] using hc
          · exact hcs u hu
        · simp only [List.length_cons]
          omega
        · change routhReconstruct (cs.length+2) (routhTerminalFamily a cs (p.coeff 0)) c = p
          have hD : cs.length+2 = d := by omega
          rw [hD, ← hqconstant, hfamily]
          exact routhReconstruct_reducedPolynomial d hd p hdegree.le hpivot.ne'

theorem routh_proper_minors_no_imaginary_axis_roots
    (p : ℝ[X]) (hdegree : 0 < p.natDegree) (hleading : 0 < p.leadingCoeff)
    (hproper : ∀ k : Fin (p.natDegree-1),
      0 < routhHurwitzMinor p.natDegree (k.val+1) p)
    (hconstant : p.coeff 0 ≠ 0) (z : ℂ) (hz : z.re = 0) :
    (p.map (algebraMap ℝ ℂ)).eval z ≠ 0 := by
  obtain ⟨a, cs, _ha, _hcs, _hlength, hfamily⟩ :=
    routh_positive_proper_minors_terminal_decomposition p hdegree hleading hproper
  rw [← hfamily]
  exact routhTerminalFamily_no_imaginary_axis_roots a cs (p.coeff 0) hconstant z hz

end
end PhosphorylationStableCapacity
