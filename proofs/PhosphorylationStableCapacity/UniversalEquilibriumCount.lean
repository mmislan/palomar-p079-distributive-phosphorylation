module
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.FieldTheory.Separable
public import proofs.PhosphorylationStableCapacity.GeneralEquilibriumBudget
public import proofs.PhosphorylationStableCapacity.RatioResidualSignedCount
public import proofs.PhosphorylationStableCapacity.RatioResidualBijection
public import proofs.PhosphorylationStableCapacity.RatioResidualRootBudget
public import proofs.PhosphorylationStableCapacity.BaseCase

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Polynomial Filter
open scoped Topology

/-- On the positive equilibrium curve, the universal polynomial
eliminant is the exact smooth enzyme residual times an algebraic
factor. The substrate-total equation is the only input. -/
private theorem equilibrium_eliminant_ratio_residual_factor {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST u : ℝ) (hST : 0 < ST) (hu : 0 < u) :
    let s := modelRatioSubstrateLevel k FT ST u
    let T := freeSubstrateInventory k u
    let B := kinaseComplexInventory k u
    let D := phosphataseComplexInventory k u
    let A := ET-FT*u
    let Q := FT*B-ET*D
    (equilibriumEliminationPoly k ET FT ST).eval u =
      ratioEnzymeResidual k ET FT ST u *
        (T*(Q+A*D)+FT*(B+D)*Q-(ST-s*T)*Q*D) := by
  dsimp only
  let s := modelRatioSubstrateLevel k FT ST u
  let T := freeSubstrateInventory k u
  let B := kinaseComplexInventory k u
  let D := phosphataseComplexInventory k u
  let A := ET-FT*u
  let Q := FT*B-ET*D
  have hs := (modelRatioSubstrateLevel_pos_and_inventory
    hn k hk FT ST u hST hu).2
  have hD : 0 < D := phosphataseComplexInventory_pos k hk hu hn
  have hsp : 0 < s := (modelRatioSubstrateLevel_pos_and_inventory
    hn k hk FT ST u hST hu).1
  have hden : 1+s*D ≠ 0 :=
    ne_of_gt (by nlinarith [mul_pos hsp hD])
  have hsub : (ST-s*T)*(1+s*D)-FT*s*(B+D)=0 := by
    change s*T+(FT*(B+D))*(s/(1+D*s))=ST at hs
    have hden' : 1+D*s ≠ 0 := by simpa [mul_comm] using hden
    have h := congrArg (fun z : ℝ => z*(1+D*s)) hs
    field_simp [hden'] at h
    nlinarith [h]
  have hres : ratioEnzymeResidual k ET FT ST u = s*Q-A := by
    simp only [ratioEnzymeResidual]
    dsimp [Q, A, s, B, D]
    ring
  rw [equilibriumEliminationPoly_eval, hres]
  change ST*Q*(Q+A*D)-A*T*(Q+A*D)-FT*A*(B+D)*Q =
    (s*Q-A)*(T*(Q+A*D)+FT*(B+D)*Q-(ST-s*T)*Q*D)
  linear_combination Q^2 * hsub

private def eliminantRatioFactor {n : ℕ} (k : Rates n)
    (ET FT ST u : ℝ) : ℝ :=
  let s := modelRatioSubstrateLevel k FT ST u
  let T := freeSubstrateInventory k u
  let B := kinaseComplexInventory k u
  let D := phosphataseComplexInventory k u
  let A := ET-FT*u
  let Q := FT*B-ET*D
  T*(Q+A*D)+FT*(B+D)*Q-(ST-s*T)*Q*D

private theorem eliminantRatioFactor_differentiableAt {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST u : ℝ) (hST : 0 < ST) (hu : 0 < u) :
    DifferentiableAt ℝ (eliminantRatioFactor k ET FT ST) u := by
  have hs := modelRatioSubstrateLevel_differentiableAt
    hn k hk FT ST u hST hu
  unfold eliminantRatioFactor freeSubstrateInventory
    kinaseComplexInventory phosphataseComplexInventory
  fun_prop

private theorem eliminant_simple_implies_residual_simple {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST u : ℝ) (hST : 0 < ST) (hu : 0 < u)
    (hroot : ratioEnzymeResidual k ET FT ST u = 0)
    (hsimple : ((equilibriumEliminationPoly k ET FT ST).derivative).eval u ≠ 0) :
    deriv (ratioEnzymeResidual k ET FT ST) u ≠ 0 := by
  let P := equilibriumEliminationPoly k ET FT ST
  let R := ratioEnzymeResidual k ET FT ST
  let G := eliminantRatioFactor k ET FT ST
  have hEq : (fun v : ℝ => P.eval v) =ᶠ[𝓝 u] R*G := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    simpa only [P, R, G, Pi.mul_apply, eliminantRatioFactor] using
      equilibrium_eliminant_ratio_residual_factor hn k hk ET FT ST v hST hv
  have hRdiff : DifferentiableAt ℝ R u :=
    ratioEnzymeResidual_differentiableAt hn k hk ET FT ST u hST hu
  have hGdiff : DifferentiableAt ℝ G u :=
    eliminantRatioFactor_differentiableAt hn k hk ET FT ST u hST hu
  have hder : P.derivative.eval u = deriv (R*G) u := by
    rw [← Polynomial.deriv]
    exact hEq.deriv_eq
  rw [deriv_mul hRdiff hGdiff] at hder
  have hRu : R u = 0 := hroot
  rw [hRu, zero_mul, add_zero] at hder
  intro hRzero
  rw [hRzero, zero_mul] at hder
  exact hsimple hder

/-- The published equilibrium ceiling follows internally from the
literal eliminant, its forced nonpositive roots, and the odd signed
crossing number of the exact positive-ratio chart. -/
theorem positive_equilibria_finite_and_ncard_le_two_n_sub_one {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST : ℝ) (hET : 0 < ET) (hFT : 0 < FT)
    (hST : 0 < ST) :
    let E : Set (State n) :=
      {x | x.Positive ∧ Equilibrium k x ∧ InClass ET FT ST x}
    E.Finite ∧ E.ncard ≤ 2*n-1 := by
  classical
  let E : Set (State n) :=
    {x | x.Positive ∧ Equilibrium k x ∧ InClass ET FT ST x}
  let R : Set ℝ :=
    {u | 0 < u ∧ ratioEnzymeResidual k ET FT ST u = 0}
  let P := equilibriumEliminationPoly k ET FT ST
  obtain ⟨hEfin, hEle⟩ := positive_equilibria_finite_and_ncard_le_two_n
    k hn hk ET FT ST hET hFT
  change E.Finite at hEfin
  change E.ncard ≤ 2*n at hEle
  refine ⟨hEfin, ?_⟩
  by_contra hbad
  change ¬ E.ncard ≤ 2*n-1 at hbad
  have hEcard : E.ncard = 2*n := by omega
  have hRfin : R.Finite :=
    (positive_ratio_residual_roots_finite_and_ncard_le_two_n
      hn k hk ET FT ST hET hFT hST).1
  have hbij : Set.BijOn (fun x : State n => x.E/x.F) E R :=
    positive_equilibria_bijOn_ratio_residual_roots
      hn k hk ET FT ST hFT hST
  have hRcard : R.ncard = 2*n := hbij.ncard_eq.symm.trans hEcard
  let roots : Finset ℝ := P.roots.toFinset
  have hPne : P ≠ 0 := by
    intro hzero
    have hcoeff := equilibriumEliminationPoly_coeff_one_neg
      k hn hk ET FT ST hET hFT
    change P.coeff 1 < 0 at hcoeff
    rw [hzero, coeff_zero] at hcoeff
    linarith
  have hroot (u : ℝ) (hu : P.eval u = 0) : u ∈ roots := by
    change u ∈ P.roots.toFinset
    rw [Multiset.mem_toFinset, mem_roots hPne]
    exact hu
  have hRroot : ∀ u ∈ R, u ∈ roots := by
    intro u hu
    obtain ⟨x, hx, heq, hclass, hratio⟩ :=
      positive_ratioEnzymeResidual_root_realizes_equilibrium
        hn k hk ET FT ST u hFT hST hu.1 hu.2
    apply hroot
    change (equilibriumEliminationPoly k ET FT ST).eval u = 0
    rw [← hratio, equilibriumEliminationPoly_eval]
    rw [← hclass.1, ← hclass.2.1, ← hclass.2.2]
    exact equilibrium_elimination_residual_zero k x hk hx heq
  obtain ⟨negative, hnegative, hnegativeRoot⟩ :=
    equilibriumEliminationPoly_negative_root
      k hn hk ET FT ST hET hFT
  let extras : Finset ℝ := {0, negative}
  have hExtrasCard : extras.card = 2 := by
    have hne : (0 : ℝ) ≠ negative := Ne.symm (ne_of_lt hnegative)
    simp [extras, hne]
  have hExtrasSub : extras ⊆ roots := by
    intro u hu
    simp only [extras, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hroot 0 (equilibriumEliminationPoly_zero_root k ET FT ST)
    · exact hroot _ hnegativeRoot
  let Rfin : Finset ℝ := hRfin.toFinset
  have hRfinCard : Rfin.card = 2*n := by
    simpa only [Rfin, Set.ncard_eq_toFinset_card R hRfin] using hRcard
  have hRfinSub : Rfin ⊆ roots := by
    intro u hu
    exact hRroot u (hRfin.mem_toFinset.mp hu)
  have hDisjoint : Disjoint Rfin extras := by
    apply Finset.disjoint_left.mpr
    intro u hu hue
    have hpos := (hRfin.mem_toFinset.mp hu).1
    simp only [extras, Finset.mem_insert, Finset.mem_singleton] at hue
    rcases hue with rfl | rfl <;> linarith
  have hUnionSub : Rfin ∪ extras ⊆ roots :=
    Finset.union_subset hRfinSub hExtrasSub
  have hUnionCard : (Rfin ∪ extras).card = 2*n+2 := by
    rw [Finset.card_union_of_disjoint hDisjoint, hRfinCard, hExtrasCard]
  have hPdegree : P.natDegree ≤ 2*n+2 :=
    equilibriumEliminationPoly_natDegree_le k ET FT ST
  have hRootsCard : roots.card = 2*n+2 := by
    have hlo := Finset.card_le_card hUnionSub
    have hhi : roots.card ≤ P.natDegree :=
      (Multiset.toFinset_card_le P.roots).trans (card_roots' P)
    omega
  have hRootsMultisetCard : P.roots.card = 2*n+2 := by
    have hlo := Multiset.toFinset_card_le P.roots
    have hhi := card_roots' P
    have hcard : P.roots.toFinset.card = 2*n+2 := hRootsCard
    omega
  have hNodup : P.roots.Nodup :=
    Multiset.toFinset_card_eq_card_iff_nodup.mp (by
      simpa only [roots] using hRootsCard.trans hRootsMultisetCard.symm)
  have hPdegreeEq : P.natDegree = 2*n+2 := by
    have hhi := card_roots' P
    omega
  have hSplits : P.Splits :=
    (splits_iff_card_roots).2 (by omega)
  have hSeparable : P.Separable :=
    (nodup_roots_iff_of_splits hPne hSplits).1 hNodup
  have hSimple : ∀ u : ℝ, 0 < u →
      ratioEnzymeResidual k ET FT ST u = 0 →
      deriv (ratioEnzymeResidual k ET FT ST) u ≠ 0 := by
    intro u hu hRu
    have hPu : P.eval u = 0 := by
      have hmem := hRroot u ⟨hu, hRu⟩
      change u ∈ P.roots.toFinset at hmem
      rw [Multiset.mem_toFinset, mem_roots hPne] at hmem
      exact hmem
    have hPderiv : P.derivative.eval u ≠ 0 := by
      have h := hSeparable.eval₂_derivative_ne_zero (RingHom.id ℝ) hPu
      simpa using h
    exact eliminant_simple_implies_residual_simple
      hn k hk ET FT ST u hST hu hRu hPderiv
  have hSum := ratio_residual_signed_crossing_one
    hn k hk ET FT ST hET hFT hST hRfin hSimple
  have hmod :
      (((∑ u ∈ Rfin, crossingCharge
        (ratioEnzymeResidual k ET FT ST) u : ℤ) : ℤ) : ZMod 2) =
        (Rfin.card : ZMod 2) := by
    rw [Int.cast_sum]
    calc
      (∑ u ∈ Rfin,
          ((crossingCharge (ratioEnzymeResidual k ET FT ST) u : ℤ) : ZMod 2)) =
          ∑ u ∈ Rfin, (1 : ZMod 2) := by
            apply Finset.sum_congr rfl
            intro u _
            by_cases h : 0 < deriv (ratioEnzymeResidual k ET FT ST) u
            · simp [crossingCharge, h]
            · simp only [crossingCharge, h, ↓reduceIte]
              decide
      _ = (Rfin.card : ZMod 2) := by simp
  have hSum' : ∑ u ∈ Rfin,
      crossingCharge (ratioEnzymeResidual k ET FT ST) u = 1 := hSum
  rw [hSum', hRfinCard] at hmod
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp [htwo] at hmod

/-- The explicit one-site witness is the complete positive equilibrium
set in its compatibility class. -/
theorem one_site_positive_equilibria_exactly_one :
    {x : State 1 |
      x.Positive ∧ Equilibrium oneRates x ∧
        InClass (3/2) (3/2) 3 x}.ncard = 1 := by
  let E : Set (State 1) :=
    {x | x.Positive ∧ Equilibrium oneRates x ∧
      InClass (3/2) (3/2) 3 x}
  have hresult := positive_equilibria_finite_and_ncard_le_two_n_sub_one
    (by omega : 0 < 1) oneRates oneRates_positive
    (3/2) (3/2) 3 (by norm_num) (by norm_num) (by norm_num)
  have hfin : E.Finite := hresult.1
  have hle : E.ncard ≤ 1 := by simpa only [E] using hresult.2
  have hmem : oneState ∈ E :=
    ⟨oneState_positive, oneState_equilibrium, oneState_inClass⟩
  have hpos : 0 < E.ncard := by
    rw [Set.ncard_eq_toFinset_card E hfin]
    exact Finset.card_pos.mpr ⟨oneState, hfin.mem_toFinset.mpr hmem⟩
  change E.ncard = 1
  omega

end
end PhosphorylationStableCapacity
