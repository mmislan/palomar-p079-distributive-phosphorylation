module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitGlobalBPositive435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitRationalSource
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitGenericPhysical435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitRootGapParity
public import proofs.PhosphorylationStableCapacity.ExactSplitEquilibriumCount
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitDetNonzero
public import proofs.PhosphorylationStableCapacity.RegularFullFamilyOpen435
public import proofs.PhosphorylationStableCapacity.PositiveRealRootParity435

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Polynomial
open scoped BigOperators
open scoped Topology

/-- The three freely prescribed positive kinetic arrays in the paper,
on one common arbitrary-root system. The source gamma array is one. -/
def paperGeneralPrescribedRates (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (b β γ : Fin (m+1) → ℝ) : Rates (m+1) :=
  retune (arbitrarySplitFiniteRates m ξ r δ) γ b β

private theorem retune_preserves_equilibrium_general {n : ℕ}
    (k : Rates n) (hk : k.Positive) (l b β : Fin n → ℝ)
    (x : State n) (heq : Equilibrium k x) :
    Equilibrium (retune k l b β) x := by
  exact retune_equilibrium k x l b β hk
    (fun i => (equilibrium_complex_balances k x heq i).1)
    (fun i => (equilibrium_complex_balances k x heq i).2)
    (equilibrium_catalytic_balance k x heq)

private theorem retune_inverse_general {n : ℕ}
    (k : Rates n) (hk : k.Positive) (l b β : Fin n → ℝ)
    (hl : ∀ i, 0 < l i) (hb : ∀ i, 0 < b i) (hβ : ∀ i, 0 < β i) :
    retune (retune k l b β) (fun i => (l i)⁻¹) k.b k.beta = k := by
  have hC (i : Fin n) : k.b i+k.c i ≠ 0 :=
    ne_of_gt (add_pos (hk i).2.1 (hk i).2.2.1)
  have hD (i : Fin n) : k.beta i+k.gamma i ≠ 0 :=
    ne_of_gt (add_pos (hk i).2.2.2.2.1 (hk i).2.2.2.2.2)
  have hC' (i : Fin n) : b i+l i*k.c i ≠ 0 :=
    ne_of_gt (add_pos (hb i) (mul_pos (hl i) (hk i).2.2.1))
  have hD' (i : Fin n) : β i+l i*k.gamma i ≠ 0 :=
    ne_of_gt (add_pos (hβ i) (mul_pos (hl i) (hk i).2.2.2.2.2))
  cases k with
  | mk a b₀ c α β₀ γ =>
    simp only [retune]
    congr 1 <;> funext i <;>
      field_simp [ne_of_gt (hl i), hC i, hD i, hC' i, hD' i]

/-- Arbitrary independent reverse binding and catalytic choices preserve
the entire equilibrium set, in both directions, for every physical state. -/
theorem retune_equilibrium_iff_general {n : ℕ}
    (k : Rates n) (hk : k.Positive) (l b β : Fin n → ℝ)
    (hl : ∀ i, 0 < l i) (hb : ∀ i, 0 < b i) (hβ : ∀ i, 0 < β i)
    (x : State n) : Equilibrium (retune k l b β) x ↔ Equilibrium k x := by
  constructor
  · intro h
    have h' := retune_preserves_equilibrium_general (retune k l b β)
      (retune_positive k l b β hk hl hb hβ) (fun i => (l i)⁻¹) k.b k.beta x h
    simpa only [retune_inverse_general k hk l b β hl hb hβ] using h'
  · exact retune_preserves_equilibrium_general k hk l b β x

/-- Literal agreement with the paper's general kinetic formulas; no
special reverse-binding or catalytic choice is imposed. Coefficient
normalization by D(0) leaves these formulas unchanged. -/
theorem paperGeneralPrescribedRates_formulas
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) (b β γ : Fin (m+1) → ℝ)
    (hD : DensePositive (arbitrarySplitRawD m ξ r δ) m)
    (hB : DensePositive (arbitrarySplitRawB m ξ r δ) m) (i : Fin (m+1)) :
    let A := (1+X)*arbitrarySplitRawD m ξ r δ
    let B := arbitrarySplitRawB m ξ r δ
    let D := arbitrarySplitRawD m ξ r δ
    let k := paperGeneralPrescribedRates m ξ r δ b β γ
    k.a i = (b i+γ i*D.coeff i/B.coeff i)*B.coeff i/A.coeff i.castSucc ∧
      k.b i = b i ∧ k.c i = γ i*D.coeff i/B.coeff i ∧
      k.alpha i = (β i+γ i)*D.coeff i/A.coeff i.succ ∧
      k.beta i = β i ∧ k.gamma i = γ i := by
  have hA := dense_inventory_product hD
  have hDi := ne_of_gt (hD.1 i (by omega))
  have hBi := ne_of_gt (hB.1 i (by omega))
  have hAi := ne_of_gt (hA.1 i.castSucc (by omega))
  have hAn := ne_of_gt (hA.1 i.succ (by omega))
  dsimp [paperGeneralPrescribedRates, retune, arbitrarySplitFiniteRates, realize]
  refine ⟨?_, rfl, ?_, ?_, rfl, ?_⟩
  · field_simp [hDi, hBi, hAi]; ring
  · ring
  · field_simp [hAn]; ring
  · ring

theorem paperGeneralPrescribedRates_positive_and_states
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) (b β γ : Fin (m+1) → ℝ)
    (hD : DensePositive (arbitrarySplitRawD m ξ r δ) m)
    (hB : DensePositive (arbitrarySplitRawB m ξ r δ) m)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j)
    (hb : ∀ i, 0 < b i) (hβ : ∀ i, 0 < β i) (hγ : ∀ i, 0 < γ i) :
    (paperGeneralPrescribedRates m ξ r δ b β γ).Positive ∧
      ∀ j : Fin (2*m+1),
        (arbitrarySplitFiniteState m ξ r δ j).Positive ∧
        Equilibrium (paperGeneralPrescribedRates m ξ r δ b β γ)
          (arbitrarySplitFiniteState m ξ r δ j) ∧
        InClass (2*r) 2 (2*(r+1)) (arbitrarySplitFiniteState m ξ r δ j) := by
  have hsource (j : Fin (2*m+1)) := arbitrarySplitFiniteState_source_of_conversion_positive
    m ξ r δ hD hB j (hroot j.val (by omega))
  have hk := (hsource ⟨0, by omega⟩).1
  refine ⟨retune_positive _ γ b β hk hγ hb hβ, ?_⟩
  intro j
  exact ⟨(hsource j).2.1,
    retune_preserves_equilibrium_general _ hk γ b β _ (hsource j).2.2.1,
    (hsource j).2.2.2⟩

theorem paperGeneralPrescribedRates_rational
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) (b β γ : Fin (m+1) → ℝ)
    (hr : RationalReal r) (hδ : RationalReal δ)
    (hξ : ∀ j, RationalReal (ξ j))
    (hb : ∀ i, RationalReal (b i)) (hβ : ∀ i, RationalReal (β i))
    (hγ : ∀ i, RationalReal (γ i)) :
    RationalRates (paperGeneralPrescribedRates m ξ r δ b β γ) ∧
      ∀ j : Fin (2*m+1), RationalState (arbitrarySplitFiniteState m ξ r δ j) := by
  have h := arbitrarySplitFiniteSource_rational m ξ hr hδ hξ
  exact ⟨retune_rational _ γ b β h.1 hγ hb hβ, h.2⟩


private theorem paperGeneral_realized_eq_reconstruct {n : ℕ}
    (hn : 0 < n) (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (ht : ∀ i, 0 < t i) (hB : ∀ i, 0 < B i)
    (hD : ∀ i, 0 < D i) (x : State n)
    (hx : x.Positive) (heq : Equilibrium (realize t B D) x) :
    x = reconstruct t B D (x.E/x.F) (x.S 0/t 0) x.F := by
  let u := x.E/x.F
  let s := x.S 0/t 0
  let z := reconstruct t B D u s x.F
  have hu : 0 < u := div_pos hx.2.1 hx.2.2.1
  have hs : 0 < s := div_pos (hx.1 0) (ht 0)
  have hz : z.Positive := reconstruct_positive t B D ht hB hD hu hs hx.2.2.1
  have hzeq : Equilibrium (realize t B D) z :=
    reconstruct_equilibrium t B D ht hB u s x.F
  have hratio : z.E/z.F = u :=
    reconstruct_ratio t B D u s x.F (ne_of_gt hx.2.2.1)
  have hS0 : z.S 0 = x.S 0 := by
    change t 0 * u^((0 : Fin (n+1)).val) * (x.S 0/t 0) = x.S 0
    simp only [Fin.val_zero, pow_zero, mul_one]
    calc
      t 0 * (x.S 0/t 0) = t 0 * x.S 0 / t 0 := by ring
      _ = x.S 0 := mul_div_cancel_left₀ _ (ne_of_gt (ht 0))
  have hF : z.F = x.F := rfl
  have hFT : totalF x = totalF z := by
    have hx' := (equilibrium_total_profiles (realize t B D) x
      (realize_positive t B D ht hB hD) hx heq).1
    have hz' := (equilibrium_total_profiles (realize t B D) z
      (realize_positive t B D ht hB hD) hz hzeq).1
    rw [hratio, hS0, hF] at hz'
    exact hx'.trans hz'.symm
  have hST : totalS x = totalS z := by
    have hx' := (equilibrium_total_profiles (realize t B D) x
      (realize_positive t B D ht hB hD) hx heq).2
    have hz' := (equilibrium_total_profiles (realize t B D) z
      (realize_positive t B D ht hB hD) hz hzeq).2
    rw [hratio, hS0, hF] at hz'
    exact hx'.trans hz'.symm
  exact positive_equilibria_enzyme_ratio_injective
    (realize t B D) x z hn (realize_positive t B D ht hB hD)
    hx hz heq hzeq hFT hST (by simpa only [u] using hratio.symm)

private theorem paperGeneral_source_ratio_is_prescribed
    (m : ℕ) (η : ℕ → ℝ) (r δ : ℝ) (hr : 0 < r)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot η δ j)
    (hD : DensePositive (arbitrarySplitRawD m η r δ) m)
    (hB : DensePositive (arbitrarySplitRawB m η r δ) m)
    (x : State (m+1)) (hx : x.Positive)
    (heq : Equilibrium (arbitrarySplitFiniteRates m η r δ) x)
    (hET : totalE x = 2*r) (hFT : totalF x = 2)
    (hST : totalS x = 2*(r+1)) :
    ∃ j : Fin (2*m+1), x.E/x.F = ratio (offsetSplitRoot η δ j.val) := by
  let B := arbitrarySplitRawB m η r δ
  let D := arbitrarySplitRawD m η r δ
  let A : ℝ[X] := (1+X)*D
  let t : Fin (m+2) → ℝ := fun i => A.coeff i
  let bcoeff : Fin (m+1) → ℝ := fun i => B.coeff i
  let dcoeff : Fin (m+1) → ℝ := fun i => D.coeff i
  let u := x.E/x.F
  let s := x.S 0/t 0
  let f := x.F
  let b := B.eval u
  let d := D.eval u
  have hA : DensePositive A (m+1) := dense_inventory_product hD
  have ht : ∀ i, 0 < t i := fun i => hA.1 i (by omega)
  have hb : ∀ i, 0 < bcoeff i := fun i => hB.1 i (by omega)
  have hd : ∀ i, 0 < dcoeff i := fun i => hD.1 i (by omega)
  have hu : 0 < u := div_pos hx.2.1 hx.2.2.1
  have hs : 0 < s := div_pos (hx.1 0) (ht 0)
  have hf : 0 < f := hx.2.2.1
  have hdu : 0 < d := hD.eval_pos hu
  have hrec : x = reconstruct t bcoeff dcoeff u s f := by
    exact paperGeneral_realized_eq_reconstruct
      (by omega : 0 < m+1) t bcoeff dcoeff ht hb hd x hx heq
  have htot := reconstruct_totals t bcoeff dcoeff u s f
  rw [dense_inventory hB u, dense_inventory hD u,
    dense_inventory hA u] at htot
  rw [← hrec] at htot
  have hEval : A.eval u = (1+u)*d := by
    simp [A, d]
  have hE : 2*r = u*f*(1+s*b) := by
    simpa only [hET, b] using htot.1
  have hF : 2 = f*(1+s*u*d) := by
    simpa only [hFT, d] using htot.2.1
  have hS : 2*(r+1) = s*(1+u)*d+u*s*f*(b+d) := by
    rw [hEval] at htot
    simpa only [hST, b, d, mul_assoc] using htot.2.2
  have hsd : s*d = f := by
    have hdiff : (1+u)*(s*d-f) = 0 := by
      calc
        (1+u)*(s*d-f) =
            (s*(1+u)*d+u*s*f*(b+d)) -
              (u*f*(1+s*b)+f*(1+s*u*d)) := by ring
        _ = 0 := by rw [← hS, ← hE, ← hF]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left
      (ne_of_gt (by linarith : 0 < 1+u)))
  have hgap : r-u = s*u*(b-r*d) := by
    have hg : f*(u-r+s*u*(b-r*d))=0 := by
      calc
        f*(u-r+s*u*(b-r*d)) =
            u*f*(1+s*b)-r*(f*(1+s*u*d)) := by ring
        _ = 0 := by rw [← hE, ← hF]; ring
    have := (mul_eq_zero.mp hg).resolve_left (ne_of_gt hf)
    linarith
  let ξ := 1+2*u*f
  have hξ : 1 < ξ := by dsimp [ξ]; nlinarith [mul_pos hu hf]
  have hquad : u*f^2+f=2 := by
    have hsu : s*u*d = u*f := by
      calc
        s*u*d = u*(s*d) := by ring
        _ = u*f := by rw [hsd]
    have h := hF
    rw [hsu] at h
    nlinarith [h]
  have hξratio : ratio ξ = u := by
    have huquad := congrArg (fun a : ℝ => u*a) hquad
    dsimp [ratio, ξ]
    nlinarith [huquad]
  have hbalance : arbitrarySplitConversionResidual m η r δ ξ = 0 := by
    have hξexpr : ξ-1=2*u*f := by dsimp [ξ]; ring
    change (ξ-1)*(B.eval (ratio ξ)-r*D.eval (ratio ξ)) -
      2*(r-ratio ξ)*D.eval (ratio ξ)=0
    rw [hξratio]
    change (ξ-1)*(b-r*d)-2*(r-u)*d=0
    calc
      (ξ-1)*(b-r*d)-2*(r-u)*d =
          2*d*(s*u*(b-r*d)-(r-u)) := by rw [hξexpr, ← hsd]; ring
      _ = 0 := by rw [← hgap]; ring
  have hfac : 0 < 4*r*(arbitrarySplitPair m η δ).1.eval r+
      (ξ-1)*(arbitrarySplitPair m η δ).2.eval r :=
    conversion_prefactor_pos (arbitrarySplitPair_dense m η δ hroot).1
      (arbitrarySplitPair_dense m η δ hroot).2 hr hξ
  have hfactor := arbitrarySplitConversionResidual_factor m η r δ ξ
  change arbitrarySplitConversionResidual m η r δ ξ =
    (4*r*(arbitrarySplitPair m η δ).1.eval r+
      (ξ-1)*(arbitrarySplitPair m η δ).2.eval r) *
        arbitrarySplitScalarProduct m η δ ξ at hfactor
  rw [hfactor] at hbalance
  have hprod : arbitrarySplitScalarProduct m η δ ξ = 0 :=
    (mul_eq_zero.mp hbalance).resolve_left (ne_of_gt hfac)
  rw [arbitrarySplitScalarProduct_eq_prod_range] at hprod
  obtain ⟨j, hj, hjzero⟩ := Finset.prod_eq_zero_iff.mp hprod
  refine ⟨⟨j, Finset.mem_range.mp hj⟩, ?_⟩
  have hξroot : ξ = offsetSplitRoot η δ j := sub_eq_zero.mp hjzero
  change u = ratio (offsetSplitRoot η δ j)
  rw [← hξratio, hξroot]


/-- No positive equilibrium is lost or added by the general kinetic
choice. This exact equality retains the original common rate vector. -/
theorem paperGeneralPrescribedRates_exact_equilibria
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) (b β γ : Fin (m+1) → ℝ)
    (hr : 0 < r)
    (hD : DensePositive (arbitrarySplitRawD m ξ r δ) m)
    (hB : DensePositive (arbitrarySplitRawB m ξ r δ) m)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j)
    (hb : ∀ i, 0 < b i) (hβ : ∀ i, 0 < β i) (hγ : ∀ i, 0 < γ i) :
    {x : State (m+1) | x.Positive ∧
      Equilibrium (paperGeneralPrescribedRates m ξ r δ b β γ) x ∧
      InClass (2*r) 2 (2*(r+1)) x} =
        Set.range (arbitrarySplitFiniteState m ξ r δ) := by
  have hsource (j : Fin (2*m+1)) := arbitrarySplitFiniteState_source_of_conversion_positive
    m ξ r δ hD hB j (hroot j.val (by omega))
  have hk := (hsource ⟨0, by omega⟩).1
  have hstates := paperGeneralPrescribedRates_positive_and_states
    m ξ r δ b β γ hD hB hroot hb hβ hγ
  ext x
  constructor
  · rintro ⟨hx, heq, hclass⟩
    have heq₀ := (retune_equilibrium_iff_general _ hk γ b β hγ hb hβ x).mp heq
    obtain ⟨j, hjratio⟩ := paperGeneral_source_ratio_is_prescribed
      m ξ r δ hr hroot hD hB x hx heq₀ hclass.1 hclass.2.1 hclass.2.2
    have hy := hsource j
    have hf : rootF (offsetSplitRoot ξ δ j.val) ≠ 0 :=
      ne_of_gt (div_pos (by norm_num) (by linarith [hroot j.val (by omega)]))
    have hyratio : (arbitrarySplitFiniteState m ξ r δ j).E /
        (arbitrarySplitFiniteState m ξ r δ j).F = ratio (offsetSplitRoot ξ δ j.val) :=
      reconstruct_ratio _ _ _ _ _ _ hf
    have hxy : x = arbitrarySplitFiniteState m ξ r δ j := by
      apply positive_equilibria_enzyme_ratio_injective
        (arbitrarySplitFiniteRates m ξ r δ) x (arbitrarySplitFiniteState m ξ r δ j)
        (by omega) hk hx hy.2.1 heq₀ hy.2.2.1
      · exact hclass.2.1.trans hy.2.2.2.2.1.symm
      · exact hclass.2.2.trans hy.2.2.2.2.2.symm
      · exact hjratio.trans hyratio.symm
    exact ⟨j, hxy.symm⟩
  · rintro ⟨j, rfl⟩
    exact hstates.2 j

theorem paperGeneralPrescribedStates_injective
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j)
    (hordered : StrictMono (fun j : Fin (2*m+1) => offsetSplitRoot ξ δ j.val)) :
    Function.Injective (arbitrarySplitFiniteState m ξ r δ) := by
  have hratio (j : Fin (2*m+1)) : (arbitrarySplitFiniteState m ξ r δ j).E /
      (arbitrarySplitFiniteState m ξ r δ j).F = ratio (offsetSplitRoot ξ δ j.val) := by
    apply reconstruct_ratio
    exact ne_of_gt (div_pos (by norm_num) (by linarith [hroot j.val (by omega)]))
  intro i j hij
  apply hordered.injective
  apply ratio_injective (hroot i.val (by omega)) (hroot j.val (by omega))
  rw [← hratio i, ← hratio j, hij]

theorem paperGeneralPrescribed_root_gap_ne_zero
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ)
    (hordered : StrictMono (fun j : Fin (2*m+1) => offsetSplitRoot ξ δ j.val))
    (j : Fin (2*m+1)) :
    (∏ i ∈ (Finset.range (2*m+1)).erase j.val, (ξ j.val-ξ i)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hmem := Finset.mem_erase.mp hi
  have hiBound := Finset.mem_range.mp hmem.2
  apply sub_ne_zero.mpr
  intro heq
  have hrootEq : offsetSplitRoot ξ δ j.val = offsetSplitRoot ξ δ i := by
    simp only [offsetSplitRoot, heq]
  have hij : j = (⟨i, hiBound⟩ : Fin (2*m+1)) := hordered.injective hrootEq
  exact hmem.1 (congrArg Fin.val hij).symm

/-- The universal maximal-count construction for all positive kinetic
arrays, under exactly the paper's coefficient-positivity hypotheses.
The equilibrium list is exhaustive and each same-system Jacobian is
nonsingular; the roots need not be near a coalesced family. -/
theorem paperGeneralPrescribedRoot_maximal_count
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) (b β γ : Fin (m+1) → ℝ)
    (hr : 0 < r) (hδ : 0 < δ)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j)
    (hordered : StrictMono (fun j : Fin (2*m+1) => offsetSplitRoot ξ δ j.val))
    (hfar : ∀ j, j ≤ 2*m → offsetSplitRoot ξ δ j < Real.sqrt (1+8*r))
    (hsum : (∑ j ∈ Finset.range (2*m+1), offsetSplitRoot ξ δ j) ≤
      4*r+Real.sqrt (1+8*r))
    (hb : ∀ i, 0 < b i) (hβ : ∀ i, 0 < β i) (hγ : ∀ i, 0 < γ i) :
    (paperGeneralPrescribedRates m ξ r δ b β γ).Positive ∧
      {x : State (m+1) | x.Positive ∧
        Equilibrium (paperGeneralPrescribedRates m ξ r δ b β γ) x ∧
        InClass (2*r) 2 (2*(r+1)) x} = Set.range (arbitrarySplitFiniteState m ξ r δ) ∧
      {x : State (m+1) | x.Positive ∧
        Equilibrium (paperGeneralPrescribedRates m ξ r δ b β γ) x ∧
        InClass (2*r) 2 (2*(r+1)) x}.ncard = 2*m+1 ∧
      ∀ j : Fin (2*m+1),
        (arbitrarySplitFiniteState m ξ r δ j).Positive ∧
        Equilibrium (paperGeneralPrescribedRates m ξ r δ b β γ)
          (arbitrarySplitFiniteState m ξ r δ j) ∧
        InClass (2*r) 2 (2*(r+1)) (arbitrarySplitFiniteState m ξ r δ j) ∧
        (arbitrarySplitFiniteState m ξ r δ j).E /
          (arbitrarySplitFiniteState m ξ r δ j).F = ratio (offsetSplitRoot ξ δ j.val) ∧
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (paperGeneralPrescribedRates m ξ r δ b β γ)
          (toCoordinateSpace (chart (arbitrarySplitFiniteState m ξ r δ j)))).det ≠ 0 := by
  have hD := arbitrarySplitRawD_dense_every_positive_source m ξ δ r hr hroot
  have hB := arbitrarySplitRawB_dense_of_global_paper_bounds m ξ δ r hr hroot hfar hsum
  have hs := paperGeneralPrescribedRates_positive_and_states m ξ r δ b β γ
    hD hB hroot hb hβ hγ
  have hex := paperGeneralPrescribedRates_exact_equilibria m ξ r δ b β γ
    hr hD hB hroot hb hβ hγ
  have hinj := paperGeneralPrescribedStates_injective m ξ r δ hroot hordered
  refine ⟨hs.1, hex, ?_, ?_⟩
  · rw [hex]
    simpa using Set.ncard_range_of_injective hinj
  · intro j
    have hy := hroot j.val (by omega)
    have hv : 0 < r-ratio (offsetSplitRoot ξ δ j.val) := by
      have hsqrt := Real.sq_sqrt (show 0 ≤ 1+8*r by positivity)
      have hρ := Real.sqrt_nonneg (1+8*r)
      have hf := hfar j.val (by omega)
      dsimp [ratio]
      nlinarith
    have hd := arbitrarySplit_jacobian_det_ne_zero_of_gap_ne_zero m ξ r δ hr hδ
      _ hs.1 hD hB j hy hv (hs.2 j).2.1
      (conversion_prefactor_pos (arbitrarySplitPair_dense m ξ δ hroot).1
        (arbitrarySplitPair_dense m ξ δ hroot).2 hr hy)
      (paperGeneralPrescribed_root_gap_ne_zero m ξ δ hordered j)
    have hratio : (arbitrarySplitFiniteState m ξ r δ j).E /
        (arbitrarySplitFiniteState m ξ r δ j).F = ratio (offsetSplitRoot ξ δ j.val) := by
      apply reconstruct_ratio
      exact ne_of_gt (div_pos (by norm_num) (by linarith))
    have hc := (hs.2 j).2.2
    dsimp only at hd
    rw [hc.1, hc.2.1, hc.2.2] at hd
    exact ⟨(hs.2 j).1, (hs.2 j).2.1, hc, hratio, hd⟩

/-- Encode an arbitrary finite root tuple without assuming an ordering
or a spacing condition outside the prescribed tuple. -/
def paperGeneralRootOffset (m : ℕ) (x : Fin (2*m+1) → ℝ) (j : ℕ) : ℝ :=
  if hj : j < 2*m+1 then x ⟨j,hj⟩-3 else 0

theorem paperGeneralRootOffset_root (m : ℕ) (x : Fin (2*m+1) → ℝ)
    (j : Fin (2*m+1)) : offsetSplitRoot (paperGeneralRootOffset m x) 1 j.val = x j := by
  simp [offsetSplitRoot, paperGeneralRootOffset, j.isLt]

def paperGeneralRootRates (m : ℕ) (x : Fin (2*m+1) → ℝ) (r : ℝ)
    (b β γ : Fin (m+1) → ℝ) : Rates (m+1) :=
  paperGeneralPrescribedRates m (paperGeneralRootOffset m x) r 1 b β γ

def paperGeneralRootState (m : ℕ) (x : Fin (2*m+1) → ℝ) (r : ℝ)
    (j : Fin (2*m+1)) : State (m+1) :=
  arbitrarySplitFiniteState m (paperGeneralRootOffset m x) r 1 j

/-- The literal universal paper quantifiers: every ordered finite real
root tuple above one, every source parameter satisfying the printed
bounds, and every positive reverse-binding/catalytic tuple. -/
theorem paperGeneralRoot_maximal_count
    (m : ℕ) (x : Fin (2*m+1) → ℝ) (r : ℝ) (b β γ : Fin (m+1) → ℝ)
    (hroot : ∀ j, 1 < x j) (hordered : StrictMono x) (hr : 0 < r)
    (hfar : ∀ j, x j < Real.sqrt (1+8*r))
    (hsum : (∑ j, x j) ≤ 4*r+Real.sqrt (1+8*r))
    (hb : ∀ i, 0 < b i) (hβ : ∀ i, 0 < β i) (hγ : ∀ i, 0 < γ i) :
    (paperGeneralRootRates m x r b β γ).Positive ∧
      {z : State (m+1) | z.Positive ∧ Equilibrium (paperGeneralRootRates m x r b β γ) z ∧
        InClass (2*r) 2 (2*(r+1)) z} = Set.range (paperGeneralRootState m x r) ∧
      {z : State (m+1) | z.Positive ∧ Equilibrium (paperGeneralRootRates m x r b β γ) z ∧
        InClass (2*r) 2 (2*(r+1)) z}.ncard = 2*m+1 ∧
      ∀ j : Fin (2*m+1), (paperGeneralRootState m x r j).Positive ∧
        Equilibrium (paperGeneralRootRates m x r b β γ) (paperGeneralRootState m x r j) ∧
        InClass (2*r) 2 (2*(r+1)) (paperGeneralRootState m x r j) ∧
        (paperGeneralRootState m x r j).E / (paperGeneralRootState m x r j).F = ratio (x j) ∧
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1)) (paperGeneralRootRates m x r b β γ)
          (toCoordinateSpace (chart (paperGeneralRootState m x r j)))).det ≠ 0 := by
  have hroots : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot (paperGeneralRootOffset m x) 1 j := by
    intro j hj
    simpa only [paperGeneralRootOffset_root m x ⟨j,by omega⟩] using hroot ⟨j,by omega⟩
  have horder : StrictMono (fun j : Fin (2*m+1) =>
      offsetSplitRoot (paperGeneralRootOffset m x) 1 j.val) := by
    simpa only [paperGeneralRootOffset_root] using hordered
  have hfar' : ∀ j, j ≤ 2*m → offsetSplitRoot (paperGeneralRootOffset m x) 1 j <
      Real.sqrt (1+8*r) := by
    intro j hj
    simpa only [paperGeneralRootOffset_root m x ⟨j,by omega⟩] using hfar ⟨j,by omega⟩
  have hsum' : (∑ j ∈ Finset.range (2*m+1),
      offsetSplitRoot (paperGeneralRootOffset m x) 1 j) ≤ 4*r+Real.sqrt (1+8*r) := by
    have heq := Fin.sum_univ_eq_sum_range
      (fun j => offsetSplitRoot (paperGeneralRootOffset m x) 1 j) (2*m+1)
    rw [← heq]
    simpa only [paperGeneralRootOffset_root] using hsum
  simpa only [Set.range, paperGeneralRootRates, paperGeneralRootState, paperGeneralRootOffset_root] using
    paperGeneralPrescribedRoot_maximal_count m (paperGeneralRootOffset m x) r 1 b β γ
      hr (by norm_num) hroots horder hfar' hsum' hb hβ hγ

theorem paperGeneralRoot_rational
    (m : ℕ) (x : Fin (2*m+1) → ℝ) (r : ℝ) (b β γ : Fin (m+1) → ℝ)
    (hx : ∀ j, RationalReal (x j)) (hr : RationalReal r)
    (hb : ∀ i, RationalReal (b i)) (hβ : ∀ i, RationalReal (β i))
    (hγ : ∀ i, RationalReal (γ i)) :
    RationalRates (paperGeneralRootRates m x r b β γ) ∧
      ∀ j : Fin (2*m+1), RationalState (paperGeneralRootState m x r j) := by
  have hξ : ∀ j, RationalReal (paperGeneralRootOffset m x j) := by
    intro j
    unfold paperGeneralRootOffset
    split_ifs with hj
    · obtain ⟨a, ha⟩ := hx ⟨j,hj⟩
      refine ⟨a-3, ?_⟩
      push_cast
      rw [ha]
    · exact ⟨0, by norm_num⟩
  exact paperGeneralPrescribedRates_rational m (paperGeneralRootOffset m x) r 1 b β γ
    hr ⟨1, by norm_num⟩ hξ hb hβ hγ


theorem paperGeneral_finite_offset_gap_alternates
    (m : ℕ) (ξ : ℕ → ℝ) (hξ : StrictMono (fun j : Fin (2*m+1) => ξ j.val))
    (j : Fin (2*m+1)) :
    (Even j.val →
      0 < ∏ i ∈ (Finset.range (2*m+1)).erase j.val,
        (ξ j.val-ξ i)) ∧
    (Odd j.val →
      (∏ i ∈ (Finset.range (2*m+1)).erase j.val,
        (ξ j.val-ξ i)) < 0) := by
  let S := (Finset.range (2*m+1)).erase j.val
  let scale : ℕ → ℝ := fun i =>
    (ξ j.val-ξ i)/((j.val : ℝ)-(i : ℝ))
  have hscale (i : ℕ) (hi : i ∈ S) : 0 < scale i := by
    have hij : i ≠ j.val := (Finset.mem_erase.mp hi).1
    have hiBound : i < 2*m+1 := Finset.mem_range.mp (Finset.mem_erase.mp hi).2
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hξij : ξ i < ξ j.val := hξ (show (⟨i,hiBound⟩ : Fin (2*m+1)) < j from hlt)
      have hcast : (i : ℝ) < (j.val : ℝ) := by exact_mod_cast hlt
      exact div_pos (sub_pos.mpr hξij) (sub_pos.mpr hcast)
    · have hξji : ξ j.val < ξ i := hξ (show j < (⟨i,hiBound⟩ : Fin (2*m+1)) from hgt)
      have hcast : (j.val : ℝ) < (i : ℝ) := by exact_mod_cast hgt
      exact div_pos_of_neg_of_neg (sub_neg.mpr hξji)
        (sub_neg.mpr hcast)
  have hscaleprod : 0 < ∏ i ∈ S, scale i := by
    apply Finset.prod_pos
    intro i hi
    exact hscale i hi
  have hgap_eq :
      (∏ i ∈ S, (ξ j.val-ξ i)) =
        (∏ i ∈ S, ((j.val : ℝ)-(i : ℝ))) *
          (∏ i ∈ S, scale i) := by
    calc
      (∏ i ∈ S, (ξ j.val-ξ i)) =
          ∏ i ∈ S, (((j.val : ℝ)-(i : ℝ))*scale i) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hij : j.val ≠ i := (Finset.mem_erase.mp hi).1.symm
        have hden : (j.val : ℝ)-(i : ℝ) ≠ 0 := by
          apply sub_ne_zero.mpr
          intro heq
          exact hij (by exact_mod_cast heq)
        dsimp [scale]
        field_simp [hden]
      _ = _ := by rw [Finset.prod_mul_distrib]
  have hnat := nat_offset_root_gap_alternates m j
  constructor
  · intro heven
    change 0 < ∏ i ∈ S, (ξ j.val-ξ i)
    rw [hgap_eq]
    exact mul_pos (hnat.1 heven) hscaleprod
  · intro hodd
    change (∏ i ∈ S, (ξ j.val-ξ i)) < 0
    rw [hgap_eq]
    exact mul_neg_of_neg_of_pos (hnat.2 hodd) hscaleprod


theorem paperGeneralRoot_charpoly_constant_negative_at_odd
    (m : ℕ) (x : Fin (2*m+1) → ℝ) (r : ℝ) (b β γ : Fin (m+1) → ℝ)
    (hroot : ∀ j, 1 < x j) (hordered : StrictMono x) (hr : 0 < r)
    (hfar : ∀ j, x j < Real.sqrt (1+8*r))
    (hsum : (∑ j, x j) ≤ 4*r+Real.sqrt (1+8*r))
    (hb : ∀ i, 0 < b i) (hβ : ∀ i, 0 < β i) (hγ : ∀ i, 0 < γ i)
    (j : Fin (2*m+1)) (hodd : Odd j.val) :
    (restrictedJacobianMatrix (2*r) 2 (2*(r+1)) (paperGeneralRootRates m x r b β γ)
      (toCoordinateSpace (chart (paperGeneralRootState m x r j)))).charpoly.coeff 0 < 0 := by
  let η := paperGeneralRootOffset m x
  have hroots : ∀ i, i ≤ 2*m → 1 < offsetSplitRoot η 1 i := by
    intro i hi
    simpa only [η, paperGeneralRootOffset_root m x ⟨i,by omega⟩] using hroot ⟨i,by omega⟩
  have hfar' : ∀ i, i ≤ 2*m → offsetSplitRoot η 1 i < Real.sqrt (1+8*r) := by
    intro i hi
    simpa only [η, paperGeneralRootOffset_root m x ⟨i,by omega⟩] using hfar ⟨i,by omega⟩
  have hsum' : (∑ i ∈ Finset.range (2*m+1), offsetSplitRoot η 1 i) ≤
      4*r+Real.sqrt (1+8*r) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => offsetSplitRoot η 1 i) (2*m+1)]
    simpa only [η, paperGeneralRootOffset_root] using hsum
  have hD := arbitrarySplitRawD_dense_every_positive_source m η 1 r hr hroots
  have hB := arbitrarySplitRawB_dense_of_global_paper_bounds m η 1 r hr hroots hfar' hsum'
  have hmax := paperGeneralRoot_maximal_count m x r b β γ hroot hordered hr hfar hsum hb hβ hγ
  have hs := hmax.2.2.2 j
  have hη : StrictMono (fun i : Fin (2*m+1) => η i.val) := by
    intro i k hik
    have hi := hordered hik
    simpa [η, paperGeneralRootOffset, i.isLt, k.isLt] using sub_lt_sub_right hi 3
  have hgap := (paperGeneral_finite_offset_gap_alternates m η hη j).2 hodd
  have hy : 1 < offsetSplitRoot η 1 j.val := hroots j.val (by omega)
  have hv : 0 < r-ratio (offsetSplitRoot η 1 j.val) := by
    have hsqrt := Real.sq_sqrt (show 0 ≤ 1+8*r by positivity)
    have hρ := Real.sqrt_nonneg (1+8*r)
    have hf := hfar' j.val (by omega)
    dsimp [ratio]
    nlinarith
  have hsign := arbitrarySplit_jacobian_det_sign_iff_root_gap m η r 1 hr
    (by norm_num) _ hmax.1 hD hB j hy hv hs.2.1
    (conversion_prefactor_pos (arbitrarySplitPair_dense m η 1 hroots).1
      (arbitrarySplitPair_dense m η 1 hroots).2 hr hy)
  dsimp only at hsign
  have hc := hs.2.2.1
  change InClass (2*r) 2 (2*(r+1)) (arbitrarySplitFiniteState m η r 1 j) at hc
  rw [hc.1, hc.2.1, hc.2.2] at hsign
  let A := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
    (paperGeneralRootRates m x r b β γ)
    (toCoordinateSpace (chart (paperGeneralRootState m x r j)))
  change 0 < (-1 : ℝ)^(m+1)*A.det ↔ 0 < _ at hsign
  have hnonpos : (-1 : ℝ)^(m+1)*A.det ≤ 0 := by
    apply le_of_not_gt
    intro hp
    exact not_lt_of_ge hgap.le (hsign.mp hp)
  have hne : (-1 : ℝ)^(m+1)*A.det ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) hs.2.2.2.2
  have hneg : (-1 : ℝ)^(m+1)*A.det < 0 := lt_of_le_of_ne hnonpos hne
  have heq : (-1 : ℝ)^(m+1)*A.det = A.charpoly.coeff 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff]
    simp only [Fintype.card_sum, Fintype.card_fin]
    rw [← mul_assoc, ← pow_add,
      show (m+1)+((m+1)+((m+1)+(m+1))) = 4*(m+1) by omega,
      pow_mul]
    norm_num
  change A.charpoly.coeff 0 < 0
  rwa [heq] at hneg

/-- A full family of regular equilibria persists with the exact maximal
count. Nonsingularity is the only spectral premise: an arbitrary
kinetic choice need not make every equilibrium hyperbolic. -/
theorem paperGeneral_open_regular_full_family_of_base
    (n : ℕ) (hn : 0 < n) (p₀ : CapacityParameter n)
    (u₀ : Fin (2*n-1) → CoordinateSpace n)
    (hparam : (ratesFromVector p₀.1).Positive ∧
      0 < p₀.2.1 ∧ 0 < p₀.2.2.1 ∧ 0 < p₀.2.2.2)
    (hinj : Function.Injective u₀)
    (hstates : ∀ j, (unChart p₀.2.1 p₀.2.2.1 p₀.2.2.2
      (ofCoordinateSpace (u₀ j))).Positive ∧ capacityParameterField (p₀,u₀ j) = 0 ∧
      (restrictedJacobianMatrix p₀.2.1 p₀.2.2.1 p₀.2.2.2
        (ratesFromVector p₀.1) (u₀ j)).det ≠ 0) :
    ∃ s : Set (CapacityParameter n), IsOpen s ∧ p₀ ∈ s ∧
      ∀ p ∈ s, ((ratesFromVector p.1).Positive ∧
        0 < p.2.1 ∧ 0 < p.2.2.1 ∧ 0 < p.2.2.2) ∧
        ∃ u : Fin (2*n-1) → CoordinateSpace n, Function.Injective u ∧
          (∀ j, (unChart p.2.1 p.2.2.1 p.2.2.2 (ofCoordinateSpace (u j))).Positive ∧
            capacityParameterField (p,u j) = 0 ∧
            (restrictedJacobianMatrix p.2.1 p.2.2.1 p.2.2.2
              (ratesFromVector p.1) (u j)).det ≠ 0) ∧
          {z : State n | z.Positive ∧ Equilibrium (ratesFromVector p.1) z ∧
            InClass p.2.1 p.2.2.1 p.2.2.2 z} =
              Set.range (fun j => unChart p.2.1 p.2.2.1 p.2.2.2
                (ofCoordinateSpace (u j))) ∧
          {z : State n | z.Positive ∧ Equilibrium (ratesFromVector p.1) z ∧
            InClass p.2.1 p.2.2.1 p.2.2.2 z}.ncard = 2*n-1 := by
  exact capacity_open_full_regular_family_of_base n hn p₀ u₀ hparam hinj hstates

/-- The exact maximal regular configuration of each admissible general
kinetic realization persists on a nonempty open neighborhood of that
very realization in the full rate-and-total parameter space. -/
theorem paperGeneralRoot_open_maximal_count
    (m : ℕ) (x : Fin (2*m+1) → ℝ) (r : ℝ) (b β γ : Fin (m+1) → ℝ)
    (hroot : ∀ j, 1 < x j) (hordered : StrictMono x) (hr : 0 < r)
    (hfar : ∀ j, x j < Real.sqrt (1+8*r))
    (hsum : (∑ j, x j) ≤ 4*r+Real.sqrt (1+8*r))
    (hb : ∀ i, 0 < b i) (hβ : ∀ i, 0 < β i) (hγ : ∀ i, 0 < γ i) :
    let p₀ : CapacityParameter (m+1) :=
      (rateVector (paperGeneralRootRates m x r b β γ), (2*r,2,2*(r+1)))
    ∃ s : Set (CapacityParameter (m+1)), IsOpen s ∧ p₀ ∈ s ∧
      ∀ p ∈ s, ((ratesFromVector p.1).Positive ∧
        0 < p.2.1 ∧ 0 < p.2.2.1 ∧ 0 < p.2.2.2) ∧
        ∃ u : Fin (2*(m+1)-1) → CoordinateSpace (m+1), Function.Injective u ∧
          (∀ j, (unChart p.2.1 p.2.2.1 p.2.2.2 (ofCoordinateSpace (u j))).Positive ∧
            capacityParameterField (p,u j) = 0 ∧
            (restrictedJacobianMatrix p.2.1 p.2.2.1 p.2.2.2
              (ratesFromVector p.1) (u j)).det ≠ 0) ∧
          {z : State (m+1) | z.Positive ∧ Equilibrium (ratesFromVector p.1) z ∧
            InClass p.2.1 p.2.2.1 p.2.2.2 z} =
              Set.range (fun j => unChart p.2.1 p.2.2.1 p.2.2.2
                (ofCoordinateSpace (u j))) ∧
          {z : State (m+1) | z.Positive ∧ Equilibrium (ratesFromVector p.1) z ∧
            InClass p.2.1 p.2.2.1 p.2.2.2 z}.ncard = 2*(m+1)-1 := by
  dsimp only
  let k := paperGeneralRootRates m x r b β γ
  let p₀ : CapacityParameter (m+1) := (rateVector k,(2*r,2,2*(r+1)))
  have hN : 2*(m+1)-1 = 2*m+1 := by omega
  let u₀ : Fin (2*(m+1)-1) → CoordinateSpace (m+1) := fun j =>
    toCoordinateSpace (chart (paperGeneralRootState m x r (Fin.cast hN j)))
  have hmax := paperGeneralRoot_maximal_count m x r b β γ
    hroot hordered hr hfar hsum hb hβ hγ
  have hs (j : Fin (2*(m+1)-1)) := hmax.2.2.2 (Fin.cast hN j)
  have hback (j : Fin (2*(m+1)-1)) :
      unChart (2*r) 2 (2*(r+1)) (ofCoordinateSpace (u₀ j)) =
        paperGeneralRootState m x r (Fin.cast hN j) := by
    dsimp only [u₀]
    rw [of_toCoordinateSpace]
    exact unChart_chart_of_inClass _ _ _ _ (hs j).2.2.1
  have hparam : (ratesFromVector p₀.1).Positive ∧
      0 < p₀.2.1 ∧ 0 < p₀.2.2.1 ∧ 0 < p₀.2.2.2 := by
    simpa only [p₀,ratesFromVector_rateVector] using
      (show k.Positive ∧ 0 < 2*r ∧ 0 < (2 : ℝ) ∧ 0 < 2*(r+1) from
        ⟨hmax.1,by positivity,by norm_num,by positivity⟩)
  have hinj : Function.Injective u₀ := by
    intro i j hij
    have hz := congrArg (fun u => unChart (2*r) 2 (2*(r+1)) (ofCoordinateSpace u)) hij
    rw [hback i,hback j] at hz
    have heq := paperGeneralPrescribedStates_injective m (paperGeneralRootOffset m x) r 1
      (by
        intro a ha
        simpa only [paperGeneralRootOffset_root m x ⟨a,by omega⟩] using hroot ⟨a,by omega⟩)
      (by simpa only [paperGeneralRootOffset_root] using hordered) hz
    exact Fin.cast_injective hN heq
  have hstates : ∀ j, (unChart p₀.2.1 p₀.2.2.1 p₀.2.2.2
      (ofCoordinateSpace (u₀ j))).Positive ∧ capacityParameterField (p₀,u₀ j) = 0 ∧
      (restrictedJacobianMatrix p₀.2.1 p₀.2.2.1 p₀.2.2.2
        (ratesFromVector p₀.1) (u₀ j)).det ≠ 0 := by
    intro j
    have heq : restrictedFieldEuclid (2*r) 2 (2*(r+1)) k (u₀ j) = 0 := by
      apply (restrictedFieldEuclid_eq_zero_iff _ _ _ k (u₀ j)).2
      rw [hback j]
      exact (hs j).2.1
    simpa only [p₀,ratesFromVector_rateVector,capacityParameterField,hback j] using
      (show (unChart (2*r) 2 (2*(r+1)) (ofCoordinateSpace (u₀ j))).Positive ∧
        restrictedFieldEuclid (2*r) 2 (2*(r+1)) k (u₀ j) = 0 ∧
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k (u₀ j)).det ≠ 0 from
          ⟨by rw [hback j]; exact (hs j).1,heq,(hs j).2.2.2.2⟩)
  exact paperGeneral_open_regular_full_family_of_base (m+1) (by omega) p₀ u₀ hparam hinj hstates

/-- The manuscript parity conclusion counts positive real eigenvalues
with algebraic multiplicity through the actual real characteristic
polynomial; no restriction on the remaining complex spectrum is used. -/
theorem paperGeneralRoot_odd_positive_real_eigenvalue_multiplicity
    (m : ℕ) (x : Fin (2*m+1) → ℝ) (r : ℝ) (b β γ : Fin (m+1) → ℝ)
    (hroot : ∀ j, 1 < x j) (hordered : StrictMono x) (hr : 0 < r)
    (hfar : ∀ j, x j < Real.sqrt (1+8*r))
    (hsum : (∑ j, x j) ≤ 4*r+Real.sqrt (1+8*r))
    (hb : ∀ i, 0 < b i) (hβ : ∀ i, 0 < β i) (hγ : ∀ i, 0 < γ i)
    (j : Fin (2*m+1)) (hodd : Odd j.val) :
    Odd (((restrictedJacobianMatrix (2*r) 2 (2*(r+1)) (paperGeneralRootRates m x r b β γ)
      (toCoordinateSpace (chart (paperGeneralRootState m x r j)))).charpoly.roots.filter
        (fun z : ℝ => 0 < z)).card) := by
  apply monic_positive_real_root_multiplicity_odd_of_coeff_zero_neg
  · exact Matrix.charpoly_monic _
  · exact paperGeneralRoot_charpoly_constant_negative_at_odd m x r b β γ
      hroot hordered hr hfar hsum hb hβ hγ j hodd

def paperGeneralNormalizedD (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) : ℝ[X] :=
  C (((arbitrarySplitRawD m ξ r δ).coeff 0)⁻¹)*arbitrarySplitRawD m ξ r δ

def paperGeneralNormalizedB (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) : ℝ[X] :=
  C (((arbitrarySplitRawD m ξ r δ).coeff 0)⁻¹)*arbitrarySplitRawB m ξ r δ

def paperGeneralNormalizedA (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) : ℝ[X] :=
  (1+X)*paperGeneralNormalizedD m ξ r δ

private theorem paperGeneral_normalized_coeff (p : ℝ[X]) (d : ℝ) (i : ℕ) :
    (C (d⁻¹)*p).coeff i = p.coeff i/d := by
  rw [coeff_C_mul]
  simp only [div_eq_mul_inv, mul_comm]

private theorem paperGeneral_normalized_eval (p : ℝ[X]) (d u : ℝ) :
    (C (d⁻¹)*p).eval u = p.eval u/d := by
  rw [eval_mul,eval_C]
  simp only [div_eq_mul_inv, mul_comm]

theorem paperGeneralNormalizedA_coeff (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) (i : ℕ) :
    (paperGeneralNormalizedA m ξ r δ).coeff i =
      ((1+X)*arbitrarySplitRawD m ξ r δ).coeff i / (arbitrarySplitRawD m ξ r δ).coeff 0 := by
  have heq : paperGeneralNormalizedA m ξ r δ =
      C (((arbitrarySplitRawD m ξ r δ).coeff 0)⁻¹)*((1+X)*arbitrarySplitRawD m ξ r δ) := by
    unfold paperGeneralNormalizedA paperGeneralNormalizedD
    ring
  rw [heq]
  exact paperGeneral_normalized_coeff _ _ _

private theorem paperGeneral_normalized_dense {p : ℝ[X]} {m : ℕ} {d : ℝ}
    (hp : DensePositive p m) (hd : 0 < d) : DensePositive (C (d⁻¹)*p) m := by
  constructor
  · intro i hi
    rw [paperGeneral_normalized_coeff]
    exact div_pos (hp.1 i hi) hd
  · intro i hi
    rw [paperGeneral_normalized_coeff,hp.2 i hi,zero_div]

/-- The positive normalization constant and all normalized coefficient
conditions follow from the global printed hypotheses, including A(0)=D(0)=1. -/
theorem paperGeneral_normalized_coefficients_positive
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) (hr : 0 < r)
    (hroot : ∀ j, j ≤ 2*m → 1 < offsetSplitRoot ξ δ j)
    (hfar : ∀ j, j ≤ 2*m → offsetSplitRoot ξ δ j < Real.sqrt (1+8*r))
    (hsum : (∑ j ∈ Finset.range (2*m+1), offsetSplitRoot ξ δ j) ≤
      4*r+Real.sqrt (1+8*r)) :
    0 < (arbitrarySplitRawD m ξ r δ).coeff 0 ∧
      DensePositive (paperGeneralNormalizedD m ξ r δ) m ∧
      DensePositive (paperGeneralNormalizedB m ξ r δ) m ∧
      DensePositive (paperGeneralNormalizedA m ξ r δ) (m+1) ∧
      (paperGeneralNormalizedD m ξ r δ).coeff 0 = 1 ∧
      (paperGeneralNormalizedA m ξ r δ).coeff 0 = 1 := by
  have hD := arbitrarySplitRawD_dense_every_positive_source m ξ δ r hr hroot
  have hB := arbitrarySplitRawB_dense_of_global_paper_bounds m ξ δ r hr hroot hfar hsum
  have hd0 := hD.1 0 (by omega)
  have hDn : DensePositive (paperGeneralNormalizedD m ξ r δ) m :=
    paperGeneral_normalized_dense hD hd0
  have hBn : DensePositive (paperGeneralNormalizedB m ξ r δ) m :=
    paperGeneral_normalized_dense hB hd0
  have hAn : DensePositive (paperGeneralNormalizedA m ξ r δ) (m+1) :=
    dense_inventory_product hDn
  have hDzero : (paperGeneralNormalizedD m ξ r δ).coeff 0 = 1 := by
    rw [paperGeneralNormalizedD,paperGeneral_normalized_coeff,div_self (ne_of_gt hd0)]
  have hAzero : (paperGeneralNormalizedA m ξ r δ).coeff 0 = 1 := by
    simp [paperGeneralNormalizedA,mul_coeff_zero,hDzero]
  exact ⟨hd0,hDn,hBn,hAn,hDzero,hAzero⟩

/-- The literal rate formulas printed after the common normalization. -/
def paperGeneralNormalizedRates (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (b β γ : Fin (m+1) → ℝ) : Rates (m+1) where
  a i := (b i+γ i*(paperGeneralNormalizedD m ξ r δ).coeff i /
    (paperGeneralNormalizedB m ξ r δ).coeff i)*
    (paperGeneralNormalizedB m ξ r δ).coeff i/(paperGeneralNormalizedA m ξ r δ).coeff i.castSucc
  b := b
  c i := γ i*(paperGeneralNormalizedD m ξ r δ).coeff i /
    (paperGeneralNormalizedB m ξ r δ).coeff i
  alpha i := (β i+γ i)*(paperGeneralNormalizedD m ξ r δ).coeff i /
    (paperGeneralNormalizedA m ξ r δ).coeff i.succ
  beta := β
  gamma := γ

private theorem paperGeneral_rates_ext {n : ℕ} (k l : Rates n)
    (ha : k.a = l.a) (hb : k.b = l.b) (hc : k.c = l.c)
    (hα : k.alpha = l.alpha) (hβ : k.beta = l.beta) (hγ : k.gamma = l.gamma) : k = l := by
  cases k
  cases l
  simp_all

private theorem paperGeneral_state_ext {n : ℕ} (x y : State n)
    (hS : x.S = y.S) (hE : x.E = y.E) (hF : x.F = y.F)
    (hC : x.C = y.C) (hD : x.D = y.D) : x = y := by
  cases x
  cases y
  simp_all

theorem paperGeneralNormalizedRates_eq_actual
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) (b β γ : Fin (m+1) → ℝ)
    (hD : DensePositive (arbitrarySplitRawD m ξ r δ) m)
    (hB : DensePositive (arbitrarySplitRawB m ξ r δ) m) :
    paperGeneralNormalizedRates m ξ r δ b β γ = paperGeneralPrescribedRates m ξ r δ b β γ := by
  have hA := dense_inventory_product hD
  have hd0 := ne_of_gt (hD.1 0 (by omega))
  have hf (i : Fin (m+1)) := paperGeneralPrescribedRates_formulas m ξ r δ b β γ hD hB i
  apply paperGeneral_rates_ext
  · funext i
    dsimp only [paperGeneralNormalizedRates]
    rw [(hf i).1,paperGeneralNormalizedA_coeff]
    simp only [paperGeneralNormalizedD,paperGeneralNormalizedB,paperGeneral_normalized_coeff]
    field_simp [hd0,ne_of_gt (hB.1 i (by omega)),ne_of_gt (hA.1 i.castSucc (by omega))]
  · rfl
  · funext i
    dsimp only [paperGeneralNormalizedRates]
    rw [(hf i).2.2.1]
    simp only [paperGeneralNormalizedD,paperGeneralNormalizedB,paperGeneral_normalized_coeff]
    field_simp [hd0,ne_of_gt (hB.1 i (by omega))]
  · funext i
    dsimp only [paperGeneralNormalizedRates]
    rw [(hf i).2.2.2.1,paperGeneralNormalizedA_coeff]
    simp only [paperGeneralNormalizedD,paperGeneral_normalized_coeff]
    field_simp [hd0,ne_of_gt (hA.1 i.succ (by omega))]
  · rfl
  · funext i
    exact ((hf i).2.2.2.2.2).symm

def paperGeneralNormalizedState (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (j : Fin (2*m+1)) : State (m+1) :=
  let x := offsetSplitRoot ξ δ j.val
  reconstruct (fun i => (paperGeneralNormalizedA m ξ r δ).coeff i)
    (fun i => (paperGeneralNormalizedB m ξ r δ).coeff i)
    (fun i => (paperGeneralNormalizedD m ξ r δ).coeff i)
    (ratio x) (rootS x ((paperGeneralNormalizedD m ξ r δ).eval (ratio x))) (rootF x)

/-- Normalizing D rescales the scalar free-substrate coordinate exactly
by D_raw(0), as required by the manuscript's source parameterization. -/
theorem paperGeneralNormalized_rootS
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) (j : Fin (2*m+1))
    (hD : DensePositive (arbitrarySplitRawD m ξ r δ) m)
    (hx : 1 < offsetSplitRoot ξ δ j.val) :
    rootS (offsetSplitRoot ξ δ j.val)
      ((paperGeneralNormalizedD m ξ r δ).eval (ratio (offsetSplitRoot ξ δ j.val))) =
        (arbitrarySplitRawD m ξ r δ).coeff 0 * rootS (offsetSplitRoot ξ δ j.val)
          ((arbitrarySplitRawD m ξ r δ).eval (ratio (offsetSplitRoot ξ δ j.val))) := by
  have hd0 := ne_of_gt (hD.1 0 (by omega))
  have hu := ne_of_gt (ratio_pos hx)
  have hd := ne_of_gt (hD.eval_pos (ratio_pos hx))
  rw [paperGeneralNormalizedD,paperGeneral_normalized_eval]
  unfold rootS
  field_simp [hd0,hu,hd]

private theorem paperGeneral_reconstruct_normalized_eq {n : ℕ}
    (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ) (d u s f : ℝ) (hd : d ≠ 0) :
    reconstruct (fun i => t i/d) (fun i => B i/d) (fun i => D i/d) u (d*s) f =
      reconstruct t B D u s f := by
  apply paperGeneral_state_ext
  · funext i
    dsimp only [reconstruct]
    field_simp [hd]
  · rfl
  · rfl
  · funext i
    dsimp only [reconstruct]
    field_simp [hd]
  · funext i
    dsimp only [reconstruct]
    field_simp [hd]

/-- Every concentration in the literal normalized state is identical
to the state used for exact exhaustion, rationality, Jacobian parity,
and full-parameter persistence. -/
theorem paperGeneralNormalizedState_eq_actual
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) (j : Fin (2*m+1))
    (hD : DensePositive (arbitrarySplitRawD m ξ r δ) m)
    (hx : 1 < offsetSplitRoot ξ δ j.val) :
    paperGeneralNormalizedState m ξ r δ j = arbitrarySplitFiniteState m ξ r δ j := by
  unfold paperGeneralNormalizedState
  dsimp only
  rw [paperGeneralNormalized_rootS m ξ r δ j hD hx]
  simp only [paperGeneralNormalizedA_coeff,paperGeneralNormalizedB,paperGeneralNormalizedD,
    paperGeneral_normalized_coeff]
  exact paperGeneral_reconstruct_normalized_eq _ _ _ _ _ _ _
    (ne_of_gt (hD.1 0 (by omega)))

/-- Exact equivalence between the manuscript's r>u_j condition and the
square-root form used by the coefficient theorem. Positivity of r is
derived from any one prescribed root; it is not an added paper premise. -/
theorem paperGeneralRoot_published_r_bounds
    (m : ℕ) (x : Fin (2*m+1) → ℝ) (r : ℝ) (hroot : ∀ j, 1 < x j) :
    (∀ j, ratio (x j) < r) ↔ (0 < r ∧ ∀ j, x j < Real.sqrt (1+8*r)) := by
  constructor
  · intro hrRoots
    refine ⟨lt_trans (ratio_pos (hroot ⟨0,by omega⟩)) (hrRoots ⟨0,by omega⟩), ?_⟩
    intro j
    apply Real.lt_sqrt_of_sq_lt
    have h := hrRoots j
    dsimp [ratio] at h
    linarith
  · rintro ⟨_hr,hfar⟩ j
    have hsq := (Real.lt_sqrt (show 0 ≤ x j by linarith [hroot j])).mp (hfar j)
    dsimp [ratio]
    linarith

theorem paperGeneralRoot_maximal_count_of_published_hypotheses
    (m : ℕ) (x : Fin (2*m+1) → ℝ) (r : ℝ) (b β γ : Fin (m+1) → ℝ)
    (hroot : ∀ j, 1 < x j) (hordered : StrictMono x)
    (hrRoots : ∀ j, ratio (x j) < r)
    (hsum : (∑ j, x j) ≤ 4*r+Real.sqrt (1+8*r))
    (hb : ∀ i, 0 < b i) (hβ : ∀ i, 0 < β i) (hγ : ∀ i, 0 < γ i) :
    (paperGeneralRootRates m x r b β γ).Positive ∧
      {z : State (m+1) | z.Positive ∧ Equilibrium (paperGeneralRootRates m x r b β γ) z ∧
        InClass (2*r) 2 (2*(r+1)) z} = Set.range (paperGeneralRootState m x r) ∧
      {z : State (m+1) | z.Positive ∧ Equilibrium (paperGeneralRootRates m x r b β γ) z ∧
        InClass (2*r) 2 (2*(r+1)) z}.ncard = 2*m+1 ∧
      ∀ j : Fin (2*m+1), (paperGeneralRootState m x r j).Positive ∧
        Equilibrium (paperGeneralRootRates m x r b β γ) (paperGeneralRootState m x r j) ∧
        InClass (2*r) 2 (2*(r+1)) (paperGeneralRootState m x r j) ∧
        (paperGeneralRootState m x r j).E / (paperGeneralRootState m x r j).F = ratio (x j) ∧
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1)) (paperGeneralRootRates m x r b β γ)
          (toCoordinateSpace (chart (paperGeneralRootState m x r j)))).det ≠ 0 := by
  have hadmit := (paperGeneralRoot_published_r_bounds m x r hroot).mp hrRoots
  exact paperGeneralRoot_maximal_count m x r b β γ hroot hordered hadmit.1 hadmit.2 hsum hb hβ hγ

theorem paperGeneralRoot_open_maximal_count_of_published_hypotheses
    (m : ℕ) (x : Fin (2*m+1) → ℝ) (r : ℝ) (b β γ : Fin (m+1) → ℝ)
    (hroot : ∀ j, 1 < x j) (hordered : StrictMono x)
    (hrRoots : ∀ j, ratio (x j) < r)
    (hsum : (∑ j, x j) ≤ 4*r+Real.sqrt (1+8*r))
    (hb : ∀ i, 0 < b i) (hβ : ∀ i, 0 < β i) (hγ : ∀ i, 0 < γ i) :
    let p₀ : CapacityParameter (m+1) :=
      (rateVector (paperGeneralRootRates m x r b β γ), (2*r,2,2*(r+1)))
    ∃ s : Set (CapacityParameter (m+1)), IsOpen s ∧ p₀ ∈ s ∧
      ∀ p ∈ s, ((ratesFromVector p.1).Positive ∧
        0 < p.2.1 ∧ 0 < p.2.2.1 ∧ 0 < p.2.2.2) ∧
        ∃ u : Fin (2*(m+1)-1) → CoordinateSpace (m+1), Function.Injective u ∧
          (∀ j, (unChart p.2.1 p.2.2.1 p.2.2.2 (ofCoordinateSpace (u j))).Positive ∧
            capacityParameterField (p,u j) = 0 ∧
            (restrictedJacobianMatrix p.2.1 p.2.2.1 p.2.2.2
              (ratesFromVector p.1) (u j)).det ≠ 0) ∧
          {z : State (m+1) | z.Positive ∧ Equilibrium (ratesFromVector p.1) z ∧
            InClass p.2.1 p.2.2.1 p.2.2.2 z} =
              Set.range (fun j => unChart p.2.1 p.2.2.1 p.2.2.2
                (ofCoordinateSpace (u j))) ∧
          {z : State (m+1) | z.Positive ∧ Equilibrium (ratesFromVector p.1) z ∧
            InClass p.2.1 p.2.2.1 p.2.2.2 z}.ncard = 2*(m+1)-1 := by
  have hadmit := (paperGeneralRoot_published_r_bounds m x r hroot).mp hrRoots
  exact paperGeneralRoot_open_maximal_count m x r b β γ hroot hordered hadmit.1 hadmit.2 hsum hb hβ hγ

theorem paperGeneralRoot_odd_positive_real_eigenvalue_multiplicity_of_published_hypotheses
    (m : ℕ) (x : Fin (2*m+1) → ℝ) (r : ℝ) (b β γ : Fin (m+1) → ℝ)
    (hroot : ∀ j, 1 < x j) (hordered : StrictMono x)
    (hrRoots : ∀ j, ratio (x j) < r)
    (hsum : (∑ j, x j) ≤ 4*r+Real.sqrt (1+8*r))
    (hb : ∀ i, 0 < b i) (hβ : ∀ i, 0 < β i) (hγ : ∀ i, 0 < γ i)
    (j : Fin (2*m+1)) (hodd : Odd j.val) :
    Odd (((restrictedJacobianMatrix (2*r) 2 (2*(r+1)) (paperGeneralRootRates m x r b β γ)
      (toCoordinateSpace (chart (paperGeneralRootState m x r j)))).charpoly.roots.filter
        (fun z : ℝ => 0 < z)).card) := by
  have hadmit := (paperGeneralRoot_published_r_bounds m x r hroot).mp hrRoots
  exact paperGeneralRoot_odd_positive_real_eigenvalue_multiplicity m x r b β γ hroot hordered hadmit.1 hadmit.2 hsum hb hβ hγ j hodd

end
end PhosphorylationStableCapacity
