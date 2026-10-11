module
public import proofs.PhosphorylationStableCapacity.SplitRetunedSource
public import proofs.PhosphorylationStableCapacity.SplitConversionResidual
public import proofs.PhosphorylationStableCapacity.GeneralEquilibriumInjection

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Polynomial

/-- Relaxing the binding reactions is reversible when the scale is nonzero. -/
private theorem relaxRates_inverse {n : ℕ} (k : Rates n) {ε : ℝ}
    (hε : ε ≠ 0) : relaxRates (relaxRates k ε) ε⁻¹ = k := by
  cases k with
  | mk a b c alpha beta gamma =>
    simp only [relaxRates]
    congr 1 <;> funext i <;> field_simp <;> ring

private theorem relaxRates_equilibrium_iff {n : ℕ} (k : Rates n)
    (x : State n) {ε : ℝ} (hε : ε ≠ 0) :
    Equilibrium (relaxRates k ε) x ↔ Equilibrium k x := by
  constructor
  · intro h
    have h' := relaxRates_preserves_equilibrium (relaxRates k ε) x
      (inv_ne_zero hε) h
    simpa only [relaxRates_inverse k hε] using h'
  · exact relaxRates_preserves_equilibrium k x hε

private theorem edgeScaledRates_inverse {n : ℕ} (w : Fin n → ℝ)
    (k : Rates n) (hw : ∀ i, w i ≠ 0) :
    edgeScaledRates (fun i => (w i)⁻¹) (edgeScaledRates w k) = k := by
  cases k with
  | mk a b c alpha beta gamma =>
    simp only [edgeScaledRates]
    congr 1 <;> funext i <;> field_simp [hw i]

private theorem edgeScaledRates_preserves_equilibrium {n : ℕ}
    (w : Fin n → ℝ) (k : Rates n) (x : State n)
    (heq : Equilibrium k x) : Equilibrium (edgeScaledRates w k) x := by
  have hC (i : Fin n) : kinaseNet k x i = k.c i * x.C i := by
    have h := heq.2.2.2.1 i
    dsimp [field] at h
    linarith
  have hD (i : Fin n) : phosphataseNet k x i = k.gamma i * x.D i := by
    have h := heq.2.2.2.2 i
    dsimp [field] at h
    linarith
  exact edgeScaledRates_equilibrium w k x hC hD
    (equilibrium_catalytic_balance k x heq)

private theorem edgeScaledRates_equilibrium_iff {n : ℕ}
    (w : Fin n → ℝ) (k : Rates n) (x : State n)
    (hw : ∀ i, w i ≠ 0) :
    Equilibrium (edgeScaledRates w k) x ↔ Equilibrium k x := by
  constructor
  · intro h
    have h' := edgeScaledRates_preserves_equilibrium
      (fun i => (w i)⁻¹) (edgeScaledRates w k) x h
    simpa only [edgeScaledRates_inverse w k hw] using h'
  · exact edgeScaledRates_preserves_equilibrium w k x

private theorem splitRetunedRates_equilibrium_iff_source (m : ℕ)
    (r τ δ ε : ℝ) (hτ : 0 < τ) (hε : ε ≠ 0)
    (x : State (m+2)) :
    Equilibrium (splitRetunedRates m r τ δ ε) x ↔
      Equilibrium (splitFiniteRates (m+1) r δ) x := by
  let w := coalescedFinalCurrentWeights m τ
  have hw : ∀ i, w i ≠ 0 := by
    intro i
    by_cases hi : i = Fin.last (m+1)
    · simp [w, coalescedFinalCurrentWeights, hi, ne_of_gt hτ]
    · simp [w, coalescedFinalCurrentWeights, hi]
  exact (relaxRates_equilibrium_iff _ x hε).trans
    (edgeScaledRates_equilibrium_iff w _ x hw)

/-- A positive equilibrium of a realized rate list has precisely the
reconstructed concentration profile, with the scalar scale fixed by S₀. -/
private theorem realized_positive_equilibrium_eq_reconstruct {n : ℕ}
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

/-- Every positive equilibrium of the realized split source, at the
constructed totals, has one of the prescribed enzyme ratios. -/
private theorem split_source_equilibrium_ratio_is_prescribed
    (m : ℕ) (r δ : ℝ) (hr : 0 < r) (hδ : 0 ≤ δ)
    (hD : DensePositive (splitRawD m r δ) m)
    (hB : DensePositive (splitRawB m r δ) m)
    (x : State (m+1)) (hx : x.Positive)
    (heq : Equilibrium (splitFiniteRates m r δ) x)
    (hET : totalE x = 2*r) (hFT : totalF x = 2)
    (hST : totalS x = 2*(r+1)) :
    ∃ j : Fin (2*m+1), x.E/x.F = ratio (splitRoot δ j.val) := by
  let B := splitRawB m r δ
  let D := splitRawD m r δ
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
    exact realized_positive_equilibrium_eq_reconstruct
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
    have h := hF
    rw [← hsd] at h
    nlinarith [h]
  have hξratio : ratio ξ = u := by
    dsimp [ratio, ξ]
    nlinarith [hquad]
  have hbalance : splitConversionResidual m r δ ξ = 0 := by
    have hξexpr : ξ-1=2*u*f := by dsimp [ξ]; ring
    change (ξ-1)*(B.eval (ratio ξ)-r*D.eval (ratio ξ)) -
      2*(r-ratio ξ)*D.eval (ratio ξ)=0
    rw [hξratio]
    change (ξ-1)*(b-r*d)-2*(r-u)*d=0
    calc
      (ξ-1)*(b-r*d)-2*(r-u)*d =
          2*d*(s*u*(b-r*d)-(r-u)) := by rw [hξexpr, ← hsd]; ring
      _ = 0 := by rw [← hgap]; ring
  have hfac : 0 < 4*r*(splitPair m δ).1.eval r+
      (ξ-1)*(splitPair m δ).2.eval r :=
    conversion_prefactor_pos (splitPair_dense m hδ).1
      (splitPair_dense m hδ).2 hr hξ
  have hfactor := split_conversion_residual_factor m r δ ξ
  change splitConversionResidual m r δ ξ =
    (4*r*(splitPair m δ).1.eval r+
      (ξ-1)*(splitPair m δ).2.eval r) *
        splitScalarProduct m δ ξ at hfactor
  rw [hfactor] at hbalance
  have hprod : splitScalarProduct m δ ξ = 0 :=
    (mul_eq_zero.mp hbalance).resolve_left (ne_of_gt hfac)
  rw [splitScalarProduct_eq_prod_range] at hprod
  obtain ⟨j, hj, hjzero⟩ := Finset.prod_eq_zero_iff.mp hprod
  refine ⟨⟨j, Finset.mem_range.mp hj⟩, ?_⟩
  have hξroot : ξ = splitRoot δ j := sub_eq_zero.mp hjzero
  change u = ratio (splitRoot δ j)
  rw [← hξratio, hξroot]

/-- The retuned split construction has no further positive equilibrium
in its fixed compatibility class. This is a statement about the literal
mass-action vector field with one common rate list and total triple. -/
theorem splitRetuned_positive_equilibria_exact_family
    (m : ℕ) (r τ δ ε : ℝ)
    (hr : 0 < r) (hτ : 0 < τ) (hδ : 0 < δ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD : DensePositive (splitRawD (m+1) r δ) (m+1))
    (hB : DensePositive (splitRawB (m+1) r δ) (m+1)) :
    {x : State (m+2) |
      x.Positive ∧ Equilibrium (splitRetunedRates m r τ δ ε) x ∧
        InClass (2*r) 2 (2*(r+1)) x} =
      Set.range (splitFiniteState (m+1) r δ) := by
  ext x
  constructor
  · rintro ⟨hx, heq, hclass⟩
    have hsource : Equilibrium (splitFiniteRates (m+1) r δ) x :=
      (splitRetunedRates_equilibrium_iff_source m r τ δ ε hτ
        (ne_of_gt hε) x).mp heq
    obtain ⟨j, hjratio⟩ :=
      split_source_equilibrium_ratio_is_prescribed
        (m+1) r δ hr hδ.le hD hB x hx hsource
        hclass.1 hclass.2.1 hclass.2.2
    have hy := splitFiniteState_source_of_conversion_positive
      (m+1) r δ hδ.le hD hB j
    have hroot : 1 < splitRoot δ j.val := by
      have := mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) j.val)
      dsimp [splitRoot]
      linarith
    have hf : rootF (splitRoot δ j.val) ≠ 0 := by
      exact ne_of_gt (div_pos (by norm_num) (by linarith))
    have hyratio :
        (splitFiniteState (m+1) r δ j).E /
          (splitFiniteState (m+1) r δ j).F =
            ratio (splitRoot δ j.val) := by
      unfold splitFiniteState
      exact reconstruct_ratio _ _ _ _ _ _ hf
    have hxy : x = splitFiniteState (m+1) r δ j := by
      apply positive_equilibria_enzyme_ratio_injective
        (splitFiniteRates (m+1) r δ) x
        (splitFiniteState (m+1) r δ j) (by omega)
        hy.1 hx hy.2.1 hsource hy.2.2.1
      · exact hclass.2.1.trans hy.2.2.2.2.1.symm
      · exact hclass.2.2.trans hy.2.2.2.2.2.symm
      · exact hjratio.trans hyratio.symm
    exact ⟨j, hxy.symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨hk, hx, heq, hET, hFT, hST⟩ :=
      splitRetunedState_source_of_conversion_positive
        m r τ δ ε hτ hδ.le hε hε1 hD hB j
    exact ⟨hx, heq, hET, hFT, hST⟩

/-- The same retuned system has exactly `2m+3` positive equilibria in
the specified class; no additional positivity or hyperbolicity
assumption is imposed on a hypothetical equilibrium. -/
theorem splitRetuned_positive_equilibria_ncard
    (m : ℕ) (r τ δ ε : ℝ)
    (hr : 0 < r) (hτ : 0 < τ) (hδ : 0 < δ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD : DensePositive (splitRawD (m+1) r δ) (m+1))
    (hB : DensePositive (splitRawB (m+1) r δ) (m+1)) :
    {x : State (m+2) |
      x.Positive ∧ Equilibrium (splitRetunedRates m r τ δ ε) x ∧
        InClass (2*r) 2 (2*(r+1)) x}.ncard = 2*(m+1)+1 := by
  rw [splitRetuned_positive_equilibria_exact_family
    m r τ δ ε hr hτ hδ hε hε1 hD hB]
  simpa using Set.ncard_range_of_injective (splitFiniteState_injective
    (m+1) r hδ)

end
end PhosphorylationStableCapacity
