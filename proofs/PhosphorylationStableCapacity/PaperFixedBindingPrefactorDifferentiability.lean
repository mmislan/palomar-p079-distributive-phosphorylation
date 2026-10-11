module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingDifferentiability
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitGenericPhysical435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitChartDerivative
public import proofs.PhosphorylationStableCapacity.CoalescedArbitraryPrefactorPositive

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- The physical determinant prefactor is differentiable for any
differentiable kinetic realization of the same split states. -/
theorem arbitrarySplitGenericPhysicalPrefactor_differentiableAt_of_rates
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ)
    (k : ℝ → Rates (m+2))
    (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (_hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1))
    (hk : DifferentiableAt ℝ (fun δ => rateVector (k δ)) 0)
    (hstate0 :
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).S 0 *
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).E *
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).F ≠ 0)
    (hchart : DifferentiableAt ℝ (fun δ =>
      let y := offsetSplitRoot ξ δ j.val
      let u := ratio y
      let d := (arbitrarySplitRawD (m+1) ξ r δ).eval u
      let ell := (arbitrarySplitRawB (m+1) ξ r δ).eval u / d - r
      chartConversionMultiplier y (r-u) ell d) 0) :
    DifferentiableAt ℝ (fun δ =>
      arbitrarySplitGenericPhysicalPrefactor m ξ r δ (k δ) j) 0 := by
  let x : ℝ → State (m+2) :=
    fun δ => arbitrarySplitFiniteState (m+1) ξ r δ j
  let y : ℝ → ℝ := fun δ => offsetSplitRoot ξ δ j.val
  let u : ℝ → ℝ := fun δ => ratio (y δ)
  have hy : Differentiable ℝ y := by
    dsimp [y, offsetSplitRoot]
    fun_prop
  have hu : Differentiable ℝ u := by
    dsimp [u, y, ratio, offsetSplitRoot]
    fun_prop
  obtain ⟨hS, hE, hF, _, _⟩ :=
    arbitrarySplitFiniteState_components_differentiableAt
      (m+1) ξ r hr hD₀ j
  have hrate (q : Fin 6) (i : Fin (m+2)) :
      DifferentiableAt ℝ (fun δ => rateVector (k δ) q i) 0 :=
    (differentiableAt_pi.mp (differentiableAt_pi.mp hk q)) i
  have hprod : DifferentiableAt ℝ (fun δ =>
      ∏ i : Fin (m+2),
        ((k δ).b i+(k δ).c i)*(k δ).alpha i*(k δ).gamma i) 0 := by
    apply DifferentiableAt.fun_finsetProd
    intro i _
    have hb : DifferentiableAt ℝ (fun δ => (k δ).b i) 0 := by
      simpa [rateVector] using hrate 1 i
    have hc : DifferentiableAt ℝ (fun δ => (k δ).c i) 0 := by
      simpa [rateVector] using hrate 2 i
    have hα : DifferentiableAt ℝ (fun δ => (k δ).alpha i) 0 := by
      simpa [rateVector] using hrate 3 i
    have hγ : DifferentiableAt ℝ (fun δ => (k δ).gamma i) 0 := by
      simpa [rateVector] using hrate 5 i
    exact ((hb.add hc).mul hα).mul hγ
  have hconversion : DifferentiableAt ℝ (fun δ =>
      4*r*(arbitrarySplitPair (m+1) ξ δ).1.eval r+
        (y δ-1)*(arbitrarySplitPair (m+1) ξ δ).2.eval r) 0 := by
    have hp := (arbitrarySplitPair_eval_differentiable (m+1) ξ r).1
    have hq := (arbitrarySplitPair_eval_differentiable (m+1) ξ r).2
    exact (((differentiable_const _).mul hp).add
      ((hy.sub (differentiable_const _)).mul hq)).differentiableAt
  have hratio : DifferentiableAt ℝ
      (fun δ => (y δ / 4) / u δ) 0 := by
    have hu0 : u 0 ≠ 0 := by norm_num [u, y, ratio, offsetSplitRoot]
    exact (hy.differentiableAt.div_const 4).div hu.differentiableAt hu0
  have hratio0 : (y 0 / 4) / u 0 ≠ 0 := by
    norm_num [u, y, ratio, offsetSplitRoot]
  have hfirst : DifferentiableAt ℝ (fun δ =>
      ((2*r)*2*(x δ).F^(m+2)*
        (∏ i : Fin (m+2),
          ((k δ).b i+(k δ).c i)*(k δ).alpha i*(k δ).gamma i)) /
        ((x δ).S 0*(x δ).E*(x δ).F)) 0 := by
    exact (((((differentiableAt_const _).mul
      (differentiableAt_const _)).mul (hF.pow (m+2))).mul hprod).div
      (((hS 0).mul hE).mul hF) hstate0)
  have hQ : DifferentiableAt ℝ (fun δ =>
      (x δ).E/(2*r)-(x δ).F/2) 0 :=
    (hE.div_const _).sub (hF.div_const _)
  have hsecond : DifferentiableAt ℝ (fun δ =>
      ((x δ).E/(2*r)-(x δ).F/2) *
        (let yy := y δ
         let uu := u δ
         let d := (arbitrarySplitRawD (m+1) ξ r δ).eval uu
         let ell := (arbitrarySplitRawB (m+1) ξ r δ).eval uu / d - r
         chartConversionMultiplier yy (r-uu) ell d) *
        (4*r*(arbitrarySplitPair (m+1) ξ δ).1.eval r+
          (y δ-1)*(arbitrarySplitPair (m+1) ξ δ).2.eval r) /
        ((y δ/4)/u δ)) 0 :=
    ((hQ.mul hchart).mul hconversion).div hratio hratio0
  exact hfirst.mul hsecond

set_option maxHeartbeats 800000 in
/-- Specialization to the literal frozen-binding split rates. -/
theorem paperFixedBindingSplit_genericPrefactor_differentiableAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (ω : Fin (m+1) → ℝ) (hr : 1 < r)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : (coalescedAllScaledRates m r
      (Fin.lastCases τ ω)).Positive)
    (j : Fin (2*(m+1)+1)) :
    DifferentiableAt ℝ (fun δ =>
      arbitrarySplitGenericPhysicalPrefactor m ξ r δ
        (paperFixedBindingSplitRates m ξ r δ ε
          (Fin.lastCases τ ω)) j) 0 := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_trans zero_lt_one hr)
  have hstate0 := arbitrarySplitFiniteState_zero_mass_den_ne_zero
    m ξ r hD₀ hB₀ j
  have hchart := arbitrarySplitPhysicalChart_differentiableAt
    m ξ r hr hD₀ j
  have hrate : DifferentiableAt ℝ (fun δ => rateVector
      (paperFixedBindingSplitRates m ξ r δ ε
        (Fin.lastCases τ ω))) 0 :=
    paperFixedBindingSplit_rateVector_differentiableAt
      m ξ r τ ε ω hr0 hD₀ hB₀ hbase
  with_reducible
    exact arbitrarySplitGenericPhysicalPrefactor_differentiableAt_of_rates
      m ξ r
      (fun δ => paperFixedBindingSplitRates m ξ r δ ε
        (Fin.lastCases τ ω)) hr0 hD₀ hB₀ j
      hrate hstate0 hchart

end
end PhosphorylationStableCapacity
