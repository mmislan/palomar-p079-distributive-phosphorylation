module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitStateDifferentiability
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitRetunedSource
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitChartDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- The reduced physical numerator of the characteristic constant term.
    The universal fast-block/current/binding determinant cancellation
    expresses the full Jacobian determinant through this scalar. -/
def arbitrarySplitPhysicalPrefactor
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (j : Fin (2*(m+1)+1)) (δ : ℝ) : ℝ :=
  let x := arbitrarySplitFiniteState (m+1) ξ r δ j
  let k := arbitrarySplitRetunedRates m ξ r τ δ ε
  let y := offsetSplitRoot ξ δ j.val
  let u := ratio y
  let d := (arbitrarySplitRawD (m+1) ξ r δ).eval u
  let ell := (arbitrarySplitRawB (m+1) ξ r δ).eval u / d - r
  let chartFactor := chartConversionMultiplier y (r-u) ell d
  let conversionFactor :=
    4*r*(arbitrarySplitPair (m+1) ξ δ).1.eval r+
      (y-1)*(arbitrarySplitPair (m+1) ξ δ).2.eval r
  let rateProduct := ∏ i : Fin (m+2),
    (k.b i+k.c i)*k.alpha i*k.gamma i
  ((2*r)*2*x.F^(m+2)*rateProduct/(x.S 0*x.E*x.F)) *
    ((x.E/(2*r)-x.F/2)*chartFactor*conversionFactor/((y/4)/u))

/-- All factors outside the chart conversion multiplier are first-order
    differentiable at the coalesced arbitrary-offset system. -/
theorem arbitrarySplitPhysicalPrefactor_differentiableAt_of_chart
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1))
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
    DifferentiableAt ℝ
      (arbitrarySplitPhysicalPrefactor m ξ r τ ε j) 0 := by
  let x : ℝ → State (m+2) :=
    fun δ => arbitrarySplitFiniteState (m+1) ξ r δ j
  let k : ℝ → Rates (m+2) :=
    fun δ => arbitrarySplitRetunedRates m ξ r τ δ ε
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
  have hrate (i : Fin (m+2)) :=
    arbitrarySplitRetunedRates_components_differentiableAt
      m ξ r τ ε hr hD₀ hB₀ i
  have hprod : DifferentiableAt ℝ (fun δ =>
      ∏ i : Fin (m+2),
        ((k δ).b i+(k δ).c i)*(k δ).alpha i*(k δ).gamma i) 0 := by
    apply DifferentiableAt.fun_finsetProd
    intro i hi
    obtain ⟨_, hb, hc, hα, _, hγ⟩ := hrate i
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

end
end PhosphorylationStableCapacity
