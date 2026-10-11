module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitGenericPhysical435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitPhysicalChart
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitStateDifferentiability

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- The common state/chart factor of the exact literal determinant,
independent of the choice of positive kinetics on the same split
states. -/
def arbitrarySplitGeometricFactor
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ)
    (j : Fin (2*(m+1)+1)) (δ : ℝ) : ℝ :=
  let x := arbitrarySplitFiniteState (m+1) ξ r δ j
  let y := offsetSplitRoot ξ δ j.val
  let u := ratio y
  let d := (arbitrarySplitRawD (m+1) ξ r δ).eval u
  let ell := (arbitrarySplitRawB (m+1) ξ r δ).eval u / d - r
  let chartFactor := chartConversionMultiplier y (r-u) ell d
  let conversionFactor :=
    4*r*(arbitrarySplitPair (m+1) ξ δ).1.eval r+
      (y-1)*(arbitrarySplitPair (m+1) ξ δ).2.eval r
  ((2*r)*2*x.F^(m+2)/(x.S 0*x.E*x.F)) *
    ((x.E/(2*r)-x.F/2)*chartFactor*conversionFactor/((y/4)/u))

theorem arbitrarySplitGenericPhysicalPrefactor_eq_geometric_mul_rateProduct
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (k : Rates (m+2)) (j : Fin (2*(m+1)+1)) :
    arbitrarySplitGenericPhysicalPrefactor m ξ r δ k j =
      arbitrarySplitGeometricFactor m ξ r j δ *
        (∏ i : Fin (m+2),
          (k.b i+k.c i)*k.alpha i*k.gamma i) := by
  unfold arbitrarySplitGenericPhysicalPrefactor
    arbitrarySplitGeometricFactor
  ring

/-- The common geometric factor is differentiable at coalescence;
every current-dependent first-order estimate therefore reduces to
the finite physical rate product. -/
theorem arbitrarySplitGeometricFactor_differentiableAt
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ)
    (hr : 1 < r)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1))
    (hstate0 :
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).S 0 *
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).E *
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).F ≠ 0) :
    DifferentiableAt ℝ (arbitrarySplitGeometricFactor m ξ r j) 0 := by
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
      (m+1) ξ r (by linarith) hD₀ j
  have hchart := arbitrarySplitPhysicalChart_differentiableAt
    m ξ r hr hD₀ j
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
      (2*r)*2*(x δ).F^(m+2) /
        ((x δ).S 0*(x δ).E*(x δ).F)) 0 := by
    exact (((differentiableAt_const _).mul
      (hF.pow (m+2))).div
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
  change DifferentiableAt ℝ
    (fun δ => ((2*r)*2*(x δ).F^(m+2) /
      ((x δ).S 0*(x δ).E*(x δ).F)) *
        (((x δ).E/(2*r)-(x δ).F/2) *
          (let yy := y δ
           let uu := u δ
           let d := (arbitrarySplitRawD (m+1) ξ r δ).eval uu
           let ell := (arbitrarySplitRawB (m+1) ξ r δ).eval uu / d-r
           chartConversionMultiplier yy (r-uu) ell d) *
          (4*r*(arbitrarySplitPair (m+1) ξ δ).1.eval r+
            (y δ-1)*(arbitrarySplitPair (m+1) ξ δ).2.eval r) /
          ((y δ/4)/u δ))) 0
  exact hfirst.mul hsecond

end

end PhosphorylationStableCapacity
