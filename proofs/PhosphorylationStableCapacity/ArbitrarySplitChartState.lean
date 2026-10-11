module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitChartDerivative
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitRetunedSource

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Filter
open scoped Topology

def arbitrarySplitChartState (m : ℕ) (ξ : ℕ → ℝ)
    (r δ x : ℝ) : State (m+1) :=
  let D := arbitrarySplitRawD m ξ r δ
  let B := arbitrarySplitRawB m ξ r δ
  let u := ratio x
  let d := D.eval u
  let ell := B.eval u / d - r
  reconstruct
    (fun i : Fin (m+2) => (((1+X)*D : ℝ[X]).coeff i))
    (fun i : Fin (m+1) => B.coeff i)
    (fun i : Fin (m+1) => D.coeff i)
    u (chartS u r ell d) (chartF u r ell)

theorem arbitrarySplitChartState_eq_finite_at_root
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (j : Fin (2*m+1))
    (hx : 1 < offsetSplitRoot ξ δ j.val)
    (hd : (arbitrarySplitRawD m ξ r δ).eval
      (ratio (offsetSplitRoot ξ δ j.val)) ≠ 0)
    (hv : r-ratio (offsetSplitRoot ξ δ j.val) ≠ 0) :
    arbitrarySplitChartState m ξ r δ (offsetSplitRoot ξ δ j.val) =
      arbitrarySplitFiniteState m ξ r δ j := by
  let x := offsetSplitRoot ξ δ j.val
  let d := (arbitrarySplitRawD m ξ r δ).eval (ratio x)
  let b := (arbitrarySplitRawB m ξ r δ).eval (ratio x)
  let ell := b/d-r
  have hell : ell = 2*(r-ratio x)/(x-1) :=
    arbitrarySplitChartEll_eq_at_root m ξ r δ j hx hd
  have hvalues := chart_values_at_conversion_root x r d ell hx hd hv hell
  unfold arbitrarySplitChartState arbitrarySplitFiniteState
  dsimp only
  rw [hvalues.1, hvalues.2]

theorem arbitrarySplitChartState_totals
    (m : ℕ) (ξ : ℕ → ℝ) (r δ x : ℝ)
    (hx : 1 < x)
    (hD : DensePositive (arbitrarySplitRawD m ξ r δ) m)
    (hB : DensePositive (arbitrarySplitRawB m ξ r δ) m)
    (hell : (arbitrarySplitRawB m ξ r δ).eval (ratio x) /
      (arbitrarySplitRawD m ξ r δ).eval (ratio x) - r ≠ 0)
    (hellv : (arbitrarySplitRawB m ξ r δ).eval (ratio x) /
      (arbitrarySplitRawD m ξ r δ).eval (ratio x) - ratio x ≠ 0) :
    totalE (arbitrarySplitChartState m ξ r δ x) = 2*r ∧
      totalF (arbitrarySplitChartState m ξ r δ x) = 2 ∧
      totalS (arbitrarySplitChartState m ξ r δ x) - 2*(r+1) =
        arbitrarySplitChartResidual m ξ r δ x := by
  let D := arbitrarySplitRawD m ξ r δ
  let B := arbitrarySplitRawB m ξ r δ
  let A : ℝ[X] := (1+X)*D
  let u := ratio x
  let d := D.eval u
  let b := B.eval u
  let ell := b/d-r
  let s := chartS u r ell d
  let f := chartF u r ell
  have hu : u ≠ 0 := ne_of_gt (ratio_pos hx)
  have hd : d ≠ 0 := ne_of_gt (hD.eval_pos (ratio_pos hx))
  have hell' : ell ≠ 0 := hell
  have hellv' : ell+(r-u) ≠ 0 := by
    convert hellv using 1
    ring
  have hbd : b = d*(r+ell) := by
    dsimp [ell]
    field_simp
    ring
  have halg := chart_totals_algebra u r ell d hu hd hell' hellv'
  dsimp only at halg
  rw [← hbd] at halg
  have hA : DensePositive A (m+1) := dense_inventory_product hD
  have htot := reconstruct_totals
    (fun i : Fin (m+2) => A.coeff i)
    (fun i : Fin (m+1) => B.coeff i)
    (fun i : Fin (m+1) => D.coeff i) u s f
  rw [dense_inventory hB, dense_inventory hD, dense_inventory hA] at htot
  simp only [A, eval_mul, eval_add, eval_one, eval_X] at htot
  change totalE (arbitrarySplitChartState m ξ r δ x) = 2*r ∧
    totalF (arbitrarySplitChartState m ξ r δ x) = 2 ∧
    totalS (arbitrarySplitChartState m ξ r δ x) - 2*(r+1) =
      arbitrarySplitChartResidual m ξ r δ x
  refine ⟨htot.1.trans halg.1, htot.2.1.trans halg.2.1, ?_⟩
  change totalS (reconstruct
    (fun i : Fin (m+2) => (((1+X)*D : ℝ[X]).coeff i))
    (fun i : Fin (m+1) => B.coeff i)
    (fun i : Fin (m+1) => D.coeff i) u s f) - 2*(r+1) =
      arbitrarySplitChartResidual m ξ r δ x
  rw [htot.2.2]
  calc
    s * ((1 + u) * eval u D) +
        u * s * f * (eval u (arbitrarySplitRawB m ξ r δ) +
          eval u (arbitrarySplitRawD m ξ r δ)) - 2 * (r + 1) =
      chartS u r ell d * (1+u) * d +
        u * chartS u r ell d * chartF u r ell * (b+d) - 2*(r+1) := by
          dsimp only [s, f, b, d, D, B]
          ring
    _ = (1+u)*((r-u)/(u*ell)-2*ell/(ell+(r-u))) := halg.2.2
    _ = arbitrarySplitChartResidual m ξ r δ x := rfl

end
end PhosphorylationStableCapacity
