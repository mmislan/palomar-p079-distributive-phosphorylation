module
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega
public import proofs.PhosphorylationStableCapacity.BilinearCauchyProduct435

@[expose] public section
namespace P079UnstableWorkbench
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem scalarSeries_sum_eq (p : FormalMultilinearSeries ℝ ℝ E) (s : ℝ) :
    p.sum s = ∑' n, s^n • p.coeff n := by
  simp only [FormalMultilinearSeries.sum, FormalMultilinearSeries.apply_eq_pow_smul_coeff]

/-- The actual Fréchet derivative of an analytic scalar-input vector series,
with its coefficient formula justified by the convergent derivative series. -/
theorem scalarSeries_derivative_eq
    (p : FormalMultilinearSeries ℝ ℝ E) (s : ℝ) (hs : ‖s‖ₑ < p.radius) :
    fderiv ℝ p.sum s 1 = ∑' n, s^n • ((n+1) • p.coeff (n+1)) := by
  have hds : ‖s‖ₑ < p.derivSeries.radius := hs.trans_le p.radius_le_radius_derivSeries
  calc
    _ = p.derivSeries.sum s 1 := congrArg (fun L : ℝ →L[ℝ] E => L 1) (p.fderiv_sum hs)
    _ = ∑' n, (p.derivSeries n (fun _ => s)) 1 := by
      exact (ContinuousLinearMap.apply ℝ E 1).map_tsum
        (p.derivSeries.summable (by simpa using hds))
    _ = _ := by
      congr 1
      funext n
      rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
        smul_apply, FormalMultilinearSeries.derivSeries_coeff_one]

/-- Finite coefficient equations imply the genuine differential invariance
equation on the disk of convergence. This theorem assumes equations on the
recursively constructible coefficients, not an invariant-curve hypothesis. -/
theorem scalarSeries_quadratic_invariance
    (p : FormalMultilinearSeries ℝ ℝ E) (A : E →L[ℝ] E)
    (Q : E →L[ℝ] E →L[ℝ] E) (lam : ℝ)
    (hcoeff : ∀ n : ℕ, ((n : ℝ)*lam) • p.coeff n = A (p.coeff n) +
      ∑ i : Fin (n+1), Q (p.coeff i.val) (p.coeff (n-i.val)))
    (s : ℝ) (hs : ‖s‖ₑ < p.radius) :
    (lam*s) • fderiv ℝ p.sum s 1 = A (p.sum s) + Q (p.sum s) (p.sum s) := by
  let f : ℕ → E := fun n => s^n • p.coeff n
  let g : ℕ → E := fun n => ((n : ℝ)*lam) • f n
  have hf : Summable fun n => ‖f n‖ := by
    simpa only [f, FormalMultilinearSeries.apply_eq_pow_smul_coeff] using
      p.summable_norm_apply (by simpa using hs)
  have hds : ‖s‖ₑ < p.derivSeries.radius := hs.trans_le p.radius_le_radius_derivSeries
  have hd : Summable fun n => s^n • ((n+1) • p.coeff (n+1)) := by
    have h := (ContinuousLinearMap.apply ℝ E 1).summable
      (p.derivSeries.summable (by simpa using hds))
    simpa only [ContinuousLinearMap.apply_apply,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_apply,
      FormalMultilinearSeries.derivSeries_coeff_one] using h
  have hterm (n : ℕ) :
      (lam*s) • (s^n • ((n+1) • p.coeff (n+1))) = g (n+1) := by
    simp only [g, f, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, pow_succ]
    congr 1
    ring
  have hshift : HasSum (fun n => g (n+1))
      ((lam*s) • fderiv ℝ p.sum s 1) := by
    rw [scalarSeries_derivative_eq p s hs]
    simpa only [hterm] using hd.hasSum.const_smul (lam*s)
  have hleft : HasSum g ((lam*s) • fderiv ℝ p.sum s 1) := by
    simpa only [g, f, Nat.cast_zero, zero_mul, zero_smul, zero_add] using hshift.zero_add
  have hweighted (n : ℕ) : g n = A (f n) +
      ∑ i : Fin (n+1), Q (f i.val) (f (n-i.val)) := by
    dsimp only [g, f]
    rw [smul_comm, hcoeff n, smul_add, A.map_smul, Finset.smul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Q.map_smul, smul_apply, (Q (p.coeff i.val)).map_smul,
      smul_smul, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]
  have hconv := bilinear_fin_convolution_summable Q f f hf hf
  have hright : HasSum g (A (p.sum s) + Q (p.sum s) (p.sum s)) := by
    have ha := hf.of_norm.hasSum.mapL A
    have hc := hconv.hasSum
    rw [← bilinear_tsum_eq_fin_convolution Q f f hf hf] at hc
    have heq : (∑' n, f n) = p.sum s := (scalarSeries_sum_eq p s).symm
    rw [heq] at ha hc
    simpa only [← hweighted] using ha.add hc
  exact hleft.unique hright

end P079UnstableWorkbench
