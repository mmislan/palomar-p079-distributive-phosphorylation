module
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section
namespace P079UnstableWorkbench
open scoped BigOperators

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [CompleteSpace G] in
/-- Absolute summability of both inputs gives absolute summability of their
actual bilinear double series. -/
theorem bilinear_doubleSeries_summable_norm
    (Q : E →L[ℝ] F →L[ℝ] G) (f : ℕ → E) (g : ℕ → F)
    (hf : Summable fun n => ‖f n‖) (hg : Summable fun n => ‖g n‖) :
    Summable fun ij : ℕ × ℕ => ‖Q (f ij.1) (g ij.2)‖ := by
  have hprod := hf.mul_of_nonneg hg (fun n => norm_nonneg (f n))
    (fun n => norm_nonneg (g n))
  apply Summable.of_nonneg_of_le (fun ij => norm_nonneg _) _ (hprod.mul_left ‖Q‖)
  intro ij
  simpa only [mul_assoc] using Q.le_opNorm₂ (f ij.1) (g ij.2)

/-- A genuine bilinear Cauchy-product identity, with no formal-composition
assumption and no assumed invariant curve. -/
theorem bilinear_tsum_eq_antidiagonal
    [CompleteSpace E] [CompleteSpace F]
    (Q : E →L[ℝ] F →L[ℝ] G) (f : ℕ → E) (g : ℕ → F)
    (hf : Summable fun n => ‖f n‖) (hg : Summable fun n => ‖g n‖) :
    Q (∑' n, f n) (∑' n, g n) =
      ∑' n, ∑ ij ∈ Finset.antidiagonal n, Q (f ij.1) (g ij.2) := by
  have hfg : Summable fun ij : ℕ × ℕ => Q (f ij.1) (g ij.2) :=
    (bilinear_doubleSeries_summable_norm Q f g hf hg).of_norm
  have hsigma : Summable fun x : Σ n : ℕ, Finset.antidiagonal n =>
      Q (f (x.2 : ℕ × ℕ).1) (g (x.2 : ℕ × ℕ).2) :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hfg
  calc
    _ = ∑' i, Q (f i) (∑' j, g j) := (Q.flip (∑' j, g j)).map_tsum hf.of_norm
    _ = ∑' i, ∑' j, Q (f i) (g j) := by
      congr 1
      funext i
      exact (Q (f i)).map_tsum hg.of_norm
    _ = ∑' ij : ℕ × ℕ, Q (f ij.1) (g ij.2) := hfg.tsum_prod.symm
    _ = ∑' x : Σ n : ℕ, Finset.antidiagonal n,
        Q (f (x.2 : ℕ × ℕ).1) (g (x.2 : ℕ × ℕ).2) :=
      (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq
        (fun ij : ℕ × ℕ => Q (f ij.1) (g ij.2))).symm
    _ = ∑' n, ∑ ij ∈ Finset.antidiagonal n, Q (f ij.1) (g ij.2) := by
      rw [hsigma.tsum_sigma]
      congr 1
      funext n
      rw [tsum_fintype]
      change (∑ ij : Finset.antidiagonal n,
        Q (f (ij : ℕ × ℕ).1) (g (ij : ℕ × ℕ).2)) = _
      exact Finset.sum_coe_sort (Finset.antidiagonal n)
        (fun ij : ℕ × ℕ => Q (f ij.1) (g ij.2))

theorem bilinear_tsum_eq_fin_convolution
    [CompleteSpace E] [CompleteSpace F]
    (Q : E →L[ℝ] F →L[ℝ] G) (f : ℕ → E) (g : ℕ → F)
    (hf : Summable fun n => ‖f n‖) (hg : Summable fun n => ‖g n‖) :
    Q (∑' n, f n) (∑' n, g n) =
      ∑' n, ∑ i : Fin (n+1), Q (f i.val) (g (n-i.val)) := by
  rw [bilinear_tsum_eq_antidiagonal Q f g hf hg]
  congr 1
  funext n
  calc
    _ = ∑ i ∈ Finset.range (n+1), Q (f i) (g (n-i)) :=
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
        (fun ij : ℕ × ℕ => Q (f ij.1) (g ij.2)) n
    _ = _ := (Fin.sum_univ_eq_sum_range
      (fun i => Q (f i) (g (n-i))) (n+1)).symm

theorem bilinear_fin_convolution_summable
    (Q : E →L[ℝ] F →L[ℝ] G) (f : ℕ → E) (g : ℕ → F)
    (hf : Summable fun n => ‖f n‖) (hg : Summable fun n => ‖g n‖) :
    Summable fun n => ∑ i : Fin (n+1), Q (f i.val) (g (n-i.val)) := by
  have hfg : Summable fun ij : ℕ × ℕ => Q (f ij.1) (g ij.2) :=
    (bilinear_doubleSeries_summable_norm Q f g hf hg).of_norm
  have hsigma : Summable fun x : Σ n : ℕ, Finset.antidiagonal n =>
      Q (f (x.2 : ℕ × ℕ).1) (g (x.2 : ℕ × ℕ).2) :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hfg
  have hdiag := hsigma.sigma' (fun n => (hasSum_fintype
    (fun ij : Finset.antidiagonal n => Q (f (ij : ℕ × ℕ).1)
      (g (ij : ℕ × ℕ).2))).summable)
  apply hdiag.congr
  intro n
  change (∑' ij : Finset.antidiagonal n,
    Q (f (ij : ℕ × ℕ).1) (g (ij : ℕ × ℕ).2)) = _
  rw [tsum_fintype]
  calc
    _ = ∑ ij ∈ Finset.antidiagonal n, Q (f ij.1) (g ij.2) :=
      Finset.sum_coe_sort (Finset.antidiagonal n)
        (fun ij : ℕ × ℕ => Q (f ij.1) (g ij.2))
    _ = ∑ i ∈ Finset.range (n+1), Q (f i) (g (n-i)) :=
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
        (fun ij : ℕ × ℕ => Q (f ij.1) (g ij.2)) n
    _ = _ := (Fin.sum_univ_eq_sum_range
      (fun i => Q (f i) (g (n-i))) (n+1)).symm

end P079UnstableWorkbench
