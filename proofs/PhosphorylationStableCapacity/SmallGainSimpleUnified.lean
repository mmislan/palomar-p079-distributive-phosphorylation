module
public import proofs.PhosphorylationStableCapacity.SaddleSmallGainRows
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Finset.Sum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.FinCases

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! ## BlockUnipotentSimilarity -/

namespace PhosphorylationStableCapacity

noncomputable section
open Matrix

/-- An eigenvector graph gives an upper block triangular conjugate by a
unipotent shear. The lower block is a rank-one update. -/
theorem block_unipotent_charpoly
    {σ ι : Type*} [Fintype σ] [DecidableEq σ]
    [Fintype ι] [DecidableEq ι]
    (A : Matrix σ σ ℂ) (B : Matrix σ ι ℂ)
    (C : Matrix ι σ ℂ) (H : Matrix ι ι ℂ)
    (U : Matrix ι σ ℂ)
    (heigen : C + H * U = U * (A + B * U)) :
    (fromBlocks A B C H).charpoly =
      (fromBlocks (A + B * U) B 0 (H - U * B)).charpoly := by
  let S : Matrix (σ ⊕ ι) (σ ⊕ ι) ℂ := fromBlocks 1 0 U 1
  let T : Matrix (σ ⊕ ι) (σ ⊕ ι) ℂ := fromBlocks 1 0 (-U) 1
  have hST : S * T = 1 := by
    simp [S, T, fromBlocks_multiply, ← fromBlocks_one]
  have hconj : T * fromBlocks A B C H * S =
      fromBlocks (A + B * U) B 0 (H - U * B) := by
    simp only [S, T, fromBlocks_multiply, Matrix.mul_one,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
      add_zero, zero_add, Matrix.neg_mul]
    have hb : -(U * A) + C + (-(U * B) + H) * U = 0 := by
      have he := heigen
      rw [Matrix.mul_add] at he
      rw [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_assoc]
      calc
        _ = (C + H * U) - (U * A + U * (B * U)) := by abel
        _ = 0 := by rw [he, sub_self]
    rw [hb]
    simp [sub_eq_add_neg, add_comm]
  calc
    (fromBlocks A B C H).charpoly =
        ((S * T) * fromBlocks A B C H).charpoly := by rw [hST, one_mul]
    _ = (T * fromBlocks A B C H * S).charpoly := by
      rw [mul_assoc]
      exact Matrix.charpoly_mul_comm S (T * fromBlocks A B C H)
    _ = (fromBlocks (A + B * U) B 0 (H - U * B)).charpoly := by rw [hconj]

end
end PhosphorylationStableCapacity

/-! ## BlockUpperSimpleRoot -/

namespace PhosphorylationStableCapacity

noncomputable section
open Polynomial Matrix

/-- An upper block triangular matrix has a simple head eigenvalue whenever
that value is absent from the lower block. -/
theorem block_upper_head_root_simple {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (x : ℂ) (b : Matrix (Fin 1) ι ℂ) (H : Matrix ι ι ℂ)
    (hH : H.charpoly.eval x ≠ 0) :
    (Matrix.fromBlocks (!![x]) b 0 H).charpoly.derivative.eval x ≠ 0 := by
  have hhead : ((!![x]) : Matrix (Fin 1) (Fin 1) ℂ).charpoly = X - C x := by
    simp [Matrix.charpoly, Matrix.charmatrix]
  rw [Matrix.charpoly_fromBlocks_zero₂₁, hhead]
  simpa [Polynomial.derivative_mul, Polynomial.eval_add,
    Polynomial.eval_mul] using hH

end
end PhosphorylationStableCapacity

/-! ## RowDominantCharpolyHalfplane -/

namespace PhosphorylationStableCapacity

noncomputable section

/-- A complex matrix whose Gershgorin rows lie strictly left of the imaginary
axis has no characteristic root in the closed right half-plane. -/
theorem row_dominant_charpoly_no_nonnegative_root
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (μ : ℝ) (hμ : 0 < μ)
    (hrow : ∀ i, (H i i).re +
      ∑ j ∈ (Finset.univ : Finset ι).erase i, ‖H i j‖ ≤ -μ)
    (z : ℂ) (hz : 0 ≤ z.re) : H.charpoly.eval z ≠ 0 := by
  intro hroot
  have heig : Module.End.HasEigenvalue (Matrix.toLin' H) z := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,
      Matrix.charpoly_toLin']
    exact hroot
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball heig
  have hnorm : ‖z - H i i‖ ≤
      ∑ j ∈ (Finset.univ : Finset ι).erase i, ‖H i j‖ := by
    simpa only [mem_closedBall_iff_norm', norm_sub_rev] using hi
  have hre : z.re - (H i i).re ≤ ‖z - H i i‖ := by
    simpa using Complex.re_le_norm (z - H i i)
  linarith [hrow i]

end
end PhosphorylationStableCapacity

/-! ## RankOneRowMargin -/

namespace PhosphorylationStableCapacity

noncomputable section

/-- The stable block stays strictly row dominant after the eigenvector shear
when the feedback gain is smaller than the original row margin. -/
theorem rank_one_row_margin
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (u b : ι → ℂ) (μ W B : ℝ)
    (hrow : ∀ i, (H i i).re +
      ∑ j ∈ (Finset.univ : Finset ι).erase i, ‖H i j‖ ≤ -μ)
    (hu : ∀ i, ‖u i‖ ≤ W) (hW : 0 ≤ W)
    (hb : (∑ j, ‖b j‖) ≤ B) (_hgain : B * W < μ) :
    ∀ i, (H i i - u i * b i).re +
      ∑ j ∈ (Finset.univ : Finset ι).erase i,
        ‖H i j - u i * b j‖ ≤ -(μ - B * W) := by
  intro i
  have hdiag : (H i i - u i * b i).re ≤
      (H i i).re + ‖u i‖ * ‖b i‖ := by
    calc
      (H i i - u i * b i).re = (H i i).re + (-(u i * b i)).re := by
        simp only [Complex.sub_re, Complex.neg_re]
        ring
      _ ≤ (H i i).re + ‖-(u i * b i)‖ :=
        add_le_add_right (Complex.re_le_norm _) _
      _ = (H i i).re + ‖u i‖ * ‖b i‖ := by simp
  have hoff :
      (∑ j ∈ (Finset.univ : Finset ι).erase i,
        ‖H i j - u i * b j‖) ≤
      (∑ j ∈ (Finset.univ : Finset ι).erase i, ‖H i j‖) +
        ‖u i‖ * (∑ j ∈ (Finset.univ : Finset ι).erase i, ‖b j‖) := by
    calc
      _ ≤ ∑ j ∈ (Finset.univ : Finset ι).erase i,
          (‖H i j‖ + ‖u i * b j‖) :=
        Finset.sum_le_sum (fun j _ => norm_sub_le _ _)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [norm_mul, ← Finset.mul_sum]
  have hsplit : ‖b i‖ +
      ∑ j ∈ (Finset.univ : Finset ι).erase i, ‖b j‖ =
      ∑ j : ι, ‖b j‖ := by
    exact Finset.add_sum_erase (Finset.univ : Finset ι)
      (fun j => ‖b j‖) (Finset.mem_univ i)
  have hnonneg : 0 ≤ ∑ j : ι, ‖b j‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hgainBound : ‖u i‖ * (∑ j : ι, ‖b j‖) ≤ B * W := by
    calc
      _ ≤ W * (∑ j : ι, ‖b j‖) :=
        mul_le_mul_of_nonneg_right (hu i) hnonneg
      _ ≤ W * B := mul_le_mul_of_nonneg_left hb hW
      _ = B * W := mul_comm _ _
  have hs := congrArg (fun t : ℝ => ‖u i‖ * t) hsplit
  rw [mul_add] at hs
  linarith [hrow i]

end
end PhosphorylationStableCapacity

/-! ## BlockSmallGainSimpleRoot -/

namespace PhosphorylationStableCapacity

noncomputable section
open Matrix

/-- The small-gain bound also makes the right-half-plane eigenvalue simple:
shearing along its normalized eigenvector leaves a strictly stable lower block. -/
theorem block_small_gain_simple_root {n : ℕ} [NeZero n]
    (a x : ℂ) (b c u : Fin n → ℂ) (H : Matrix (Fin n) (Fin n) ℂ)
    (μ W Bbound : ℝ) (_hμ : 0 < μ) (hW : 0 ≤ W)
    (hrow : ∀ i, (H i i).re +
      ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, ‖H i j‖ ≤ -μ)
    (hu : ∀ i, ‖u i‖ ≤ W)
    (hb : (∑ j : Fin n, ‖b j‖) ≤ Bbound)
    (hgain : Bbound * W < μ)
    (hhead : x = a + ∑ j : Fin n, b j * u j)
    (hlower : ∀ i, x * u i = c i + ∑ j : Fin n, H i j * u j)
    (hx : 0 ≤ x.re) :
    (fromBlocks (!![a]) (fun _ j => b j)
      (fun i _ => c i) H).charpoly.derivative.eval x ≠ 0 := by
  let A : Matrix (Fin 1) (Fin 1) ℂ := !![a]
  let B : Matrix (Fin 1) (Fin n) ℂ := fun _ j => b j
  let C : Matrix (Fin n) (Fin 1) ℂ := fun i _ => c i
  let U : Matrix (Fin n) (Fin 1) ℂ := fun i _ => u i
  have hheadMatrix : A + B * U = !![x] := by
    ext i j
    fin_cases i
    fin_cases j
    simp only [Matrix.add_apply, Matrix.mul_apply]
    simpa [A, B, U] using hhead.symm
  have hlowerMatrix : C + H * U = U * (!![x]) := by
    ext i j
    fin_cases j
    simp only [Matrix.add_apply, Matrix.mul_apply]
    simpa [C, U, mul_comm] using (hlower i).symm
  have heigen : C + H * U = U * (A + B * U) := by
    rw [hheadMatrix]
    exact hlowerMatrix
  have hmargin : 0 < μ - Bbound * W := by linarith
  have hrow' : ∀ i, ((H - U * B) i i).re +
      ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        ‖(H - U * B) i j‖ ≤ -(μ - Bbound * W) := by
    have h := rank_one_row_margin H u b μ W Bbound hrow hu hW hb hgain
    intro i
    have hUB (j k : Fin n) : (U * B) j k = u j * b k := by
      rw [Matrix.mul_apply]
      simp [U, B]
    simpa only [Matrix.sub_apply, hUB] using h i
  have hH : (H - U * B).charpoly.eval x ≠ 0 :=
    row_dominant_charpoly_no_nonnegative_root
      (H - U * B) (μ - Bbound * W) hmargin hrow' x hx
  change (fromBlocks A B C H).charpoly.derivative.eval x ≠ 0
  rw [show (fromBlocks A B C H).charpoly =
      (fromBlocks (A + B * U) B 0 (H - U * B)).charpoly from
        block_unipotent_charpoly A B C H U heigen,
      hheadMatrix]
  exact block_upper_head_root_simple x B (H - U * B) hH

end
end PhosphorylationStableCapacity

/-! ## SaddleSmallGainEigenvector -/

namespace PhosphorylationStableCapacity

noncomputable section
open Matrix

private theorem right_block_eigenvector_equations {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (v : Fin (n + 1) → ℂ) (z : ℂ)
    (hev : M *ᵥ v = z • v) :
    z * v 0 = M 0 0 * v 0 + ∑ j : Fin n, M 0 j.succ * v j.succ ∧
    ∀ i : Fin n,
      z * v i.succ = M i.succ 0 * v 0 +
        ∑ j : Fin n, M i.succ j.succ * v j.succ := by
  constructor
  · have hi := congrFun hev 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      mul_comm, mul_left_comm, mul_assoc] using hi.symm
  · intro i
    have hi := congrFun hev i.succ
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      mul_comm, mul_left_comm, mul_assoc] using hi.symm

private theorem right_block_stable_equation {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (c w : ι → ℂ) (z t : ℂ)
    (heq : ∀ i, z * w i = c i * t + ∑ j, H i j * w j) :
    ∀ i, (z - H i i) * w i =
      (∑ j ∈ (Finset.univ : Finset ι).erase i, H i j * w j) + c i * t := by
  intro i
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset ι)
    (fun j => H i j * w j) (Finset.mem_univ i)
  have hi := heq i
  rw [← hsplit] at hi
  ring_nf at hi ⊢
  linear_combination hi

private theorem right_block_head_ne_zero {n : ℕ} [NeZero n]
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (v : Fin (n + 1) → ℂ) (z : ℂ) (μ : ℝ)
    (hμ : 0 < μ) (hz : 0 ≤ z.re)
    (hrow : ∀ i : Fin n,
      (M i.succ i.succ).re +
        ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          ‖M i.succ j.succ‖ ≤ -μ)
    (hv : v ≠ 0) (hev : M *ᵥ v = z • v) : v 0 ≠ 0 := by
  intro h0
  obtain ⟨_, hstable⟩ := right_block_eigenvector_equations M v z hev
  let H : Matrix (Fin n) (Fin n) ℂ := fun i j => M i.succ j.succ
  let w : Fin n → ℂ := fun i => v i.succ
  have heq : ∀ i, z * w i = (0 : ℂ) * (0 : ℂ) + ∑ j, H i j * w j := by
    intro i
    simpa [H, w, h0] using hstable i
  have hbound := rowResolvent_max_bound H (fun _ => (0 : ℂ)) w
    z 0 μ 0 hμ hz (by simpa [H] using hrow)
    (by simp) (right_block_stable_equation H (fun _ => (0 : ℂ)) w z 0 heq)
  have hw (i : Fin n) : w i = 0 := by
    have hi := hbound i
    have : ‖w i‖ = 0 := by nlinarith [norm_nonneg (w i)]
    exact norm_eq_zero.mp this
  apply hv
  funext i
  cases i using Fin.cases with
  | zero => exact h0
  | succ i => exact hw i

private theorem normalized_right_block_equations {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (v : Fin (n + 1) → ℂ) (z : ℂ)
    (h0 : v 0 ≠ 0) (hev : M *ᵥ v = z • v) :
    ∃ w : Fin n → ℂ,
      z = M 0 0 + ∑ j, M 0 j.succ * w j ∧
      ∀ i, z * w i = M i.succ 0 +
        ∑ j, M i.succ j.succ * w j := by
  let u : Fin (n + 1) → ℂ := (v 0)⁻¹ • v
  have hu0 : u 0 = 1 := by simp [u, smul_eq_mul, h0]
  have hueig : M *ᵥ u = z • u := by
    dsimp [u]
    rw [Matrix.mulVec_smul, hev]
    exact SMulCommClass.smul_comm _ _ _
  obtain ⟨hhead, hstable⟩ := right_block_eigenvector_equations M u z hueig
  refine ⟨fun i => u i.succ, ?_, ?_⟩
  · simpa [hu0] using hhead
  · intro i
    simpa [hu0] using hstable i

/-- A right-half-plane characteristic root has a normalized eigenvector with
explicit stable-block coordinate bounds under the small-gain row premises. -/
theorem bounded_right_block_eigenvector {n : ℕ} [NeZero n]
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (μ C W : ℝ) (hμ : 0 < μ)
    (hrow : ∀ i : Fin n,
      (M i.succ i.succ).re +
        ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          ‖M i.succ j.succ‖ ≤ -μ)
    (hc : ∀ i : Fin n, ‖M i.succ 0‖ ≤ C)
    (hCW : C ≤ μ * W)
    (z : ℂ) (hz : 0 ≤ z.re)
    (hroot : M.charpoly.eval z = 0) :
    ∃ w : Fin n → ℂ,
      (z = M 0 0 + ∑ j, M 0 j.succ * w j) ∧
      (∀ i, z * w i = M i.succ 0 +
        ∑ j, M i.succ j.succ * w j) ∧
      (∀ i, ‖w i‖ ≤ W) := by
  have heig : Module.End.HasEigenvalue (Matrix.toLin' M) z := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,
      Matrix.charpoly_toLin']
    exact hroot
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  have hev : M *ᵥ v = z • v := hv.apply_eq_smul
  obtain ⟨w, hhead, hstable⟩ := normalized_right_block_equations M v z
    (right_block_head_ne_zero M v z μ hμ hz hrow hv.2 hev) hev
  let H : Matrix (Fin n) (Fin n) ℂ := fun i j => M i.succ j.succ
  let c : Fin n → ℂ := fun i => M i.succ 0
  have heq : ∀ i, (z - H i i) * w i =
      (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        H i j * w j) + c i := by
    simpa [H, c] using right_block_stable_equation H c w z 1
      (by intro i; simpa [H, c] using hstable i)
  have hbound := rowResolvent_max_bound H c w z 1 μ C hμ hz
    (by simpa [H] using hrow) (by simpa [c] using hc)
    (by intro i; simpa using heq i)
  refine ⟨w, hhead, hstable, ?_⟩
  intro i
  have hi := hbound i
  have hi' : μ * ‖w i‖ ≤ μ * W := le_trans (by simpa using hi) hCW
  exact (mul_le_mul_iff_of_pos_left hμ).mp hi'

end
end PhosphorylationStableCapacity

/-! ## BlockFinReindex -/

namespace PhosphorylationStableCapacity

open Matrix

/-- Explicit head/tail equivalence for a finite matrix. -/
def headTailIndexEquiv (n : ℕ) : Fin (n + 1) ≃ Fin 1 ⊕ Fin n where
  toFun := Fin.cases (Sum.inl 0) Sum.inr
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv i := by
    cases i using Fin.cases with
    | zero => rfl
    | succ i => rfl
  right_inv x := by
    cases x with
    | inl i => fin_cases i; rfl
    | inr i => rfl

@[simp] theorem headTailIndexEquiv_symm_inl (n : ℕ) (i : Fin 1) :
    (headTailIndexEquiv n).symm (Sum.inl i) = 0 := by
  fin_cases i
  rfl

@[simp] theorem headTailIndexEquiv_symm_inr (n : ℕ) (i : Fin n) :
    (headTailIndexEquiv n).symm (Sum.inr i) = i.succ := rfl

/-- The `Fin (n+1)` matrix and its explicit `1+n` block presentation have
identical characteristic polynomials. -/
theorem headTail_charpoly_eq_fromBlocks {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    M.charpoly =
      (fromBlocks (!![M 0 0]) (fun (_ : Fin 1) (j : Fin n) => M 0 j.succ)
        (fun (i : Fin n) (_ : Fin 1) => M i.succ 0) (fun (i j : Fin n) => M i.succ j.succ)).charpoly := by
  have hmatrix : Matrix.reindex (headTailIndexEquiv n)
      (headTailIndexEquiv n) M =
      fromBlocks (!![M 0 0]) (fun (_ : Fin 1) (j : Fin n) => M 0 j.succ)
        (fun (i : Fin n) (_ : Fin 1) => M i.succ 0) (fun (i j : Fin n) => M i.succ j.succ) := by
    ext i j
    cases i with
    | inl a =>
        fin_cases a
        cases j with
        | inl b => fin_cases b; simp [Matrix.reindex_apply, Matrix.fromBlocks]
        | inr b => simp [Matrix.reindex_apply, Matrix.fromBlocks]
    | inr a =>
        cases j with
        | inl b => fin_cases b; simp [Matrix.reindex_apply, Matrix.fromBlocks]
        | inr b => simp [Matrix.reindex_apply, Matrix.fromBlocks]
  calc
    M.charpoly = (Matrix.reindex (headTailIndexEquiv n)
        (headTailIndexEquiv n) M).charpoly :=
      (Matrix.charpoly_reindex _ _).symm
    _ = _ := by rw [hmatrix]

end PhosphorylationStableCapacity

/-! ## SaddleSmallGainSimpleSpectrum -/

namespace PhosphorylationStableCapacity

noncomputable section
open Matrix

/-- The same quantitative small-gain premises that isolate the sole possible
right-half-plane spectral point also make it algebraically simple. -/
theorem block_spectrum_simple_right {n : ℕ} [NeZero n]
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (μ C W B : ℝ) (hμ : 0 < μ)
    (hrow : ∀ i : Fin n,
      (M i.succ i.succ).re +
        ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          ‖M i.succ j.succ‖ ≤ -μ)
    (hc : ∀ i : Fin n, ‖M i.succ 0‖ ≤ C)
    (hCW : C ≤ μ * W) (hW : 0 ≤ W)
    (hb : (∑ i : Fin n, ‖M 0 i.succ‖) ≤ B)
    (hgain : B * W < μ)
    (z : ℂ) (hz : 0 ≤ z.re)
    (hroot : M.charpoly.eval z = 0) :
    M.charpoly.derivative.eval z ≠ 0 := by
  obtain ⟨w, hhead, hstable, hw⟩ :=
    bounded_right_block_eigenvector M μ C W hμ hrow hc hCW z hz hroot
  have hsimple := block_small_gain_simple_root
    (M 0 0) z (fun j : Fin n => M 0 j.succ)
    (fun i : Fin n => M i.succ 0) w
    (fun i j : Fin n => M i.succ j.succ)
    μ W B hμ hW (by simpa using hrow) hw
    (by simpa using hb) hgain hhead hstable hz
  rw [headTail_charpoly_eq_fromBlocks M]
  exact hsimple

end
end PhosphorylationStableCapacity
