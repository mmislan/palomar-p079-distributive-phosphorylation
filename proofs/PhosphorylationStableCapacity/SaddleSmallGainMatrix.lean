module
public import proofs.PhosphorylationStableCapacity.SaddleSmallGainRows
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open Matrix
open scoped Matrix

private theorem block_eigenvector_equations {n : ℕ}
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

private theorem stableRow_equation {ι : Type*} [Fintype ι] [DecidableEq ι]
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

private theorem block_head_ne_zero {n : ℕ} [NeZero n]
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (v : Fin (n + 1) → ℂ) (z : ℂ) (μ : ℝ)
    (hμ : 0 < μ) (hz : 0 ≤ z.re)
    (hrow : ∀ i : Fin n,
      (M i.succ i.succ).re +
        ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          ‖M i.succ j.succ‖ ≤ -μ)
    (hv : v ≠ 0) (hev : M *ᵥ v = z • v) : v 0 ≠ 0 := by
  intro h0
  obtain ⟨_, hstable⟩ := block_eigenvector_equations M v z hev
  let H : Matrix (Fin n) (Fin n) ℂ := fun i j => M i.succ j.succ
  let w : Fin n → ℂ := fun i => v i.succ
  have heq : ∀ i, z * w i = (0 : ℂ) * (0 : ℂ) + ∑ j, H i j * w j := by
    intro i
    simpa [H, w, h0] using hstable i
  have hbound := rowResolvent_max_bound H (fun _ => (0 : ℂ)) w
    z 0 μ 0 hμ hz (by simpa [H] using hrow)
    (by simp) (stableRow_equation H (fun _ => (0 : ℂ)) w z 0 heq)
  have hw (i : Fin n) : w i = 0 := by
    have hi := hbound i
    have : ‖w i‖ = 0 := by nlinarith [norm_nonneg (w i)]
    exact norm_eq_zero.mp this
  apply hv
  funext i
  cases i using Fin.cases with
  | zero => exact h0
  | succ i => exact hw i

private theorem normalized_block_equations {n : ℕ}
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
  obtain ⟨hhead, hstable⟩ := block_eigenvector_equations M u z hueig
  refine ⟨fun i => u i.succ, ?_, ?_⟩
  · simpa [hu0] using hhead
  · intro i
    simpa [hu0] using hstable i

/-- A real or complex block matrix has at most one characteristic root in the
closed right half-plane under a strict row-dominant stable block and a
small-gain feedback inequality. The theorem includes algebraic multiplicity
only through the separate derivative requirement used downstream. -/
theorem block_spectrum_unique_right {n : ℕ} [NeZero n]
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
    (z z' : ℂ) (hz : 0 ≤ z.re) (hz' : 0 ≤ z'.re)
    (hroot : M.charpoly.eval z = 0)
    (hroot' : M.charpoly.eval z' = 0) : z = z' := by
  have hvect (q : ℂ) (hq : 0 ≤ q.re) (hr : M.charpoly.eval q = 0) :
      ∃ w : Fin n → ℂ,
        q = M 0 0 + ∑ j, M 0 j.succ * w j ∧
        ∀ i, q * w i = M i.succ 0 + ∑ j, M i.succ j.succ * w j := by
    have heig : Module.End.HasEigenvalue (Matrix.toLin' M) q := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
      exact hr
    obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
    have hev : M *ᵥ v = q • v := hv.apply_eq_smul
    exact normalized_block_equations M v q
      (block_head_ne_zero M v q μ hμ hq hrow hv.2 hev) hev
  obtain ⟨w, hhead, hstable⟩ := hvect z hz hroot
  obtain ⟨w', hhead', hstable'⟩ := hvect z' hz' hroot'
  let H : Matrix (Fin n) (Fin n) ℂ := fun i j => M i.succ j.succ
  let c : Fin n → ℂ := fun i => M i.succ 0
  let b : Fin n → ℂ := fun i => M 0 i.succ
  have hrow' : ∀ i, (H i i).re +
      ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, ‖H i j‖ ≤ -μ := by
    simpa [H] using hrow
  have hc' : ∀ i, ‖c i‖ ≤ C := by simpa [c] using hc
  have heq' : ∀ i, (z' - H i i) * w' i =
      (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, H i j * w' j) + c i := by
    simpa [H, c] using stableRow_equation H c w' z' 1
      (by intro i; simpa [H, c] using hstable' i)
  have hw' : ∀ i, ‖w' i‖ ≤ W := by
    have hbound := rowResolvent_max_bound H c w' z' 1 μ C hμ hz'
      hrow' hc' (by simpa using heq')
    intro i
    have hi := hbound i
    have hi' : μ * ‖w' i‖ ≤ μ * W := le_trans (by simpa using hi) hCW
    exact (mul_le_mul_iff_of_pos_left hμ).mp hi'
  have hdiff0 : ∀ i, z * (w i - w' i) =
      w' i * (z' - z) + ∑ j, H i j * (w j - w' j) := by
    intro i
    have hsum : (∑ j, H i j * (w j - w' j)) =
        (∑ j, H i j * w j) - (∑ j, H i j * w' j) := by
      simp [mul_sub, Finset.sum_sub_distrib]
    rw [hsum]
    have h1 := hstable i
    have h2 := hstable' i
    dsimp [H, c] at *
    linear_combination h1 - h2
  have hdiff : ∀ i, (z - H i i) * (w i - w' i) =
      (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        H i j * (w j - w' j)) + w' i * (z' - z) := by
    simpa [add_comm] using stableRow_equation H w' (fun i => w i - w' i)
      z (z' - z) (by intro i; rw [hdiff0 i])
  have hscalar : z - z' = ∑ i, b i * (w i - w' i) := by
    have hsum : (∑ i, b i * (w i - w' i)) =
        (∑ i, b i * w i) - (∑ i, b i * w' i) := by
      simp [mul_sub, Finset.sum_sub_distrib]
    rw [hsum]
    dsimp [b]
    linear_combination hhead - hhead'
  exact rowResolvent_unique_parameter H b w w' z z' μ W B hμ hW hz
    hrow' hw' hdiff hscalar (by simpa [b] using hb) hgain

end
end PhosphorylationStableCapacity
