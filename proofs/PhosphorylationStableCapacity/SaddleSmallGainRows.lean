module
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open scoped Matrix

/-- A strictly left-row-dominant complex block controls the largest coordinate
of every right-half-plane resolvent solution. -/
theorem rowResolvent_max_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℂ) (c w : ι → ℂ) (z t : ℂ) (μ C : ℝ)
    (hμ : 0 < μ) (hz : 0 ≤ z.re)
    (hrow : ∀ i, (H i i).re +
        ∑ j ∈ (Finset.univ : Finset ι).erase i, ‖H i j‖ ≤ -μ)
    (hc : ∀ i, ‖c i‖ ≤ C)
    (heq : ∀ i, (z - H i i) * w i =
        (∑ j ∈ (Finset.univ : Finset ι).erase i, H i j * w j) + c i * t) :
    ∀ i, μ * ‖w i‖ ≤ C * ‖t‖ := by
  obtain ⟨i₀, _, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) (fun i => ‖w i‖)
      Finset.univ_nonempty
  have hmax' (j : ι) : ‖w j‖ ≤ ‖w i₀‖ := hmax j (Finset.mem_univ j)
  have hnorm :
      ‖z - H i₀ i₀‖ * ‖w i₀‖ ≤
        (∑ j ∈ (Finset.univ : Finset ι).erase i₀, ‖H i₀ j‖) * ‖w i₀‖ +
          C * ‖t‖ := by
    calc
      ‖z - H i₀ i₀‖ * ‖w i₀‖ = ‖(z - H i₀ i₀) * w i₀‖ := by rw [norm_mul]
      _ = ‖(∑ j ∈ (Finset.univ : Finset ι).erase i₀, H i₀ j * w j) + c i₀ * t‖ := by
        rw [heq i₀]
      _ ≤ ‖∑ j ∈ (Finset.univ : Finset ι).erase i₀, H i₀ j * w j‖ +
          ‖c i₀ * t‖ := norm_add_le _ _
      _ ≤ (∑ j ∈ (Finset.univ : Finset ι).erase i₀, ‖H i₀ j‖ * ‖w j‖) +
          ‖c i₀‖ * ‖t‖ := by
        have hs := norm_sum_le ((Finset.univ : Finset ι).erase i₀)
          (fun j => H i₀ j * w j)
        simpa only [norm_mul] using add_le_add_left hs (‖c i₀‖ * ‖t‖)
      _ ≤ (∑ j ∈ (Finset.univ : Finset ι).erase i₀, ‖H i₀ j‖ * ‖w i₀‖) +
          C * ‖t‖ := by
        gcongr
        · exact hmax' _
        · exact hc i₀
      _ = (∑ j ∈ (Finset.univ : Finset ι).erase i₀, ‖H i₀ j‖) * ‖w i₀‖ +
          C * ‖t‖ := by rw [Finset.sum_mul]
  have hre : z.re - (H i₀ i₀).re ≤ ‖z - H i₀ i₀‖ := by
    simpa using Complex.re_le_norm (z - H i₀ i₀)
  have hmain : μ * ‖w i₀‖ ≤ C * ‖t‖ := by
    have hw : 0 ≤ ‖w i₀‖ := norm_nonneg _
    have hprod := mul_le_mul_of_nonneg_right hre hw
    nlinarith [hrow i₀]
  intro i
  exact le_trans (mul_le_mul_of_nonneg_left (hmax' i) hμ.le) hmain

/-- If the stable coordinates vary by at most `W/μ` times the spectral
parameter and the feedback row has size `B`, a strict small-gain inequality
precludes two distinct right-half-plane spectral parameters. -/
theorem rowResolvent_unique_parameter
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℂ) (b w w' : ι → ℂ) (z z' : ℂ) (μ W B : ℝ)
    (hμ : 0 < μ) (hW : 0 ≤ W)
    (hz : 0 ≤ z.re) (hrow : ∀ i, (H i i).re +
      ∑ j ∈ (Finset.univ : Finset ι).erase i, ‖H i j‖ ≤ -μ)
    (hw' : ∀ i, ‖w' i‖ ≤ W)
    (hdiff : ∀ i, (z - H i i) * (w i - w' i) =
      (∑ j ∈ (Finset.univ : Finset ι).erase i, H i j * (w j - w' j)) +
        w' i * (z' - z))
    (hscalar : z - z' = ∑ i, b i * (w i - w' i))
    (hb : (∑ i, ‖b i‖) ≤ B)
    (hgain : B * W < μ) : z = z' := by
  have hbound := rowResolvent_max_bound H w' (fun i => w i - w' i)
    z (z' - z) μ W hμ hz hrow hw' hdiff
  have hsum : ‖z - z'‖ ≤ (∑ i, ‖b i‖) * (W / μ * ‖z' - z‖) := by
    calc
      ‖z - z'‖ = ‖∑ i, b i * (w i - w' i)‖ := by rw [hscalar]
      _ ≤ ∑ i, ‖b i * (w i - w' i)‖ := norm_sum_le _ _
      _ = ∑ i, ‖b i‖ * ‖w i - w' i‖ := by simp only [norm_mul]
      _ ≤ ∑ i, ‖b i‖ * (W / μ * ‖z' - z‖) := by
        gcongr with i
        calc
          ‖w i - w' i‖ ≤ W * ‖z' - z‖ / μ :=
            (le_div_iff₀ hμ).2 (by simpa [mul_comm] using hbound i)
          _ = W / μ * ‖z' - z‖ := by ring
      _ = (∑ i, ‖b i‖) * (W / μ * ‖z' - z‖) := by rw [Finset.sum_mul]
  have hzero : ‖z - z'‖ = 0 := by
    have hnormeq : ‖z' - z‖ = ‖z - z'‖ := norm_sub_rev _ _
    rw [hnormeq] at hsum
    by_contra hn
    have hp : 0 < ‖z - z'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    have hbw : (∑ i, ‖b i‖) * W < μ := by
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hb hW) hgain
    have hdiv : (∑ i, ‖b i‖) * (W / μ) < 1 := by
      calc
        (∑ i, ‖b i‖) * (W / μ) = ((∑ i, ‖b i‖) * W) / μ := by ring
        _ < 1 := (div_lt_iff₀ hμ).2 (by simpa using hbw)
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

end
end PhosphorylationStableCapacity
