module
public import proofs.PhosphorylationStableCapacity.HurwitzSchurEuler
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open scoped Matrix.Norms.Frobenius

/-- A Schur complex matrix has a contracting positive power in the
Frobenius norm. -/
theorem schur_matrix_exists_frobenius_contracting_power
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (B : Matrix ι ι ℂ)
    (hroots : ∀ z : ℂ, B.charpoly.eval z = 0 → ‖z‖ < 1) :
    ∃ m : ℕ, 0 < m ∧ ‖B^m‖ < 1 := by
  have hspec : ∀ z ∈ spectrum ℂ B, ‖z‖₊ < (1 : NNReal) := by
    intro z hz
    have hroot : B.charpoly.eval z = 0 :=
      (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz).eq_zero
    exact_mod_cast hroots z hroot
  have hradius : spectralRadius ℂ B < 1 :=
    spectrum.spectralRadius_lt_of_forall_lt B hspec
  have hlimit :=
    spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius B
  have hev : ∀ᶠ m : ℕ in Filter.atTop,
      ENNReal.ofReal (‖B^m‖ ^ (1/(m:ℝ))) < 1 :=
    hlimit.eventually (Iio_mem_nhds hradius)
  obtain ⟨m, hm, hpow⟩ :=
    ((Filter.eventually_ge_atTop (1 : ℕ)).and hev).exists
  have hmpos : 0 < m := hm
  have hrpow : ‖B^m‖ ^ (1/(m:ℝ)) < 1 :=
    ENNReal.ofReal_lt_one.mp hpow
  have hexp : 0 < (1/(m:ℝ)) := by positivity
  exact ⟨m, hmpos,
    (Real.rpow_lt_one_iff' (norm_nonneg _) hexp).mp hrpow⟩

/-- A real Hurwitz matrix has a positive Euler step with a genuinely
real matrix power contracting in Frobenius norm. -/
theorem isHurwitz_exists_real_frobenius_contracting_power
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : IsHurwitz A) :
    ∃ h : ℝ, 0 < h ∧ ∃ m : ℕ, 0 < m ∧
      ‖((1 : Matrix ι ι ℝ) + h • A)^m‖ < 1 := by
  obtain ⟨h, hh, hroots⟩ := isHurwitz_exists_schur_euler_step A hA
  let B : Matrix ι ι ℝ := 1 + h • A
  obtain ⟨m, hm, hcontract⟩ :=
    schur_matrix_exists_frobenius_contracting_power
      (B.map (algebraMap ℝ ℂ)) hroots
  have hnorm : ‖(B.map (algebraMap ℝ ℂ))^m‖ = ‖B^m‖ := by
    rw [← Matrix.map_pow]
    exact Matrix.frobenius_norm_map_eq (B^m)
      (algebraMap ℝ ℂ) (fun a => Complex.norm_real a)
  exact ⟨h, hh, m, hm, hnorm ▸ hcontract⟩

end
end PhosphorylationStableCapacity
