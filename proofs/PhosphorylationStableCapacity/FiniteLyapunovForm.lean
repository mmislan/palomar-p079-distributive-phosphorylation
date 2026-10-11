module
public import Mathlib.Analysis.InnerProductSpace.LinearMap

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The finite quadratic form associated with a positive power of a
continuous linear endomorphism. -/
def finiteLyapunovForm (T : E →L[ℝ] E) (m : ℕ) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ j ∈ Finset.range m,
    (innerSL ℝ).bilinearComp (T^j) (T^j)

theorem finiteLyapunovForm_apply (T : E →L[ℝ] E) (m : ℕ) (v w : E) :
    finiteLyapunovForm T m v w =
       ∑ j ∈ Finset.range m, ⟪(T^j) v, (T^j) w⟫ := by
  simp [finiteLyapunovForm, ContinuousLinearMap.bilinearComp]

/-- The zeroth summand makes the finite form coercive. -/
theorem finiteLyapunovForm_lower (T : E →L[ℝ] E)
    (m : ℕ) (hm : 0 < m) (v : E) :
    ‖v‖^2 ≤ finiteLyapunovForm T m v v := by
  rw [finiteLyapunovForm_apply]
  simp_rw [real_inner_self_eq_norm_sq]
  have hmem : 0 ∈ Finset.range m := Finset.mem_range.mpr hm
  simpa using (Finset.single_le_sum
    (s := Finset.range m) (f := fun j => ‖(T^j) v‖^2)
    (fun j _ => sq_nonneg _) hmem)

/-- The finite operator-norm sum bounds the form from above. -/
theorem finiteLyapunovForm_upper (T : E →L[ℝ] E)
    (m : ℕ) (v : E) :
    finiteLyapunovForm T m v v ≤
      (∑ j ∈ Finset.range m, ‖T^j‖^2) * ‖v‖^2 := by
  rw [finiteLyapunovForm_apply]
  simp_rw [real_inner_self_eq_norm_sq]
  calc
    (∑ j ∈ Finset.range m, ‖(T^j) v‖^2) ≤
        ∑ j ∈ Finset.range m, ‖T^j‖^2 * ‖v‖^2 := by
      apply Finset.sum_le_sum
      intro j _
      have hj := (T^j).le_opNorm v
      have hj2 : ‖(T^j) v‖^2 ≤ (‖T^j‖ * ‖v‖)^2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hj
      simpa only [mul_pow] using hj2
    _ = (∑ j ∈ Finset.range m, ‖T^j‖^2) * ‖v‖^2 := by
      rw [Finset.sum_mul]

/-- Finite telescoping in the indexing form used by the Lyapunov sum. -/
private theorem sum_shift (f : ℕ → ℝ) (m : ℕ) :
    (∑ j ∈ Finset.range m, f (j+1)) + f 0 =
      (∑ j ∈ Finset.range m, f j) + f m := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [Finset.sum_range_succ]
      linarith

private theorem iterate_succ (T : E →L[ℝ] E) (j : ℕ) (v : E) :
    (T^j) (T v) = (T^(j+1)) v := by
  rw [pow_succ]
  rfl

/-- The finite form satisfies the exact discrete Lyapunov identity. -/
theorem finiteLyapunovForm_shift (T : E →L[ℝ] E)
    (m : ℕ) (v : E) :
    finiteLyapunovForm T m (T v) (T v) + ‖v‖^2 =
      finiteLyapunovForm T m v v + ‖(T^m) v‖^2 := by
  rw [finiteLyapunovForm_apply, finiteLyapunovForm_apply]
  simp_rw [real_inner_self_eq_norm_sq, iterate_succ]
  simpa using sum_shift (fun j => ‖(T^j) v‖^2) m

end
end PhosphorylationStableCapacity
