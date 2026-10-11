module
public import proofs.PhosphorylationStableCapacity.FiniteLyapunovForm

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Bilinear expansion of the Euler-step quadratic energy. -/
theorem finiteLyapunovForm_euler_expand
    (A : E →L[ℝ] E) (h : ℝ) (m : ℕ) (v : E) :
    let T : E →L[ℝ] E := 1 + h • A
    finiteLyapunovForm T m (T v) (T v) =
      finiteLyapunovForm T m v v +
        h * (finiteLyapunovForm T m v (A v) +
          finiteLyapunovForm T m (A v) v) +
        h^2 * finiteLyapunovForm T m (A v) (A v) := by
  dsimp
  simp
  ring

/-- A contracting Euler power gives strict dissipation for the
continuous generator in the same finite quadratic form. -/
theorem finiteLyapunovForm_dissipative_of_contracting_power
    (A : E →L[ℝ] E) (h : ℝ) (m : ℕ) (r : ℝ)
    (hh : 0 < h) (hm : 0 < m) (hr0 : 0 ≤ r)
    (hcontract : ∀ v : E,
      ‖(((1 : E →L[ℝ] E) + h • A)^m) v‖ ≤ r * ‖v‖)
    (v : E) :
    let T : E →L[ℝ] E := 1 + h • A
    finiteLyapunovForm T m v (A v) +
      finiteLyapunovForm T m (A v) v ≤
        -((1-r^2)/h) * ‖v‖^2 := by
  dsimp
  let T : E →L[ℝ] E := 1 + h • A
  have hshift := finiteLyapunovForm_shift T m v
  have hexpand := finiteLyapunovForm_euler_expand A h m v
  have hquad : 0 ≤ finiteLyapunovForm T m (A v) (A v) :=
    le_trans (sq_nonneg _) (finiteLyapunovForm_lower T m hm (A v))
  have hsq : ‖(T^m) v‖^2 ≤ r^2 * ‖v‖^2 := by
    have hb := hcontract v
    have hb2 := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hr0 (norm_nonneg _))).mpr hb
    simpa only [mul_pow] using hb2
  have hnonneg : 0 ≤ h^2 * finiteLyapunovForm T m (A v) (A v) :=
    mul_nonneg (sq_nonneg _) hquad
  have hraw : h * (finiteLyapunovForm T m v (A v) +
      finiteLyapunovForm T m (A v) v) ≤
      -(1-r^2) * ‖v‖^2 := by
    dsimp [T] at hshift hexpand hsq hnonneg ⊢
    nlinarith [hexpand]
  calc
    finiteLyapunovForm T m v (A v) +
        finiteLyapunovForm T m (A v) v ≤
        (-(1-r^2) * ‖v‖^2) / h := by
      apply (le_div_iff₀ hh).mpr
      nlinarith [hraw]
    _ = -((1-r^2)/h) * ‖v‖^2 := by ring

end
end PhosphorylationStableCapacity
