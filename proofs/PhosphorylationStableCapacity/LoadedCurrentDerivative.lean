module
public import proofs.PhosphorylationStableCapacity.LoadedBindingRealization

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- The inherited literal rate realization balances the two catalytic
currents at every reconstructed state. -/
theorem realize_reconstruct_catalytic_balance {n : ℕ}
    (t : Fin (n + 1) → ℝ) (B D : Fin n → ℝ)
    (u s f : ℝ) (i : Fin n) (hB : B i ≠ 0) :
    (realize t B D).c i * (reconstruct t B D u s f).C i =
      (realize t B D).gamma i * (reconstruct t B D u s f).D i := by
  dsimp [realize, reconstruct]
  field_simp [hB]

/-- One catalytic edge current evaluated on the reversible binding map. -/
def bindingCatalyticCurrent {ι ε : Type*} [Fintype ι]
    (ET FT : ℝ) (p q : ι → ℝ) (left right : ε → ι)
    (kc ky : ε → ℝ) (S : ι → ℝ) (e : ε) : ℝ :=
  kc e * bindingComplex ET p S (left e) -
    ky e * bindingComplex FT q S (right e)

/-- At a balanced edge with common catalytic current `w`, its derivative
is the adjacent substrate difference plus the two enzyme-total corrections. -/
theorem bindingCatalyticCurrent_hasDerivAt_linearPath
    {ι ε : Type*} [Fintype ι]
    (ET FT : ℝ) (p q S σ : ι → ℝ)
    (left right : ε → ι) (kc ky w : ε → ℝ) (e : ε)
    (hET : ET ≠ 0) (hFT : FT ≠ 0)
    (hp : bindingDenominator p S ≠ 0)
    (hq : bindingDenominator q S ≠ 0)
    (hkc : kc e * bindingComplex ET p S (left e) = w e)
    (hky : ky e * bindingComplex FT q S (right e) = w e) :
    HasDerivAt (fun t : ℝ =>
      bindingCatalyticCurrent ET FT p q left right kc ky
        (bindingLinearPath S σ t) e)
      (w e * (σ (left e) - σ (right e) +
        (∑ j, bindingComplex FT q S j * σ j) / FT -
        (∑ j, bindingComplex ET p S j * σ j) / ET)) 0 := by
  have hC := bindingComplex_hasDerivAt_linearPath
    ET p S σ (left e) hET hp
  have hY := bindingComplex_hasDerivAt_linearPath
    FT q S σ (right e) hFT hq
  have h := (hC.const_mul (kc e)).sub (hY.const_mul (ky e))
  have hvalue :
      kc e * (bindingComplex ET p S (left e) *
          (σ (left e) -
            (∑ j, bindingComplex ET p S j * σ j) / ET)) -
        ky e * (bindingComplex FT q S (right e) *
          (σ (right e) -
            (∑ j, bindingComplex FT q S j * σ j) / FT)) =
      w e * (σ (left e) - σ (right e) +
        (∑ j, bindingComplex FT q S j * σ j) / FT -
        (∑ j, bindingComplex ET p S j * σ j) / ET) := by
    rw [← mul_assoc, ← mul_assoc, hkc, hky]
    ring
  rw [hvalue] at h
  have hfun : (fun t : ℝ =>
      bindingCatalyticCurrent ET FT p q left right kc ky
        (bindingLinearPath S σ t) e) =
      (fun t => kc e * bindingComplex ET p (bindingLinearPath S σ t) (left e)) -
        (fun t => ky e * bindingComplex FT q (bindingLinearPath S σ t) (right e)) := by
    funext t
    rfl
  rw [hfun]
  exact h

/-- The balanced-edge derivative written in literal substrate and complex
concentrations, with the binding coefficients recovered from those values. -/
theorem bindingCatalyticCurrent_hasDerivAt_from_concentrations
    {ι ε : Type*} [Fintype ι]
    (ET FT : ℝ) (S C Y σ : ι → ℝ)
    (left right : ε → ι) (kc ky w : ε → ℝ) (e : ε)
    (hS : ∀ j, S j ≠ 0)
    (hET : ET = 1 + ∑ j, C j)
    (hFT : FT = 1 + ∑ j, Y j)
    (hET0 : ET ≠ 0) (hFT0 : FT ≠ 0)
    (hkc : kc e * C (left e) = w e)
    (hky : ky e * Y (right e) = w e) :
    HasDerivAt (fun t : ℝ =>
      bindingCatalyticCurrent ET FT (fun j => C j / S j)
        (fun j => Y j / S j) left right kc ky
        (bindingLinearPath S σ t) e)
      (w e * (σ (left e) - σ (right e) +
        (∑ j, Y j * σ j) / FT - (∑ j, C j * σ j) / ET)) 0 := by
  have hp : bindingDenominator (fun j => C j / S j) S ≠ 0 := by
    rw [bindingDenominator_ratio S C hS, ← hET]
    exact hET0
  have hq : bindingDenominator (fun j => Y j / S j) S ≠ 0 := by
    rw [bindingDenominator_ratio S Y hS, ← hFT]
    exact hFT0
  have hC : bindingComplex ET (fun j => C j / S j) S = C := by
    funext j
    exact bindingComplex_ratio ET S C hS hET hET0 j
  have hY : bindingComplex FT (fun j => Y j / S j) S = Y := by
    funext j
    exact bindingComplex_ratio FT S Y hS hFT hFT0 j
  have h := bindingCatalyticCurrent_hasDerivAt_linearPath ET FT
    (fun j => C j / S j) (fun j => Y j / S j) S σ
    left right kc ky w e hET0 hFT0 hp hq
    (by simpa only [hC] using hkc) (by simpa only [hY] using hky)
  simpa only [hC, hY] using h

end
end PhosphorylationStableCapacity
