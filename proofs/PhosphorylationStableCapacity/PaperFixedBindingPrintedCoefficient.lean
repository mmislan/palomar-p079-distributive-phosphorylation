module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitGenericPrefactorZero435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingRealization435
public import proofs.PhosphorylationStableCapacity.AllCurrentWeightedDerivative435
public import proofs.PhosphorylationStableCapacity.SimpleNeutralPositiveCoefficient435
public import proofs.PhosphorylationStableCapacity.TransverseEigenvalueProduct
public import proofs.PhosphorylationStableCapacity.CoalescedPublishedMoment

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- The manuscript's common positive splitting coefficient for its literal
frozen-binding kinetic realization. The rate-product numerator and
transverse characteristic coefficient are evaluated on the same
coalesced rate vector. -/
def paperFixedBindingPrintedCoefficient
    (m : ℕ) (r τ ε : ℝ) (ω : Fin (m+1) → ℝ) : ℝ :=
  let k := relaxRates
    (paperFixedBindingRates (coalescedAllScaledRates m r
      (Fin.lastCases τ ω))) ε
  let x := coalescedFiniteState (m+1) r
  let C := 2*r*(coalescedPair (m+1)).1.eval r+
    (coalescedPair (m+1)).2.eval r
  let M := kinaseComplexInventory k 1-phosphataseComplexInventory k 1
  let R := ∏ i : Fin (m+2),
    (k.b i+k.c i)*k.alpha i*k.gamma i
  let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k
    (fromLoadedCoord (loadedCoordOfState x))
  ((4*C*M/((r-1)*(coalescedRawD (m+1) r).eval 1))*R) /
    J.charpoly.coeff 1

/-- The literal printed coefficient is the zero-parameter physical
determinant prefactor divided by the simple transverse coefficient.
The right hand side does not depend on the split index. -/
theorem paperFixedBindingPrintedCoefficient_eq_physical_ratio
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (ω : Fin (m+1) → ℝ) (j : Fin (2*(m+1)+1))
    (hr : 1 < r)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hk : (relaxRates
      (paperFixedBindingRates (coalescedAllScaledRates m r
        (Fin.lastCases τ ω))) ε).Positive)
    (hx : (coalescedFiniteState (m+1) r).Positive)
    (heq : Equilibrium
      (relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
      (coalescedFiniteState (m+1) r))
    (hET : totalE (coalescedFiniteState (m+1) r) = 2*r)
    (hFT : totalF (coalescedFiniteState (m+1) r) = 2) :
    arbitrarySplitGenericPhysicalPrefactor m ξ r 0
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε) j /
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (relaxRates (paperFixedBindingRates
            (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
          (fromLoadedCoord (loadedCoordOfState
            (coalescedFiniteState (m+1) r)))).charpoly.coeff 1 =
      paperFixedBindingPrintedCoefficient m r τ ε ω := by
  rw [arbitrarySplitGenericPhysicalPrefactor_zero_eq_printed
    m ξ r _ j hr hD₀ hk hx heq hET hFT]
  rfl

theorem paperFixedBindingPrintedCoefficient_pos
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (ω : Fin (m+1) → ℝ) (j : Fin (2*(m+1)+1))
    (hr : 1 < r)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hk : (relaxRates
      (paperFixedBindingRates (coalescedAllScaledRates m r
        (Fin.lastCases τ ω))) ε).Positive)
    (hx : (coalescedFiniteState (m+1) r).Positive)
    (heq : Equilibrium
      (relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
      (coalescedFiniteState (m+1) r))
    (hET : totalE (coalescedFiniteState (m+1) r) = 2*r)
    (hFT : totalF (coalescedFiniteState (m+1) r) = 2)
    (hspec : SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
        (fromLoadedCoord (loadedCoordOfState
          (coalescedFiniteState (m+1) r))))) :
    0 < paperFixedBindingPrintedCoefficient m r τ ε ω := by
  rw [← paperFixedBindingPrintedCoefficient_eq_physical_ratio
    m ξ r τ ε ω j hr hD₀ hk hx heq hET hFT]
  apply div_pos
  · exact arbitrarySplitGenericPhysicalPrefactor_zero_pos
      m ξ r _ j hr hD₀ hk hx heq hET hFT
  · exact simpleNeutral_real_charpoly_coeff_one_pos _ hspec

/-- Literal Equation (aconst): the denominator is the absolute product
of every nonzero eigenvalue of the actual coalesced complexified class
Jacobian, counted with algebraic multiplicity. -/
theorem paperFixedBindingPrintedCoefficient_eq_published_aconst
    (m : ℕ) (r τ ε : ℝ) (ω : Fin (m+1) → ℝ)
    (hr : 1 < r)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hk : (relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε).Positive)
    (hx : (coalescedFiniteState (m+1) r).Positive)
    (heq : Equilibrium
      (relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
      (coalescedFiniteState (m+1) r))
    (hET : totalE (coalescedFiniteState (m+1) r) = 2*r)
    (hFT : totalF (coalescedFiniteState (m+1) r) = 2)
    (hspec : SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
        (fromLoadedCoord (loadedCoordOfState
          (coalescedFiniteState (m+1) r))))) :
    let k := relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε
    let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k
      (fromLoadedCoord (loadedCoordOfState
        (coalescedFiniteState (m+1) r)))
    let Θ₀ : ℂ := ((J.map (algebraMap ℝ ℂ)).charpoly.roots.erase 0).prod
    let C := 2*r*(coalescedPair (m+1)).1.eval r+
      (coalescedPair (m+1)).2.eval r
    let M := ((coalescedRawB (m+1) r).eval 1 -
      (coalescedRawD (m+1) r).eval 1) /
      (coalescedRawD (m+1) r).coeff 0
    paperFixedBindingPrintedCoefficient m r τ ε ω =
      (4*C*M/((r-1)*(coalescedRawD (m+1) r).eval 1*‖Θ₀‖)) *
        (∏ i : Fin (m+2), (k.b i+k.c i)*k.alpha i*k.gamma i) := by
  dsimp only
  let k := relaxRates (paperFixedBindingRates
    (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε
  let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k
    (fromLoadedCoord (loadedCoordOfState
      (coalescedFiniteState (m+1) r)))
  let p : ℝ[X] := J.charpoly
  let Θ₀ : ℂ := ((J.map (algebraMap ℝ ℂ)).charpoly.roots.erase 0).prod
  have hMpublished :=
    coalesced_inventory_difference_eq_published_M_one
      (m+1) r k hr hD₀ hk hx heq hET hFT
  rw [← hMpublished]
  have hp1 : 0 < J.charpoly.coeff 1 :=
    simpleNeutral_real_charpoly_coeff_one_pos J hspec
  obtain ⟨q, hfactor, hq0, hleft⟩ := hspec
  have hp : p.Monic := J.charpoly_monic
  have hcomplex : p.map (algebraMap ℝ ℂ) = X*q := by
    simpa only [p, Matrix.charpoly_map] using hfactor
  have hp0 : p.coeff 0 = 0 := by
    have h := congrArg (fun u : ℂ[X] => u.coeff 0) hcomplex
    have hcast : ((p.coeff 0 : ℝ) : ℂ) = 0 := by
      simpa only [Polynomial.coeff_map,
        Polynomial.coeff_X_mul_zero, Complex.coe_algebraMap] using h
    exact_mod_cast hcast
  have hΘ : ‖Θ₀‖ = p.coeff 1 := by
    have hroots := zero_root_deflation_multiset p hp hp0
    have hΘeq : Θ₀ = transversePolynomialRootProduct p := by
      dsimp only [Θ₀, transversePolynomialRootProduct]
      rw [Matrix.charpoly_map]
      exact congrArg Multiset.prod hroots
    rw [hΘeq]
    exact simple_neutral_transverse_root_product_norm
      p q hp hp0 hcomplex hleft
  change 0 < p.coeff 1 at hp1
  have hΘne : ‖Θ₀‖ ≠ 0 := by rw [hΘ]; exact ne_of_gt hp1
  have hrne : r-1 ≠ 0 := by linarith
  have hdne : (coalescedRawD (m+1) r).eval 1 ≠ 0 :=
    ne_of_gt (hD₀.eval_pos (by norm_num))
  change ((4*(2*r*(coalescedPair (m+1)).1.eval r+
      (coalescedPair (m+1)).2.eval r)*
      (kinaseComplexInventory k 1-phosphataseComplexInventory k 1) /
      ((r-1)*(coalescedRawD (m+1) r).eval 1)) *
      (∏ i : Fin (m+2), (k.b i+k.c i)*k.alpha i*k.gamma i)) /
      p.coeff 1 =
    (4*(2*r*(coalescedPair (m+1)).1.eval r+
      (coalescedPair (m+1)).2.eval r)*
      (kinaseComplexInventory k 1-phosphataseComplexInventory k 1) /
      ((r-1)*(coalescedRawD (m+1) r).eval 1*‖Θ₀‖)) *
      (∏ i : Fin (m+2), (k.b i+k.c i)*k.alpha i*k.gamma i)
  rw [hΘ]
  field_simp [hrne, hdne, ne_of_gt hp1]

end
end PhosphorylationStableCapacity
