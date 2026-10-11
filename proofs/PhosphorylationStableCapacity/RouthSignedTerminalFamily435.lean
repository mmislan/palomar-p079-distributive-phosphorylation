module
public import proofs.PhosphorylationStableCapacity.RouthSignedCriterion435
public import proofs.PhosphorylationStableCapacity.RouthSignedReconstruction435
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial Filter
open scoped Topology

/-- Positive scalar normalization preserves the same literal coefficient
transition cut, including all zero coefficients. -/
theorem signedCoefficientTransition_C_mul
    (p : ℝ[X]) (cut : ℕ) (h : SignedCoefficientTransition p cut)
    (b : ℝ) (hb : 0 < b) : SignedCoefficientTransition (C b*p) cut := by
  obtain ⟨hcut, hconstant, hbelow, habove⟩ := h
  refine ⟨hcut, ?_, ?_, ?_⟩
  · rw [Polynomial.coeff_C_mul]
    exact mul_neg_of_pos_of_neg hb hconstant
  · intro i hi
    rw [Polynomial.coeff_C_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hb.le (hbelow i hi)
  · intro i hi
    rw [Polynomial.coeff_C_mul]
    exact mul_nonneg hb.le (habove i hi)

/-- Normalize the actual terminal family by its common, parameter-independent
positive leading coefficient. Only the original terminal constant varies. -/
def routhNormalizedTerminalFamily (a : ℝ) (cs : List ℝ) (lam : ℝ) : ℝ[X] :=
  C ((a*cs.prod)⁻¹)*routhTerminalFamily a cs lam

/-- Every negative terminal constant in the actual fixed-ratio family has
one simple positive real root and a monic Hurwitz tail after normalization.
The coefficient transition, axis exclusion and neutral boundary are proved
for this same family, so no signed stability/counting criterion is assumed. -/
theorem routhTerminalFamily_normalized_signed_factorization
    (a : ℝ) (ha : 0 < a) (cs : List ℝ) (hcs : ∀ c ∈ cs, 0 < c)
    (lam : ℝ) (hlam : lam < 0) :
    PositiveRealRootHurwitzFactorization (cs.length+1)
      ((routhNormalizedTerminalFamily a cs lam).map (algebraMap ℝ ℂ)) := by
  classical
  let L : ℝ := a*cs.prod
  have hLpos : 0 < L := mul_pos ha (List.prod_pos hcs)
  have hLne : L ≠ 0 := hLpos.ne'
  have hLinvpos : 0 < L⁻¹ := inv_pos.mpr hLpos
  have hLinvCne : (L⁻¹ : ℂ) ≠ 0 := by exact_mod_cast hLinvpos.ne'
  let N : ℝ → ℝ[X] := routhNormalizedTerminalFamily a cs
  have hFstructure (s : ℝ) := routhTerminalFamily_structure a ha cs hcs s
  have hNmonic (s : ℝ) : (N s).Monic := by
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [(hFstructure s).2.1]
    exact inv_mul_cancel₀ hLne
  have hNdegree (s : ℝ) : (N s).natDegree = cs.length+1 := by
    change (C L⁻¹*routhTerminalFamily a cs s).natDegree = cs.length+1
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hLne)]
    exact (hFstructure s).1
  have hNcoeff (n : ℕ) : Continuous (fun s : ℝ => (N s).coeff n) := by
    change Continuous (fun s : ℝ => (C L⁻¹*routhTerminalFamily a cs s).coeff n)
    simp only [Polynomial.coeff_C_mul]
    exact continuous_const.mul (routhTerminalFamily_coeff_continuous a cs n)
  let T := Set.Iio (0 : ℝ)
  let : PreconnectedSpace T := Subtype.preconnectedSpace isPreconnected_Iio
  let P : T → ℝ[X] := fun t => N t.val
  have hPmonic (t : T) : (P t).Monic := hNmonic t.val
  have hPdegree (t : T) : (P t).natDegree = cs.length+1 := hNdegree t.val
  have hPcoeff (n : ℕ) (_hn : n ≤ cs.length+1) :
      Continuous (fun t : T => (P t).coeff n) :=
    (hNcoeff n).comp continuous_subtype_val
  choose cut hcut using
    (fun t : T => routhTerminalFamily_signed_transition a ha cs hcs t.val t.property)
  have htransition (t : T) : SignedCoefficientTransition (P t) (cut t) :=
    signedCoefficientTransition_C_mul (routhTerminalFamily a cs t.val)
      (cut t) (hcut t) L⁻¹ hLinvpos
  have haxis (t : T) (z : ℂ) (hz : z.re = 0) :
      ((P t).map (algebraMap ℝ ℂ)).eval z ≠ 0 := by
    have hno := routhTerminalFamily_no_imaginary_axis_roots
      a cs t.val (ne_of_lt t.property) z hz
    change ((C L⁻¹*routhTerminalFamily a cs t.val).map
      (algebraMap ℝ ℂ)).eval z ≠ 0
    simpa only [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul,
      Polynomial.eval_C, Complex.coe_algebraMap, Complex.ofReal_inv] using
      mul_ne_zero hLinvCne hno
  let l : Filter T := comap (fun t : T => t.val) (𝓝[<] (0 : ℝ))
  let : NeBot l := comap_coe_neBot_of_le_principal (by
    change 𝓝 (0 : ℝ) ⊓ 𝓟 T ≤ 𝓟 T
    exact inf_le_right)
  have hval : Tendsto (fun t : T => t.val) l (𝓝 (0 : ℝ)) :=
    (tendsto_comap : Tendsto (fun t : T => t.val) l (𝓝[<] (0 : ℝ))).mono_right
      nhdsWithin_le_nhds
  have hlimit (n : ℕ) (_hn : n ≤ cs.length+1) :
      Tendsto (fun t : T => (P t).coeff n) l (𝓝 ((N 0).coeff n)) :=
    ((hNcoeff n).tendsto 0).comp hval
  let F₀ := routhTerminalFamily a cs 0
  let q₀ : ℝ[X] := C L⁻¹*F₀.divX
  obtain ⟨hFtaillead, _hFtailconstant, hFtailstable⟩ :=
    routhTerminalFamily_zero_hurwitz_deflation a ha cs hcs
  have hFfactor : F₀ = X*F₀.divX := by
    have hf := Polynomial.X_mul_divX_add F₀
    have hc : F₀.coeff 0 = 0 := (hFstructure 0).2.2.1
    simpa only [hc, Polynomial.C_0, add_zero] using hf.symm
  have hfactor₀ : N 0 = X*q₀ := by
    change C L⁻¹*F₀ = X*(C L⁻¹*F₀.divX)
    calc
      C L⁻¹*F₀ = C L⁻¹*(X*F₀.divX) :=
        congrArg (fun p : ℝ[X] => C L⁻¹*p) hFfactor
      _ = X*(C L⁻¹*F₀.divX) := by ring
  have hq₀lead : 0 < q₀.leadingCoeff := by
    change 0 < (C L⁻¹*F₀.divX).leadingCoeff
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    exact mul_pos hLinvpos hFtaillead
  have hq₀stable (z : ℂ) (hz : (q₀.map (algebraMap ℝ ℂ)).eval z = 0) :
      z.re < 0 := by
    apply hFtailstable z
    have hm : (L⁻¹ : ℂ)*(F₀.divX.map (algebraMap ℝ ℂ)).eval z = 0 := by
      simpa only [q₀, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.eval_mul, Polynomial.eval_C, Complex.coe_algebraMap,
        Complex.ofReal_inv] using hz
    exact (mul_eq_zero.mp hm).resolve_left hLinvCne
  have hall := signed_coefficient_family_factorization_of_neutral_boundary
    P (cs.length+1) (by omega) hPmonic hPdegree hPcoeff cut htransition haxis
      l (N 0) q₀ (hNmonic 0) (hNdegree 0) hlimit hfactor₀ hq₀lead hq₀stable
  exact hall ⟨lam, hlam⟩

end
end PhosphorylationStableCapacity
