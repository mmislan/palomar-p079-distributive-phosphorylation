module
public import proofs.PhosphorylationStableCapacity.RouthPositiveRootContinuity435
public import proofs.PhosphorylationStableCapacity.RouthSignedSeed435

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial Filter
open scoped Topology

private theorem signedCriterion_eval_map_real (p : ℝ[X]) (u : ℝ) :
    (p.map (algebraMap ℝ ℂ)).eval (u : ℂ) = ((p.eval u : ℝ) : ℂ) := by
  simpa only [Complex.coe_algebraMap] using
    (Polynomial.eval_map_apply (p := p) (f := algebraMap ℝ ℂ) u)

/-- The complete connected-family signed argument: coefficient transition
proves and continuously selects the unique simple positive root; a neutral
Hurwitz boundary provides a seed; axis exclusion and the evaluation margin
propagate the actual one-positive-root/Hurwitz-tail factorization. Every
root and polynomial remains in this one family. The terminal reconstruction
will discharge the family hypotheses for the signed Routh criterion. -/
theorem signed_coefficient_family_factorization_of_neutral_boundary
    {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    (P : T → ℝ[X]) (d : ℕ) (hd : 1 ≤ d)
    (hmonic : ∀ t, (P t).Monic) (hdegree : ∀ t, (P t).natDegree = d)
    (hcoeff : ∀ n ≤ d, Continuous (fun t => (P t).coeff n))
    (cut : T → ℕ) (htransition : ∀ t, SignedCoefficientTransition (P t) (cut t))
    (haxis : ∀ t, ∀ z : ℂ, z.re = 0 → ((P t).map (algebraMap ℝ ℂ)).eval z ≠ 0)
    (l : Filter T) [NeBot l] (p₀ q₀ : ℝ[X])
    (hmonic₀ : p₀.Monic) (hdegree₀ : p₀.natDegree = d)
    (hlimit : ∀ n ≤ d, Tendsto (fun t => (P t).coeff n) l (𝓝 (p₀.coeff n)))
    (hfactor₀ : p₀ = X*q₀) (hleading₀ : 0 < q₀.leadingCoeff)
    (hstable₀ : ∀ z : ℂ, (q₀.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0) :
    ∀ t, PositiveRealRootHurwitzFactorization d ((P t).map (algebraMap ℝ ℂ)) := by
  have hleading (t : T) : 0 < (P t).leadingCoeff := by
    rw [(hmonic t).leadingCoeff]
    norm_num
  obtain ⟨u, hu, hrootdata⟩ := signedCoefficientTransition_continuous_simple_positive_root_exists
    P d (fun t => (hdegree t).le) hcoeff cut htransition hleading
  have hupos (t : T) : 0 < u t := (hrootdata t).1
  have huroot (t : T) : (P t).eval (u t) = 0 := (hrootdata t).2.1
  have hunique (t : T) : ∀ v : ℝ, 0 < v → (P t).eval v = 0 → v = u t :=
    (hrootdata t).2.2.2
  have hbrackets : ∀ c : ℝ, 0 < c → ∃ b : ℝ,
      0 < b ∧ b < c ∧ 0 < p₀.eval b := by
    intro c hc
    have hb : 0 < c/2 := by linarith
    refine ⟨c/2, hb, by linarith, ?_⟩
    exact neutral_hurwitz_factor_positive_brackets p₀ q₀ hfactor₀ hleading₀ hstable₀ _ hb
  have hu₀ : Tendsto u l (𝓝 0) :=
    bounded_degree_selected_positive_root_tendsto_zero l P p₀ d
      (fun t => (hdegree t).le) hdegree₀.le hlimit u
      (Eventually.of_forall hupos)
      (Eventually.of_forall (fun t => by
        simpa only [← Polynomial.coeff_zero_eq_eval_zero] using (htransition t).2.1))
      (Eventually.of_forall hunique) hbrackets
  let PC : T → ℂ[X] := fun t => (P t).map (algebraMap ℝ ℂ)
  let pC₀ := p₀.map (algebraMap ℝ ℂ)
  have hPCmonic (t : T) : (PC t).Monic := (hmonic t).map _
  have hPCdegree (t : T) : (PC t).natDegree = d := by
    simpa only [PC, Polynomial.natDegree_map] using hdegree t
  have hpCdegree₀ : pC₀.natDegree = d := by
    simpa only [pC₀, Polynomial.natDegree_map] using hdegree₀
  have hPCcoeff (n : ℕ) (hn : n ≤ d) : Continuous (fun t => (PC t).coeff n) := by
    simpa only [PC, Polynomial.coeff_map, Complex.coe_algebraMap, Function.comp_def] using
      Complex.continuous_ofReal.comp (hcoeff n hn)
  have hPClimit (n : ℕ) (hn : n ≤ d) :
      Tendsto (fun t => (PC t).coeff n) l (𝓝 (pC₀.coeff n)) := by
    simpa only [PC, pC₀, Polynomial.coeff_map, Complex.coe_algebraMap, Function.comp_def] using
      (Complex.continuous_ofReal.tendsto (p₀.coeff n)).comp (hlimit n hn)
  have hPCroot (t : T) : (PC t).eval (u t : ℂ) = 0 := by
    simp only [PC, signedCriterion_eval_map_real, huroot t, Complex.ofReal_zero]
  have hPCsimple (t : T) : (PC t).derivative.eval (u t : ℂ) ≠ 0 := by
    have hnonzero : (((P t).derivative.eval (u t) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (hrootdata t).2.2.1.ne'
    simpa only [PC, Polynomial.derivative_map, signedCriterion_eval_map_real] using hnonzero
  have hPCunique (t : T) (v : ℝ) (hv : 0 < v)
      (hroot : (PC t).eval (v : ℂ) = 0) : v = u t := by
    apply hunique t v hv
    have hcast : (((P t).eval v : ℝ) : ℂ) = 0 := by
      simpa only [PC, signedCriterion_eval_map_real] using hroot
    exact_mod_cast hcast
  have hpCfactor₀ : pC₀ = X*(q₀.map (algebraMap ℝ ℂ)) := by
    dsimp only [pC₀]
    rw [hfactor₀, Polynomial.map_mul, Polynomial.map_X]
  have hpCroot₀ : pC₀.eval (0 : ℂ) = 0 := by rw [hpCfactor₀]; simp
  have hpCtail₀ : ∀ z : ℂ,
      (pC₀ /ₘ (X-C (0 : ℂ))).eval z = 0 → z.re < 0 := by
    rw [Polynomial.C_0, sub_zero, hpCfactor₀, Polynomial.mul_divByMonic_cancel_left _ monic_X]
    exact hstable₀
  have hseed := signed_factorization_eventually_of_boundary_tail l PC pC₀ d hd
    hPCmonic hPCdegree hpCdegree₀ (hmonic₀.map _) hPClimit u 0 hu₀ hPCroot
      (Eventually.of_forall hupos) hpCroot₀ hpCtail₀
  obtain ⟨t₀, ht₀⟩ := hseed.exists
  exact signed_factorization_of_connected_family PC d hd hPCmonic hPCdegree
    hPCcoeff u hu hupos hPCroot hPCsimple hPCunique haxis t₀ ht₀

/-- Nonzero scalar normalization preserves the positive simple root and
every complementary spectral conclusion. This transfers the terminal
family's monic factorization back to the original polynomial. -/
theorem signed_root_classification_of_scalar_normalization
    (p : ℝ[X]) (d : ℕ) (c : ℝ) (hc : c ≠ 0)
    (hf : PositiveRealRootHurwitzFactorization d
      ((C c*p).map (algebraMap ℝ ℂ))) :
    ∃ u : ℝ, 0 < u ∧ (p.map (algebraMap ℝ ℂ)).eval (u : ℂ) = 0 ∧
      (p.map (algebraMap ℝ ℂ)).derivative.eval (u : ℂ) ≠ 0 ∧
      ∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).eval z = 0 → z = (u : ℂ) ∨ z.re < 0 := by
  obtain ⟨u, hu, hroot, hsimple, hclass⟩ :=
    positiveRealRootHurwitzFactorization_root_classification d _ hf
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have heval (z : ℂ) : ((C c*p).map (algebraMap ℝ ℂ)).eval z =
      (c : ℂ)*(p.map (algebraMap ℝ ℂ)).eval z := by
    simp
  have hderiv (z : ℂ) : ((C c*p).map (algebraMap ℝ ℂ)).derivative.eval z =
      (c : ℂ)*(p.map (algebraMap ℝ ℂ)).derivative.eval z := by
    simp [Polynomial.derivative_mul]
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · rw [heval] at hroot
    exact (mul_eq_zero.mp hroot).resolve_left hcC
  · intro hz
    apply hsimple
    rw [hderiv, hz, mul_zero]
  · intro z hz
    apply hclass z
    rw [heval, hz, mul_zero]

end
end PhosphorylationStableCapacity
