module
public import proofs.PhosphorylationStableCapacity.PaperCoalescedRationalDiagonal435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingRouthAcceptedBranch435
public import proofs.PhosphorylationStableCapacity.PaperAcceptedPrefixCoalescedLimit435

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

open Polynomial Matrix PhosphorylationSharpness Filter
open scoped Topology BigOperators

/-- Finite rational versions of the literal realization operations. -/
def paperOrderedRationalRealize {n : ℕ}
    (T : Fin (n+1) → ℚ) (B D : Fin n → ℚ) : RationalSiteRates n where
  a i := 2*D i/T i.castSucc
  b i := D i/B i
  c i := D i/B i
  alpha i := 2*D i/T i.succ
  beta _ := 1
  gamma _ := 1

def paperOrderedRationalScale {n : ℕ} (w : Fin n → ℚ)
    (k : RationalSiteRates n) : RationalSiteRates n where
  a i := w i*k.a i
  b i := w i*k.b i
  c i := w i*k.c i
  alpha i := w i*k.alpha i
  beta i := w i*k.beta i
  gamma i := w i*k.gamma i

def paperOrderedRationalFixedBinding {n : ℕ}
    (k : RationalSiteRates n) : RationalSiteRates n where
  a i := (1+k.c i)*(k.a i/(k.b i+k.c i))
  b _ := 1
  c := k.c
  alpha i := (1+k.gamma i)*(k.alpha i/(k.beta i+k.gamma i))
  beta _ := 1
  gamma := k.gamma

def paperOrderedRationalRelax {n : ℕ}
    (k : RationalSiteRates n) (ε : ℚ) : RationalSiteRates n where
  a i := k.a i/ε
  b i := (k.b i+k.c i)/ε-k.c i
  c := k.c
  alpha i := k.alpha i/ε
  beta i := (k.beta i+k.gamma i)/ε-k.gamma i
  gamma := k.gamma

noncomputable section

/-- The catalytic factors are frozen from the accepted coalesced state;
the prescribed actual currents are exactly (1,...,1,t). -/
def paperOrderedRationalFactors (m : ℕ) (r t : ℚ) : Fin (m+2) → ℚ :=
  Fin.lastCases (motive := fun _ => ℚ) (t/paperRationalCoalescedComplexD m r (Fin.last (m+1)))
    (fun i => 1/paperRationalCoalescedComplexD m r i.castSucc)

def paperOrderedRationalSplitRates (m : ℕ) (ξ : ℕ → ℚ)
    (r t ε δ : ℚ) : RationalSiteRates (m+2) :=
  paperOrderedRationalRelax (paperOrderedRationalFixedBinding
    (paperOrderedRationalScale (paperOrderedRationalFactors m r t)
      (paperOrderedRationalRealize
        (fun i => ((1+X)*orderedRationalRawD (m+1) ξ r δ).coeff i.val)
        (fun i => (orderedRationalRawB (m+1) ξ r δ).coeff i.val)
        (fun i => (orderedRationalRawD (m+1) ξ r δ).coeff i.val)))) ε

def paperOrderedRationalSplitCoordinate (m : ℕ) (ξ : ℕ → ℚ)
    (r δ : ℚ) (j : Fin (2*(m+1)+1)) : RationalSiteCoordinate (m+2) :=
  let x : ℚ := 3+δ*ξ j.val
  let u : ℚ := (x^2-1)/8
  let s : ℚ := (x-1)/(2*u*(orderedRationalRawD (m+1) ξ r δ).eval u)
  let f : ℚ := 4/(x+1)
  ((fun i => ((1+X)*orderedRationalRawD (m+1) ξ r δ).coeff i.succ.val*u^i.succ.val*s),
    ((fun i => (orderedRationalRawB (m+1) ξ r δ).coeff i.val*u^(i.val+1)*s*f),
      (fun i => (orderedRationalRawD (m+1) ξ r δ).coeff i.val*u^(i.val+1)*s*f)))

/-- Actual finite rational class characteristic polynomial. No polynomial
or matrix witness is selected nonconstructively after a spectral success. -/
def paperOrderedRouthPolynomial (m : ℕ) (ξ : ℕ → ℚ)
    (a b c : ℕ) (j : Fin (2*(m+1)+1)) (δ : ℚ) : ℚ[X] :=
  let r : ℚ := 2^a
  let t : ℚ := (1/2)^b
  let ε : ℚ := (1/2)^c
  (rationalJacobianMatrix (2*r) 2 (2*(r+1))
    (paperOrderedRationalSplitRates m ξ r t ε δ)
    (paperOrderedRationalSplitCoordinate m ξ r δ j)).charpoly

def paperOrderedRationalCurrentJacobian (m : ℕ) (r : ℚ) :
    Matrix (Fin (m+2)) (Fin (m+3)) ℚ :=
  fun i k => paperRationalCoalescedComplexD m r i*
    ((if k = i.castSucc then 1 else 0)-(if k = i.succ then 1 else 0)+
      (paperRationalYLevel m r k/2-paperRationalCLevel m r k/(2*r)))

def paperOrderedRationalFullForcing (m : ℕ) :
    Matrix (Fin (m+3)) (Fin (m+2)) ℚ :=
  fun k j => (if k = j.succ then 1 else 0)-(if k = j.castSucc then 1 else 0)

def paperOrderedSlowMatrix (m a b : ℕ) : Matrix (Fin (m+2)) (Fin (m+2)) ℚ :=
  let r : ℚ := 2^a
  let t : ℚ := (1/2)^b
  paperOrderedRationalCurrentJacobian m r*
    paperRationalAdjugateInverse (paperRationalFullMass m r)*
    paperOrderedRationalFullForcing m*Matrix.diagonal (paperOrderedRationalFactors m r t)

def paperOrderedSlowRouthAccepts (m a b : ℕ) : Bool :=
  rationalNeutralMatrixRouthAccepts (paperOrderedSlowMatrix m a b)

def paperOrderedCoalescedRouthAccepts (m : ℕ) (ξ : ℕ → ℚ) (a b c : ℕ) : Bool :=
  rationalNeutralDeflationRouthAccepts (3*(m+2)-1)
    (paperOrderedRouthPolynomial m ξ a b c 0 0).divX

def paperOrderedSplitRouthAccepts (m : ℕ) (ξ : ℕ → ℚ) (a b c d : ℕ) : Bool :=
  decide (∀ j : Fin (2*(m+1)+1),
    rationalLocalRouthAccepts (3*(m+2))
      (paperOrderedRouthPolynomial m ξ a b c j ((1/2 : ℚ)^d))
      (decide (Odd j.val)) = true)

private theorem paperOrdered_rates_ext {n : ℕ} (k l : Rates n)
    (ha : k.a = l.a) (hb : k.b = l.b) (hc : k.c = l.c)
    (hα : k.alpha = l.alpha) (hβ : k.beta = l.beta) (hγ : k.gamma = l.gamma) : k = l := by
  cases k
  cases l
  simp_all

private theorem paperOrdered_rational_algebraMap_real (q : ℚ) :
    algebraMap ℚ ℝ q = (q : ℝ) := by
  have h : algebraMap ℚ ℝ = Rat.castHom ℝ := Subsingleton.elim _ _
  simpa only [Rat.coe_castHom] using RingHom.congr_fun h q

private theorem paperOrdered_rational_ite_real (p : Prop) [Decidable p] (a b : ℚ) :
    ((if p then a else b : ℚ) : ℝ) = if p then (a : ℝ) else (b : ℝ) := by
  by_cases hp : p <;> simp [hp]

theorem paperOrderedRationalRealize_cast {n : ℕ}
    (T : Fin (n+1) → ℚ) (B D : Fin n → ℚ) :
    (paperOrderedRationalRealize T B D).toReal =
      realize (fun i => (T i : ℝ)) (fun i => (B i : ℝ)) (fun i => (D i : ℝ)) := by
  apply paperOrdered_rates_ext <;> funext i <;> simp [paperOrderedRationalRealize, RationalSiteRates.toReal, realize]

theorem paperOrderedRationalScale_cast {n : ℕ}
    (w : Fin n → ℚ) (k : RationalSiteRates n) :
    (paperOrderedRationalScale w k).toReal = edgeScaledRates (fun i => (w i : ℝ)) k.toReal := by
  apply paperOrdered_rates_ext <;> funext i <;> simp [paperOrderedRationalScale, RationalSiteRates.toReal, edgeScaledRates]

theorem paperOrderedRationalFixedBinding_cast {n : ℕ} (k : RationalSiteRates n) :
    (paperOrderedRationalFixedBinding k).toReal = paperFixedBindingRates k.toReal := by
  apply paperOrdered_rates_ext <;> funext i <;> simp [paperOrderedRationalFixedBinding, RationalSiteRates.toReal,
    paperFixedBindingRates, sourceBindingP_castSucc, sourceBindingQ_succ]

theorem paperOrderedRationalRelax_cast {n : ℕ} (k : RationalSiteRates n) (ε : ℚ) :
    (paperOrderedRationalRelax k ε).toReal = relaxRates k.toReal (ε : ℝ) := by
  apply paperOrdered_rates_ext <;> funext i <;> simp [paperOrderedRationalRelax, RationalSiteRates.toReal, relaxRates]

theorem paperOrderedRationalFactors_cast (m : ℕ) (r t : ℚ) :
    (fun i => (paperOrderedRationalFactors m r t i : ℝ)) =
      Fin.lastCases (motive := fun _ => ℝ) ((t : ℝ)/(coalescedFiniteState (m+1) (r : ℝ)).D (Fin.last (m+1)))
        (fun i => 1/(coalescedFiniteState (m+1) (r : ℝ)).D i.castSucc) := by
  funext i
  cases i using Fin.lastCases with
  | last => simp [paperOrderedRationalFactors, (paperRationalCoalesced_species_cast m r).2.2]
  | cast i => simp [paperOrderedRationalFactors, (paperRationalCoalesced_species_cast m r).2.2]

theorem paperOrderedRationalSplitRates_cast (m : ℕ) (ξ : ℕ → ℚ) (r t ε δ : ℚ) :
    (paperOrderedRationalSplitRates m ξ r t ε δ).toReal =
      paperFixedBindingSplitRates m (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ) (ε : ℝ)
        (Fin.lastCases (motive := fun _ => ℝ) ((t : ℝ)/(coalescedFiniteState (m+1) (r : ℝ)).D (Fin.last (m+1)))
          (fun i => 1/(coalescedFiniteState (m+1) (r : ℝ)).D i.castSucc)) := by
  have hD := orderedRationalRawD_cast (m+1) ξ r δ
  have hB := orderedRationalRawB_cast (m+1) ξ r δ
  have hT : (((1+X)*orderedRationalRawD (m+1) ξ r δ).map (algebraMap ℚ ℝ)) =
      (1+X)*arbitrarySplitRawD (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ) := by
    simp [hD]
  have hDc (i : ℕ) : ((orderedRationalRawD (m+1) ξ r δ).coeff i : ℝ) =
      (arbitrarySplitRawD (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ)).coeff i := by
    simpa only [Polynomial.coeff_map, paperOrdered_rational_algebraMap_real] using congrArg (fun p : ℝ[X] => p.coeff i) hD
  have hBc (i : ℕ) : ((orderedRationalRawB (m+1) ξ r δ).coeff i : ℝ) =
      (arbitrarySplitRawB (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ)).coeff i := by
    simpa only [Polynomial.coeff_map, paperOrdered_rational_algebraMap_real] using congrArg (fun p : ℝ[X] => p.coeff i) hB
  have hTc (i : ℕ) : (((1+X)*orderedRationalRawD (m+1) ξ r δ).coeff i : ℝ) =
      ((1+X)*arbitrarySplitRawD (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ)).coeff i := by
    simpa only [Polynomial.coeff_map, paperOrdered_rational_algebraMap_real] using congrArg (fun p : ℝ[X] => p.coeff i) hT
  simp only [paperOrderedRationalSplitRates, paperOrderedRationalRelax_cast,
    paperOrderedRationalFixedBinding_cast, paperOrderedRationalScale_cast,
    paperOrderedRationalRealize_cast, hTc, hBc, hDc, paperOrderedRationalFactors_cast,
    paperFixedBindingSplitRates, arbitrarySplitFiniteRates]

theorem paperOrderedRationalSplitCoordinate_cast (m : ℕ) (ξ : ℕ → ℚ)
    (r δ : ℚ) (j : Fin (2*(m+1)+1)) :
    (paperOrderedRationalSplitCoordinate m ξ r δ j).toReal =
      toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) (fun i => (ξ i : ℝ)) (r : ℝ) (δ : ℝ) j)) := by
  have hD := orderedRationalRawD_cast (m+1) ξ r δ
  have hB := orderedRationalRawB_cast (m+1) ξ r δ
  have hT : (((1+X)*orderedRationalRawD (m+1) ξ r δ).map (algebraMap ℚ ℝ)) =
      (1+X)*arbitrarySplitRawD (m+1) (fun i => (ξ i : ℝ)) (r : ℝ) (δ : ℝ) := by
    simp [hD]
  have hDc (i : ℕ) : ((orderedRationalRawD (m+1) ξ r δ).coeff i : ℝ) =
      (arbitrarySplitRawD (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ)).coeff i := by
    simpa only [Polynomial.coeff_map, paperOrdered_rational_algebraMap_real] using
      congrArg (fun p : ℝ[X] => p.coeff i) hD
  have hBc (i : ℕ) : ((orderedRationalRawB (m+1) ξ r δ).coeff i : ℝ) =
      (arbitrarySplitRawB (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ)).coeff i := by
    simpa only [Polynomial.coeff_map, paperOrdered_rational_algebraMap_real] using
      congrArg (fun p : ℝ[X] => p.coeff i) hB
  have hTc (i : ℕ) : (((1+X)*orderedRationalRawD (m+1) ξ r δ).coeff i : ℝ) =
      ((1+X)*arbitrarySplitRawD (m+1) (fun j => (ξ j : ℝ)) (r : ℝ) (δ : ℝ)).coeff i := by
    simpa only [Polynomial.coeff_map, paperOrdered_rational_algebraMap_real] using
      congrArg (fun p : ℝ[X] => p.coeff i) hT
  have hdeval (x : ℚ) : (((orderedRationalRawD (m+1) ξ r δ).eval x : ℚ) : ℝ) =
      (arbitrarySplitRawD (m+1) (fun i => (ξ i : ℝ)) (r : ℝ) (δ : ℝ)).eval (x : ℝ) := by
    have hev := Polynomial.eval_map_apply
      (p := orderedRationalRawD (m+1) ξ r δ) (f := algebraMap ℚ ℝ) x
    rw [hD] at hev
    exact hev.symm
  apply Prod.ext
  · funext i
    simp [paperOrderedRationalSplitCoordinate, RationalSiteCoordinate.toReal,
      toCoordinateSpace, chart, arbitrarySplitFiniteState, reconstruct,
      offsetSplitRoot, ratio, rootS, rootF, hTc, hdeval]
  · apply Prod.ext <;> funext i
    · simp [paperOrderedRationalSplitCoordinate, RationalSiteCoordinate.toReal,
        toCoordinateSpace, chart, arbitrarySplitFiniteState, reconstruct,
        offsetSplitRoot, ratio, rootS, rootF, hBc, hdeval]
    · simp [paperOrderedRationalSplitCoordinate, RationalSiteCoordinate.toReal,
        toCoordinateSpace, chart, arbitrarySplitFiniteState, reconstruct,
        offsetSplitRoot, ratio, rootS, rootF, hDc, hdeval]

theorem paperOrderedRouthPolynomial_cast (m : ℕ) (ξ : ℕ → ℚ) (a b c : ℕ)
    (j : Fin (2*(m+1)+1)) (δ : ℚ) :
    (paperOrderedRouthPolynomial m ξ a b c j δ).map (algebraMap ℚ ℝ) =
      paperFixedBindingRouthPolynomial m (fun i => (ξ i : ℝ))
        ((2 : ℚ)^a : ℚ)
        ((((1/2 : ℚ)^b : ℚ) : ℝ)/(coalescedFiniteState (m+1)
          (((2 : ℚ)^a : ℚ) : ℝ)).D (Fin.last (m+1)))
        ((1/2 : ℚ)^c : ℚ) (δ : ℝ)
        (fun i => 1/(coalescedFiniteState (m+1) (((2 : ℚ)^a : ℚ) : ℝ)).D i.castSucc) j := by
  unfold paperOrderedRouthPolynomial
  rw [← Matrix.charpoly_map, rationalJacobianMatrix_cast,
    paperOrderedRationalSplitRates_cast, paperOrderedRationalSplitCoordinate_cast,
    allSiteExplicitFinMatrix_charpoly_eq_restricted]
  simp only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_add, Rat.cast_one,
    paperFixedBindingRouthPolynomial]

theorem paperOrderedSlowMatrix_cast (m a b : ℕ) :
    (paperOrderedSlowMatrix m a b).map (algebraMap ℚ ℝ) =
      coalescedFullLoadedMatrix m (((2 : ℚ)^a : ℚ) : ℝ)*
        Matrix.diagonal (Fin.lastCases (motive := fun _ => ℝ)
          ((((1/2 : ℚ)^b : ℚ) : ℝ)/(coalescedFiniteState (m+1)
            (((2 : ℚ)^a : ℚ) : ℝ)).D (Fin.last (m+1)))
          (fun i => 1/(coalescedFiniteState (m+1) (((2 : ℚ)^a : ℚ) : ℝ)).D i.castSucc)) := by
  let r : ℚ := 2^a
  have hcurrent : (paperOrderedRationalCurrentJacobian m r).map (algebraMap ℚ ℝ) =
      coalescedCurrentJacobianMatrix m (r : ℝ) := by
    obtain ⟨hc,hy⟩ := paperRational_levels_cast m r
    ext i k
    simp [paperOrderedRationalCurrentJacobian, coalescedCurrentJacobianMatrix,
      hc, hy, (paperRationalCoalesced_species_cast m r).2.2,
      paperOrdered_rational_ite_real]
  have hforcing : (paperOrderedRationalFullForcing m).map (algebraMap ℚ ℝ) =
      coalescedFullEdgeForcingMatrix m := by
    ext i j
    simp [paperOrderedRationalFullForcing, coalescedFullEdgeForcingMatrix,
      paperOrdered_rational_ite_real]
  have hdiag (t : ℚ) : (Matrix.diagonal (paperOrderedRationalFactors m r t)).map
      (algebraMap ℚ ℝ) = Matrix.diagonal
        (Fin.lastCases (motive := fun _ => ℝ) ((t : ℝ)/(coalescedFiniteState (m+1) (r : ℝ)).D (Fin.last (m+1)))
          (fun i => 1/(coalescedFiniteState (m+1) (r : ℝ)).D i.castSucc)) := by
    have hm : (Matrix.diagonal (paperOrderedRationalFactors m r t)).map
        (algebraMap ℚ ℝ) = Matrix.diagonal
          (fun i => (paperOrderedRationalFactors m r t i : ℝ)) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
    rw [hm, paperOrderedRationalFactors_cast]
  change ((paperOrderedRationalCurrentJacobian m r*
      paperRationalAdjugateInverse (paperRationalFullMass m r)*
      paperOrderedRationalFullForcing m*Matrix.diagonal
        (paperOrderedRationalFactors m r ((1/2 : ℚ)^b))).map (algebraMap ℚ ℝ)) = _
  rw [Matrix.map_mul, Matrix.map_mul,
    Matrix.map_mul, hcurrent, paperRationalAdjugateInverse_cast,
    paperRationalFullMass_cast, hforcing, hdiag]
  rfl

/-- Completeness of the literal rational matrix test for an actual
simple-neutral Hurwitz complement. This is derived from minor necessity. -/
theorem rationalNeutralMatrixRouthAccepts_of_simpleNeutral
    {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι ℚ)
    (hspec : SimpleNeutralHurwitzComplement (J.map (algebraMap ℚ ℝ))) :
    rationalNeutralMatrixRouthAccepts J = true := by
  have hrealzero := simpleNeutral_real_charpoly_coeff_zero _ hspec
  rw [Matrix.charpoly_map, Polynomial.coeff_map] at hrealzero
  have hzero : J.charpoly.coeff 0 = 0 := by
    rw [paperOrdered_rational_algebraMap_real] at hrealzero
    exact_mod_cast hrealzero
  have hcastDiv : J.charpoly.divX.map (algebraMap ℚ ℝ) =
      (J.map (algebraMap ℚ ℝ)).charpoly.divX := by
    rw [Matrix.charpoly_map]
    ext n
    simp [Polynomial.coeff_divX, Polynomial.coeff_map]
  simp only [rationalNeutralMatrixRouthAccepts, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hzero, ?_⟩
  rw [rationalNeutralDeflationRouthAccepts_iff_real_minors, hcastDiv]
  refine ⟨characteristic_deflation_natDegree _, ?_⟩
  intro k
  exact simpleNeutral_real_charpoly_divX_routh_minors_positive _ hspec (k.val+1) (by omega)

theorem paperOrdered_halving_tendsto_right :
    Tendsto (fun b : ℕ => (1/2 : ℝ)^b) atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num), ?_⟩
  exact Eventually.of_forall (fun b => pow_pos (by norm_num) b)

/-- The second literal loop terminates for EVERY accepted predecessor.
It retains the first accepted source and uses its unit-current factors. -/
theorem paperOrderedSlowRouth_eventually_accepts (m a : ℕ)
    (hprefix : orderedRationalPhysicalPrefixTest m
      (paperRationalPrefixDiagonalAccepts m) a = true) :
    ∀ᶠ b : ℕ in atTop, paperOrderedSlowRouthAccepts m a b = true := by
  obtain ⟨hadmit, haccept⟩ := Bool.and_eq_true_iff.mp hprefix
  have hslow := paperRationalPrefixDiagonal_accepted_eventually_slow_actual_current
    m a hadmit haccept
  have hdyadic := paperOrdered_halving_tendsto_right.eventually hslow
  filter_upwards [hdyadic] with b hb
  apply rationalNeutralMatrixRouthAccepts_of_simpleNeutral
  rw [paperOrderedSlowMatrix_cast]
  simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hb

/-- Every accepted second-loop test supplies the actual slow spectral
premise for the third loop, at the same earlier source/current indices. -/
theorem paperOrderedSlowRouth_accepted_simpleNeutral (m a b : ℕ)
    (haccept : paperOrderedSlowRouthAccepts m a b = true) :
    SimpleNeutralHurwitzComplement
      (coalescedFullLoadedMatrix m (((2 : ℚ)^a : ℚ) : ℝ)*
        Matrix.diagonal (Fin.lastCases (motive := fun _ => ℝ)
          ((((1/2 : ℚ)^b : ℚ) : ℝ)/(coalescedFiniteState (m+1)
            (((2 : ℚ)^a : ℚ) : ℝ)).D (Fin.last (m+1)))
          (fun i => 1/(coalescedFiniteState (m+1) (((2 : ℚ)^a : ℚ) : ℝ)).D i.castSucc))) := by
  have h := rationalNeutralMatrixRouthAccepts_sound (paperOrderedSlowMatrix m a b) haccept
  rwa [paperOrderedSlowMatrix_cast] at h

/-- The third original halving loop accepts for every accepted source
and slow predecessor, keeping their actual common catalytic factors. -/
theorem paperOrderedCoalescedRouth_eventually_accepts
    (m : ℕ) (ξ : ℕ → ℚ) (a b : ℕ)
    (hprefix : orderedRationalPhysicalPrefixTest m
      (paperRationalPrefixDiagonalAccepts m) a = true)
    (hslow : paperOrderedSlowRouthAccepts m a b = true) :
    ∀ᶠ c : ℕ in atTop, paperOrderedCoalescedRouthAccepts m ξ a b c = true := by
  let r : ℚ := 2^a
  let t : ℚ := (1/2)^b
  let x := coalescedFiniteState (m+1) (r : ℝ)
  let w : Fin (m+2) → ℝ := Fin.lastCases (motive := fun _ => ℝ) ((t : ℝ)/x.D (Fin.last (m+1)))
    (fun i => 1/x.D i.castSucc)
  have hadmit : orderedRationalPrefixAdmits m r = true := (Bool.and_eq_true_iff.mp hprefix).1
  have ht : 0 < (t : ℝ) := by
    dsimp [t]
    exact_mod_cast (pow_pos (by norm_num : (0 : ℚ) < 1/2) b)
  have hw : ∀ i, 0 < w i :=
    orderedRationalPrefixAdmits_frozen_factors_positive m r hadmit (t : ℝ) ht
  have hslowActual : SimpleNeutralHurwitzComplement
      (coalescedFullLoadedMatrix m (r : ℝ)*Matrix.diagonal w) :=
    paperOrderedSlowRouth_accepted_simpleNeutral m a b hslow
  have hε := orderedRationalPrefixAdmits_acceptedSlow_eventually_fixedBinding_simpleNeutral
    m r hadmit w hw hslowActual
  have hdyadic := paperOrdered_halving_tendsto_right.eventually hε
  filter_upwards [hdyadic] with c hc
  apply paperFixedBinding_coalesced_rational_routh_accepts_of_simpleNeutral
    m (fun i => (ξ i : ℝ)) (r : ℝ)
    ((t : ℝ)/x.D (Fin.last (m+1))) (((1/2 : ℚ)^c : ℚ) : ℝ)
    (fun i => 1/x.D i.castSucc)
    (paperOrderedRouthPolynomial m ξ a b c)
    (paperOrderedRouthPolynomial_cast m ξ a b c)
  simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc

/-- All original simultaneous odd/even local tests eventually accept for
every admitted source and accepted coalesced predecessor. The same a,b,c
remain frozen when the final distance is halved. -/
theorem paperOrderedSplitRouth_eventually_accepts
    (m : ℕ) (ξ : ℕ → ℚ) (hξ : StrictMono ξ) (a b c : ℕ)
    (hprefix : orderedRationalPhysicalPrefixTest m
      (paperRationalPrefixDiagonalAccepts m) a = true)
    (hcoalesced : paperOrderedCoalescedRouthAccepts m ξ a b c = true) :
    ∀ᶠ d : ℕ in atTop, paperOrderedSplitRouthAccepts m ξ a b c d = true := by
  let r : ℚ := 2^a
  let t : ℚ := (1/2)^b
  let ε : ℚ := (1/2)^c
  let x := coalescedFiniteState (m+1) (r : ℝ)
  let τ : ℝ := (t : ℝ)/x.D (Fin.last (m+1))
  let θ : Fin (m+1) → ℝ := fun i => 1/x.D i.castSucc
  let w : Fin (m+2) → ℝ := Fin.lastCases (motive := fun _ => ℝ) τ θ
  let k₀ := coalescedAllScaledRates m (r : ℝ) w
  let k := relaxRates (paperFixedBindingRates k₀) (ε : ℝ)
  have hadmit : orderedRationalPrefixAdmits m r = true := (Bool.and_eq_true_iff.mp hprefix).1
  obtain ⟨hr, _hrbound, hD, hB⟩ := (orderedRationalPrefixAdmits_iff m r).mp hadmit
  have hdata := orderedRationalPrefixAdmits_physicalData m r hadmit
  have ht : 0 < (t : ℝ) := by
    dsimp [t]
    exact_mod_cast (pow_pos (by norm_num : (0 : ℚ) < 1/2) b)
  have hε : 0 < (ε : ℝ) := by
    dsimp [ε]
    exact_mod_cast (pow_pos (by norm_num : (0 : ℚ) < 1/2) c)
  have hε1 : (ε : ℝ) ≤ 1 := by
    dsimp [ε]
    exact_mod_cast (pow_le_one₀ (by norm_num : (0 : ℚ) ≤ 1/2)
      (by norm_num : (1/2 : ℚ) ≤ 1) : (1/2 : ℚ)^c ≤ 1)
  have hθ : ∀ i, 0 < θ i := by
    intro i
    exact div_pos zero_lt_one (hdata.statePositive.2.2.2.2 i.castSucc)
  have hτ : 0 < τ := div_pos ht (hdata.statePositive.2.2.2.2 (Fin.last (m+1)))
  have hw : ∀ i, 0 < w i :=
    orderedRationalPrefixAdmits_frozen_factors_positive m r hadmit (t : ℝ) ht
  have hbase : k₀.Positive := edgeScaledRates_positive _ _ hw hdata.ratesPositive
  have hphysical := orderedRationalPrefixAdmits_coalesced_actual_currents
    m r hadmit (t : ℝ) (ε : ℝ) ht hε hε1
  have hk : k.Positive := by
    simpa only [k, k₀, w, τ, θ, x, paperFixedBindingSplitRates,
      arbitrarySplitFiniteRates_zero_eq_coalesced, coalescedAllScaledRates] using hphysical.1
  have heq : Equilibrium k x := by
    simpa only [k, k₀, w, τ, θ, x, paperFixedBindingSplitRates,
      arbitrarySplitFiniteRates_zero_eq_coalesced, coalescedAllScaledRates] using hphysical.2.2.1
  have hQ := paperOrderedRouthPolynomial_cast m ξ a b c
  have hspec := paperFixedBinding_accepted_coalesced_branch_simpleNeutral
    m (fun i => (ξ i : ℝ)) (r : ℝ) τ (ε : ℝ) θ
      hθ hr hτ hε hε1 hD hB (paperOrderedRouthPolynomial m ξ a b c) hQ hcoalesced
  have hξR : StrictMono (fun i => (ξ i : ℝ)) := by
    intro i j hij
    change (ξ i : ℝ) < (ξ j : ℝ)
    exact (Rat.cast_lt (K := ℝ)).mpr (hξ hij)
  have hrouth := paperFixedBinding_routh_pattern_eventually_of_simpleNeutral
    m (fun i => (ξ i : ℝ)) hξR (r : ℝ) τ (ε : ℝ) θ
      hθ hr hτ hε hε1 hD hB hbase hk hdata.statePositive heq
      hdata.totalE_eq hdata.totalF_eq hspec
  have hdyadic := paperOrdered_halving_tendsto_right.eventually hrouth
  filter_upwards [hdyadic] with d hd
  simp only [paperOrderedSplitRouthAccepts, decide_eq_true_eq]
  intro j
  rw [rationalLocalRouthAccepts_iff, hQ j ((1/2 : ℚ)^d)]
  simpa only [r, t, ε, τ, θ, x, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hd j

/-- Genuine termination of all four prescribed nested first-success
loops. Every successor argument is universal over the actual accepted
predecessor; the algorithm is not replaced by a favorable quadruple. -/
theorem paperOrderedRouthDesign_first_acceptance
    (m : ℕ) (ξ : ℕ → ℚ) (hξ : StrictMono ξ) :
    ∃ a b c d : ℕ, OrderedDesignAccepted
      (orderedRationalPhysicalPrefixTest m (paperRationalPrefixDiagonalAccepts m))
      (paperOrderedSlowRouthAccepts m) (paperOrderedCoalescedRouthAccepts m ξ)
      (orderedRationalPhysicalSplitTest m ξ (paperOrderedSplitRouthAccepts m ξ)) a b c d := by
  apply orderedRationalPhysicalDesign_first_acceptance m ξ
    (paperRationalPrefixDiagonalAccepts m) (paperOrderedSlowRouthAccepts m)
    (paperOrderedCoalescedRouthAccepts m ξ) (paperOrderedSplitRouthAccepts m ξ)
    (paperRationalPrefixDiagonal_eventually_accepts m)
  · intro a ha
    exact (paperOrderedSlowRouth_eventually_accepts m a ha).exists
  · intro a b ha hb
    exact (paperOrderedCoalescedRouth_eventually_accepts m ξ a b ha hb).exists
  · intro a b c ha _hb hc
    exact paperOrderedSplitRouth_eventually_accepts m ξ hξ a b c ha hc

end
end PhosphorylationStableCapacity
