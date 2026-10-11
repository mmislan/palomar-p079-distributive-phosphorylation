module
public import proofs.PhosphorylationStableCapacity.SplitStateContinuity
public import proofs.PhosphorylationStableCapacity.MatrixSpectralNeighborhood

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Matrix
open scoped Topology

@[fun_prop] private theorem contDiff_ite_fixed {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p : Prop) [Decidable p]
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (fun x => if p then f x else g x) := by
  by_cases hp : p <;> simp [hp, hf, hg]

@[fun_prop] private theorem contDiff_fin_cases_fixed {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (i : Fin (n+1)) {f : E → ℝ} {g : E → Fin n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (fun x => Fin.cases (motive := fun _ => ℝ) (f x) (g x) i) := by
  cases i using Fin.cases with
  | zero => simpa using hf
  | succ j => simpa using (contDiff_pi.mp hg) j

/-- All six edge-rate arrays as one finite-dimensional real parameter. -/
abbrev RateVector (n : ℕ) := Fin 6 → Fin n → ℝ

def ratesFromVector {n : ℕ} (v : RateVector n) : Rates n where
  a := v 0
  b := v 1
  c := v 2
  alpha := v 3
  beta := v 4
  gamma := v 5

def rateVector {n : ℕ} (k : Rates n) : RateVector n :=
  fun j => if j = 0 then k.a else if j = 1 then k.b else
    if j = 2 then k.c else if j = 3 then k.alpha else
    if j = 4 then k.beta else k.gamma

theorem ratesFromVector_rateVector {n : ℕ} (k : Rates n) :
    ratesFromVector (rateVector k) = k := by
  cases k
  simp [ratesFromVector, rateVector]

/-- The literal restricted mass-action field with rates included among its
finite-dimensional inputs. -/
def jointRestrictedField {n : ℕ} (ET FT ST : ℝ)
    (p : RateVector n × CoordinateSpace n) : CoordinateSpace n :=
  restrictedFieldEuclid ET FT ST (ratesFromVector p.1) p.2

theorem contDiff_jointRestrictedField {n : ℕ} (ET FT ST : ℝ) :
    ContDiff ℝ 2 (jointRestrictedField (n := n) ET FT ST) := by
  classical
  unfold jointRestrictedField restrictedFieldEuclid restrictedField
    ratesFromVector toCoordinateSpace chart field unChart ofCoordinateSpace
    kinaseNet phosphataseNet
  dsimp
  fun_prop

/-- The original class-restricted Fréchet Jacobian is continuous jointly
in all six literal rate arrays and the class coordinates. -/
theorem continuous_restrictedJacobian_fromVector {n : ℕ}
    (ET FT ST : ℝ) :
    Continuous (fun p : RateVector n × CoordinateSpace n =>
      restrictedJacobian ET FT ST (ratesFromVector p.1) p.2) := by
  have hproj : ContDiff ℝ 1
      (fun q : (RateVector n × CoordinateSpace n) × CoordinateSpace n =>
        (q.1.1, q.2)) := by fun_prop
  have hj : ContDiff ℝ 1 (jointRestrictedField (n := n) ET FT ST) :=
    (contDiff_jointRestrictedField ET FT ST).of_le (by norm_num)
  have hf : ContDiff ℝ 1
      (fun q : (RateVector n × CoordinateSpace n) × CoordinateSpace n =>
        jointRestrictedField ET FT ST (q.1.1, q.2)) := hj.comp hproj
  have hg : Continuous (fun p : RateVector n × CoordinateSpace n => p.2) :=
    continuous_snd
  have h := Continuous.fderiv_one
    (f := fun p : RateVector n × CoordinateSpace n => fun u : CoordinateSpace n =>
      jointRestrictedField ET FT ST (p.1, u)) hf hg
  simpa only [restrictedJacobian, jointRestrictedField] using h

theorem splitRetuned_rateVector_continuousAt
    (m : ℕ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1)) :
    ContinuousAt (fun δ => rateVector (splitRetunedRates m r τ δ ε)) 0 := by
  apply continuousAt_pi.mpr
  intro j
  apply continuousAt_pi.mpr
  intro i
  obtain ⟨ha, hb, hc, hα, hβ, hγ⟩ :=
    splitRetunedRates_components_continuousAt m r τ ε hr hD₀ hB₀ i
  fin_cases j <;>
    first
    | simpa [rateVector] using ha
    | simpa [rateVector] using hb
    | simpa [rateVector] using hc
    | simpa [rateVector] using hα
    | simpa [rateVector] using hβ
    | simpa [rateVector] using hγ

theorem splitState_coordinate_continuousAt
    (m : ℕ) (r : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1)) :
    ContinuousAt (fun δ =>
      toCoordinateSpace (chart (splitFiniteState (m+1) r δ j))) 0 := by
  obtain ⟨hS, _, _, hC, hD⟩ :=
    splitFiniteState_components_continuousAt (m+1) r hr hD₀ j
  exact (continuousAt_pi.mpr (fun i : Fin (m+2) => hS i.succ)).prodMk
    ((continuousAt_pi.mpr hC).prodMk (continuousAt_pi.mpr hD))

/-- The actual class-restricted Jacobian at each split equilibrium tends
to the coalesced Jacobian along the one common retuned rate path. -/
theorem split_restrictedJacobian_continuousAt
    (m : ℕ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1)) :
    ContinuousAt (fun δ => restrictedJacobian (2*r) 2 (2*(r+1))
      (splitRetunedRates m r τ δ ε)
      (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))) 0 := by
  have hk := splitRetuned_rateVector_continuousAt m r τ ε hr hD₀ hB₀
  have hu := splitState_coordinate_continuousAt m r hr hD₀ j
  have h := (continuous_restrictedJacobian_fromVector
    (n := m+2) (2*r) 2 (2*(r+1))).continuousAt.comp (hk.prodMk hu)
  simpa [Function.comp_def, ratesFromVector_rateVector] using h

theorem continuous_coordinateJacobian_matrix (n : ℕ) :
    Continuous (fun L : CoordinateSpace n →L[ℝ] CoordinateSpace n =>
      LinearMap.toMatrix (coordinateBasis n) (coordinateBasis n) L.toLinearMap) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have heval : Continuous (fun L : CoordinateSpace n →L[ℝ] CoordinateSpace n =>
      L (coordinateBasis n j)) :=
    (ContinuousLinearMap.apply ℝ (CoordinateSpace n) (coordinateBasis n j)).continuous
  have hrepr : Continuous (fun x : CoordinateSpace n =>
      (coordinateBasis n).repr x i) :=
    (continuous_apply i).comp (coordinateBasis n).continuous_coe_repr
  simpa [Function.comp_def, LinearMap.toMatrix_apply] using hrepr.comp heval

/-- Matrix-entry continuity for the literal split Jacobian, in the same
basis used to define the characteristic polynomial and Hurwitz predicate. -/
theorem split_restrictedJacobianMatrix_continuousAt
    (m : ℕ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1)) :
    ContinuousAt (fun δ => restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (splitRetunedRates m r τ δ ε)
      (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))) 0 := by
  exact (continuous_coordinateJacobian_matrix (m+2)).continuousAt.comp
    (split_restrictedJacobian_continuousAt m r τ ε hr hD₀ hB₀ j)

theorem split_restrictedJacobianMatrix_zero_eq_coalesced
    (m : ℕ) (r τ ε : ℝ) (j : Fin (2*(m+1)+1)) :
    restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (splitRetunedRates m r τ 0 ε)
      (toCoordinateSpace (chart (splitFiniteState (m+1) r 0 j))) =
    restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (relaxRates (coalescedFinalScaledRates m r τ) ε)
      (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r))) := by
  rw [splitRetunedRates_zero_eq_coalesced,
    splitFiniteState_zero_eq_coalesced]
  simp only [loadedCoordOfState, from_toLoadedCoord]

theorem continuous_complexification_matrix (n : ℕ) :
    Continuous (fun M : Matrix (Fin n ⊕ (Fin n ⊕ Fin n))
        (Fin n ⊕ (Fin n ⊕ Fin n)) ℝ => M.map (algebraMap ℝ ℂ)) := by
  fun_prop

theorem split_complexJacobian_continuousAt
    (m : ℕ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1)) :
    ContinuousAt (fun δ =>
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (splitRetunedRates m r τ δ ε)
        (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).map
          (algebraMap ℝ ℂ)) 0 := by
  exact (continuous_complexification_matrix (m+2)).continuousAt.comp
    (split_restrictedJacobianMatrix_continuousAt m r τ ε hr hD₀ hB₀ j)

/-- The verified coalesced spectral gap transfers to an arbitrarily small
neighborhood of the slow root at every split equilibrium. It does not yet
count or sign the roots in that neighborhood. -/
theorem split_spectrum_eventually_left_or_near_zero
    (m : ℕ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hspec : SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (coalescedFinalScaledRates m r τ) ε)
        (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r)))))
    (j : Fin (2*(m+1)+1)) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ δ : ℝ in nhds 0,
      ∀ z : ℂ, z ∈ spectrum ℂ
        ((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (splitRetunedRates m r τ δ ε)
          (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).map
            (algebraMap ℝ ℂ)) →
        z.re < 0 ∨ ‖z‖ < η := by
  let J : ℝ → Matrix (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2)))
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) ℂ := fun δ =>
    (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (splitRetunedRates m r τ δ ε)
      (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).map
        (algebraMap ℝ ℂ)
  have hJ : ContinuousAt J 0 :=
    split_complexJacobian_continuousAt m r τ ε hr hD₀ hB₀ j
  have hzero : J 0 =
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (coalescedFinalScaledRates m r τ) ε)
        (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r)))).map
          (algebraMap ℝ ℂ) := by
    exact congrArg (fun M => M.map (algebraMap ℝ ℂ))
      (split_restrictedJacobianMatrix_zero_eq_coalesced m r τ ε j)
  obtain ⟨p, hfactor, _, hleft⟩ := hspec
  have hsource : ∀ z : ℂ, z ∈ spectrum ℂ (J 0) → z.re < 0 ∨ z = 0 := by
    intro z hz
    rw [hzero] at hz
    have hzroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
    rw [hfactor] at hzroot
    have heval : z * p.eval z = 0 := by
      simpa using hzroot.eq_zero
    rcases mul_eq_zero.mp heval with hzero' | hp
    · exact Or.inr hzero'
    · exact Or.inl (hleft z hp)
  exact matrix_family_spectrum_eventually_left_or_near_zero
    J 0 hJ hsource η hη

/-- A single sufficiently small split works for the spectral neighborhood
at every member of the finite equilibrium family. -/
theorem split_spectrum_uniform_eventually_left_or_near_zero
    (m : ℕ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hspec : SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (coalescedFinalScaledRates m r τ) ε)
        (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r)))))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ δ : ℝ in nhds 0,
      ∀ j : Fin (2*(m+1)+1), ∀ z : ℂ,
        z ∈ spectrum ℂ
          ((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (splitRetunedRates m r τ δ ε)
            (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).map
              (algebraMap ℝ ℂ)) →
          z.re < 0 ∨ ‖z‖ < η := by
  apply Filter.eventually_all.mpr
  intro j
  exact split_spectrum_eventually_left_or_near_zero
    m r τ ε hr hD₀ hB₀ hspec j η hη

/-- Common-rate admissibility and the uniform spectral neighborhood hold
simultaneously for one sufficiently small positive splitting parameter. -/
theorem split_admissible_and_spectrally_near_eventually
    (m : ℕ) (r τ ε : ℝ)
    (hr : 0 < r) (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hspec : SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (coalescedFinalScaledRates m r τ) ε)
        (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r)))))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      SplitRetunedFamilyAdmissible m r τ δ ε ∧
      ∀ j : Fin (2*(m+1)+1), ∀ z : ℂ,
        z ∈ spectrum ℂ
          ((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (splitRetunedRates m r τ δ ε)
            (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).map
              (algebraMap ℝ ℂ)) →
          z.re < 0 ∨ ‖z‖ < η := by
  have hgeom := splitRetunedSource_eventually_admissible
    m r τ ε hr hτ hε hε1 hD₀ hB₀
  have hnear : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j : Fin (2*(m+1)+1), ∀ z : ℂ,
        z ∈ spectrum ℂ
          ((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (splitRetunedRates m r τ δ ε)
            (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).map
              (algebraMap ℝ ℂ)) →
          z.re < 0 ∨ ‖z‖ < η := by
    exact (split_spectrum_uniform_eventually_left_or_near_zero
      m r τ ε (ne_of_gt hr) hD₀ hB₀ hspec η hη).filter_mono
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  filter_upwards [hgeom, hnear] with δ hgeom hnear
  exact ⟨hgeom, hnear⟩

/-- For every chain size, the large-source/small-weight/fast-binding
parameters can be selected so that one near-coalescent positive family has
the certified transverse spectral gap simultaneously at every state. -/
theorem coalescedSpectral_splitFamily_near_eventually
    (m : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ r : ℝ in atTop,
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        ∀ᶠ ε : ℝ in nhds 0,
          0 < ε → ε ≤ 1 →
            ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
              SplitRetunedFamilyAdmissible m r τ δ ε ∧
              ∀ j : Fin (2*(m+1)+1), ∀ z : ℂ,
                z ∈ spectrum ℂ
                  ((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
                    (splitRetunedRates m r τ δ ε)
                    (toCoordinateSpace
                      (chart (splitFiniteState (m+1) r δ j)))).map
                        (algebraMap ℝ ℂ)) →
                  z.re < 0 ∨ ‖z‖ < η := by
  obtain ⟨hp, hq⟩ := coalescedPair_dense (m+1)
  have hconv := conversion_eventually_positive hp hq
  have hrpos : ∀ᶠ r : ℝ in atTop, 0 < r := eventually_gt_atTop 0
  filter_upwards [coalescedSpectral_and_splitFamily_eventually m,
    hconv, hrpos] with r hsource hconv hr
  have hτpos : ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), 0 < τ :=
    self_mem_nhdsWithin
  filter_upwards [hsource, hτpos] with τ hsource hτ
  filter_upwards [hsource] with ε hsource hε hε1
  have hspec := (hsource hε hε1).1
  rw [splitRetunedRates_zero_eq_coalesced] at hspec
  exact split_admissible_and_spectrally_near_eventually
    m r τ ε hr hτ hε hε1 hconv.1 hconv.2 hspec η hη

end
end PhosphorylationStableCapacity
