module
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import proofs.PhosphorylationStableCapacity.SplitSlowRootExistence

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial Filter
open scoped Topology

/-- A fixed degree bound and coefficient continuity make the real
spectral derivative jointly continuous in parameter and spectral variable. -/
theorem polynomial_family_derivative_joint_continuousAt
    (P : ℝ → ℝ[X]) (N : ℕ)
    (hdegree : ∀ δ, (P δ).natDegree < N)
    (hcoeff : ∀ k, ContinuousAt (fun δ => (P δ).coeff k) 0) :
    ContinuousAt
      (fun y : ℝ × ℝ => (P y.1).derivative.eval y.2) (0, 0) := by
  have heval (δ x : ℝ) :
      (P δ).derivative.eval x =
        ∑ k ∈ Finset.range N,
          ((P δ).coeff (k+1) * (k+1 : ℝ)) * x^k := by
    have hd : (P δ).derivative.natDegree < N := by
      have := Polynomial.natDegree_derivative_le (P δ)
      have := hdegree δ
      omega
    rw [Polynomial.eval_eq_sum_range' hd]
    simp only [Polynomial.coeff_derivative]
  simp_rw [heval]
  apply tendsto_finsetSum (Finset.range N)
  intro k hk
  have hc : ContinuousAt
      (fun y : ℝ × ℝ => (P y.1).coeff (k+1)) (0, 0) :=
    ContinuousAt.comp (f := Prod.fst) (x := ((0 : ℝ), (0 : ℝ)))
      (hcoeff (k+1)) continuousAt_fst
  exact ((hc.mul continuousAt_const).mul (continuousAt_snd.pow k)).tendsto

private def CoeffContinuousAt (P : ℝ → ℝ[X]) : Prop :=
  ∀ k, ContinuousAt (fun δ => (P δ).coeff k) 0

private theorem coeffContinuousAt_add {P Q : ℝ → ℝ[X]}
    (hP : CoeffContinuousAt P) (hQ : CoeffContinuousAt Q) :
    CoeffContinuousAt (fun δ => P δ + Q δ) := by
  intro k
  simp only [Polynomial.coeff_add]
  have hfun : (fun δ => (P δ).coeff k + (Q δ).coeff k) =
      (fun δ => (P δ).coeff k) + (fun δ => (Q δ).coeff k) := by
    funext δ
    simp
  rw [hfun]
  exact (hP k).add (hQ k)

private theorem coeffContinuousAt_mul {P Q : ℝ → ℝ[X]}
    (hP : CoeffContinuousAt P) (hQ : CoeffContinuousAt Q) :
    CoeffContinuousAt (fun δ => P δ * Q δ) := by
  intro k
  simp only [Polynomial.coeff_mul]
  apply tendsto_finsetSum (Finset.HasAntidiagonal.antidiagonal k)
  intro ij hij
  exact ((hP ij.1).mul (hQ ij.2)).tendsto

private theorem coeffContinuousAt_const (P : ℝ[X]) :
    CoeffContinuousAt (fun _ => P) := by
  intro k
  exact continuousAt_const

private theorem coeffContinuousAt_C {g : ℝ → ℝ}
    (hg : ContinuousAt g 0) :
    CoeffContinuousAt (fun δ => Polynomial.C (g δ)) := by
  intro k
  cases k with
  | zero => simpa using hg
  | succ k => simpa using (continuousAt_const :
      ContinuousAt (fun _ : ℝ => (0 : ℝ)) 0)

private theorem coeffContinuousAt_neg {P : ℝ → ℝ[X]}
    (hP : CoeffContinuousAt P) :
    CoeffContinuousAt (fun δ => -(P δ)) := by
  intro k
  simp only [Polynomial.coeff_neg]
  have hfun : (fun δ => -(P δ).coeff k) =
      -(fun δ => (P δ).coeff k) := by
    funext δ
    simp
  rw [hfun]
  exact (hP k).neg

private theorem coeffContinuousAt_finset_prod {ι : Type*}
    (s : Finset ι) (P : ι → ℝ → ℝ[X])
    (hP : ∀ i ∈ s, CoeffContinuousAt (P i)) :
    CoeffContinuousAt (fun δ => ∏ i ∈ s, P i δ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.prod_empty] using
        (coeffContinuousAt_const (1 : ℝ[X]))
  | @insert a s ha ih =>
      simpa only [Finset.prod_insert ha] using
        coeffContinuousAt_mul (hP a (Finset.mem_insert_self ..))
          (ih (fun i hi => hP i (Finset.mem_insert_of_mem hi)))

/-- Every coefficient of the characteristic polynomial varies continuously
with a continuous finite real matrix family. -/
theorem matrix_real_charpoly_coeff_continuousAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ℝ → Matrix ι ι ℝ) (hJ : ContinuousAt J 0) (k : ℕ) :
    ContinuousAt (fun δ => (J δ).charpoly.coeff k) 0 := by
  let M : ℝ → Matrix ι ι ℝ[X] := fun δ => (J δ).charmatrix
  have hentry (i j : ι) : CoeffContinuousAt (fun δ => M δ i j) := by
    have hval : ContinuousAt (fun δ => J δ i j) 0 := by
      exact ContinuousAt.comp (f := J) (x := 0)
        (continuous_apply_apply i j).continuousAt hJ
    by_cases hij : i = j
    · subst j
      simpa [M, Matrix.charmatrix_apply_eq, sub_eq_add_neg] using
        coeffContinuousAt_add (coeffContinuousAt_const Polynomial.X)
          (coeffContinuousAt_neg (coeffContinuousAt_C hval))
    · simpa only [M, Matrix.charmatrix_apply_ne _ _ _ hij] using
        coeffContinuousAt_neg (coeffContinuousAt_C hval)
  change ContinuousAt (fun δ => (M δ).det.coeff k) 0
  simp only [Matrix.det_apply, Polynomial.finsetSum_coeff]
  apply tendsto_finsetSum Finset.univ
  intro σ hσ
  have hprod : CoeffContinuousAt (fun δ =>
      ∏ i : ι, M δ (σ i) i) :=
    coeffContinuousAt_finset_prod Finset.univ
      (fun i δ => M δ (σ i) i)
      (by intro i hi; exact hentry (σ i) i)
  have hsign : ContinuousAt (fun _ : ℝ => Equiv.Perm.sign σ) 0 :=
    continuousAt_const
  have hterm : ContinuousAt
      (fun δ => Equiv.Perm.sign σ • (∏ i, M δ (σ i) i).coeff k) 0 := by
    convert hsign.smul (hprod k) using 1
  simpa [Polynomial.coeff_smul] using hterm.tendsto

/-- The derivative of the characteristic polynomial of a continuous finite
matrix family is jointly continuous at the coalesced matrix and root. -/
theorem matrix_real_charpoly_derivative_joint_continuousAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ℝ → Matrix ι ι ℝ) (hJ : ContinuousAt J 0) :
    ContinuousAt
      (fun y : ℝ × ℝ => (J y.1).charpoly.derivative.eval y.2) (0, 0) := by
  exact polynomial_family_derivative_joint_continuousAt
    (fun δ => (J δ).charpoly) (Fintype.card ι + 1)
    (by intro δ; simp) (matrix_real_charpoly_coeff_continuousAt J hJ)

/-- A positive derivative at the limiting zero gives a common small real
interval on which every sufficiently small perturbation has at most one root. -/
theorem polynomial_family_root_unique_near_of_deriv_pos
    (P : ℝ → ℝ[X])
    (hjoint : ContinuousAt
      (fun y : ℝ × ℝ => (P y.1).derivative.eval y.2) (0, 0))
    (hpos : 0 < (P 0).derivative.eval 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ δ : ℝ in nhds 0,
        ∀ x y : ℝ, |x| < ρ → |y| < ρ →
          (P δ).IsRoot x → (P δ).IsRoot y → x = y := by
  have hlocal : ∀ᶠ v : ℝ × ℝ in nhds (0, 0),
      0 < (P v.1).derivative.eval v.2 :=
    hjoint.eventually (eventually_gt_nhds hpos)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ] with δ hδ x y hx hy hrootx hrooty
  have hδabs : |δ| < ρ := by
    simpa [Metric.mem_ball, Real.dist_eq] using hδ
  have hderiv (z : ℝ) (hz : z ∈ Set.Ioo (-ρ) ρ) :
      0 < deriv (fun t => (P δ).eval t) z := by
    have hzabs : |z| < ρ := abs_lt.mpr ⟨hz.1, hz.2⟩
    have hmem : (δ, z) ∈ Metric.ball (0, 0) ρ := by
      simpa [Metric.mem_ball, Prod.dist_eq, Real.dist_eq,
        max_lt_iff] using (And.intro hδabs hzabs)
    simpa [Polynomial.deriv] using hball hmem
  have hmono : StrictMonoOn (fun t => (P δ).eval t) (Set.Ioo (-ρ) ρ) :=
    strictMonoOn_of_deriv_pos (convex_Ioo (-ρ) ρ) (P δ).continuous.continuousOn
      (by simpa only [interior_Ioo] using hderiv)
  exact hmono.injOn (abs_lt.mp hx) (abs_lt.mp hy)
    (by simpa only [Polynomial.IsRoot] using hrootx.trans hrooty.symm)

/-- A simple limiting real root is the only real root in a common small
interval for all sufficiently small parameters. -/
theorem polynomial_family_root_unique_near
    (P : ℝ → ℝ[X])
    (hjoint : ContinuousAt
      (fun y : ℝ × ℝ => (P y.1).derivative.eval y.2) (0, 0))
    (hsimple : (P 0).derivative.eval 0 ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ δ : ℝ in nhds 0,
        ∀ x y : ℝ, |x| < ρ → |y| < ρ →
          (P δ).IsRoot x → (P δ).IsRoot y → x = y := by
  rcases lt_or_gt_of_ne hsimple with hneg | hpos
  · have hjoint' : ContinuousAt
        (fun y : ℝ × ℝ => (-(P y.1)).derivative.eval y.2) (0, 0) := by
      convert hjoint.neg using 1
      ext y
      simp [Polynomial.derivative_neg, Polynomial.eval_neg]
    have hpos' : 0 < (-(P 0)).derivative.eval 0 := by
      simpa only [Polynomial.derivative_neg, Polynomial.eval_neg] using
        (neg_pos.mpr hneg)
    obtain ⟨ρ, hρ, huniq⟩ :=
      polynomial_family_root_unique_near_of_deriv_pos
        (fun δ => -(P δ)) hjoint' hpos'
    refine ⟨ρ, hρ, ?_⟩
    filter_upwards [huniq] with δ hδ x y hx hy hPx hPy
    apply hδ x y hx hy
    · simpa [Polynomial.IsRoot] using hPx
    · simpa [Polynomial.IsRoot] using hPy
  · exact polynomial_family_root_unique_near_of_deriv_pos P hjoint hpos

/-- Each split state has exactly one real characteristic root in a fixed
small interval, for all sufficiently small splitting parameters. -/
theorem split_real_slow_root_exists_unique_eventually
    (m : ℕ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : PhosphorylationSharpness.DensePositive
      (coalescedRawD (m+1) r) (m+1))
    (hB₀ : PhosphorylationSharpness.DensePositive
      (coalescedRawB (m+1) r) (m+1))
    (hspec : SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (coalescedFinalScaledRates m r τ) ε)
        (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r)))))
    (j : Fin (2*(m+1)+1)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ δ : ℝ in nhds 0,
        ∃ x : ℝ,
          (|x| < ρ ∧
            (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
              (splitRetunedRates m r τ δ ε)
              (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).charpoly.IsRoot x) ∧
          ∀ y : ℝ, |y| < ρ →
            (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
              (splitRetunedRates m r τ δ ε)
              (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).charpoly.IsRoot y →
            y = x := by
  let J : ℝ → Matrix (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2)))
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) ℝ := fun δ =>
    restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (splitRetunedRates m r τ δ ε)
      (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))
  have hJ : ContinuousAt J 0 :=
    split_restrictedJacobianMatrix_continuousAt m r τ ε hr hD₀ hB₀ j
  have hzero : J 0 =
      restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (coalescedFinalScaledRates m r τ) ε)
        (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r))) :=
    split_restrictedJacobianMatrix_zero_eq_coalesced m r τ ε j
  have hsimple : (J 0).charpoly.derivative.eval 0 ≠ 0 := by
    rw [hzero]
    exact simpleNeutral_real_charpoly_derivative_nonzero _ hspec
  obtain ⟨ρ, hρ, huniq⟩ := polynomial_family_root_unique_near
    (fun δ => (J δ).charpoly)
    (matrix_real_charpoly_derivative_joint_continuousAt J hJ) hsimple
  have hexists := split_real_slow_root_eventually
    m r τ ε hr hD₀ hB₀ hspec j ρ hρ
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [huniq, hexists] with δ huniq hexists
  obtain ⟨x, hx, hroot⟩ := hexists
  exact ⟨x, ⟨hx, hroot⟩,
    fun y hy hyroot => huniq y x hy hx hyroot hroot⟩

/-- A single sufficiently small splitting parameter works at every split
state. The isolation radius may depend on the state index. -/
theorem split_real_slow_roots_unique_uniform_eventually
    (m : ℕ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : PhosphorylationSharpness.DensePositive
      (coalescedRawD (m+1) r) (m+1))
    (hB₀ : PhosphorylationSharpness.DensePositive
      (coalescedRawB (m+1) r) (m+1))
    (hspec : SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (coalescedFinalScaledRates m r τ) ε)
        (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r))))) :
    ∃ ρ : Fin (2*(m+1)+1) → ℝ,
      (∀ j, 0 < ρ j) ∧
      ∀ᶠ δ : ℝ in nhds 0,
        ∀ j : Fin (2*(m+1)+1),
          ∃! x : ℝ,
            |x| < ρ j ∧
            (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
              (splitRetunedRates m r τ δ ε)
              (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).charpoly.IsRoot x := by
  classical
  have h (j : Fin (2*(m+1)+1)) :=
    split_real_slow_root_exists_unique_eventually
      m r τ ε hr hD₀ hB₀ hspec j
  choose ρ hρ hEv using h
  refine ⟨ρ, hρ, ?_⟩
  apply Filter.eventually_all.mpr
  intro j
  filter_upwards [hEv j] with δ hδ
  obtain ⟨x, hx, hunique⟩ := hδ
  exact ⟨x, hx, fun y hy => hunique y hy.1 hy.2⟩

/-- Common-rate admissibility, transverse spectral proximity, and one
isolated real slow root at each split state can be obtained simultaneously. -/
theorem split_admissible_spectral_unique_real_eventually
    (m : ℕ) (r τ ε : ℝ)
    (hr : 0 < r) (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD₀ : PhosphorylationSharpness.DensePositive
      (coalescedRawD (m+1) r) (m+1))
    (hB₀ : PhosphorylationSharpness.DensePositive
      (coalescedRawB (m+1) r) (m+1))
    (hspec : SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (coalescedFinalScaledRates m r τ) ε)
        (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r)))))
    (η : ℝ) (hη : 0 < η) :
    ∃ ρ : Fin (2*(m+1)+1) → ℝ,
      (∀ j, 0 < ρ j) ∧
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        SplitRetunedFamilyAdmissible m r τ δ ε ∧
        (∀ j : Fin (2*(m+1)+1), ∀ z : ℂ,
          z ∈ spectrum ℂ
            ((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
              (splitRetunedRates m r τ δ ε)
              (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).map
                (algebraMap ℝ ℂ)) →
            z.re < 0 ∨ ‖z‖ < η) ∧
        (∀ j : Fin (2*(m+1)+1),
          ∃! x : ℝ,
            |x| < ρ j ∧
            (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
              (splitRetunedRates m r τ δ ε)
              (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).charpoly.IsRoot x) := by
  obtain ⟨ρ, hρ, huniq⟩ :=
    split_real_slow_roots_unique_uniform_eventually
      m r τ ε (ne_of_gt hr) hD₀ hB₀ hspec
  have huniq' : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j : Fin (2*(m+1)+1),
        ∃! x : ℝ,
          |x| < ρ j ∧
          (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (splitRetunedRates m r τ δ ε)
            (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).charpoly.IsRoot x :=
    huniq.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hgeom := split_admissible_and_spectrally_near_eventually
    m r τ ε hr hτ hε hε1 hD₀ hB₀ hspec η hη
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [hgeom, huniq'] with δ hgeom huniq
  exact ⟨hgeom.1, hgeom.2, huniq⟩

end
end PhosphorylationStableCapacity
