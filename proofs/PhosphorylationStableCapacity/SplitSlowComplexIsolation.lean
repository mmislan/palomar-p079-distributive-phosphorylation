module
public import proofs.PhosphorylationStableCapacity.SplitSlowRootUniqueness

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial Filter PhosphorylationSharpness
open scoped Topology

/-- A finite divided difference for a bounded-degree complex polynomial. -/
private def dividedDifference (P : ℝ → ℂ[X]) (N : ℕ)
    (v : ℝ × (ℂ × ℂ)) : ℂ :=
  ∑ n ∈ Finset.range N,
    (P v.1).coeff n *
      ∑ i ∈ Finset.range n, v.2.1^i * v.2.2^(n-1-i)

private theorem dividedDifference_factor
    (P : ℝ → ℂ[X]) (N : ℕ)
    (hdegree : ∀ δ, (P δ).natDegree < N)
    (δ : ℝ) (z w : ℂ) :
    (P δ).eval z - (P δ).eval w =
      (z-w) * dividedDifference P N (δ, (z,w)) := by
  rw [Polynomial.eval_eq_sum_range' (hdegree δ) z,
    Polynomial.eval_eq_sum_range' (hdegree δ) w]
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  simp_rw [← (Commute.all z w).mul_geom_sum₂]
  simp only [dividedDifference, Finset.mul_sum]
  congr 1
  ext n
  ring_nf

private theorem divided_power_sum_at_zero (n : ℕ) :
    (∑ i ∈ Finset.range n,
      (0 : ℂ)^i * (0 : ℂ)^(n-1-i)) = if n = 1 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero => simp
      | succ n =>
          split_ifs with h
          · omega
          apply Finset.sum_eq_zero
          intro i hi
          have hi' : i < n + 2 := Finset.mem_range.mp hi
          by_cases hiz : i = 0
          · subst i
            simp
          · simp [hiz]

private theorem dividedDifference_zero
    (P : ℝ → ℂ[X]) (N : ℕ) (hN : 1 < N) :
    dividedDifference P N (0, (0,0)) = (P 0).coeff 1 := by
  simp only [dividedDifference, divided_power_sum_at_zero,
    mul_ite, mul_one, mul_zero]
  simp [Finset.mem_range, hN]

private theorem dividedDifference_continuousAt
    (P : ℝ → ℂ[X]) (N : ℕ)
    (hcoeff : ∀ n, ContinuousAt (fun δ => (P δ).coeff n) 0) :
    ContinuousAt (dividedDifference P N) (0, (0,0)) := by
  unfold dividedDifference
  apply tendsto_finsetSum (Finset.range N)
  intro n hn
  have hc : ContinuousAt
      (fun v : ℝ × (ℂ × ℂ) => (P v.1).coeff n) (0, (0,0)) :=
    ContinuousAt.comp (f := Prod.fst)
      (x := ((0 : ℝ), ((0 : ℂ), (0 : ℂ))))
      (hcoeff n) continuousAt_fst
  have hsum : ContinuousAt
      (fun v : ℝ × (ℂ × ℂ) =>
        ∑ i ∈ Finset.range n, v.2.1^i * v.2.2^(n-1-i))
      (0, (0,0)) := by
    apply tendsto_finsetSum (Finset.range n)
    intro i hi
    have hterm : ContinuousAt
        (fun v : ℝ × (ℂ × ℂ) => v.2.1^i * v.2.2^(n-1-i))
        (0, (0,0)) := by
      fun_prop
    exact hterm.tendsto
  exact (hc.mul hsum).tendsto

/-- A nonzero linear coefficient at a simple limiting zero makes every
sufficiently small complex polynomial injective on a common root disk. -/
theorem complex_polynomial_family_unique_root_near_zero
    (P : ℝ → ℂ[X]) (N : ℕ) (hN : 1 < N)
    (hdegree : ∀ δ, (P δ).natDegree < N)
    (hcoeff : ∀ n, ContinuousAt (fun δ => (P δ).coeff n) 0)
    (hsimple : (P 0).coeff 1 ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ δ : ℝ in nhds 0,
        ∀ z w : ℂ, ‖z‖ < ρ → ‖w‖ < ρ →
          (P δ).IsRoot z → (P δ).IsRoot w → z = w := by
  have hD0 : dividedDifference P N (0, (0,0)) ≠ 0 := by
    rw [dividedDifference_zero P N hN]
    exact hsimple
  have hlocal : ∀ᶠ v : ℝ × (ℂ × ℂ) in nhds (0, (0,0)),
      dividedDifference P N v ≠ 0 :=
    (dividedDifference_continuousAt P N hcoeff).eventually_ne hD0
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ] with δ hδ z w hz hw hrootz hrootw
  have hδnorm : |δ| < ρ := by
    simpa [Metric.mem_ball, Real.dist_eq] using hδ
  have hmem : (δ, (z,w)) ∈ Metric.ball (0, (0,0)) ρ := by
    simpa [Metric.mem_ball, Prod.dist_eq, dist_eq_norm,
      max_lt_iff] using (And.intro hδnorm (And.intro hz hw))
  have hDne := hball hmem
  have hfactor := dividedDifference_factor P N hdegree δ z w
  rw [hrootz, hrootw] at hfactor
  have hprod : (z-w) * dividedDifference P N (δ, (z,w)) = 0 := by
    simpa using hfactor.symm
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hDne)

/-- Fixed degree and coefficient continuity give joint continuity of the
complex spectral derivative. -/
theorem complex_polynomial_family_derivative_joint_continuousAt
    (P : ℝ → ℂ[X]) (N : ℕ)
    (hdegree : ∀ δ, (P δ).natDegree < N)
    (hcoeff : ∀ n, ContinuousAt (fun δ => (P δ).coeff n) 0) :
    ContinuousAt
      (fun v : ℝ × ℂ => (P v.1).derivative.eval v.2) (0, 0) := by
  have heval (δ : ℝ) (z : ℂ) :
      (P δ).derivative.eval z =
        ∑ n ∈ Finset.range N,
          ((P δ).coeff (n+1) * (n+1 : ℂ)) * z^n := by
    have hd : (P δ).derivative.natDegree < N := by
      have := Polynomial.natDegree_derivative_le (P δ)
      have := hdegree δ
      omega
    rw [Polynomial.eval_eq_sum_range' hd]
    simp only [Polynomial.coeff_derivative]
  simp_rw [heval]
  apply tendsto_finsetSum (Finset.range N)
  intro n hn
  have hc : ContinuousAt
      (fun v : ℝ × ℂ => (P v.1).coeff (n+1)) (0, 0) :=
    ContinuousAt.comp (f := Prod.fst) (x := ((0 : ℝ), (0 : ℂ)))
      (hcoeff (n+1)) continuousAt_fst
  exact ((hc.mul continuousAt_const).mul (continuousAt_snd.pow n)).tendsto

/-- In a fixed small disk, the derivative of every sufficiently small
polynomial perturbation stays nonzero. -/
theorem complex_polynomial_family_derivative_near_nonzero
    (P : ℝ → ℂ[X]) (N : ℕ)
    (hdegree : ∀ δ, (P δ).natDegree < N)
    (hcoeff : ∀ n, ContinuousAt (fun δ => (P δ).coeff n) 0)
    (hsimple : (P 0).coeff 1 ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ δ : ℝ in nhds 0,
        ∀ z : ℂ, ‖z‖ < ρ → (P δ).derivative.eval z ≠ 0 := by
  have hderiv0 : (P 0).derivative.eval 0 ≠ 0 := by
    simpa [← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_derivative] using hsimple
  have hlocal : ∀ᶠ v : ℝ × ℂ in nhds (0, 0),
      (P v.1).derivative.eval v.2 ≠ 0 :=
    (complex_polynomial_family_derivative_joint_continuousAt
      P N hdegree hcoeff).eventually_ne hderiv0
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ] with δ hδ z hz
  have hδabs : |δ| < ρ := by
    simpa [Metric.mem_ball, Real.dist_eq] using hδ
  have hmem : (δ, z) ∈ Metric.ball (0, 0) ρ := by
    simpa [Metric.mem_ball, Prod.dist_eq, dist_eq_norm,
      max_lt_iff] using (And.intro hδabs hz)
  exact hball hmem

/-- A continuous real matrix family with a simple coalesced neutral mode
has at most one complex spectral value in a common small disk. -/
theorem matrix_complex_slow_root_unique_eventually
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (J : ℝ → Matrix ι ι ℝ) (hJ : ContinuousAt J 0)
    (hspec : SimpleNeutralHurwitzComplement (J 0)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ δ : ℝ in nhds 0,
        ∀ z w : ℂ, ‖z‖ < ρ → ‖w‖ < ρ →
          z ∈ spectrum ℂ ((J δ).map (algebraMap ℝ ℂ)) →
          w ∈ spectrum ℂ ((J δ).map (algebraMap ℝ ℂ)) → z = w := by
  let P : ℝ → ℂ[X] := fun δ => ((J δ).map (algebraMap ℝ ℂ)).charpoly
  have hN : 1 < Fintype.card ι + 1 := by
    have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ‹Nonempty ι›
    omega
  have hdegree (δ : ℝ) : (P δ).natDegree < Fintype.card ι + 1 := by
    simp [P]
  have hcoeff (n : ℕ) : ContinuousAt (fun δ => (P δ).coeff n) 0 := by
    have hc := matrix_real_charpoly_coeff_continuousAt J hJ n
    have hc' : ContinuousAt
        (fun δ => ((J δ).charpoly.coeff n : ℂ)) 0 :=
      ContinuousAt.comp
        (f := fun δ => (J δ).charpoly.coeff n) (x := 0)
        Complex.continuous_ofReal.continuousAt hc
    simpa only [P, Matrix.charpoly_map, Polynomial.coeff_map,
      ← Complex.coe_algebraMap] using hc'
  have hcoeff1 : (P 0).coeff 1 ≠ 0 := by
    have hc := simpleNeutral_real_charpoly_coeff_one_ne_zero (J 0) hspec
    simpa only [P, Matrix.charpoly_map, Polynomial.coeff_map,
      ← Complex.coe_algebraMap] using
      (Complex.ofReal_ne_zero.mpr hc)
  obtain ⟨ρ, hρ, huniq⟩ := complex_polynomial_family_unique_root_near_zero
    P (Fintype.card ι + 1) hN hdegree hcoeff hcoeff1
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [huniq] with δ hδ z w hz hw hzroot hwroot
  exact hδ z w hz hw
    (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hzroot)
    (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hwroot)

/-- The nearby complex spectral root of the continuous real matrix family
is algebraically simple, as witnessed by a nonzero polynomial derivative. -/
theorem matrix_complex_slow_root_derivative_near_nonzero_eventually
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (J : ℝ → Matrix ι ι ℝ) (hJ : ContinuousAt J 0)
    (hspec : SimpleNeutralHurwitzComplement (J 0)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ δ : ℝ in nhds 0,
        ∀ z : ℂ, ‖z‖ < ρ →
          (((J δ).map (algebraMap ℝ ℂ)).charpoly).derivative.eval z ≠ 0 := by
  let P : ℝ → ℂ[X] := fun δ => ((J δ).map (algebraMap ℝ ℂ)).charpoly
  have hdegree (δ : ℝ) : (P δ).natDegree < Fintype.card ι + 1 := by
    simp [P]
  have hcoeff (n : ℕ) : ContinuousAt (fun δ => (P δ).coeff n) 0 := by
    have hc := matrix_real_charpoly_coeff_continuousAt J hJ n
    have hc' : ContinuousAt
        (fun δ => ((J δ).charpoly.coeff n : ℂ)) 0 :=
      ContinuousAt.comp
        (f := fun δ => (J δ).charpoly.coeff n) (x := 0)
        Complex.continuous_ofReal.continuousAt hc
    simpa only [P, Matrix.charpoly_map, Polynomial.coeff_map,
      ← Complex.coe_algebraMap] using hc'
  have hcoeff1 : (P 0).coeff 1 ≠ 0 := by
    have hc := simpleNeutral_real_charpoly_coeff_one_ne_zero (J 0) hspec
    simpa only [P, Matrix.charpoly_map, Polynomial.coeff_map,
      ← Complex.coe_algebraMap] using
      (Complex.ofReal_ne_zero.mpr hc)
  exact complex_polynomial_family_derivative_near_nonzero
    P (Fintype.card ι + 1) hdegree hcoeff hcoeff1

/-- A literal split equilibrium has one nearby real characteristic root,
and every complex spectral value in the same small disk equals it. -/
theorem split_slow_root_complex_unique_eventually
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
          |x| < ρ ∧
          (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (splitRetunedRates m r τ δ ε)
            (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).charpoly.IsRoot x ∧
          ∀ z : ℂ,
            ‖z‖ < ρ →
            z ∈ spectrum ℂ
              ((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
                (splitRetunedRates m r τ δ ε)
                (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).map
                  (algebraMap ℝ ℂ)) →
            z = (x : ℂ) := by
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
  have hsource : SimpleNeutralHurwitzComplement (J 0) := by
    rw [hzero]
    exact hspec
  obtain ⟨ρ, hρ, huniq⟩ :=
    matrix_complex_slow_root_unique_eventually J hJ hsource
  have hexists := split_real_slow_root_eventually
    m r τ ε hr hD₀ hB₀ hspec j ρ hρ
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [huniq, hexists] with δ huniq hexists
  obtain ⟨x, hx, hroot⟩ := hexists
  have hrootC : (x : ℂ) ∈ spectrum ℂ ((J δ).map (algebraMap ℝ ℂ)) := by
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    simpa only [Matrix.charpoly_map, ← Complex.coe_algebraMap] using
      (Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) hroot)
  have hxC : ‖(x : ℂ)‖ < ρ := by simpa using hx
  exact ⟨x, hx, hroot,
    fun z hz hzs => huniq z (x : ℂ) hz hxC hzs hrootC⟩

/-- Every sufficiently small split has one simple real slow eigenvalue;
every other complex eigenvalue is strictly left of the imaginary axis. The
sign of the slow eigenvalue remains to be determined. -/
theorem split_slow_mode_simple_transverse_left_eventually
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
          |x| < ρ ∧
          (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (splitRetunedRates m r τ δ ε)
            (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).charpoly.IsRoot x ∧
          (((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (splitRetunedRates m r τ δ ε)
            (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).map
              (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
          ∀ z : ℂ,
            z ∈ spectrum ℂ
              ((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
                (splitRetunedRates m r τ δ ε)
                (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).map
                  (algebraMap ℝ ℂ)) →
            z.re < 0 ∨ z = (x : ℂ) := by
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
  have hsource : SimpleNeutralHurwitzComplement (J 0) := by
    rw [hzero]
    exact hspec
  obtain ⟨ρu, hρu, huniq⟩ :=
    matrix_complex_slow_root_unique_eventually J hJ hsource
  obtain ⟨ρd, hρd, hderiv⟩ :=
    matrix_complex_slow_root_derivative_near_nonzero_eventually J hJ hsource
  let ρ := min ρu ρd
  have hρ : 0 < ρ := lt_min hρu hρd
  have hρu' : ρ ≤ ρu := min_le_left ..
  have hρd' : ρ ≤ ρd := min_le_right ..
  have hexists := split_real_slow_root_eventually
    m r τ ε hr hD₀ hB₀ hspec j ρ hρ
  have hnear := split_spectrum_eventually_left_or_near_zero
    m r τ ε hr hD₀ hB₀ hspec j ρ hρ
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [huniq, hderiv, hexists, hnear] with
    δ huniq hderiv hexists hnear
  obtain ⟨x, hx, hroot⟩ := hexists
  have hxC : ‖(x : ℂ)‖ < ρ := by simpa using hx
  have hrootC : (x : ℂ) ∈ spectrum ℂ ((J δ).map (algebraMap ℝ ℂ)) := by
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    simpa only [Matrix.charpoly_map, ← Complex.coe_algebraMap] using
      (Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) hroot)
  refine ⟨x, hx, hroot,
    hderiv (x : ℂ) (lt_of_lt_of_le hxC hρd'), ?_⟩
  intro z hz
  rcases hnear z hz with hzleft | hznear
  · exact Or.inl hzleft
  · exact Or.inr (huniq z (x : ℂ)
      (lt_of_lt_of_le hznear hρu')
      (lt_of_lt_of_le hxC hρu') hz hrootC)

/-- Exact spectral conclusion at one split equilibrium. The remaining
unresolved datum is the sign of `x`. -/
def SplitSlowModeCertificate
    (m : ℕ) (r τ δ ε : ℝ)
    (j : Fin (2*(m+1)+1)) (ρ : ℝ) : Prop :=
  ∃ x : ℝ,
    |x| < ρ ∧
    (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (splitRetunedRates m r τ δ ε)
      (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).charpoly.IsRoot x ∧
    (((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (splitRetunedRates m r τ δ ε)
      (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).map
        (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
    ∀ z : ℂ,
      z ∈ spectrum ℂ
        ((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (splitRetunedRates m r τ δ ε)
          (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).map
            (algebraMap ℝ ℂ)) →
      z.re < 0 ∨ z = (x : ℂ)

/-- The exact remaining stability test for a certified split state is the
sign of its one simple real slow eigenvalue. -/
theorem splitSlowModeCertificate_hurwitz_iff_negative
    (m : ℕ) (r τ δ ε : ℝ)
    (j : Fin (2*(m+1)+1)) (ρ : ℝ)
    (hcert : SplitSlowModeCertificate m r τ δ ε j ρ) :
    ∃ x : ℝ,
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (splitRetunedRates m r τ δ ε)
        (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).charpoly.IsRoot x ∧
      ((∀ z : ℂ,
          z ∈ spectrum ℂ
            ((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
              (splitRetunedRates m r τ δ ε)
              (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).map
                (algebraMap ℝ ℂ)) → z.re < 0) ↔ x < 0) := by
  obtain ⟨x, _, hroot, _, hrest⟩ := hcert
  refine ⟨x, hroot, ?_⟩
  have hxspec : (x : ℂ) ∈ spectrum ℂ
      ((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (splitRetunedRates m r τ δ ε)
        (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).map
          (algebraMap ℝ ℂ)) := by
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    simpa only [Matrix.charpoly_map, ← Complex.coe_algebraMap] using
      (Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) hroot)
  constructor
  · intro hstable
    simpa using hstable (x : ℂ) hxspec
  · intro hxneg z hz
    rcases hrest z hz with hzleft | heq
    · exact hzleft
    · rw [heq]
      simpa using hxneg

/-- One sufficiently small splitting parameter gives the exact simple slow
mode and left-half-plane transverse spectrum at every member of the finite
family, with a fixed radius for each state. -/
theorem split_slow_mode_uniform_eventually
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
          SplitSlowModeCertificate m r τ δ ε j (ρ j) := by
  classical
  have h (j : Fin (2*(m+1)+1)) :=
    split_slow_mode_simple_transverse_left_eventually
      m r τ ε hr hD₀ hB₀ hspec j
  choose ρ hρ hEv using h
  refine ⟨ρ, hρ, ?_⟩
  apply Filter.eventually_all.mpr
  intro j
  simpa only [SplitSlowModeCertificate] using hEv j

/-- The common-rate positive split family and its exact one-slow-mode
spectral decomposition coexist for one small positive split. -/
theorem split_admissible_simple_slow_uniform_eventually
    (m : ℕ) (r τ ε : ℝ)
    (hr : 0 < r) (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
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
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        SplitRetunedFamilyAdmissible m r τ δ ε ∧
        ∀ j : Fin (2*(m+1)+1),
          SplitSlowModeCertificate m r τ δ ε j (ρ j) := by
  obtain ⟨ρ, hρ, hslow⟩ := split_slow_mode_uniform_eventually
    m r τ ε (ne_of_gt hr) hD₀ hB₀ hspec
  have hslow' : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j : Fin (2*(m+1)+1),
        SplitSlowModeCertificate m r τ δ ε j (ρ j) :=
    hslow.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hgeom := splitRetunedSource_eventually_admissible
    m r τ ε hr hτ hε hε1 hD₀ hB₀
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [hgeom, hslow'] with δ hgeom hslow
  exact ⟨hgeom, hslow⟩

/-- For every chain size, the source parameters can be chosen so that one
positive split yields the full finite family with a single simple real slow
eigenvalue and stable transverse spectrum at every state. The theorem leaves
the slow eigenvalue's sign open. -/
theorem coalescedSpectral_splitFamily_simpleSlow_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        ∀ᶠ ε : ℝ in nhds 0,
          0 < ε → ε ≤ 1 →
            ∃ ρ : Fin (2*(m+1)+1) → ℝ,
              (∀ j, 0 < ρ j) ∧
              ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
                SplitRetunedFamilyAdmissible m r τ δ ε ∧
                ∀ j : Fin (2*(m+1)+1),
                  SplitSlowModeCertificate m r τ δ ε j (ρ j) := by
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
  exact split_admissible_simple_slow_uniform_eventually
    m r τ ε hr hτ hε hε1 hconv.1 hconv.2 hspec

end
end PhosphorylationStableCapacity
