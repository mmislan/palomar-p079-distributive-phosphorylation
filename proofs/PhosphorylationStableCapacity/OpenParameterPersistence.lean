module
import all proofs.PhosphorylationStableCapacity.FullFieldCutoff
import all proofs.PhosphorylationStableCapacity.SplitJacobianContinuity
public import proofs.PhosphorylationStableCapacity.FullHyperbolicConfiguration435
public import proofs.PhosphorylationStableCapacity.UniversalEquilibriumCount
public import proofs.PhosphorylationStableCapacity.RationalFullFamilyAllSizes435
public import proofs.PhosphorylationStableCapacity.SaddleSpectrumOpenness435
public import Mathlib.Analysis.Calculus.ImplicitContDiff

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Filter
open scoped Topology Matrix.Norms.L2Operator

/-- Strict left-half-plane spectra are an open condition on the real
matrix entries. -/
theorem isOpen_isHurwitz_matrix
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsOpen {A : Matrix ι ι ℝ | IsHurwitz A} := by
  classical
  apply isOpen_iff_mem_nhds.mpr
  intro A hA
  let U : Set ℂ := {z | z.re < 0}
  have hU : IsOpen U := isOpen_Iio.preimage Complex.continuous_re
  have hspec : spectrum ℂ (A.map (algebraMap ℝ ℂ)) ⊆ U := by
    intro z hz
    exact hA z ((Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz).eq_zero)
  have hnear :=
    (upperHemicontinuous_spectrum ℂ (Matrix ι ι ℂ)).forall_isOpen
      (A.map (algebraMap ℝ ℂ)) U hU hspec
  have hmap : Continuous (fun B : Matrix ι ι ℝ =>
      B.map (algebraMap ℝ ℂ)) := by
    apply continuous_matrix
    intro i j
    exact Complex.continuous_ofReal.comp (continuous_apply j |>.comp (continuous_apply i))
  apply Filter.mem_of_superset (hmap.continuousAt.tendsto.eventually hnear)
  intro B hB z hz
  exact hB ((Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    (Polynomial.IsRoot.def.mpr hz)))

/-- Hyperbolicity allows stable and unstable eigenvalues but excludes
the imaginary axis; it is open under entrywise matrix perturbation. -/
def IsHyperbolicMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Prop :=
  ∀ z : ℂ, z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) → z.re ≠ 0

theorem isOpen_isHyperbolicMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsOpen {A : Matrix ι ι ℝ | IsHyperbolicMatrix A} := by
  classical
  apply isOpen_iff_mem_nhds.mpr
  intro A hA
  let U : Set ℂ := {z | z.re ≠ 0}
  have hU : IsOpen U := isOpen_ne.preimage Complex.continuous_re
  have hspec : spectrum ℂ (A.map (algebraMap ℝ ℂ)) ⊆ U :=
    fun z hz => hA z hz
  have hnear :=
    (upperHemicontinuous_spectrum ℂ (Matrix ι ι ℂ)).forall_isOpen
      (A.map (algebraMap ℝ ℂ)) U hU hspec
  have hmap : Continuous (fun B : Matrix ι ι ℝ =>
      B.map (algebraMap ℝ ℂ)) := by
    apply continuous_matrix
    intro i j
    exact Complex.continuous_ofReal.comp (continuous_apply j |>.comp (continuous_apply i))
  exact Filter.mem_of_superset (hmap.continuousAt.tendsto.eventually hnear)
    (fun B hB z hz => hB hz)

theorem isHyperbolicMatrix_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : IsHyperbolicMatrix A) : A.det ≠ 0 := by
  intro hdet
  have hmap : (A.map (algebraMap ℝ ℂ)).det = 0 := by
    change Matrix.det ((algebraMap ℝ ℂ).mapMatrix A) = 0
    rw [← RingHom.map_det, hdet, map_zero]
  have hmap' : (A.map Complex.ofReal).det = 0 := by
    simpa using hmap
  have hroot : ((A.map (algebraMap ℝ ℂ)).charpoly).eval 0 = 0 := by
    rw [Matrix.eval_charpoly]
    simp [Matrix.det_neg, hmap']
  have hzero : (0 : ℂ) ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
      (Polynomial.IsRoot.def.mpr hroot)
  have hne := hA 0 hzero
  norm_num at hne

/-- Six rate arrays and three conserved totals as one parameter. -/
abbrev CapacityParameter (n : ℕ) := RateVector n × (ℝ × ℝ × ℝ)

/-- The literal restricted field with rates and totals varying jointly. -/
def capacityParameterField {n : ℕ}
    (q : CapacityParameter n × CoordinateSpace n) : CoordinateSpace n :=
  restrictedFieldEuclid q.1.2.1 q.1.2.2.1 q.1.2.2.2
    (ratesFromVector q.1.1) q.2

theorem contDiff_capacityParameterField (n : ℕ) :
    ContDiff ℝ 2 (capacityParameterField (n := n)) := by
  classical
  unfold capacityParameterField restrictedFieldEuclid restrictedField
    ratesFromVector toCoordinateSpace chart field unChart ofCoordinateSpace
    kinaseNet phosphataseNet
  dsimp
  fun_prop

theorem fderiv_capacityParameterField_inr {n : ℕ}
    (p : CapacityParameter n) (u : CoordinateSpace n) :
    fderiv ℝ (capacityParameterField (n := n)) (p, u) ∘L
      ContinuousLinearMap.inr ℝ (CapacityParameter n) (CoordinateSpace n) =
    restrictedJacobian p.2.1 p.2.2.1 p.2.2.2
      (ratesFromVector p.1) u := by
  have hι : HasFDerivAt (fun v : CoordinateSpace n => (p, v))
      (ContinuousLinearMap.inr ℝ (CapacityParameter n) (CoordinateSpace n)) u := by
    have hclm : ContinuousLinearMap.inr ℝ (CapacityParameter n) (CoordinateSpace n) =
        (0 : CoordinateSpace n →L[ℝ] CapacityParameter n).prod
          (ContinuousLinearMap.id ℝ (CoordinateSpace n)) := by
      apply ContinuousLinearMap.ext
      intro v
      change (0, v) = (0, v)
      rfl
    rw [hclm]
    simpa only [id_eq] using
      (hasFDerivAt_const (x := u) p).prodMk (hasFDerivAt_id u)
  have hf : DifferentiableAt ℝ (capacityParameterField (n := n)) (p, u) :=
    (contDiff_capacityParameterField n).differentiable (by norm_num) _
  have hcomp := fderiv_comp
    (f := fun v : CoordinateSpace n => (p, v))
    (g := capacityParameterField (n := n)) (x := u)
    hf hι.differentiableAt
  simpa only [Function.comp_def, hι.fderiv, restrictedJacobian,
    capacityParameterField] using hcomp.symm

/-- Nonsingularity of the literal class Jacobian is precisely the
invertible partial derivative required by the implicit-function theorem. -/
theorem capacity_parameter_field_regular_of_det_ne_zero {n : ℕ}
    (p : CapacityParameter n) (u : CoordinateSpace n)
    (hdet : (restrictedJacobianMatrix p.2.1 p.2.2.1 p.2.2.2
      (ratesFromVector p.1) u).det ≠ 0) :
    (fderiv ℝ (capacityParameterField (n := n)) (p, u) ∘L
      ContinuousLinearMap.inr ℝ (CapacityParameter n) (CoordinateSpace n)).IsInvertible := by
  let L := restrictedJacobian p.2.1 p.2.2.1 p.2.2.2
    (ratesFromVector p.1) u
  have hmatrix : IsUnit (LinearMap.toMatrix (coordinateBasis n)
      (coordinateBasis n) L.toLinearMap) := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    exact isUnit_iff_ne_zero.mpr hdet
  have hlin : IsUnit L.toLinearMap :=
    (LinearMap.isUnit_toMatrix_iff (coordinateBasis n)).1 hmatrix
  have hclm : IsUnit L :=
    ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr hlin
  have hbij : Function.Bijective L :=
    L.isUnit_iff_bijective.mp hclm
  let e := ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hbij.1)
    (LinearMap.range_eq_top.mpr hbij.2)
  rw [fderiv_capacityParameterField_inr]
  exact ⟨e, by
    apply ContinuousLinearMap.ext
    intro x
    rfl⟩

/-- The physical class Jacobian varies continuously when all rates,
totals, and class coordinates vary. -/
theorem continuous_capacityParameterJacobianMatrix (n : ℕ) :
    Continuous (fun q : CapacityParameter n × CoordinateSpace n =>
      restrictedJacobianMatrix q.1.2.1 q.1.2.2.1 q.1.2.2.2
        (ratesFromVector q.1.1) q.2) := by
  have hproj : ContDiff ℝ 1
      (fun q : (CapacityParameter n × CoordinateSpace n) × CoordinateSpace n =>
        (q.1.1, q.2)) := by fun_prop
  have hf : ContDiff ℝ 1 (capacityParameterField (n := n)) :=
    (contDiff_capacityParameterField n).of_le (by norm_num)
  have haux : ContDiff ℝ 1
      (fun q : (CapacityParameter n × CoordinateSpace n) × CoordinateSpace n =>
        capacityParameterField (q.1.1, q.2)) := hf.comp hproj
  have hc : Continuous (fun q : CapacityParameter n × CoordinateSpace n =>
      restrictedJacobian q.1.2.1 q.1.2.2.1 q.1.2.2.2
        (ratesFromVector q.1.1) q.2) := by
    have h := Continuous.fderiv_one
      (f := fun q : CapacityParameter n × CoordinateSpace n =>
        fun u : CoordinateSpace n => capacityParameterField (q.1, u))
      haux continuous_snd
    simpa only [restrictedJacobian, capacityParameterField] using h
  simpa only [restrictedJacobianMatrix, Function.comp_def] using
    (continuous_coordinateJacobian_matrix n).comp hc

theorem isOpen_capacityParameterOneUnstableSaddle {n : ℕ}
    (hn : 0 < n) :
    IsOpen {q : CapacityParameter n × CoordinateSpace n |
      IsOneUnstableSaddle q.1.2.1 q.1.2.2.1 q.1.2.2.2
        (ratesFromVector q.1.1) q.2} := by
  have hNonempty : Nonempty (Fin n ⊕ (Fin n ⊕ Fin n)) :=
    ⟨Sum.inl ⟨0, hn⟩⟩
  simpa only [IsOneUnstableSaddle, Set.preimage, Set.mem_ofPred_eq] using
    ((@isOpen_isOneUnstableSaddle_matrix _ _ _ hNonempty).preimage
      (continuous_capacityParameterJacobianMatrix n))

/-- Positivity of the reconstructed physical state is open jointly in
the three totals and the class coordinates. -/
theorem isOpen_capacityParameterStatePositive (n : ℕ) :
    IsOpen {q : CapacityParameter n × CoordinateSpace n |
      (unChart q.1.2.1 q.1.2.2.1 q.1.2.2.2
        (ofCoordinateSpace q.2)).Positive} := by
  let state : CapacityParameter n × CoordinateSpace n → State n :=
    fun q => unChart q.1.2.1 q.1.2.2.1 q.1.2.2.2 (ofCoordinateSpace q.2)
  have hS (i : Fin (n+1)) : Continuous (fun q => (state q).S i) := by
    cases i using Fin.cases with
    | zero =>
      dsimp [state, unChart, ofCoordinateSpace]
      fun_prop
    | succ j =>
      dsimp [state, unChart, ofCoordinateSpace]
      fun_prop
  have hE : Continuous (fun q => (state q).E) := by
    dsimp [state, unChart, ofCoordinateSpace]
    fun_prop
  have hF : Continuous (fun q => (state q).F) := by
    dsimp [state, unChart, ofCoordinateSpace]
    fun_prop
  have hC (i : Fin n) : Continuous (fun q => (state q).C i) := by
    dsimp [state, unChart, ofCoordinateSpace]
    fun_prop
  have hD (i : Fin n) : Continuous (fun q => (state q).D i) := by
    dsimp [state, unChart, ofCoordinateSpace]
    fun_prop
  have hSopen : IsOpen {q | ∀ i : Fin (n+1), 0 < (state q).S i} := by
    have heq : {q | ∀ i : Fin (n+1), 0 < (state q).S i} =
        ⋂ i : Fin (n+1), {q | 0 < (state q).S i} := by
      ext q
      simp
    rw [heq]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (hS i))
  have hCopen : IsOpen {q | ∀ i : Fin n, 0 < (state q).C i} := by
    have heq : {q | ∀ i : Fin n, 0 < (state q).C i} =
        ⋂ i : Fin n, {q | 0 < (state q).C i} := by
      ext q
      simp
    rw [heq]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (hC i))
  have hDopen : IsOpen {q | ∀ i : Fin n, 0 < (state q).D i} := by
    have heq : {q | ∀ i : Fin n, 0 < (state q).D i} =
        ⋂ i : Fin n, {q | 0 < (state q).D i} := by
      ext q
      simp
    rw [heq]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (hD i))
  change IsOpen {q | (state q).Positive}
  simpa only [State.Positive, Set.ofPred_and] using
    hSopen.inter ((isOpen_lt continuous_const hE).inter
      ((isOpen_lt continuous_const hF).inter (hCopen.inter hDopen)))

/-- The physical positivity domain for rates and totals is open in the
full ambient parameter space. -/
theorem isOpen_capacityParameterPositive (n : ℕ) :
    IsOpen {p : CapacityParameter n |
      (ratesFromVector p.1).Positive ∧
        0 < p.2.1 ∧ 0 < p.2.2.1 ∧ 0 < p.2.2.2} := by
  have hrate_i (i : Fin n) : IsOpen
      {p : CapacityParameter n |
        0 < (ratesFromVector p.1).a i ∧
        0 < (ratesFromVector p.1).b i ∧
        0 < (ratesFromVector p.1).c i ∧
        0 < (ratesFromVector p.1).alpha i ∧
        0 < (ratesFromVector p.1).beta i ∧
        0 < (ratesFromVector p.1).gamma i} := by
    have ha : Continuous (fun p : CapacityParameter n =>
        (ratesFromVector p.1).a i) := by
      dsimp [ratesFromVector]
      fun_prop
    have hb : Continuous (fun p : CapacityParameter n =>
        (ratesFromVector p.1).b i) := by
      dsimp [ratesFromVector]
      fun_prop
    have hc : Continuous (fun p : CapacityParameter n =>
        (ratesFromVector p.1).c i) := by
      dsimp [ratesFromVector]
      fun_prop
    have hα : Continuous (fun p : CapacityParameter n =>
        (ratesFromVector p.1).alpha i) := by
      dsimp [ratesFromVector]
      fun_prop
    have hβ : Continuous (fun p : CapacityParameter n =>
        (ratesFromVector p.1).beta i) := by
      dsimp [ratesFromVector]
      fun_prop
    have hγ : Continuous (fun p : CapacityParameter n =>
        (ratesFromVector p.1).gamma i) := by
      dsimp [ratesFromVector]
      fun_prop
    simpa only [Set.ofPred_and] using
      (isOpen_lt continuous_const ha).inter
        ((isOpen_lt continuous_const hb).inter
          ((isOpen_lt continuous_const hc).inter
            ((isOpen_lt continuous_const hα).inter
              ((isOpen_lt continuous_const hβ).inter
                (isOpen_lt continuous_const hγ)))))
  have hrate : IsOpen {p : CapacityParameter n |
      (ratesFromVector p.1).Positive} := by
    have heq : {p : CapacityParameter n | (ratesFromVector p.1).Positive} =
        ⋂ i : Fin n, {p : CapacityParameter n |
          0 < (ratesFromVector p.1).a i ∧
          0 < (ratesFromVector p.1).b i ∧
          0 < (ratesFromVector p.1).c i ∧
          0 < (ratesFromVector p.1).alpha i ∧
          0 < (ratesFromVector p.1).beta i ∧
          0 < (ratesFromVector p.1).gamma i} := by
      ext p
      simp [Rates.Positive]
    rw [heq]
    exact isOpen_iInter_of_finite hrate_i
  have hET : Continuous (fun p : CapacityParameter n => p.2.1) := by fun_prop
  have hFT : Continuous (fun p : CapacityParameter n => p.2.2.1) := by fun_prop
  have hST : Continuous (fun p : CapacityParameter n => p.2.2.2) := by fun_prop
  simpa only [Set.ofPred_and] using
    hrate.inter ((isOpen_lt continuous_const hET).inter
      ((isOpen_lt continuous_const hFT).inter
        (isOpen_lt continuous_const hST)))

/-- A regular equilibrium of a smooth finite-dimensional parameter family
continues to nearby parameters. The continuation uses the *same* varying
parameter in the equation. -/
theorem regular_equilibrium_local_continuation
    {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : P × E → E) (p₀ : P) (x₀ : E)
    (hf : ContDiffAt ℝ 2 f (p₀, x₀))
    (hz : f (p₀, x₀) = 0)
    (hreg : (fderiv ℝ f (p₀, x₀) ∘L
      ContinuousLinearMap.inr ℝ P E).IsInvertible) :
    ∃ ψ : P → E, ContinuousAt ψ p₀ ∧ ψ p₀ = x₀ ∧
      ∀ᶠ p in 𝓝 p₀, f (p, ψ p) = 0 := by
  let ψ := hf.implicitFunction (by norm_num) hreg
  refine ⟨ψ, (hf.contDiffAt_implicitFunction (by norm_num) hreg).continuousAt,
    hf.implicitFunction_apply_self (by norm_num) hreg, ?_⟩
  simpa only [hz] using hf.eventually_apply_implicitFunction (by norm_num) hreg

/-- Any finite list of distinct regular equilibria, with arbitrary open
conditions on its parameter-state pairs, persists on one nonempty open
parameter neighborhood. This is the finite-family step needed for the
simultaneous split construction. -/
theorem finite_regular_family_open_persistence
    {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (N : ℕ) (f : P × E → E) (good : Fin N → Set (P × E))
    (p₀ : P) (x₀ : Fin N → E)
    (hf : ContDiff ℝ 2 f)
    (hgood : ∀ i, IsOpen (good i))
    (hbase : Function.Injective x₀ ∧
      ∀ i, f (p₀, x₀ i) = 0 ∧ (p₀, x₀ i) ∈ good i ∧
        (fderiv ℝ f (p₀, x₀ i) ∘L
          ContinuousLinearMap.inr ℝ P E).IsInvertible) :
    ∃ s : Set P, IsOpen s ∧ p₀ ∈ s ∧
      ∀ p ∈ s, ∃ x : Fin N → E, Function.Injective x ∧
        ∀ i, f (p, x i) = 0 ∧ (p, x i) ∈ good i := by
  classical
  have hcontinuation (i : Fin N) :=
    regular_equilibrium_local_continuation f p₀ (x₀ i)
      hf.contDiffAt (hbase.2 i).1 (hbase.2 i).2.2
  let ψ : Fin N → P → E := fun i => Classical.choose (hcontinuation i)
  have hψ (i : Fin N) : ContinuousAt (ψ i) p₀ ∧
      ψ i p₀ = x₀ i ∧ ∀ᶠ p in 𝓝 p₀, f (p, ψ i p) = 0 :=
    Classical.choose_spec (hcontinuation i)
  have hzero : ∀ᶠ p in 𝓝 p₀, ∀ i, f (p, ψ i p) = 0 :=
    Filter.eventually_all.mpr (fun i => (hψ i).2.2)
  have hmem : ∀ᶠ p in 𝓝 p₀, ∀ i, (p, ψ i p) ∈ good i := by
    apply Filter.eventually_all.mpr
    intro i
    have ht : Tendsto (fun p : P => (p, ψ i p)) (𝓝 p₀) (𝓝 (p₀, x₀ i)) := by
      simpa only [id_eq, (hψ i).2.1] using
        tendsto_id.prodMk_nhds (hψ i).1.tendsto
    exact ht.eventually ((hgood i).mem_nhds (hbase.2 i).2.1)
  have hinj : ∀ᶠ p in 𝓝 p₀, Function.Injective (fun i => ψ i p) := by
    have hpairs : ∀ᶠ p in 𝓝 p₀,
        ∀ i j : Fin N, i ≠ j → ψ i p ≠ ψ j p := by
      apply Filter.eventually_all.mpr
      intro i
      apply Filter.eventually_all.mpr
      intro j
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall (fun _ h => (h hij).elim)
      · have hne : ψ i p₀ ≠ ψ j p₀ := by
          simpa only [(hψ i).2.1, (hψ j).2.1] using hbase.1.ne hij
        exact (((hψ i).1.ne_iff_eventually_ne (hψ j).1).mp hne).mono
          (fun _ h _ => h)
    filter_upwards [hpairs] with p hp i j heq
    by_contra hij
    exact hp i j hij heq
  let s₀ : Set P := {p | Function.Injective (fun i => ψ i p) ∧
    ∀ i, f (p, ψ i p) = 0 ∧ (p, ψ i p) ∈ good i}
  have hs₀ : s₀ ∈ 𝓝 p₀ := by
    filter_upwards [hinj, hzero, hmem] with p hi hz hm
    exact ⟨hi, fun i => ⟨hz i, hm i⟩⟩
  obtain ⟨s, hs_subset, hs_open, hp₀⟩ := mem_nhds_iff.mp hs₀
  refine ⟨s, hs_open, hp₀, ?_⟩
  intro p hp
  exact ⟨fun i => ψ i p, (hs_subset hp).1, (hs_subset hp).2⟩

/-- A finite family of literal positive hyperbolic class equilibria
continues under independent perturbations of all six rate arrays and all
three conserved totals. Any designated Hurwitz members stay Hurwitz. -/
theorem capacity_open_hyperbolic_family_of_base
    (n N : ℕ) (hn : 0 < n)
    (sink saddle : Fin N → Prop)
    (p₀ : CapacityParameter n) (x₀ : Fin N → CoordinateSpace n)
    (hbase : Function.Injective x₀ ∧
      ∀ j, (unChart p₀.2.1 p₀.2.2.1 p₀.2.2.2
          (ofCoordinateSpace (x₀ j))).Positive ∧
        capacityParameterField (p₀, x₀ j) = 0 ∧
        IsHyperbolicMatrix
          (restrictedJacobianMatrix p₀.2.1 p₀.2.2.1 p₀.2.2.2
            (ratesFromVector p₀.1) (x₀ j)) ∧
        (sink j → IsLinearlyStable p₀.2.1 p₀.2.2.1 p₀.2.2.2
          (ratesFromVector p₀.1) (x₀ j)) ∧
        (saddle j → IsOneUnstableSaddle
          p₀.2.1 p₀.2.2.1 p₀.2.2.2
          (ratesFromVector p₀.1) (x₀ j))) :
    ∃ s : Set (CapacityParameter n), IsOpen s ∧ p₀ ∈ s ∧
      ∀ p ∈ s, ∃ x : Fin N → CoordinateSpace n,
        Function.Injective x ∧ ∀ j,
          (unChart p.2.1 p.2.2.1 p.2.2.2
            (ofCoordinateSpace (x j))).Positive ∧
          capacityParameterField (p, x j) = 0 ∧
          IsHyperbolicMatrix
            (restrictedJacobianMatrix p.2.1 p.2.2.1 p.2.2.2
              (ratesFromVector p.1) (x j)) ∧
          (sink j → IsLinearlyStable p.2.1 p.2.2.1 p.2.2.2
            (ratesFromVector p.1) (x j)) ∧
          (saddle j → IsOneUnstableSaddle
            p.2.1 p.2.2.1 p.2.2.2
            (ratesFromVector p.1) (x j)) := by
  let J : CapacityParameter n × CoordinateSpace n →
      Matrix (Fin n ⊕ (Fin n ⊕ Fin n))
        (Fin n ⊕ (Fin n ⊕ Fin n)) ℝ :=
    fun q => restrictedJacobianMatrix q.1.2.1 q.1.2.2.1 q.1.2.2.2
      (ratesFromVector q.1.1) q.2
  let good (j : Fin N) : Set (CapacityParameter n × CoordinateSpace n) :=
    {q | (unChart q.1.2.1 q.1.2.2.1 q.1.2.2.2
          (ofCoordinateSpace q.2)).Positive ∧
      IsHyperbolicMatrix (J q) ∧
      (sink j → IsHurwitz (J q)) ∧
      (saddle j → IsOneUnstableSaddle
        q.1.2.1 q.1.2.2.1 q.1.2.2.2
        (ratesFromVector q.1.1) q.2)}
  have hgood (j : Fin N) : IsOpen (good j) := by
    have hpos := isOpen_capacityParameterStatePositive n
    have hhyper : IsOpen {q | IsHyperbolicMatrix (J q)} :=
      isOpen_isHyperbolicMatrix.preimage
        (continuous_capacityParameterJacobianMatrix n)
    have hsink : IsOpen {q | sink j → IsHurwitz (J q)} := by
      by_cases hj : sink j
      · simpa [hj, J] using
          isOpen_isHurwitz_matrix.preimage
            (continuous_capacityParameterJacobianMatrix n)
      · simpa only [hj, false_implies, Set.ofPred_true] using
          (isOpen_univ : IsOpen (Set.univ : Set (CapacityParameter n × CoordinateSpace n)))
    have hsaddle : IsOpen {q : CapacityParameter n × CoordinateSpace n |
        saddle j → IsOneUnstableSaddle
          q.1.2.1 q.1.2.2.1 q.1.2.2.2
          (ratesFromVector q.1.1) q.2} := by
      by_cases hj : saddle j
      · simpa only [hj, true_implies] using
          isOpen_capacityParameterOneUnstableSaddle hn
      · simpa only [hj, false_implies, Set.ofPred_true] using
          (isOpen_univ : IsOpen (Set.univ : Set (CapacityParameter n × CoordinateSpace n)))
    exact hpos.inter (hhyper.inter (hsink.inter hsaddle))
  have hfamilystart : Function.Injective x₀ ∧
      ∀ j, capacityParameterField (p₀, x₀ j) = 0 ∧
        (p₀, x₀ j) ∈ good j ∧
        (fderiv ℝ (capacityParameterField (n := n)) (p₀, x₀ j) ∘L
          ContinuousLinearMap.inr ℝ (CapacityParameter n)
            (CoordinateSpace n)).IsInvertible := by
    refine ⟨hbase.1, ?_⟩
    intro j
    obtain ⟨hpos, heq, hhyper, hsink, hsaddle⟩ := hbase.2 j
    refine ⟨heq, ⟨hpos, hhyper, hsink, hsaddle⟩, ?_⟩
    exact capacity_parameter_field_regular_of_det_ne_zero p₀ (x₀ j)
      (isHyperbolicMatrix_det_ne_zero hhyper)
  obtain ⟨s, hsopen, hp₀, hpersist⟩ :=
    finite_regular_family_open_persistence N
      (capacityParameterField (n := n)) good p₀ x₀
      (contDiff_capacityParameterField n) hgood hfamilystart
  refine ⟨s, hsopen, hp₀, ?_⟩
  intro p hp
  obtain ⟨x, hinj, hstates⟩ := hpersist p hp
  refine ⟨x, hinj, ?_⟩
  intro j
  obtain ⟨heq, hpos, hhyper, hsink, hsaddle⟩ := hstates j
  exact ⟨hpos, heq, hhyper, hsink, hsaddle⟩

theorem isOneUnstableSaddle_isHyperbolic {n : ℕ}
    {ET FT ST : ℝ} {k : Rates n} {u : CoordinateSpace n}
    (h : IsOneUnstableSaddle ET FT ST k u) :
    IsHyperbolicMatrix (restrictedJacobianMatrix ET FT ST k u) := by
  obtain ⟨x, hx, _, _, hspec⟩ := h
  intro z hz
  rcases hspec z hz with hleft | heq
  · exact ne_of_lt hleft
  · rw [heq]
    simpa only [Complex.ofReal_re] using ne_of_gt hx

theorem isLinearlyStable_isHyperbolic {n : ℕ}
    {ET FT ST : ℝ} {k : Rates n} {u : CoordinateSpace n}
    (h : IsLinearlyStable ET FT ST k u) :
    IsHyperbolicMatrix (restrictedJacobianMatrix ET FT ST k u) := by
  intro z hz
  exact ne_of_lt (h z
    ((Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz).eq_zero))

/-- A base configuration with the prescribed even sinks and odd saddles
gives a nonempty open neighborhood of positive rate/total parameters.
Every parameter in it has the same number of distinct positive
hyperbolic equilibrium branches, and its even branches remain sinks.
The base rates/totals are explicit, so a rational witness may be used. -/
theorem capacity_open_full_hyperbolic_family_of_base
    (n : ℕ) (hn : 0 < n) (p₀ : CapacityParameter n)
    (x₀ : Fin (2*n-1) → CoordinateSpace n)
    (hparam : (ratesFromVector p₀.1).Positive ∧
      0 < p₀.2.1 ∧ 0 < p₀.2.2.1 ∧ 0 < p₀.2.2.2)
    (hinj : Function.Injective x₀)
    (hstates : ∀ j,
      (unChart p₀.2.1 p₀.2.2.1 p₀.2.2.2
        (ofCoordinateSpace (x₀ j))).Positive ∧
      capacityParameterField (p₀, x₀ j) = 0)
    (heven : ∀ j : Fin (2*n-1), Even j.val →
      IsLinearlyStable p₀.2.1 p₀.2.2.1 p₀.2.2.2
        (ratesFromVector p₀.1) (x₀ j))
    (hodd : ∀ j : Fin (2*n-1), Odd j.val →
      IsOneUnstableSaddle p₀.2.1 p₀.2.2.1 p₀.2.2.2
        (ratesFromVector p₀.1) (x₀ j)) :
    ∃ s : Set (CapacityParameter n), IsOpen s ∧ p₀ ∈ s ∧
      ∀ p ∈ s,
        ((ratesFromVector p.1).Positive ∧
          0 < p.2.1 ∧ 0 < p.2.2.1 ∧ 0 < p.2.2.2) ∧
        ∃ x : Fin (2*n-1) → CoordinateSpace n,
          Function.Injective x ∧ ∀ j,
            (unChart p.2.1 p.2.2.1 p.2.2.2
              (ofCoordinateSpace (x j))).Positive ∧
            capacityParameterField (p, x j) = 0 ∧
            IsHyperbolicMatrix
              (restrictedJacobianMatrix p.2.1 p.2.2.1 p.2.2.2
                (ratesFromVector p.1) (x j)) ∧
            (Even j.val → IsLinearlyStable p.2.1 p.2.2.1 p.2.2.2
              (ratesFromVector p.1) (x j)) ∧
            (Odd j.val → IsOneUnstableSaddle
              p.2.1 p.2.2.1 p.2.2.2
              (ratesFromVector p.1) (x j)) := by
  have hbase : Function.Injective x₀ ∧
      ∀ j, (unChart p₀.2.1 p₀.2.2.1 p₀.2.2.2
          (ofCoordinateSpace (x₀ j))).Positive ∧
        capacityParameterField (p₀, x₀ j) = 0 ∧
        IsHyperbolicMatrix
          (restrictedJacobianMatrix p₀.2.1 p₀.2.2.1 p₀.2.2.2
            (ratesFromVector p₀.1) (x₀ j)) ∧
        (Even j.val → IsLinearlyStable p₀.2.1 p₀.2.2.1 p₀.2.2.2
          (ratesFromVector p₀.1) (x₀ j)) ∧
        (Odd j.val → IsOneUnstableSaddle
          p₀.2.1 p₀.2.2.1 p₀.2.2.2
          (ratesFromVector p₀.1) (x₀ j)) := by
    refine ⟨hinj, ?_⟩
    intro j
    obtain ⟨hpos, heq⟩ := hstates j
    refine ⟨hpos, heq, ?_, heven j, hodd j⟩
    by_cases hj : Even j.val
    · exact isLinearlyStable_isHyperbolic (heven j hj)
    · have hjodd : Odd j.val := Nat.not_even_iff_odd.1 hj
      exact isOneUnstableSaddle_isHyperbolic (hodd j hjodd)
  obtain ⟨s, hsopen, hp₀, hpersist⟩ :=
    capacity_open_hyperbolic_family_of_base n (2*n-1) hn
      (fun j => Even j.val) (fun j => Odd j.val) p₀ x₀ hbase
  let t : Set (CapacityParameter n) :=
    s ∩ {p | (ratesFromVector p.1).Positive ∧
      0 < p.2.1 ∧ 0 < p.2.2.1 ∧ 0 < p.2.2.2}
  refine ⟨t, hsopen.inter (isOpen_capacityParameterPositive n),
    ⟨hp₀, hparam⟩, ?_⟩
  intro p hp
  exact ⟨hp.2, hpersist p hp.1⟩

/-- The universal `2n−1` ceiling converts the persisted injective
family into the exact equilibrium count for every nearby parameter. -/
theorem capacity_exact_count_of_full_positive_family
    (n : ℕ) (hn : 0 < n) (p : CapacityParameter n)
    (hparam : (ratesFromVector p.1).Positive ∧
      0 < p.2.1 ∧ 0 < p.2.2.1 ∧ 0 < p.2.2.2)
    (u : Fin (2*n-1) → CoordinateSpace n)
    (hinj : Function.Injective u)
    (hstates : ∀ j,
      (unChart p.2.1 p.2.2.1 p.2.2.2
        (ofCoordinateSpace (u j))).Positive ∧
      capacityParameterField (p, u j) = 0) :
    {x : State n | x.Positive ∧
      Equilibrium (ratesFromVector p.1) x ∧
      InClass p.2.1 p.2.2.1 p.2.2.2 x} =
      Set.range (fun j : Fin (2*n-1) =>
        unChart p.2.1 p.2.2.1 p.2.2.2
          (ofCoordinateSpace (u j))) ∧
    {x : State n | x.Positive ∧
      Equilibrium (ratesFromVector p.1) x ∧
      InClass p.2.1 p.2.2.1 p.2.2.2 x}.ncard = 2*n-1 := by
  let k := ratesFromVector p.1
  let ET := p.2.1
  let FT := p.2.2.1
  let ST := p.2.2.2
  let z : Fin (2*n-1) → State n :=
    fun j => unChart ET FT ST (ofCoordinateSpace (u j))
  let E : Set (State n) :=
    {x | x.Positive ∧ Equilibrium k x ∧ InClass ET FT ST x}
  obtain ⟨hfinite, hceiling⟩ :=
    positive_equilibria_finite_and_ncard_le_two_n_sub_one
      hn k hparam.1 ET FT ST
      hparam.2.1 hparam.2.2.1 hparam.2.2.2
  have hzinj : Function.Injective z := by
    intro i j hij
    apply hinj
    have h := congrArg (fun x : State n => toCoordinateSpace (chart x)) hij
    simpa only [z, chart_unChart, to_ofCoordinateSpace] using h
  have hsub : Set.range z ⊆ E := by
    rintro x ⟨j, rfl⟩
    have ⟨hpos, heq⟩ := hstates j
    refine ⟨hpos, ?_, unChart_inClass ET FT ST (ofCoordinateSpace (u j))⟩
    exact (restrictedFieldEuclid_eq_zero_iff ET FT ST k (u j)).1 heq
  have hcard : (Set.range z).ncard = 2*n-1 := by
    simpa using Set.ncard_range_of_injective hzinj
  have hge : 2*n-1 ≤ E.ncard := by
    rw [← hcard]
    exact Set.ncard_le_ncard hsub hfinite
  have heq : E = Set.range z := by
    apply (Set.eq_of_subset_of_ncard_le hsub ?_ hfinite).symm
    rw [hcard]
    exact hceiling
  change E.Finite at hfinite
  change E.ncard ≤ 2*n-1 at hceiling
  constructor
  · exact heq
  · change E.ncard = 2*n-1
    omega

/-- An open set of genuine positive mass-action parameter vectors has a
common-class family of `2n−1` distinct positive hyperbolic equilibria;
the even-indexed `n` states are Hurwitz sinks. -/
def OpenFullHyperbolicFamily (n : ℕ) : Prop :=
  ∃ s : Set (CapacityParameter n), IsOpen s ∧
    (∃ p₀ ∈ s,
      RationalRates (ratesFromVector p₀.1) ∧
      RationalReal p₀.2.1 ∧ RationalReal p₀.2.2.1 ∧
      RationalReal p₀.2.2.2 ∧
      ∃ x₀ : Fin (2*n-1) → CoordinateSpace n,
        Function.Injective x₀ ∧
        (∀ j, RationalState
          (unChart p₀.2.1 p₀.2.2.1 p₀.2.2.2
            (ofCoordinateSpace (x₀ j))) ∧
          (unChart p₀.2.1 p₀.2.2.1 p₀.2.2.2
            (ofCoordinateSpace (x₀ j))).Positive ∧
          capacityParameterField (p₀, x₀ j) = 0) ∧
        (∀ j : Fin (2*n-1), Odd j.val →
          IsOneUnstableSaddle p₀.2.1 p₀.2.2.1 p₀.2.2.2
            (ratesFromVector p₀.1) (x₀ j))) ∧
    ∀ p ∈ s,
      ((ratesFromVector p.1).Positive ∧
        0 < p.2.1 ∧ 0 < p.2.2.1 ∧ 0 < p.2.2.2) ∧
      ∃ x : Fin (2*n-1) → CoordinateSpace n,
        Function.Injective x ∧ (∀ j,
          (unChart p.2.1 p.2.2.1 p.2.2.2
            (ofCoordinateSpace (x j))).Positive ∧
          capacityParameterField (p, x j) = 0 ∧
          IsHyperbolicMatrix
            (restrictedJacobianMatrix p.2.1 p.2.2.1 p.2.2.2
              (ratesFromVector p.1) (x j)) ∧
          (Even j.val →
            IsLinearlyStable p.2.1 p.2.2.1 p.2.2.2
              (ratesFromVector p.1) (x j) ∧
            IsLocallyAsymptoticallyStableClass
              p.2.1 p.2.2.1 p.2.2.2
              (ratesFromVector p.1) (x j)) ∧
          (Odd j.val → IsOneUnstableSaddle
            p.2.1 p.2.2.1 p.2.2.2
            (ratesFromVector p.1) (x j))) ∧
        {y : State n | y.Positive ∧
          Equilibrium (ratesFromVector p.1) y ∧
          InClass p.2.1 p.2.2.1 p.2.2.2 y} =
            Set.range (fun j : Fin (2*n-1) =>
              unChart p.2.1 p.2.2.1 p.2.2.2
                (ofCoordinateSpace (x j))) ∧
        {y : State n | y.Positive ∧
          Equilibrium (ratesFromVector p.1) y ∧
          InClass p.2.1 p.2.2.1 p.2.2.2 y}.ncard = 2*n-1

theorem all_positive_sizes_open_full_hyperbolic_family
    (n : ℕ) (hn : 1 ≤ n) : OpenFullHyperbolicFamily n := by
  obtain ⟨k, ET, FT, ST, u, hkrational, hETrational,
    hFTrational, hSTrational, hk, hET, hFT, hST,
    hinj, hstates, hsinks, hsaddles, _, _⟩ :=
      all_positive_sizes_rational_full_family_with_sinks_and_saddles n hn
  let p₀ : CapacityParameter n := (rateVector k, (ET, FT, ST))
  have hparam : (ratesFromVector p₀.1).Positive ∧
      0 < p₀.2.1 ∧ 0 < p₀.2.2.1 ∧ 0 < p₀.2.2.2 := by
    simpa only [p₀, ratesFromVector_rateVector] using
      (show k.Positive ∧ 0 < ET ∧ 0 < FT ∧ 0 < ST from
        ⟨hk, hET, hFT, hST⟩)
  have heqstate (j : Fin (2*n-1)) :
      (unChart p₀.2.1 p₀.2.2.1 p₀.2.2.2
        (ofCoordinateSpace (u j))).Positive ∧
      capacityParameterField (p₀, u j) = 0 := by
    simpa only [p₀, ratesFromVector_rateVector, capacityParameterField]
      using ⟨(hstates j).2.1, (hstates j).2.2⟩
  have heven (j : Fin (2*n-1)) (hj : Even j.val) :
      IsLinearlyStable p₀.2.1 p₀.2.2.1 p₀.2.2.2
        (ratesFromVector p₀.1) (u j) := by
    obtain ⟨t, ht⟩ := hj
    let i : Fin n := ⟨t, by have := j.isLt; omega⟩
    obtain ⟨j', hj', hstable, _⟩ := hsinks i
    have hjeq : j' = j := Fin.ext (by dsimp [i] at hj'; omega)
    simpa only [p₀, ratesFromVector_rateVector, hjeq] using hstable
  have hodd (j : Fin (2*n-1)) (hj : Odd j.val) :
      IsOneUnstableSaddle p₀.2.1 p₀.2.2.1 p₀.2.2.2
        (ratesFromVector p₀.1) (u j) := by
    simpa only [p₀, ratesFromVector_rateVector] using hsaddles j hj
  obtain ⟨s, hsopen, hp₀, hpersist⟩ :=
    capacity_open_full_hyperbolic_family_of_base
      n hn p₀ u hparam hinj heqstate heven hodd
  refine ⟨s, hsopen,
    ⟨p₀, hp₀, by simpa only [p₀, ratesFromVector_rateVector] using hkrational,
      hETrational, hFTrational, hSTrational,
      u, hinj, ?_, hodd⟩, ?_⟩
  · intro j
    obtain ⟨hrational, hpositive, heq⟩ := hstates j
    exact ⟨hrational, hpositive, by
      simpa only [p₀, ratesFromVector_rateVector, capacityParameterField]
        using heq⟩
  intro p hp
  obtain ⟨hparam', x, hinj', hstates'⟩ := hpersist p hp
  have hstates'' (j : Fin (2*n-1)) :
      (unChart p.2.1 p.2.2.1 p.2.2.2
        (ofCoordinateSpace (x j))).Positive ∧
      capacityParameterField (p, x j) = 0 ∧
      IsHyperbolicMatrix
        (restrictedJacobianMatrix p.2.1 p.2.2.1 p.2.2.2
          (ratesFromVector p.1) (x j)) ∧
      (Even j.val →
        IsLinearlyStable p.2.1 p.2.2.1 p.2.2.2
          (ratesFromVector p.1) (x j) ∧
        IsLocallyAsymptoticallyStableClass
          p.2.1 p.2.2.1 p.2.2.2
          (ratesFromVector p.1) (x j)) ∧
      (Odd j.val → IsOneUnstableSaddle
        p.2.1 p.2.2.1 p.2.2.2
        (ratesFromVector p.1) (x j)) := by
    obtain ⟨hpositive, heq, hhyper, hstable, hsaddle⟩ := hstates' j
    refine ⟨hpositive, heq, hhyper, ?_, hsaddle⟩
    intro hj
    have hlin := hstable hj
    have hx : x j ∈ classPolytopeStrict n p.2.1 p.2.2.1 p.2.2.2 := by
      have hp := positive_state_mem_classPolytopeStrict
        p.2.1 p.2.2.1 p.2.2.2
        (unChart p.2.1 p.2.2.1 p.2.2.2
          (ofCoordinateSpace (x j))) hpositive
        (unChart_inClass p.2.1 p.2.2.1 p.2.2.2 _)
      simpa only [chart_unChart, to_ofCoordinateSpace] using hp
    have heq' : restrictedFieldEuclid p.2.1 p.2.2.1 p.2.2.2
        (ratesFromVector p.1) (x j) = 0 := heq
    exact ⟨hlin,
      isLinearlyStable_locally_asymptotically_stable
        hn p.2.1 p.2.2.1 p.2.2.2
        hparam'.2.1 (ratesFromVector p.1) hparam'.1
        (x j) hx heq' hlin⟩
  refine ⟨hparam', x, hinj', hstates'', ?_⟩
  exact capacity_exact_count_of_full_positive_family n hn
    p hparam' x hinj' (fun j => ⟨(hstates' j).1, (hstates' j).2.1⟩)

theorem all_size_open_full_hyperbolic_family
    (n : ℕ) (hn : 2 ≤ n) : OpenFullHyperbolicFamily n :=
  all_positive_sizes_open_full_hyperbolic_family n (by omega)

end
end PhosphorylationStableCapacity
