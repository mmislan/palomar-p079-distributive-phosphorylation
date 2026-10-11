module
public import proofs.PhosphorylationStableCapacity.SplitSlowComplexIsolation

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial Filter
open scoped Topology Matrix.Norms.L2Operator

private def MatrixCoeffContinuousAt {α : Type*} [TopologicalSpace α]
    (a : α) (P : α → ℝ[X]) : Prop :=
  ∀ k, ContinuousAt (fun b => (P b).coeff k) a

private theorem matrixCoeffContinuousAt_add {α : Type*} [TopologicalSpace α]
    {a : α} {P Q : α → ℝ[X]}
    (hP : MatrixCoeffContinuousAt a P) (hQ : MatrixCoeffContinuousAt a Q) :
    MatrixCoeffContinuousAt a (fun b => P b + Q b) := by
  intro k
  simp only [Polynomial.coeff_add]
  have hfun : (fun b => (P b).coeff k + (Q b).coeff k) =
      (fun b => (P b).coeff k) + (fun b => (Q b).coeff k) := by
    funext b
    simp
  rw [hfun]
  exact (hP k).add (hQ k)

private theorem matrixCoeffContinuousAt_mul {α : Type*} [TopologicalSpace α]
    {a : α} {P Q : α → ℝ[X]}
    (hP : MatrixCoeffContinuousAt a P) (hQ : MatrixCoeffContinuousAt a Q) :
    MatrixCoeffContinuousAt a (fun b => P b * Q b) := by
  intro k
  simp only [Polynomial.coeff_mul]
  apply tendsto_finsetSum (Finset.HasAntidiagonal.antidiagonal k)
  intro ij hij
  exact ((hP ij.1).mul (hQ ij.2)).tendsto

private theorem matrixCoeffContinuousAt_const {α : Type*} [TopologicalSpace α]
    (a : α) (P : ℝ[X]) : MatrixCoeffContinuousAt a (fun _ => P) := by
  intro k
  exact continuousAt_const

private theorem matrixCoeffContinuousAt_C {α : Type*} [TopologicalSpace α]
    {a : α} {g : α → ℝ} (hg : ContinuousAt g a) :
    MatrixCoeffContinuousAt a (fun b => Polynomial.C (g b)) := by
  intro k
  cases k with
  | zero => simpa using hg
  | succ k => simpa using (continuousAt_const : ContinuousAt (fun _ : α => (0 : ℝ)) a)

private theorem matrixCoeffContinuousAt_neg {α : Type*} [TopologicalSpace α]
    {a : α} {P : α → ℝ[X]} (hP : MatrixCoeffContinuousAt a P) :
    MatrixCoeffContinuousAt a (fun b => -(P b)) := by
  intro k
  simp only [Polynomial.coeff_neg]
  have hfun : (fun b => -(P b).coeff k) =
      -(fun b => (P b).coeff k) := by
    funext b
    simp
  rw [hfun]
  exact (hP k).neg

private theorem matrixCoeffContinuousAt_finset_prod {α ι : Type*}
    [TopologicalSpace α] {a : α} (s : Finset ι) (P : ι → α → ℝ[X])
    (hP : ∀ i ∈ s, MatrixCoeffContinuousAt a (P i)) :
    MatrixCoeffContinuousAt a (fun b => ∏ i ∈ s, P i b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.prod_empty] using
        (matrixCoeffContinuousAt_const a (1 : ℝ[X]))
  | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi] using
        matrixCoeffContinuousAt_mul (hP i (Finset.mem_insert_self ..))
          (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)))

/-- Characteristic-polynomial coefficients vary continuously with every
entry of a finite real matrix. -/
theorem continuousAt_matrix_charpoly_coeff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (k : ℕ) :
    ContinuousAt (fun B : Matrix ι ι ℝ => B.charpoly.coeff k) A := by
  let M : Matrix ι ι ℝ → Matrix ι ι ℝ[X] := fun B => B.charmatrix
  have hentry (i j : ι) : MatrixCoeffContinuousAt A (fun B => M B i j) := by
    have hval : ContinuousAt (fun B : Matrix ι ι ℝ => B i j) A :=
      (continuous_apply_apply i j).continuousAt
    by_cases hij : i = j
    · subst j
      simpa [M, Matrix.charmatrix_apply_eq, sub_eq_add_neg] using
        matrixCoeffContinuousAt_add
          (matrixCoeffContinuousAt_const A Polynomial.X)
          (matrixCoeffContinuousAt_neg (matrixCoeffContinuousAt_C hval))
    · simpa only [M, Matrix.charmatrix_apply_ne _ _ _ hij] using
        matrixCoeffContinuousAt_neg (matrixCoeffContinuousAt_C hval)
  change ContinuousAt (fun B => (M B).det.coeff k) A
  simp only [Matrix.det_apply, Polynomial.finsetSum_coeff]
  apply tendsto_finsetSum Finset.univ
  intro σ hσ
  have hprod : MatrixCoeffContinuousAt A (fun B =>
      ∏ i : ι, M B (σ i) i) :=
    matrixCoeffContinuousAt_finset_prod Finset.univ
      (fun i B => M B (σ i) i)
      (by intro i hi; exact hentry (σ i) i)
  have hsign : ContinuousAt (fun _ : Matrix ι ι ℝ => Equiv.Perm.sign σ) A :=
    continuousAt_const
  have hterm : ContinuousAt
      (fun B : Matrix ι ι ℝ =>
        Equiv.Perm.sign σ • (∏ i, M B (σ i) i).coeff k) A := by
    convert hsign.smul (hprod k) using 1
  simpa [Polynomial.coeff_smul] using hterm.tendsto

private def matrixDividedDifference {α : Type*} (P : α → ℂ[X]) (N : ℕ)
    (v : α × (ℂ × ℂ)) : ℂ :=
  ∑ n ∈ Finset.range N,
    (P v.1).coeff n *
      ∑ i ∈ Finset.range n, v.2.1^i * v.2.2^(n-1-i)

private theorem matrixDividedDifference_factor
    {α : Type*} (P : α → ℂ[X]) (N : ℕ)
    (hdegree : ∀ a, (P a).natDegree < N)
    (a : α) (z w : ℂ) :
    (P a).eval z - (P a).eval w =
      (z-w) * matrixDividedDifference P N (a, (z,w)) := by
  rw [Polynomial.eval_eq_sum_range' (hdegree a) z,
    Polynomial.eval_eq_sum_range' (hdegree a) w]
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  simp_rw [← (Commute.all z w).mul_geom_sum₂]
  simp only [matrixDividedDifference, Finset.mul_sum]
  congr 1
  ext n
  ring_nf

private theorem matrix_divided_power_sum_at_zero (n : ℕ) :
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

private theorem matrixDividedDifference_zero
    {α : Type*} (P : α → ℂ[X]) (N : ℕ) (a : α) (hN : 1 < N) :
    matrixDividedDifference P N (a, (0,0)) = (P a).coeff 1 := by
  simp only [matrixDividedDifference, matrix_divided_power_sum_at_zero,
    mul_ite, mul_one, mul_zero]
  simp [Finset.mem_range, hN]

private theorem matrixDividedDifference_continuousAt
    {α : Type*} [TopologicalSpace α] (P : α → ℂ[X]) (N : ℕ) (a : α)
    (hcoeff : ∀ n, ContinuousAt (fun b => (P b).coeff n) a) :
    ContinuousAt (matrixDividedDifference P N) (a, (0,0)) := by
  unfold matrixDividedDifference
  apply tendsto_finsetSum (Finset.range N)
  intro n hn
  have hc : ContinuousAt
      (fun v : α × (ℂ × ℂ) => (P v.1).coeff n) (a, (0,0)) :=
    ContinuousAt.comp (f := Prod.fst)
      (x := (a, ((0 : ℂ), (0 : ℂ))))
      (hcoeff n) continuousAt_fst
  have hsum : ContinuousAt
      (fun v : α × (ℂ × ℂ) =>
        ∑ i ∈ Finset.range n, v.2.1^i * v.2.2^(n-1-i))
      (a, (0,0)) := by
    apply tendsto_finsetSum (Finset.range n)
    intro i hi
    have hterm : ContinuousAt
        (fun v : α × (ℂ × ℂ) => v.2.1^i * v.2.2^(n-1-i))
        (a, (0,0)) := by
      fun_prop
    exact hterm.tendsto
  exact (hc.mul hsum).tendsto

/-- A simple root at zero remains the only complex root in a small common
disk for all sufficiently close parameters. -/
theorem complex_polynomial_family_unique_root_near_zero_at
    {α : Type*} [PseudoMetricSpace α] (P : α → ℂ[X]) (N : ℕ)
    (a : α) (hN : 1 < N)
    (hdegree : ∀ b, (P b).natDegree < N)
    (hcoeff : ∀ n, ContinuousAt (fun b => (P b).coeff n) a)
    (hsimple : (P a).coeff 1 ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ b : α in 𝓝 a,
        ∀ z w : ℂ, ‖z‖ < ρ → ‖w‖ < ρ →
          (P b).IsRoot z → (P b).IsRoot w → z = w := by
  have hD0 : matrixDividedDifference P N (a, (0,0)) ≠ 0 := by
    rw [matrixDividedDifference_zero P N a hN]
    exact hsimple
  have hlocal : ∀ᶠ v : α × (ℂ × ℂ) in 𝓝 (a, (0,0)),
      matrixDividedDifference P N v ≠ 0 :=
    (matrixDividedDifference_continuousAt P N a hcoeff).eventually_ne hD0
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [Metric.ball_mem_nhds a hρ] with b hb z w hz hw hrootz hrootw
  have hmem : (b, (z,w)) ∈ Metric.ball (a, (0,0)) ρ := by
    simpa [Metric.mem_ball, Prod.dist_eq, dist_eq_norm, max_lt_iff] using
      (And.intro hb (And.intro hz hw))
  have hDne := hball hmem
  have hfactor := matrixDividedDifference_factor P N hdegree b z w
  rw [hrootz, hrootw] at hfactor
  have hprod : (z-w) * matrixDividedDifference P N (b, (z,w)) = 0 := by
    simpa using hfactor.symm
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hDne)

private theorem polynomial_family_root_between_eventually_at
    {α : Type*} [TopologicalSpace α]
    (P : α → ℝ[X]) (a : α) (l r : ℝ) (hlr : l ≤ r)
    (hl : ContinuousAt (fun b => (P b).eval l) a)
    (hr : ContinuousAt (fun b => (P b).eval r) a)
    (hneg : (P a).eval l < 0) (hpos : 0 < (P a).eval r) :
    ∀ᶠ b : α in 𝓝 a, ∃ x ∈ Set.Icc l r, (P b).IsRoot x := by
  have hneg' : ∀ᶠ b : α in 𝓝 a, (P b).eval l < 0 :=
    hl.eventually (eventually_lt_nhds hneg)
  have hpos' : ∀ᶠ b : α in 𝓝 a, 0 < (P b).eval r :=
    hr.eventually (eventually_gt_nhds hpos)
  filter_upwards [hneg', hpos'] with b hbl hbr
  have hzero : (0 : ℝ) ∈ Set.Icc ((P b).eval l) ((P b).eval r) :=
    ⟨le_of_lt hbl, le_of_lt hbr⟩
  obtain ⟨x, hx, hroot⟩ := (Set.mem_image _ _ _).mp
    (intermediate_value_Icc hlr (P b).continuous.continuousOn hzero)
  exact ⟨x, hx, hroot⟩

/-- A simple real root at zero persists for every sufficiently small
perturbation in any topological parameter space. -/
theorem polynomial_simple_zero_real_root_eventually_at
    {α : Type*} [TopologicalSpace α]
    (P : α → ℝ[X]) (a : α)
    (hzero : (P a).coeff 0 = 0)
    (hsimple : (P a).coeff 1 ≠ 0)
    (hcont : ∀ x : ℝ, ContinuousAt (fun b => (P b).eval x) a)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ b : α in 𝓝 a,
      ∃ x : ℝ, |x| < η ∧ (P b).IsRoot x := by
  obtain ⟨t, ht, htη, hprod⟩ :=
    polynomial_simple_zero_opposite_near (P a) hzero hsimple η hη
  have hbounds : -t ≤ t := by linarith
  have hroot : ∀ᶠ b : α in 𝓝 a,
      ∃ x ∈ Set.Icc (-t) t, (P b).IsRoot x := by
    rcases mul_neg_iff.mp hprod with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · have hneg : (-(P a)).eval (-t) < 0 := by
        simpa only [Polynomial.eval_neg] using (neg_lt_zero.mpr hl)
      have hpos : 0 < (-(P a)).eval t := by
        simpa only [Polynomial.eval_neg] using (neg_pos.mpr hr)
      have hnegative := polynomial_family_root_between_eventually_at
        (fun b => -(P b)) a (-t) t hbounds
        (by
          convert (hcont (-t)).neg using 1
          ext b
          simp [Polynomial.eval_neg])
        (by
          convert (hcont t).neg using 1
          ext b
          simp [Polynomial.eval_neg])
        hneg hpos
      filter_upwards [hnegative] with b hb
      obtain ⟨x, hx, hroot⟩ := hb
      exact ⟨x, hx, by simpa [Polynomial.IsRoot] using hroot⟩
    · exact polynomial_family_root_between_eventually_at
        P a (-t) t hbounds (hcont (-t)) (hcont t) hl hr
  filter_upwards [hroot] with b hb
  obtain ⟨x, hx, hroot⟩ := hb
  exact ⟨x, abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩, hroot⟩

theorem continuousAt_matrix_charpoly_eval
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : ℝ) :
    ContinuousAt (fun B : Matrix ι ι ℝ => B.charpoly.eval x) A := by
  simp_rw [Matrix.eval_charpoly]
  fun_prop

private theorem complex_polynomial_derivative_joint_continuousAt_at
    {α : Type*} [TopologicalSpace α]
    (P : α → ℂ[X]) (N : ℕ) (a : α)
    (hdegree : ∀ b, (P b).natDegree < N)
    (hcoeff : ∀ n, ContinuousAt (fun b => (P b).coeff n) a) :
    ContinuousAt
      (fun v : α × ℂ => (P v.1).derivative.eval v.2) (a, 0) := by
  have heval (b : α) (z : ℂ) :
      (P b).derivative.eval z =
        ∑ n ∈ Finset.range N,
          ((P b).coeff (n+1) * (n+1 : ℂ)) * z^n := by
    have hd : (P b).derivative.natDegree < N := by
      have := Polynomial.natDegree_derivative_le (P b)
      have := hdegree b
      omega
    rw [Polynomial.eval_eq_sum_range' hd]
    simp only [Polynomial.coeff_derivative]
  simp_rw [heval]
  apply tendsto_finsetSum (Finset.range N)
  intro n hn
  have hc : ContinuousAt
      (fun v : α × ℂ => (P v.1).coeff (n+1)) (a, 0) :=
    ContinuousAt.comp (f := Prod.fst) (x := (a, (0 : ℂ)))
      (hcoeff (n+1)) continuousAt_fst
  exact ((hc.mul continuousAt_const).mul (continuousAt_snd.pow n)).tendsto

theorem complex_polynomial_derivative_near_nonzero_at
    {α : Type*} [PseudoMetricSpace α]
    (P : α → ℂ[X]) (N : ℕ) (a : α)
    (hdegree : ∀ b, (P b).natDegree < N)
    (hcoeff : ∀ n, ContinuousAt (fun b => (P b).coeff n) a)
    (hsimple : (P a).coeff 1 ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ b : α in 𝓝 a,
        ∀ z : ℂ, ‖z‖ < ρ → (P b).derivative.eval z ≠ 0 := by
  have hderiv0 : (P a).derivative.eval 0 ≠ 0 := by
    simpa [← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_derivative] using hsimple
  have hlocal : ∀ᶠ v : α × ℂ in 𝓝 (a, 0),
      (P v.1).derivative.eval v.2 ≠ 0 :=
    (complex_polynomial_derivative_joint_continuousAt_at
      P N a hdegree hcoeff).eventually_ne hderiv0
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [Metric.ball_mem_nhds a hρ] with b hb z hz
  have hmem : (b, z) ∈ Metric.ball (a, 0) ρ := by
    simpa [Metric.mem_ball, Prod.dist_eq, dist_eq_norm, max_lt_iff] using
      (And.intro hb hz)
  exact hball hmem

private theorem matrix_charpoly_derivative_complex_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : ℝ) :
    ((A.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) =
      Complex.ofReal (A.charpoly.derivative.eval x) := by
  rw [Matrix.charpoly_map, Polynomial.derivative_map]
  simpa only [← Complex.coe_algebraMap] using
    (Polynomial.eval_map_apply (f := algebraMap ℝ ℂ)
      (p := A.charpoly.derivative) x)

private theorem matrix_charpoly_shift_derivative_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : ℝ) :
    ((A - Matrix.scalar ι x).charpoly).derivative.eval 0 =
      A.charpoly.derivative.eval x := by
  rw [Matrix.charpoly_sub_scalar, Polynomial.derivative_comp]
  simp

private theorem matrix_charpoly_shift_root_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x y : ℝ) :
    ((A - Matrix.scalar ι x).charpoly).IsRoot y ↔
      A.charpoly.IsRoot (y+x) := by
  rw [Matrix.charpoly_sub_scalar]
  simp [Polynomial.IsRoot, Polynomial.eval_comp]

private theorem matrix_charpoly_shift_complex_root_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : ℝ) (z : ℂ) :
    (((A - Matrix.scalar ι x).map (algebraMap ℝ ℂ)).charpoly).IsRoot z ↔
      ((A.map (algebraMap ℝ ℂ)).charpoly).IsRoot (z+(x:ℂ)) := by
  have hmap : (A - Matrix.scalar ι x).map (algebraMap ℝ ℂ) =
      A.map (algebraMap ℝ ℂ) - Matrix.scalar ι (x : ℂ) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.sub_apply, Matrix.scalar_apply, hij]
  rw [hmap, Matrix.charpoly_sub_scalar]
  simp [Polynomial.IsRoot, Polynomial.eval_comp]

private theorem matrix_charpoly_shift_complex_derivative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : ℝ) (z : ℂ) :
    ((((A - Matrix.scalar ι x).map (algebraMap ℝ ℂ)).charpoly).derivative).eval z =
      (((A.map (algebraMap ℝ ℂ)).charpoly).derivative).eval (z+(x:ℂ)) := by
  have hmap : (A - Matrix.scalar ι x).map (algebraMap ℝ ℂ) =
      A.map (algebraMap ℝ ℂ) - Matrix.scalar ι (x : ℂ) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.sub_apply, Matrix.scalar_apply, hij]
  rw [hmap, Matrix.charpoly_sub_scalar, Polynomial.derivative_comp]
  simp

/-- A simple positive real eigenvalue with every other eigenvalue in the
strict left half-plane persists under perturbation of a finite real matrix. -/
theorem isOpen_isOneUnstableSaddle_matrix
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    IsOpen {A : Matrix ι ι ℝ |
      ∃ x : ℝ, 0 < x ∧ A.charpoly.IsRoot x ∧
        ((A.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
        ∀ z : ℂ, z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) →
          z.re < 0 ∨ z = (x : ℂ)} := by
  classical
  apply isOpen_iff_mem_nhds.mpr
  intro A hA
  obtain ⟨x, hx, hroot, hsimple, hrest⟩ := hA
  let S : Matrix ι ι ℝ → Matrix ι ι ℝ :=
    fun B => B - Matrix.scalar ι x
  let P : Matrix ι ι ℝ → ℝ[X] := fun B => (S B).charpoly
  let Q : Matrix ι ι ℝ → ℂ[X] :=
    fun B => ((S B).map (algebraMap ℝ ℂ)).charpoly
  have hS : Continuous S := by
    unfold S
    fun_prop
  have hzero : (P A).coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact (matrix_charpoly_shift_root_iff A x 0).2 (by simpa using hroot)
  have hsimpleR : (P A).coeff 1 ≠ 0 := by
    have hD : A.charpoly.derivative.eval x ≠ 0 := by
      intro h
      apply hsimple
      rw [matrix_charpoly_derivative_complex_eq, h]
      simp
    intro h
    apply hD
    have hDshift := matrix_charpoly_shift_derivative_zero A x
    have hDzero : (P A).derivative.eval 0 = 0 := by
      simpa [P, ← Polynomial.coeff_zero_eq_eval_zero,
        Polynomial.coeff_derivative] using h
    simpa [P, S] using hDshift.symm.trans hDzero
  have hcoeffR (k : ℕ) :
      ContinuousAt (fun B => (P B).coeff k) A := by
    exact (continuousAt_matrix_charpoly_coeff (S A) k).comp hS.continuousAt
  have hcoeffC (k : ℕ) :
      ContinuousAt (fun B => (Q B).coeff k) A := by
    have hc : ContinuousAt
        (fun B => ((P B).coeff k : ℂ)) A :=
      Complex.continuous_ofReal.continuousAt.comp (hcoeffR k)
    simpa only [Q, P, Matrix.charpoly_map, Polynomial.coeff_map,
      ← Complex.coe_algebraMap] using hc
  have hsimpleC : (Q A).coeff 1 ≠ 0 := by
    simpa only [Q, P, Matrix.charpoly_map, Polynomial.coeff_map,
      ← Complex.coe_algebraMap] using
      (Complex.ofReal_ne_zero.mpr hsimpleR)
  let N := Fintype.card ι + 1
  have hN : 1 < N := by
    dsimp [N]
    have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ‹Nonempty ι›
    omega
  have hdegree (B : Matrix ι ι ℝ) : (Q B).natDegree < N := by
    simp [Q, N]
  obtain ⟨ρu, hρu, huniq⟩ :=
    complex_polynomial_family_unique_root_near_zero_at
      Q N A hN hdegree hcoeffC hsimpleC
  obtain ⟨ρd, hρd, hderiv⟩ :=
    complex_polynomial_derivative_near_nonzero_at
      Q N A hdegree hcoeffC hsimpleC
  let r := min ρu ρd
  have hr : 0 < r := lt_min hρu hρd
  let η := min (x / 2) r
  have hη : 0 < η := lt_min (by positivity) hr
  have hcont (y : ℝ) :
      ContinuousAt (fun B => (P B).eval y) A := by
    exact (continuousAt_matrix_charpoly_eval (S A) y).comp hS.continuousAt
  have hrootnear :=
    polynomial_simple_zero_real_root_eventually_at
      P A hzero hsimpleR hcont η hη
  let U : Set ℂ := {z | z.re < 0} ∪ Metric.ball (x : ℂ) r
  have hU : IsOpen U :=
    (isOpen_Iio.preimage Complex.continuous_re).union Metric.isOpen_ball
  have hspec : spectrum ℂ (A.map (algebraMap ℝ ℂ)) ⊆ U := by
    intro z hz
    rcases hrest z hz with hleft | heq
    · exact Or.inl hleft
    · right
      subst z
      exact Metric.mem_ball_self hr
  have hnear :=
    (upperHemicontinuous_spectrum ℂ (Matrix ι ι ℂ)).forall_isOpen
      (A.map (algebraMap ℝ ℂ)) U hU hspec
  have hmap : Continuous (fun B : Matrix ι ι ℝ =>
      B.map (algebraMap ℝ ℂ)) := by
    apply continuous_matrix
    intro i j
    exact Complex.continuous_ofReal.comp
      (continuous_apply j |>.comp (continuous_apply i))
  have hspecnear : ∀ᶠ B : Matrix ι ι ℝ in 𝓝 A,
      spectrum ℂ (B.map (algebraMap ℝ ℂ)) ⊆ U :=
    hmap.continuousAt.tendsto.eventually hnear
  apply Filter.mem_of_superset
    (Filter.Eventually.and huniq
      (Filter.Eventually.and hderiv
        (Filter.Eventually.and hrootnear hspecnear)))
  intro B hB
  obtain ⟨hu, hd, hex, hs⟩ := hB
  obtain ⟨y, hy, hyroot⟩ := hex
  have hyu : ‖(y : ℂ)‖ < ρu := by
    have hy' : |y| < ρu :=
      lt_of_lt_of_le hy (le_trans (min_le_right ..) (min_le_left ..))
    simpa using hy'
  have hyd : ‖(y : ℂ)‖ < ρd := by
    have hy' : |y| < ρd :=
      lt_of_lt_of_le hy (le_trans (min_le_right ..) (min_le_right ..))
    simpa using hy'
  have hxypos : 0 < y + x := by
    have := (abs_lt.mp hy).1
    have := min_le_left (x / 2) r
    dsimp [η] at hy
    linarith
  have hyrootB : B.charpoly.IsRoot (y+x) :=
    (matrix_charpoly_shift_root_iff B x y).1 hyroot
  have hyrootC : (Q B).IsRoot (y : ℂ) := by
    have hc := Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) hyroot
    simpa only [Q, P, Matrix.charpoly_map,
      ← Complex.coe_algebraMap] using hc
  have hyderiv :
      ((B.map (algebraMap ℝ ℂ)).charpoly).derivative.eval ((y+x : ℝ) : ℂ) ≠ 0 := by
    have hD := hd (y : ℂ) hyd
    have hD' :
        ((B.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
          ((y : ℂ) + (x : ℂ)) ≠ 0 := by
      rw [← matrix_charpoly_shift_complex_derivative B x (y : ℂ)]
      exact hD
    simpa only [Complex.ofReal_add] using hD'
  refine ⟨y+x, hxypos, hyrootB, hyderiv, ?_⟩
  intro z hz
  rcases hs hz with hleft | hball
  · exact Or.inl hleft
  · right
    have hball' : ‖z - (x : ℂ)‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hball
    have hzabs : ‖z - (x : ℂ)‖ < ρu :=
      lt_of_lt_of_le hball' (min_le_left ..)
    have hzroot : ((B.map (algebraMap ℝ ℂ)).charpoly).IsRoot z :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
    have hzQ : (Q B).IsRoot (z - (x : ℂ)) := by
      apply (matrix_charpoly_shift_complex_root_iff B x (z - (x : ℂ))).2
      simpa only [sub_add_cancel] using hzroot
    have heq := hu (z - (x : ℂ)) (y : ℂ) hzabs hyu hzQ hyrootC
    have heq' : z = (y : ℂ) + (x : ℂ) := (sub_eq_iff_eq_add).mp heq
    simpa only [Complex.ofReal_add] using heq'

end

end PhosphorylationStableCapacity
