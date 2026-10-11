module
public import proofs.PhosphorylationStableCapacity.FastSlowPencilPolynomial

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix Polynomial

/-- Coefficientwise continuity of a polynomial family over an arbitrary
topological parameter type. -/
def ParamCoeffContinuous {β : Type*} [TopologicalSpace β]
    (p : β → ℂ[X]) : Prop :=
  ∀ n : ℕ, Continuous fun t => (p t).coeff n

private theorem paramCoeffContinuous_add
    {β : Type*} [TopologicalSpace β] {p q : β → ℂ[X]}
    (hp : ParamCoeffContinuous p) (hq : ParamCoeffContinuous q) :
    ParamCoeffContinuous (fun t => p t + q t) := by
  intro n
  have heq : (fun t => (p t + q t).coeff n) =
      (fun t => (p t).coeff n) + (fun t => (q t).coeff n) := by
    funext t
    simp [Pi.add_apply]
  rw [heq]
  exact (hp n).add (hq n)

private theorem paramCoeffContinuous_mul
    {β : Type*} [TopologicalSpace β] {p q : β → ℂ[X]}
    (hp : ParamCoeffContinuous p) (hq : ParamCoeffContinuous q) :
    ParamCoeffContinuous (fun t => p t * q t) := by
  intro n
  have h : Continuous (fun t : β =>
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        (p t).coeff ij.1 * (q t).coeff ij.2) := by
    apply continuous_finsetSum
    intro ij hij
    exact (hp ij.1).mul (hq ij.2)
  simpa only [Polynomial.coeff_mul] using h

private theorem paramCoeffContinuous_const
    {β : Type*} [TopologicalSpace β] (p : ℂ[X]) :
    ParamCoeffContinuous (fun _ : β => p) := by
  intro n
  exact continuous_const

private theorem paramCoeffContinuous_C
    {β : Type*} [TopologicalSpace β] {g : β → ℂ}
    (hg : Continuous g) :
    ParamCoeffContinuous (fun t => Polynomial.C (g t)) := by
  intro n
  cases n with
  | zero => simpa using hg
  | succ n => simpa using (continuous_const : Continuous fun _ : β => (0 : ℂ))

private theorem paramCoeffContinuous_finset_prod
    {β ι : Type*} [TopologicalSpace β]
    (u : Finset ι) (p : ι → β → ℂ[X])
    (hp : ∀ i ∈ u, ParamCoeffContinuous (p i)) :
    ParamCoeffContinuous (fun t => ∏ i ∈ u, p i t) := by
  classical
  induction u using Finset.induction_on with
  | empty =>
      intro n
      simpa only [Finset.prod_empty] using
        (continuous_const : Continuous fun _ : β => (1 : ℂ[X]).coeff n)
  | @insert a u ha ih =>
      simpa only [Finset.prod_insert ha] using
        paramCoeffContinuous_mul (hp a (Finset.mem_insert_self ..))
          (ih (fun i hi => hp i (Finset.mem_insert_of_mem hi)))

/-- The determinant of a finite matrix polynomial has continuous
coefficients whenever every entry does. -/
theorem continuous_coeff_matrix_det_param
    {β ι : Type*} [TopologicalSpace β]
    [Fintype ι] [DecidableEq ι]
    (M : β → Matrix ι ι ℂ[X])
    (hM : ∀ i j, ParamCoeffContinuous (fun t => M t i j))
    (n : ℕ) :
    Continuous fun t => (M t).det.coeff n := by
  classical
  simp only [Matrix.det_apply, Polynomial.finsetSum_coeff]
  apply continuous_finsetSum
  intro σ hσ
  have hprod : ParamCoeffContinuous (fun t =>
      ∏ i : ι, M t (σ i) i) :=
    paramCoeffContinuous_finset_prod Finset.univ
      (fun i t => M t (σ i) i)
      (by intro i hi; exact hM (σ i) i)
  have heq :
      (fun t : β => ((Equiv.Perm.sign σ) •
        (∏ i : ι, M t (σ i) i)).coeff n) =
      (fun _ : β => (Equiv.Perm.sign σ : ℂ)) •
        (fun t : β => (∏ i : ι, M t (σ i) i).coeff n) := by
    funext t
    simp only [Polynomial.coeff_smul, Units.smul_def,
      ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul, Pi.mul_apply]
  rw [heq]
  have hsign : Continuous (fun _ : β => (Equiv.Perm.sign σ : ℂ)) :=
    continuous_const
  exact hsign.smul (hprod n)

/-- The physical fast/slow pencil's spectral-parameter coefficient is
jointly continuous in all four matrix blocks and the binding scale. -/
theorem continuous_fastSlowPencilPolynomial_coeff_parameter_family
    {α s f : Type*} [TopologicalSpace α]
    [Fintype s] [Fintype f] [DecidableEq s] [DecidableEq f]
    (A : α → Matrix s s ℂ) (B : α → Matrix s f ℂ)
    (C : α → Matrix f s ℂ) (D : α → Matrix f f ℂ)
    (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hD : Continuous D)
    (n : ℕ) :
    Continuous (fun p : α × ℂ =>
      (fastSlowPencilPolynomial
        (A p.1) (B p.1) (C p.1) (D p.1) p.2).coeff n) := by
  let M₀ : α × ℂ → Matrix (s ⊕ f) (s ⊕ f) ℂ := fun p =>
    Matrix.fromBlocks (-A p.1) (-B p.1) (-C p.1) (-D p.1)
  let M₁ : α × ℂ → Matrix (s ⊕ f) (s ⊕ f) ℂ := fun p =>
    Matrix.fromBlocks (1 : Matrix s s ℂ) 0 0
      (p.2 • (1 : Matrix f f ℂ))
  let M : α × ℂ → Matrix (s ⊕ f) (s ⊕ f) ℂ[X] := fun p =>
    (M₀ p).map Polynomial.C + (Polynomial.X : ℂ[X]) •
      (M₁ p).map Polynomial.C
  have hM₀ (i j : s ⊕ f) : Continuous fun p => M₀ p i j := by
    cases i <;> cases j <;>
      simp only [M₀, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.neg_apply] <;>
      fun_prop
  have hM₁ (i j : s ⊕ f) : Continuous fun p => M₁ p i j := by
    cases i <;> cases j <;>
      simp only [M₁, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.smul_apply] <;>
      fun_prop
  have hM (i j : s ⊕ f) :
      ParamCoeffContinuous (fun p => M p i j) := by
    have hentry (p : α × ℂ) : M p i j =
        Polynomial.C (M₀ p i j) +
          Polynomial.X * Polynomial.C (M₁ p i j) := by
      simp [M, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
        smul_eq_mul]
    have h := paramCoeffContinuous_add
      (paramCoeffContinuous_C (hM₀ i j))
      (paramCoeffContinuous_mul
        (paramCoeffContinuous_const Polynomial.X)
        (paramCoeffContinuous_C (hM₁ i j)))
    simpa only [hentry] using h
  exact continuous_coeff_matrix_det_param M hM n

/-- Joint continuity of the deflated characteristic-pencil evaluation in
the physical parameter, binding scale, and spectral parameter. -/
theorem continuous_fastSlowPencilPolynomial_divX_eval_parameter_family
    {α s f : Type*} [TopologicalSpace α]
    [Fintype s] [Fintype f] [DecidableEq s] [DecidableEq f]
    (A : α → Matrix s s ℂ) (B : α → Matrix s f ℂ)
    (C : α → Matrix f s ℂ) (D : α → Matrix f f ℂ)
    (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hD : Continuous D) :
    Continuous (fun p : (α × ℂ) × ℂ =>
      (fastSlowPencilPolynomial
        (A p.1.1) (B p.1.1) (C p.1.1) (D p.1.1) p.1.2).divX.eval p.2) := by
  let N := Fintype.card (s ⊕ f) + 1
  have hdegree (a : α) (ε : ℂ) :
      (fastSlowPencilPolynomial
        (A a) (B a) (C a) (D a) ε).divX.natDegree < N := by
    exact lt_of_le_of_lt
      ((fastSlowPencilPolynomial (A a) (B a) (C a) (D a) ε).natDegree_divX_le.trans
        (fastSlowPencilPolynomial_natDegree_le
          (A a) (B a) (C a) (D a) ε))
      (Nat.lt_succ_self _)
  have heq (a : α) (ε z : ℂ) :
      (fastSlowPencilPolynomial
        (A a) (B a) (C a) (D a) ε).divX.eval z =
        ∑ i ∈ Finset.range N,
          (fastSlowPencilPolynomial
            (A a) (B a) (C a) (D a) ε).coeff (i + 1) * z ^ i := by
    simpa only [Polynomial.coeff_divX] using
      (Polynomial.eval_eq_sum_range' (hdegree a ε) z)
  have hsum : Continuous fun p : (α × ℂ) × ℂ =>
      ∑ i ∈ Finset.range N,
        (fastSlowPencilPolynomial
          (A p.1.1) (B p.1.1) (C p.1.1) (D p.1.1) p.1.2).coeff (i + 1) *
          p.2 ^ i := by
    apply continuous_finsetSum
    intro i hi
    exact ((continuous_fastSlowPencilPolynomial_coeff_parameter_family
      A B C D hA hB hC hD (i + 1)).comp continuous_fst).mul
        (continuous_snd.pow i)
  simpa only [heq] using hsum

end

end PhosphorylationStableCapacity
