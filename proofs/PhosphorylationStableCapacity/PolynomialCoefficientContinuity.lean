module
public import proofs.PhosphorylationStableCapacity.FastSlowPencilPolynomial

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix Polynomial
open Filter
open scoped Topology

/-- Continuity of every coefficient of a one-parameter polynomial family. -/
def CoeffContinuous (p : ℂ → ℂ[X]) : Prop :=
  ∀ n : ℕ, Continuous fun ε => (p ε).coeff n

private theorem coeffContinuous_add {p q : ℂ → ℂ[X]}
    (hp : CoeffContinuous p) (hq : CoeffContinuous q) :
    CoeffContinuous (fun ε => p ε + q ε) := by
  intro n
  have heq : (fun ε => (p ε + q ε).coeff n) =
      (fun ε => (p ε).coeff n) + (fun ε => (q ε).coeff n) := by
    funext ε
    simp [Pi.add_apply]
  rw [heq]
  exact (hp n).add (hq n)

private theorem coeffContinuous_mul {p q : ℂ → ℂ[X]}
    (hp : CoeffContinuous p) (hq : CoeffContinuous q) :
    CoeffContinuous (fun ε => p ε * q ε) := by
  intro n
  have h : Continuous (fun ε : ℂ =>
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        (p ε).coeff ij.1 * (q ε).coeff ij.2) := by
    apply continuous_finsetSum
    intro ij hij
    exact (hp ij.1).mul (hq ij.2)
  simpa only [Polynomial.coeff_mul] using h

private theorem coeffContinuous_const (p : ℂ[X]) :
    CoeffContinuous (fun _ => p) := by
  intro n
  exact continuous_const

private theorem coeffContinuous_C {g : ℂ → ℂ}
    (hg : Continuous g) :
    CoeffContinuous (fun ε => Polynomial.C (g ε)) := by
  intro n
  cases n with
  | zero => simpa using hg
  | succ n => simpa using (continuous_const : Continuous fun _ : ℂ => (0 : ℂ))

private theorem coeffContinuous_finset_prod {ι : Type*}
    (u : Finset ι) (p : ι → ℂ → ℂ[X])
    (hp : ∀ i ∈ u, CoeffContinuous (p i)) :
    CoeffContinuous (fun ε => ∏ i ∈ u, p i ε) := by
  classical
  induction u using Finset.induction_on with
  | empty =>
      intro n
      simpa using continuous_const
  | @insert a u ha ih =>
      simpa only [Finset.prod_insert ha] using
        coeffContinuous_mul (hp a (Finset.mem_insert_self ..))
          (ih (fun i hi => hp i (Finset.mem_insert_of_mem hi)))

/-- A matrix-polynomial family with continuous scalar coefficients has
a determinant family with continuous scalar coefficients. -/
theorem continuous_coeff_matrix_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℂ → Matrix ι ι ℂ[X])
    (hM : ∀ i j, CoeffContinuous (fun ε => M ε i j))
    (n : ℕ) :
    Continuous fun ε => (M ε).det.coeff n := by
  classical
  simp only [Matrix.det_apply, Polynomial.finsetSum_coeff]
  apply continuous_finsetSum
  intro σ hσ
  have hprod : CoeffContinuous (fun ε =>
      ∏ i : ι, M ε (σ i) i) :=
    coeffContinuous_finset_prod Finset.univ
      (fun i ε => M ε (σ i) i)
      (by intro i hi; exact hM (σ i) i)
  have heq :
      (fun ε : ℂ => ((Equiv.Perm.sign σ) •
        (∏ i : ι, M ε (σ i) i)).coeff n) =
      (fun _ : ℂ => (Equiv.Perm.sign σ : ℂ)) •
        (fun ε : ℂ => (∏ i : ι, M ε (σ i) i).coeff n) := by
    funext ε
    simp only [Polynomial.coeff_smul, Units.smul_def,
      ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul, Pi.mul_apply]
  rw [heq]
  have hsign : Continuous (fun _ : ℂ => (Equiv.Perm.sign σ : ℂ)) :=
    continuous_const
  exact hsign.smul (hprod n)

/-- Every spectral-parameter coefficient of the scaled fast/slow block
pencil varies continuously with the binding time scale. -/
theorem fastSlowPencilPolynomial_coeff_continuous
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (n : ℕ) :
    Continuous fun ε : ℂ =>
      (fastSlowPencilPolynomial A B C D ε).coeff n := by
  let M₀ : Matrix (s ⊕ f) (s ⊕ f) ℂ :=
    Matrix.fromBlocks (-A) (-B) (-C) (-D)
  let M₁ (ε : ℂ) : Matrix (s ⊕ f) (s ⊕ f) ℂ :=
    Matrix.fromBlocks (1 : Matrix s s ℂ) 0 0
      (ε • (1 : Matrix f f ℂ))
  let M (ε : ℂ) : Matrix (s ⊕ f) (s ⊕ f) ℂ[X] :=
    M₀.map Polynomial.C + (Polynomial.X : ℂ[X]) • (M₁ ε).map Polynomial.C
  have hM1 (i j : s ⊕ f) : Continuous fun ε => M₁ ε i j := by
    cases i <;> cases j <;>
      simp [M₁, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.smul_apply] <;>
      first | exact continuous_const | exact continuous_id.mul continuous_const
  have hM (i j : s ⊕ f) :
      CoeffContinuous (fun ε => M ε i j) := by
    have hentry (ε : ℂ) : M ε i j =
        Polynomial.C (M₀ i j) +
          Polynomial.X * Polynomial.C (M₁ ε i j) := by
      simp [M, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
        smul_eq_mul]
    have h := coeffContinuous_add
      (coeffContinuous_const (Polynomial.C (M₀ i j)))
      (coeffContinuous_mul (coeffContinuous_const Polynomial.X)
        (coeffContinuous_C (hM1 i j)))
    simpa only [hentry] using h
  exact continuous_coeff_matrix_det M hM n

/-- The exact zero factor stays algebraically simple for all sufficiently
small binding scales, provided the Schur zero is simple. -/
theorem fastSlowPencilPolynomial_coeff_one_eventually_ne_zero
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0)
    (q : ℂ[X])
    (hS : (A - B * D⁻¹ * C).charpoly = q * Polynomial.X)
    (hq : q.eval 0 ≠ 0) :
    ∀ᶠ ε : ℂ in 𝓝 0,
      (fastSlowPencilPolynomial A B C D ε).coeff 1 ≠ 0 := by
  have hzero := fastSlowPencilPolynomial_zero_coeff_one_ne_zero
    A B C D hD q hS hq
  exact (fastSlowPencilPolynomial_coeff_continuous A B C D 1).continuousAt.eventually_ne
    hzero

/-- The quotient by the exact spectral zero factor is jointly continuous
in binding scale and spectral parameter. -/
theorem fastSlowPencilPolynomial_divX_eval_continuous
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ) :
    Continuous fun p : ℂ × ℂ =>
      (fastSlowPencilPolynomial A B C D p.1).divX.eval p.2 := by
  let N := Fintype.card (s ⊕ f) + 1
  have hdegree (ε : ℂ) :
      (fastSlowPencilPolynomial A B C D ε).divX.natDegree < N := by
    exact lt_of_le_of_lt
      ((fastSlowPencilPolynomial A B C D ε).natDegree_divX_le.trans
        (fastSlowPencilPolynomial_natDegree_le A B C D ε))
      (Nat.lt_succ_self _)
  have heq (ε z : ℂ) :
      (fastSlowPencilPolynomial A B C D ε).divX.eval z =
        ∑ i ∈ Finset.range N,
          (fastSlowPencilPolynomial A B C D ε).coeff (i + 1) * z ^ i := by
    simpa only [Polynomial.coeff_divX] using
      (Polynomial.eval_eq_sum_range' (hdegree ε) z)
  have hsum : Continuous fun p : ℂ × ℂ =>
      ∑ i ∈ Finset.range N,
        (fastSlowPencilPolynomial A B C D p.1).coeff (i + 1) * p.2 ^ i := by
    apply continuous_finsetSum
    intro i hi
    exact ((fastSlowPencilPolynomial_coeff_continuous A B C D (i + 1)).comp
      continuous_fst).mul (continuous_snd.pow i)
  simpa only [heq] using hsum

/-- One common punctured spectral neighborhood contains no block-pencil
roots for all sufficiently small binding scales. -/
theorem fastSlowPencilPolynomial_uniform_zero_isolation
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0)
    (q : ℂ[X])
    (hS : (A - B * D⁻¹ * C).charpoly = q * Polynomial.X)
    (hq : q.eval 0 ≠ 0) :
    ∃ δ η : ℝ, 0 < δ ∧ 0 < η ∧
      ∀ ε z : ℂ, ε ∈ Metric.ball 0 δ → z ∈ Metric.ball 0 η →
        z ≠ 0 → (fastSlowPencilPolynomial A B C D ε).eval z ≠ 0 := by
  have hqzero :
      (fastSlowPencilPolynomial A B C D 0).divX.eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_divX]
    exact fastSlowPencilPolynomial_zero_coeff_one_ne_zero A B C D hD q hS hq
  have hnear :
      {p : ℂ × ℂ |
        (fastSlowPencilPolynomial A B C D p.1).divX.eval p.2 ≠ 0} ∈
        𝓝 ((0 : ℂ), (0 : ℂ)) :=
    (fastSlowPencilPolynomial_divX_eval_continuous A B C D).continuousAt.eventually_ne
      hqzero
  obtain ⟨u, hu, v, hv, hsub⟩ := mem_nhds_prod_iff.mp hnear
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hu
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp hv
  refine ⟨δ, η, hδ, hη, ?_⟩
  intro ε z hε hz hz0
  have hquot : (fastSlowPencilPolynomial A B C D ε).divX.eval z ≠ 0 :=
    hsub (show (ε, z) ∈ u ×ˢ v from ⟨hδsub hε, hηsub hz⟩)
  have hfactor := fastSlowPencilPolynomial_X_factor A B C D hD
    (by
      exact Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (by
        rw [hS]
        simp [Polynomial.IsRoot])) ε
  rw [hfactor, Polynomial.eval_mul, Polynomial.eval_X]
  exact mul_ne_zero hz0 hquot

end
end PhosphorylationStableCapacity
