module
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Tactic.FunProp
public import Mathlib.Order.Filter.Defs

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter Topology
open scoped Matrix.Norms.L2Operator

/-- The finite matrix obtained by multiplying the fast/slow Jacobian by
the binding time scale. At nonzero scale this is `ε • Jε`; its definition
extends continuously to zero. -/
def fastSlowScaledMatrix {s f : Type*} [Fintype s] [Fintype f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ) (ε : ℂ) :
    Matrix (s ⊕ f) (s ⊕ f) ℂ :=
  Matrix.fromBlocks (ε • A) (ε • B) C D

def fastSlowMatrix {s f : Type*} [Fintype s] [Fintype f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ) (ε : ℂ) :
    Matrix (s ⊕ f) (s ⊕ f) ℂ :=
  Matrix.fromBlocks A B (ε⁻¹ • C) (ε⁻¹ • D)

theorem fastSlowScaledMatrix_eq_smul_fastSlowMatrix
    {s f : Type*} [Fintype s] [Fintype f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    {ε : ℂ} (hε : ε ≠ 0) :
    fastSlowScaledMatrix A B C D ε =
      ε • fastSlowMatrix A B C D ε := by
  simp [fastSlowScaledMatrix, fastSlowMatrix, Matrix.fromBlocks_smul,
    smul_smul, hε]

theorem fastSlowScaledMatrix_continuous {s f : Type*}
    [Fintype s] [Fintype f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ) :
    Continuous (fastSlowScaledMatrix A B C D) := by
  apply continuous_matrix
  intro i j
  cases i <;> cases j <;>
    simp only [fastSlowScaledMatrix, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul] <;>
    fun_prop

theorem fastSlowScaledMatrix_tendsto_zero {s f : Type*}
    [Fintype s] [Fintype f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ) :
    Tendsto (fastSlowScaledMatrix A B C D) (nhds 0)
      (nhds (Matrix.fromBlocks 0 0 C D)) := by
  simpa [fastSlowScaledMatrix] using
    ((fastSlowScaledMatrix_continuous A B C D).continuousAt (x := 0)).tendsto

theorem fastSlowScaledMatrix_zero_charpoly {s f : Type*}
    [Fintype s] [Fintype f] [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ) :
    (fastSlowScaledMatrix A B C D 0).charpoly =
      (0 : Matrix s s ℂ).charpoly * D.charpoly := by
  simp [fastSlowScaledMatrix]

theorem fastSlowScaledMatrix_zero_spectrum_subset {s f : Type*}
    [Fintype s] [Fintype f] [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ) :
    spectrum ℂ (fastSlowScaledMatrix A B C D 0) ⊆
      ({0} ∪ spectrum ℂ D) := by
  intro z hz
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,
    fastSlowScaledMatrix_zero_charpoly A B C D,
    Polynomial.IsRoot, Polynomial.eval_mul,
    Matrix.charpoly_zero, Polynomial.eval_pow,
    Polynomial.eval_X] at hz
  rcases mul_eq_zero.mp hz with hzero | hfast
  · refine Or.inl (Set.mem_singleton_iff.mpr ?_)
    by_contra hne
    exact (pow_ne_zero _ hne) hzero
  · exact Or.inr (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hfast)

/-- A scaled fast/slow eigenvalue is eventually either close to the origin
or strictly in the stable half-plane. Further analysis of the eigenvalues
near the origin is needed to recover the unscaled slow spectrum. -/
theorem fastSlowScaledMatrix_eventually_spectrum_near_zero_or_left
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ z : ℂ, z ∈ spectrum ℂ D → z.re < 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε : ℂ in nhds 0, ∀ z : ℂ,
      z ∈ spectrum ℂ (fastSlowScaledMatrix A B C D ε) →
        z.re < 0 ∨ z ∈ Metric.ball 0 δ := by
  let U : Set ℂ := {z | z.re < 0} ∪ Metric.ball 0 δ
  have hUopen : IsOpen U :=
    (isOpen_Iio.preimage Complex.continuous_re).union Metric.isOpen_ball
  have hUlimit : U ∈ 𝓝ˢ (spectrum ℂ (fastSlowScaledMatrix A B C D 0)) := by
    apply hUopen.mem_nhdsSet.mpr
    intro z hz
    rcases fastSlowScaledMatrix_zero_spectrum_subset A B C D hz with hzero | hfast
    · subst z
      exact Or.inr (Metric.mem_ball_self hδ)
    · exact Or.inl (hD z hfast)
  have hnear : ∀ᶠ M : Matrix (s ⊕ f) (s ⊕ f) ℂ in
      nhds (fastSlowScaledMatrix A B C D 0),
      U ∈ 𝓝ˢ (spectrum ℂ M) :=
    (upperHemicontinuous_spectrum ℂ
      (Matrix (s ⊕ f) (s ⊕ f) ℂ)).upperHemicontinuousAt
        (fastSlowScaledMatrix A B C D 0) U hUlimit
  have hnear' : ∀ᶠ M : Matrix (s ⊕ f) (s ⊕ f) ℂ in
      nhds (Matrix.fromBlocks 0 0 C D), U ∈ 𝓝ˢ (spectrum ℂ M) := by
    simpa [fastSlowScaledMatrix] using hnear
  filter_upwards [(fastSlowScaledMatrix_tendsto_zero A B C D).eventually hnear']
    with ε hε z hz
  exact (subset_of_mem_nhdsSet hε) hz

end
end PhosphorylationStableCapacity
