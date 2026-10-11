module
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import proofs.PhosphorylationStableCapacity.Jacobian
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- A Hurwitz matrix has one strictly positive real spectral margin,
uniform over all roots of its characteristic polynomial. This is the
finite-spectrum input needed for a matrix-exponential decay theorem. -/
theorem isHurwitz_uniform_spectral_gap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : IsHurwitz A) :
    ∃ α : ℝ, 0 < α ∧
      ∀ z : ℂ,
        ((A.map (algebraMap ℝ ℂ)).charpoly).eval z = 0 →
          z.re ≤ -α := by
  classical
  let p : Polynomial ℂ := (A.map (algebraMap ℝ ℂ)).charpoly
  let S : Set ℂ := {z | p.eval z = 0}
  have hp : p ≠ 0 :=
    (A.map (algebraMap ℝ ℂ)).charpoly_monic.ne_zero
  have hfinite : S.Finite := by
    have heq : S = (p.roots.toFinset : Set ℂ) := by
      ext z
      simp [S, Polynomial.IsRoot, Polynomial.mem_roots hp]
    rw [heq]
    exact p.roots.toFinset.finite_toSet
  rcases S.eq_empty_or_nonempty with hempty | hnonempty
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz
    have hzS : z ∈ S := hz
    rw [hempty] at hzS
    exact hzS.elim
  · obtain ⟨z₀, hz₀, hmin⟩ :=
      Set.exists_min_image S (fun z : ℂ => -z.re) hfinite hnonempty
    have hpos : 0 < -z₀.re := by
      have h := hA z₀ hz₀
      linarith
    refine ⟨-z₀.re, hpos, ?_⟩
    intro z hz
    have hle := hmin z hz
    linarith

/-- The verified literal fixed-class Jacobian inherits a strict
uniform spectral margin at every linearly stable equilibrium. -/
theorem linearlyStableClass_spectral_gap {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n)
    (hu : IsLinearlyStable ET FT ST k u) :
    ∃ α : ℝ, 0 < α ∧
      ∀ z : ℂ,
        (((restrictedJacobianMatrix ET FT ST k u).map
          (algebraMap ℝ ℂ)).charpoly).eval z = 0 →
          z.re ≤ -α :=
  isHurwitz_uniform_spectral_gap
    (restrictedJacobianMatrix ET FT ST k u) hu

end
end PhosphorylationStableCapacity
