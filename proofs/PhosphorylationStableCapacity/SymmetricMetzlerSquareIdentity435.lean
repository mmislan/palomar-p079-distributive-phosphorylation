module
public import proofs.PhosphorylationStableCapacity.DiagonalAlgebra
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open scoped BigOperators

/-- The exact weighted-square identity underlying the paper's diagonal
Lyapunov proof, with each unordered pair represented twice. Symmetry and
nonzero weights suffice for the identity; positivity is used separately
to deduce strict negative definiteness. -/
theorem symmetric_energy_square_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : ∀ i j, Q i j = Q j i)
    (z a : ι → ℝ) (hz : ∀ i, z i ≠ 0) :
    (∑ i, a i * ∑ j, Q i j * a j) =
      (∑ i, ((∑ j, Q i j*z j)/z i)*a i^2) -
        (1/2 : ℝ)*(∑ i, ∑ j,
          Q i j*z i*z j*(a i/z i-a j/z j)^2) := by
  have hpair (i j : ι) := energy_pair (Q i j) (z i) (z j)
    (a i) (a j) (hz i) (hz j)
  have hleft : (∑ i, ∑ j, 2*Q i j*a i*a j) =
      2*(∑ i, a i*∑ j, Q i j*a j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hfirst : (∑ i, ∑ j, Q i j*z j/z i*a i^2) =
      ∑ i, ((∑ j, Q i j*z j)/z i)*a i^2 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Finset.sum_div, Finset.sum_mul]
  have hsecond : (∑ i, ∑ j, Q i j*z i/z j*a j^2) =
      ∑ i, ((∑ j, Q i j*z j)/z i)*a i^2 := by
    rw [Finset.sum_comm]
    calc
      (∑ i, ∑ j, Q j i*z j/z i*a i^2) =
          ∑ i, ∑ j, Q i j*z j/z i*a i^2 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hQ j i]
      _ = _ := hfirst
  have hsum : (∑ i, ∑ j, 2*Q i j*a i*a j) =
      (∑ i, ∑ j, Q i j*z j/z i*a i^2) +
        (∑ i, ∑ j, Q i j*z i/z j*a j^2) -
        (∑ i, ∑ j, Q i j*z i*z j*(a i/z i-a j/z j)^2) := by
    calc
      (∑ i, ∑ j, 2*Q i j*a i*a j) =
          ∑ i, ∑ j, (Q i j*z j/z i*a i^2 +
            Q i j*z i/z j*a j^2 -
            Q i j*z i*z j*(a i/z i-a j/z j)^2) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact hpair i j
      _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hleft, hfirst, hsecond] at hsum
  linarith

/-- The manuscript's printed form: the second sum has exactly one term
for each pair i < j. The diagonal square vanishes and symmetric terms
coincide, so this is the same identity without a factor one half. -/
theorem symmetric_energy_square_identity_ordered
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (Q : Matrix ι ι ℝ) (hQ : ∀ i j, Q i j = Q j i)
    (z a : ι → ℝ) (hz : ∀ i, z i ≠ 0) :
    (∑ i, a i * ∑ j, Q i j * a j) =
      (∑ i, ((∑ j, Q i j*z j)/z i)*a i^2) -
        ∑ i, ∑ j, if i < j then Q i j*z i*z j*(a i/z i-a j/z j)^2 else 0 := by
  let e : ι → ι → ℝ := fun i j =>
    Q i j*z i*z j*(a i/z i-a j/z j)^2
  have esymm (i j : ι) : e i j = e j i := by
    dsimp [e]
    rw [hQ i j]
    ring
  have esplit (i j : ι) : e i j =
      (if i < j then e i j else 0)+(if j < i then e i j else 0) := by
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, not_lt_of_ge hij.le]
    · subst j
      simp [e]
    · simp [hij, not_lt_of_ge hij.le]
  have lower : (∑ i, ∑ j, if j < i then e i j else 0) =
      ∑ i, ∑ j, if i < j then e i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [esymm j i]
  have hsum : (∑ i, ∑ j, e i j) =
      2*(∑ i, ∑ j, if i < j then e i j else 0) := by
    calc
      (∑ i, ∑ j, e i j) = ∑ i, ∑ j,
          ((if i < j then e i j else 0)+(if j < i then e i j else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact esplit i j
      _ = (∑ i, ∑ j, if i < j then e i j else 0) +
          (∑ i, ∑ j, if j < i then e i j else 0) := by
        simp only [Finset.sum_add_distrib]
      _ = _ := by rw [lower]; ring
  have h := symmetric_energy_square_identity Q hQ z a hz
  change (∑ i, a i*∑ j, Q i j*a j) =
    (∑ i, ((∑ j, Q i j*z j)/z i)*a i^2) -
      (1/2 : ℝ)*(∑ i, ∑ j, e i j) at h
  rw [hsum] at h
  have hcancel : (1/2 : ℝ)*(2*(∑ i, ∑ j, if i < j then e i j else 0)) =
      (∑ i, ∑ j, if i < j then e i j else 0) := by ring
  rw [hcancel] at h
  exact h

end
end PhosphorylationStableCapacity
