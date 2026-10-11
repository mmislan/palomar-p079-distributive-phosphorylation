module
public import proofs.PhosphorylationStableCapacity.ScaledIntegerMatrixCertificates
public import proofs.PhosphorylationStableCapacity.SymmetricMatrixDiagonalDominance

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open Matrix
open scoped BigOperators

/-- An integer strict diagonal margin is a sound positive-definiteness
certificate for the decoded real rational matrix. -/
theorem ScaledIntegerMatrix.posDef_of_integer_row_margin
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ScaledIntegerMatrix ι ι) (hden : 0 < A.denominator)
    (hsym : A.entries.IsSymm)
    (hmargin : ∀ i,
      ∑ j, |(diagonal (fun a => A.entries a a) - A.entries) i j| ≤ A.entries i i - 1) :
    A.realMatrix.PosDef := by
  let R := A.entries.map (Int.castRingHom ℝ)
  have hR : R.IsSymm := by
    ext i j
    change (A.entries j i : ℝ) = (A.entries i j : ℝ)
    rw [hsym.apply i j]
  have hdiff : diagonal (fun a => R a a) - R =
      (diagonal (fun a => A.entries a a) - A.entries).map (Int.castRingHom ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [R]
    · simp [R, hij]
  have hrealMargin (i : ι) :
      ∑ j, |(diagonal (fun a => R a a) - R) i j| ≤ R i i - 1 := by
    rw [hdiff]
    simp only [Matrix.map_apply]
    change (∑ j, |((diagonal (fun a => A.entries a a) - A.entries) i j : ℝ)|) ≤
      (A.entries i i : ℝ) - 1
    exact_mod_cast hmargin i
  have hpositive := posDef_of_symmetric_strict_row_margin R hR 1 (by norm_num) hrealMargin
  exact hpositive.smul (inv_pos.mpr (Nat.cast_pos.mpr hden))

end
end PhosphorylationStableCapacity
