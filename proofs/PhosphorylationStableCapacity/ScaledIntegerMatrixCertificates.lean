module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- An exact rational matrix with a common positive integer denominator.
Clearing denominators lets the finite certificate checker use integer
arithmetic instead of repeatedly normalizing large rational expressions. -/
structure ScaledIntegerMatrix (ι κ : Type*) where
  denominator : ℕ
  entries : Matrix ι κ ℤ

namespace ScaledIntegerMatrix

def realMatrix {ι κ : Type*} (A : ScaledIntegerMatrix ι κ) : Matrix ι κ ℝ :=
  (A.denominator : ℝ)⁻¹ • A.entries.map (Int.castRingHom ℝ)

/-- A kernel-checked integer product certificate gives an exact real inverse.
The integer identity, not an unchecked inverse producer, is the evidence. -/
theorem inverse_of_integer_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ScaledIntegerMatrix ι ι)
    (hA : 0 < A.denominator) (hB : 0 < B.denominator)
    (hproduct : A.entries * B.entries =
      ((A.denominator : ℤ) * (B.denominator : ℤ)) • (1 : Matrix ι ι ℤ)) :
    A.realMatrix * B.realMatrix = 1 := by
  have hA0 : (A.denominator : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hA)
  have hB0 : (B.denominator : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hB)
  have hmap : A.entries.map (Int.castRingHom ℝ) * B.entries.map (Int.castRingHom ℝ) =
      ((A.denominator : ℝ) * (B.denominator : ℝ)) • (1 : Matrix ι ι ℝ) := by
    rw [← Matrix.map_mul, hproduct]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.map, Matrix.smul_apply]
    · simp [Matrix.map, Matrix.smul_apply, hij]
  simp only [realMatrix, Matrix.smul_mul, Matrix.mul_smul, hmap, smul_smul]
  have hcoef : (B.denominator : ℝ)⁻¹ *
      ((A.denominator : ℝ)⁻¹ * ((A.denominator : ℝ) * (B.denominator : ℝ))) = 1 := by
    field_simp
  rw [hcoef, one_smul]

theorem realMatrix_mul {ι κ ν : Type*} [Fintype κ]
    (A : ScaledIntegerMatrix ι κ) (B : ScaledIntegerMatrix κ ν) :
    A.realMatrix * B.realMatrix =
      (ScaledIntegerMatrix.mk (A.denominator * B.denominator)
        (A.entries * B.entries)).realMatrix := by
  simp only [realMatrix, Nat.cast_mul, mul_inv_rev, Matrix.smul_mul,
    Matrix.mul_smul, ← Matrix.map_mul, smul_smul]

theorem realMatrix_transpose {ι κ : Type*} (A : ScaledIntegerMatrix ι κ) :
    A.realMatrix.transpose =
      (ScaledIntegerMatrix.mk A.denominator A.entries.transpose).realMatrix := by
  simp only [realMatrix, Matrix.transpose_smul, Matrix.transpose_map]

theorem realMatrix_lyapunov {ι : Type*} [Fintype ι]
    (A P : ScaledIntegerMatrix ι ι) :
    A.realMatrix.transpose * P.realMatrix + P.realMatrix * A.realMatrix =
      (ScaledIntegerMatrix.mk (A.denominator * P.denominator)
        (A.entries.transpose * P.entries + P.entries * A.entries)).realMatrix := by
  rw [realMatrix_transpose, realMatrix_mul, realMatrix_mul]
  simp only [realMatrix, Nat.mul_comm]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.map_apply, map_add]
  ring

theorem realMatrix_neg {ι κ : Type*} (A : ScaledIntegerMatrix ι κ) :
    (ScaledIntegerMatrix.mk A.denominator (-A.entries)).realMatrix = -A.realMatrix := by
  ext i j
  simp only [realMatrix, Matrix.map_apply, Matrix.neg_apply,
    Matrix.smul_apply, smul_eq_mul, map_neg]
  ring

/-- Cross multiplication is a sound equality certificate for two
denominator-cleared rational matrices. -/
theorem realMatrix_eq_of_integer_cross_product {ι κ : Type*}
    (A B : ScaledIntegerMatrix ι κ)
    (hA : 0 < A.denominator) (hB : 0 < B.denominator)
    (hcross : (B.denominator : ℤ) • A.entries =
      (A.denominator : ℤ) • B.entries) : A.realMatrix = B.realMatrix := by
  have hA0 : (A.denominator : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hA)
  have hB0 : (B.denominator : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hB)
  ext i j
  have h := congrArg (Int.castRingHom ℝ) (congr_fun (congr_fun hcross i) j)
  simp only [Matrix.smul_apply, zsmul_eq_mul, map_mul] at h
  change (B.denominator : ℝ) * (A.entries i j : ℝ) =
    (A.denominator : ℝ) * (B.entries i j : ℝ) at h
  change (A.denominator : ℝ)⁻¹ * (A.entries i j : ℝ) =
    (B.denominator : ℝ)⁻¹ * (B.entries i j : ℝ)
  field_simp
  simpa only [mul_comm] using h

theorem diagonal_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ScaledIntegerMatrix ι ι) (v : ι → ℤ)
    (hden : 0 < A.denominator) (hdiag : A.entries = Matrix.diagonal v)
    (hv : ∀ i, 0 < v i) : A.realMatrix.PosDef := by
  have hdenReal : 0 < (A.denominator : ℝ) := Nat.cast_pos.mpr hden
  have hmatrix : A.realMatrix = Matrix.diagonal
      (fun i => (A.denominator : ℝ)⁻¹ * (v i : ℝ)) := by
    ext i j
    simp [realMatrix, hdiag, Matrix.diagonal_apply]
  rw [hmatrix]
  apply Matrix.PosDef.diagonal
  intro i
  exact mul_pos (inv_pos.mpr hdenReal) (Int.cast_pos.mpr (hv i))

end ScaledIntegerMatrix

/-- A common exact LDL certificate proves positive definiteness once the
triangular factor has a checked right inverse. -/
theorem posDef_of_ldl_with_right_inverse {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (P L D R : Matrix ι ι ℝ) (hD : D.PosDef)
    (hLR : L * R = 1) (hP : P = L * D * L.transpose) : P.PosDef := by
  have htranspose : R.transpose * L.transpose = 1 := by
    have h := congrArg Matrix.transpose hLR
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using h
  have hinj : Function.Injective L.transpose.mulVec := by
    intro x y hxy
    have h := congrArg R.transpose.mulVec hxy
    simpa only [Matrix.mulVec_mulVec, htranspose, Matrix.one_mulVec] using h
  have hconj : L.transpose.conjTranspose = L := by
    ext i j
    simp
  have hpos := hD.conjTranspose_mul_mul_same hinj
  rw [hconj] at hpos
  rw [hP]
  exact hpos

end
end PhosphorylationStableCapacity
