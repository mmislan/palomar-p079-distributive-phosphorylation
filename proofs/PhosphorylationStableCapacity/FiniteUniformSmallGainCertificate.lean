module
public import proofs.PhosphorylationStableCapacity.ScaledComplexEntry
public import proofs.PhosphorylationStableCapacity.SaddleSmallGainMatrix
public import proofs.PhosphorylationStableCapacity.SaddleSmallGainSimpleSpectrum
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section

/-- Exact integer certificate data with fixed rational small-gain margins.
Each concrete instance must prove its integer equalities and inequalities;
this structure does not trust a numerical basis producer. -/
structure UniformSmallGainCertificate (N : ℕ) where
  A : ScaledIntegerMatrix (Fin (N+1)) (Fin (N+1))
  T : ScaledIntegerMatrix (Fin (N+1)) (Fin (N+1))
  U : ScaledIntegerMatrix (Fin (N+1)) (Fin (N+1))
  B : ScaledIntegerMatrix (Fin (N+1)) (Fin (N+1))
  positiveA : 0 < A.denominator
  positiveT : 0 < T.denominator
  positiveU : 0 < U.denominator
  positiveB : 0 < B.denominator
  inverse : T.entries * U.entries =
    ((T.denominator : ℤ)*(U.denominator : ℤ)) •
      (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℤ)
  intertwine :
    ((T.denominator*A.denominator : ℕ) : ℤ) • (B.entries*T.entries) =
      ((B.denominator*T.denominator : ℕ) : ℤ) • (T.entries*A.entries)
  row : ∀ i : Fin N,
    8*(B.entries i.succ i.succ +
      ∑ j ∈ (Finset.univ : Finset (Fin N)).erase i,
        |B.entries i.succ j.succ|) ≤ -(B.denominator : ℤ)
  column : ∀ i : Fin N,
    1000*|B.entries i.succ 0| ≤ (B.denominator : ℤ)
  feedback : 10*(∑ j : Fin N, |B.entries 0 j.succ|) ≤ (B.denominator : ℤ)

namespace UniformSmallGainCertificate

variable {N : ℕ} (C : UniformSmallGainCertificate N)

theorem inverse_real : C.T.realMatrix * C.U.realMatrix = 1 :=
  ScaledIntegerMatrix.inverse_of_integer_product C.T C.U
    C.positiveT C.positiveU C.inverse

theorem intertwine_real : C.B.realMatrix*C.T.realMatrix =
    C.T.realMatrix*C.A.realMatrix := by
  rw [ScaledIntegerMatrix.realMatrix_mul, ScaledIntegerMatrix.realMatrix_mul]
  apply ScaledIntegerMatrix.realMatrix_eq_of_integer_cross_product
  · exact Nat.mul_pos C.positiveB C.positiveT
  · exact Nat.mul_pos C.positiveT C.positiveA
  · exact C.intertwine

theorem charpoly_eq : C.B.realMatrix.charpoly = C.A.realMatrix.charpoly := by
  have hUT : C.U.realMatrix*C.T.realMatrix = 1 := mul_eq_one_comm.mp C.inverse_real
  calc
    C.B.realMatrix.charpoly =
        (C.B.realMatrix*(C.T.realMatrix*C.U.realMatrix)).charpoly := by
          rw [C.inverse_real, mul_one]
    _ = ((C.B.realMatrix*C.T.realMatrix)*C.U.realMatrix).charpoly := by
          rw [Matrix.mul_assoc]
    _ = ((C.T.realMatrix*C.A.realMatrix)*C.U.realMatrix).charpoly := by
          rw [C.intertwine_real]
    _ = (C.U.realMatrix*(C.T.realMatrix*C.A.realMatrix)).charpoly :=
          Matrix.charpoly_mul_comm _ _
    _ = ((C.U.realMatrix*C.T.realMatrix)*C.A.realMatrix).charpoly := by
          rw [Matrix.mul_assoc]
    _ = C.A.realMatrix.charpoly := by rw [hUT, one_mul]

def complexMatrix : Matrix (Fin (N+1)) (Fin (N+1)) ℂ :=
  C.B.realMatrix.map (algebraMap ℝ ℂ)

theorem complex_charpoly_eq : C.complexMatrix.charpoly =
    (C.A.realMatrix.map (algebraMap ℝ ℂ)).charpoly := by
  rw [complexMatrix, Matrix.charpoly_map, C.charpoly_eq, ← Matrix.charpoly_map]

theorem row_real (i : Fin N) :
    (C.complexMatrix i.succ i.succ).re +
      ∑ j ∈ (Finset.univ : Finset (Fin N)).erase i,
        ‖C.complexMatrix i.succ j.succ‖ ≤ -(1/8 : ℝ) := by
  let D : ℝ := C.B.denominator
  have hD : 0 < D := Nat.cast_pos.mpr C.positiveB
  have hcast : 8*((C.B.entries i.succ i.succ : ℝ) +
      ∑ j ∈ (Finset.univ : Finset (Fin N)).erase i,
        (|C.B.entries i.succ j.succ| : ℝ)) ≤ -D := by
    dsimp [D]
    exact_mod_cast C.row i
  have hupper : (C.B.entries i.succ i.succ : ℝ) +
      ∑ j ∈ (Finset.univ : Finset (Fin N)).erase i,
        (|C.B.entries i.succ j.succ| : ℝ) ≤ -D/8 := by linarith
  simp only [complexMatrix, scaledComplex_entry_re,
    scaledComplex_entry_norm C.B C.positiveB]
  rw [← Finset.sum_div]
  calc
    _ = ((C.B.entries i.succ i.succ : ℝ) +
        ∑ j ∈ (Finset.univ : Finset (Fin N)).erase i,
          (|C.B.entries i.succ j.succ| : ℝ))/D := by ring
    _ ≤ (-D/8)/D := (div_le_div_iff_of_pos_right hD).2 hupper
    _ = -(1/8 : ℝ) := by field_simp [ne_of_gt hD]

theorem column_real (i : Fin N) :
    ‖C.complexMatrix i.succ 0‖ ≤ (1/1000 : ℝ) := by
  let D : ℝ := C.B.denominator
  have hD : 0 < D := Nat.cast_pos.mpr C.positiveB
  have hcast : 1000*(|C.B.entries i.succ 0| : ℝ) ≤ D := by
    dsimp [D]
    exact_mod_cast C.column i
  rw [complexMatrix, scaledComplex_entry_norm C.B C.positiveB]
  apply (div_le_iff₀ hD).2
  norm_num
  linarith

theorem feedback_real : (∑ j : Fin N, ‖C.complexMatrix 0 j.succ‖) ≤ (1/10 : ℝ) := by
  let D : ℝ := C.B.denominator
  have hD : 0 < D := Nat.cast_pos.mpr C.positiveB
  have hcast : 10*(∑ j : Fin N, (|C.B.entries 0 j.succ| : ℝ)) ≤ D := by
    dsimp [D]
    exact_mod_cast C.feedback
  simp only [complexMatrix, scaledComplex_entry_norm C.B C.positiveB]
  rw [← Finset.sum_div]
  apply (div_le_iff₀ hD).2
  norm_num
  linarith

theorem unique_right [NeZero N] (z z' : ℂ) (hz : 0 ≤ z.re) (hz' : 0 ≤ z'.re)
    (hr : (C.A.realMatrix.map (algebraMap ℝ ℂ)).charpoly.eval z = 0)
    (hr' : (C.A.realMatrix.map (algebraMap ℝ ℂ)).charpoly.eval z' = 0) : z = z' := by
  apply block_spectrum_unique_right C.complexMatrix
    (1/8) (1/1000) (1/100) (1/10) (by norm_num)
    C.row_real C.column_real (by norm_num) (by norm_num)
    C.feedback_real (by norm_num) z z' hz hz'
  · rwa [C.complex_charpoly_eq]
  · rwa [C.complex_charpoly_eq]

theorem simple_right [NeZero N] (z : ℂ) (hz : 0 ≤ z.re)
    (hr : (C.A.realMatrix.map (algebraMap ℝ ℂ)).charpoly.eval z = 0) :
    (C.A.realMatrix.map (algebraMap ℝ ℂ)).charpoly.derivative.eval z ≠ 0 := by
  rw [← C.complex_charpoly_eq]
  apply block_spectrum_simple_right C.complexMatrix
    (1/8) (1/1000) (1/100) (1/10) (by norm_num)
    C.row_real C.column_real (by norm_num) (by norm_num)
    C.feedback_real (by norm_num) z hz
  rwa [C.complex_charpoly_eq]

end UniformSmallGainCertificate
end
end PhosphorylationStableCapacity
