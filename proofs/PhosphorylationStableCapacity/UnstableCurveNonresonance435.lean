module
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.NormCast
public import Lean.Elab.Tactic.Omega
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum

@[expose] public section
namespace P079UnstableWorkbench

/-- The spectral saddle hypothesis excludes every nonlinear parameterization
resonance klam, k≥2. No invariant curve is assumed in this lemma. -/
theorem scaled_positive_eigenvalue_not_mem_spectrum
    {A : Type*} [Ring A] [Algebra ℂ A] (a : A) (lam : ℝ)
    (hlam : 0 < lam)
    (hspectrum : ∀ z : ℂ, z ∈ spectrum ℂ a → z.re < 0 ∨ z = (lam : ℂ))
    (k : ℕ) (hk : 2 ≤ k) :
    (((k : ℝ) * lam : ℝ) : ℂ) ∉ spectrum ℂ a := by
  intro hmem
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hpositive : 0 < (k : ℝ) * lam := by nlinarith
  rcases hspectrum _ hmem with hleft | heq
  · have hnegative : (k : ℝ) * lam < 0 := by simpa using hleft
    linarith
  · have heqR : (k : ℝ) * lam = lam := by
      simpa using congrArg Complex.re heq
    nlinarith

theorem scaled_positive_eigenvalue_resolvent_isUnit
    {A : Type*} [Ring A] [Algebra ℂ A] (a : A) (lam : ℝ)
    (hlam : 0 < lam)
    (hspectrum : ∀ z : ℂ, z ∈ spectrum ℂ a → z.re < 0 ∨ z = (lam : ℂ))
    (k : ℕ) (hk : 2 ≤ k) :
    IsUnit (algebraMap ℂ A (((k : ℝ) * lam : ℝ) : ℂ) - a) := by
  have hnot := scaled_positive_eigenvalue_not_mem_spectrum a lam hlam hspectrum k hk
  simpa only [spectrum.mem_iff, not_not] using hnot

/-- This applies directly to the actual Jacobian at any currently proved odd
saddle. It proves nonresonance, not the existence of a nonlinear manifold. -/
theorem actual_saddle_parameterization_nonresonance
    {n : ℕ} (ET FT ST : ℝ) (k : PhosphorylationSharpness.Rates n)
    (u : PhosphorylationStableCapacity.CoordinateSpace n)
    (hsaddle : PhosphorylationStableCapacity.IsOneUnstableSaddle ET FT ST k u) :
    ∃ lam : ℝ, 0 < lam ∧
      (PhosphorylationStableCapacity.restrictedJacobianMatrix ET FT ST k u).charpoly.IsRoot lam ∧
      ∀ j : ℕ, 2 ≤ j →
        IsUnit (algebraMap ℂ _ (((j : ℝ) * lam : ℝ) : ℂ) -
          (PhosphorylationStableCapacity.restrictedJacobianMatrix ET FT ST k u).map
            (algebraMap ℝ ℂ)) := by
  obtain ⟨lam, hlam, hroot, -, hspectrum⟩ := hsaddle
  exact ⟨lam, hlam, hroot, fun j hj =>
    scaled_positive_eigenvalue_resolvent_isUnit _ lam hlam hspectrum j hj⟩

/-- Complex invertibility of a real matrix reflects to real invertibility.
This uses the literal determinant under scalar extension. -/
theorem real_matrix_isUnit_of_complex_map
    {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ)
    (hB : IsUnit (B.map (algebraMap ℝ ℂ))) : IsUnit B := by
  have hdet : IsUnit ((algebraMap ℝ ℂ) B.det) := by
    rw [(algebraMap ℝ ℂ).map_det]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hB
  have hne : B.det ≠ 0 := by
    intro hzero
    apply (isUnit_iff_ne_zero.mp hdet)
    rw [hzero, map_zero]
  exact (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hne)

theorem real_matrix_resolvent_isUnit_of_complex
    {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ) (x : ℝ)
    (hB : IsUnit (algebraMap ℂ (Matrix ι ι ℂ) (x : ℂ) -
      B.map (algebraMap ℝ ℂ))) :
    IsUnit (algebraMap ℝ (Matrix ι ι ℝ) x - B) := by
  apply real_matrix_isUnit_of_complex_map
  have hmap : (algebraMap ℝ (Matrix ι ι ℝ) x - B).map (algebraMap ℝ ℂ) =
      algebraMap ℂ (Matrix ι ι ℂ) (x : ℂ) - B.map (algebraMap ℝ ℂ) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.algebraMap_matrix_apply, Matrix.map_apply, hij]
  rw [hmap]
  exact hB

/-- Matrix nonresonance gives the real bounded-operator inverse required by
the coefficient recursion. No real resolvent is assumed here. -/
theorem real_operator_resolvent_isUnit_of_complex_matrix
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    (A : E →L[ℝ] E) (x : ℝ)
    (hA : IsUnit (algebraMap ℂ (Matrix ι ι ℂ) (x : ℂ) -
      (LinearMap.toMatrix b b A.toLinearMap).map (algebraMap ℝ ℂ))) :
    IsUnit (x • (1 : E →L[ℝ] E) - A) := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap,
    ← LinearMap.isUnit_toMatrix_iff b]
  have hm : LinearMap.toMatrix b b (x • (1 : E →L[ℝ] E) - A).toLinearMap =
      algebraMap ℝ (Matrix ι ι ℝ) x - LinearMap.toMatrix b b A.toLinearMap := by
    change (LinearMap.toMatrixAlgEquiv b) (x • (1 : Module.End ℝ E) - A.toLinearMap) = _
    rw [map_sub, map_smul, map_one]
    simp only [Algebra.algebraMap_eq_smul_one]
    congr 1
  rw [hm]
  exact real_matrix_resolvent_isUnit_of_complex _ x hA

/-- A real characteristic root supplies a genuinely nonzero real eigenvector
in the actual coordinate space, without selecting a complex vector. -/
theorem real_operator_eigenvector_of_matrix_root
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    (A : E →L[ℝ] E) (lam : ℝ)
    (hroot : (LinearMap.toMatrix b b A.toLinearMap).charpoly.IsRoot lam) :
    ∃ v : E, v ≠ 0 ∧ A v = lam • v := by
  have hmatrix : lam ∈ spectrum ℝ (LinearMap.toMatrix b b A.toLinearMap) :=
    Matrix.mem_spectrum_of_isRoot_charpoly hroot
  have hspectrum : lam ∈ spectrum ℝ A.toLinearMap := by
    rw [← AlgEquiv.spectrum_eq (R := ℝ)
      (f := LinearMap.toMatrixAlgEquiv b) (a := A.toLinearMap)]
    have hrepr : (LinearMap.toMatrixAlgEquiv b) A.toLinearMap =
        LinearMap.toMatrix b b A.toLinearMap := by
      ext i j
      simp only [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
    simpa only [hrepr] using hmatrix
  obtain ⟨v, hv⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hspectrum).exists_hasEigenvector
  exact ⟨v, hv.2, hv.apply_eq_smul⟩

theorem actual_saddle_real_operator_data
    {n : ℕ} (ET FT ST : ℝ) (k : PhosphorylationSharpness.Rates n)
    (u : PhosphorylationStableCapacity.CoordinateSpace n)
    (hsaddle : PhosphorylationStableCapacity.IsOneUnstableSaddle ET FT ST k u) :
    ∃ (lam : ℝ) (v : PhosphorylationStableCapacity.CoordinateSpace n),
      0 < lam ∧ v ≠ 0 ∧
      PhosphorylationStableCapacity.restrictedJacobian ET FT ST k u v = lam • v ∧
      ∀ j : ℕ, 2 ≤ j → IsUnit (((j : ℝ)*lam) •
        (1 : PhosphorylationStableCapacity.CoordinateSpace n →L[ℝ]
          PhosphorylationStableCapacity.CoordinateSpace n) -
        PhosphorylationStableCapacity.restrictedJacobian ET FT ST k u) := by
  classical
  obtain ⟨lam, hlam, hroot, hinv⟩ :=
    actual_saddle_parameterization_nonresonance ET FT ST k u hsaddle
  obtain ⟨v, hv, heigen⟩ := real_operator_eigenvector_of_matrix_root
    (PhosphorylationStableCapacity.coordinateBasis n)
    (PhosphorylationStableCapacity.restrictedJacobian ET FT ST k u) lam hroot
  refine ⟨lam, v, hlam, hv, heigen, fun j hj => ?_⟩
  exact real_operator_resolvent_isUnit_of_complex_matrix
    (PhosphorylationStableCapacity.coordinateBasis n)
    (PhosphorylationStableCapacity.restrictedJacobian ET FT ST k u) _ (hinv j hj)

end P079UnstableWorkbench
