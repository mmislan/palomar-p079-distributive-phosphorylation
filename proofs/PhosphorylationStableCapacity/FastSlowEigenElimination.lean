module
public import proofs.PhosphorylationStableCapacity.FastSlowScaledLimit

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix
open Filter Topology
open scoped Matrix.Norms.L2Operator

/-- The fast resolvent matrix at spectral parameter `λ` and time scale `ε`. -/
def fastSlowResolventMatrix {f : Type*} [Fintype f] [DecidableEq f]
    (D : Matrix f f ℂ) (ε z : ℂ) : Matrix f f ℂ :=
  (ε * z) • (1 : Matrix f f ℂ) - D

/-- A Hurwitz fast block has an invertible fast resolvent for a nonnegative
real-part spectral parameter and a positive real binding time scale. -/
theorem fastSlowResolventMatrix_isUnit_det_of_hurwitz
    {f : Type*} [Fintype f] [DecidableEq f]
    (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0)
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) (hz : 0 ≤ z.re) :
    IsUnit (fastSlowResolventMatrix D (ε : ℂ) z).det := by
  have hμre : 0 ≤ ((ε : ℂ) * z).re := by
    simpa using mul_nonneg (le_of_lt hε) hz
  have hnot : (ε : ℂ) * z ∉ spectrum ℂ D := by
    intro hmem
    exact (not_lt_of_ge hμre) (hD _ hmem)
  have hdet : IsUnit (D.charpoly.eval ((ε : ℂ) * z)) := by
    by_contra h
    exact hnot (Matrix.mem_spectrum_iff_not_isUnit_eval_charpoly.mpr h)
  have hscalar :
      (Matrix.scalar f ((ε : ℂ) * z) : Matrix f f ℂ) =
        ((ε : ℂ) * z) • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  rw [Matrix.eval_charpoly, hscalar] at hdet
  exact hdet

/-- The fast resolvent depends jointly continuously on time scale and
spectral parameter. At zero time scale its value is `-D`. -/
theorem fastSlowResolventMatrix_joint_continuous
    {f : Type*} [Fintype f] [DecidableEq f]
    (D : Matrix f f ℂ) :
    Continuous (fun p : ℂ × ℂ => fastSlowResolventMatrix D p.1 p.2) := by
  apply continuous_matrix
  intro i j
  simp only [fastSlowResolventMatrix, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  fun_prop

/-- A Hurwitz fast block has a jointly continuous inverse resolvent at
every point `(0,z)`, where the inverse limit is `(-D)⁻¹`. -/
theorem fastSlowResolventMatrix_inv_tendsto_zero
    {f : Type*} [Fintype f] [DecidableEq f]
    (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0)
    (z : ℂ) :
    Tendsto (fun p : ℂ × ℂ => (fastSlowResolventMatrix D p.1 p.2)⁻¹)
      (nhds (0, z)) (nhds (-D)⁻¹) := by
  have hunit : IsUnit (-D).det := by
    simpa [fastSlowResolventMatrix] using
      (fastSlowResolventMatrix_isUnit_det_of_hurwitz D hD
        (show (0 : ℝ) < 1 by norm_num) 0 (le_refl 0))
  have hInv : ContinuousAt (Inv.inv : Matrix f f ℂ → Matrix f f ℂ) (-D) :=
    continuousAt_matrix_inv (-D) (by
      simpa using (continuousAt_inv₀ hunit.ne_zero))
  have hR := (fastSlowResolventMatrix_joint_continuous D).continuousAt
    (x := (0, z))
  have hR' : Tendsto (fun p : ℂ × ℂ => fastSlowResolventMatrix D p.1 p.2)
      (nhds (0, z)) (nhds (-D)) := by
    simpa [fastSlowResolventMatrix] using hR.tendsto
  exact hInv.tendsto.comp hR'

/-- The spectral Schur operator converges jointly as time scale tends to
zero and the spectral parameter approaches any fixed complex value. -/
theorem fastSlowSpectralSchur_tendsto_zero
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0)
    (z : ℂ) :
    Tendsto (fun p : ℂ × ℂ =>
        A + B * (fastSlowResolventMatrix D p.1 p.2)⁻¹ * C)
      (nhds (0, z)) (nhds (A + B * (-D)⁻¹ * C)) := by
  have hInv := fastSlowResolventMatrix_inv_tendsto_zero D hD z
  have hA : Continuous (fun _ : Matrix f f ℂ => A) := continuous_const
  have hB : Continuous (fun _ : Matrix f f ℂ => B) := continuous_const
  have hM : Continuous (fun M : Matrix f f ℂ => M) := continuous_id
  have hC : Continuous (fun _ : Matrix f f ℂ => C) := continuous_const
  have hMap : Continuous (fun M : Matrix f f ℂ => A + B * M * C) :=
    hA.add ((hB.matrix_mul hM).matrix_mul hC)
  exact hMap.continuousAt.tendsto.comp hInv

theorem fastSlowSchur_limit_eq
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ) :
    A + B * (-D)⁻¹ * C = A - B * D⁻¹ * C := by
  by_cases hunit : IsUnit D.det
  · have hnegunit : IsUnit (-D).det :=
      (Matrix.isUnit_iff_isUnit_det (-D)).mp
        ((Matrix.isUnit_iff_isUnit_det D).mpr hunit).neg
    have hneg : (-D)⁻¹ = -D⁻¹ := by
      have hprod : (-D) * (-D⁻¹) = 1 := by
        simpa using Matrix.mul_nonsing_inv D hunit
      calc
        (-D)⁻¹ = (-D)⁻¹ * 1 := (mul_one _).symm
        _ = (-D)⁻¹ * ((-D) * (-D⁻¹)) := by rw [hprod]
        _ = ((-D)⁻¹ * (-D)) * (-D⁻¹) := by rw [Matrix.mul_assoc]
        _ = -D⁻¹ := by rw [Matrix.nonsing_inv_mul (-D) hnegunit, one_mul]
    rw [hneg]
    simp [sub_eq_add_neg, Matrix.mul_assoc]
  · have hnegunit : ¬IsUnit (-D).det := by
      intro h
      apply hunit
      have hm : IsUnit (-D) := (Matrix.isUnit_iff_isUnit_det (-D)).mpr h
      exact (Matrix.isUnit_iff_isUnit_det D).mp (by simpa using hm.neg)
    rw [Matrix.nonsing_inv_apply_not_isUnit D hunit,
      Matrix.nonsing_inv_apply_not_isUnit (-D) hnegunit]
    simp

theorem fastSlowSpectralSchur_tendsto_schur
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0)
    (z : ℂ) :
    Tendsto (fun p : ℂ × ℂ =>
        A + B * (fastSlowResolventMatrix D p.1 p.2)⁻¹ * C)
      (nhds (0, z)) (nhds (A - B * D⁻¹ * C)) := by
  rw [← fastSlowSchur_limit_eq A B C D]
  exact fastSlowSpectralSchur_tendsto_zero A B C D hD z

theorem matrix_mem_spectrum_of_mulVec_eq_smul
    {s : Type*} [Fintype s] [DecidableEq s]
    (M : Matrix s s ℂ) (z : ℂ) (x : s → ℂ)
    (hx : x ≠ 0) (heig : M *ᵥ x = z • x) :
    z ∈ spectrum ℂ M := by
  have hzero : (z • (1 : Matrix s s ℂ) - M) *ᵥ x = 0 := by
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact sub_eq_zero.mpr heig.symm
  obtain ⟨i, hi⟩ : ∃ i : s, x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    exact h i
  have hdet : (z • (1 : Matrix s s ℂ) - M).det = 0 :=
    Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hzero
      (i := i) (by simpa using hi)
  have hscalar : (Matrix.scalar s z : Matrix s s ℂ) = z • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot,
    Matrix.eval_charpoly, hscalar]
  exact hdet

/-- Exact eigenvector elimination, conditional on the fast resolvent being
invertible. This is an algebraic identity, without an asymptotic premise. -/
theorem fastSlow_eigen_eliminate {s f : Type*}
    [Fintype s] [Fintype f] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (ε z : ℂ) (x : s → ℂ) (y : f → ℂ)
    (hslow : A *ᵥ x + B *ᵥ y = z • x)
    (hfast : C *ᵥ x + D *ᵥ y = (ε * z) • y)
    (hunit : IsUnit (fastSlowResolventMatrix D ε z).det) :
    y = (fastSlowResolventMatrix D ε z)⁻¹ *ᵥ (C *ᵥ x) ∧
      (A + B * (fastSlowResolventMatrix D ε z)⁻¹ * C) *ᵥ x = z • x := by
  let R := fastSlowResolventMatrix D ε z
  have hR : R *ᵥ y = C *ᵥ x := by
    simp only [R, fastSlowResolventMatrix, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    exact ((eq_sub_iff_add_eq).mpr hfast).symm
  have hy : y = R⁻¹ *ᵥ (C *ᵥ x) := by
    calc
      y = (1 : Matrix f f ℂ) *ᵥ y := (Matrix.one_mulVec y).symm
      _ = (R⁻¹ * R) *ᵥ y := by rw [Matrix.nonsing_inv_mul R hunit]
      _ = R⁻¹ *ᵥ (R *ᵥ y) := (Matrix.mulVec_mulVec y R⁻¹ R).symm
      _ = R⁻¹ *ᵥ (C *ᵥ x) := by rw [hR]
  constructor
  · exact hy
  · rw [hy] at hslow
    change (A + B * R⁻¹ * C) *ᵥ x = z • x
    simpa only [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc] using hslow

/-- An eigenvector of the literal block matrix satisfies the two unscaled
block equations used by the resolvent elimination theorem. -/
theorem fastSlowMatrix_eigen_blocks {s f : Type*}
    [Fintype s] [Fintype f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    {ε : ℂ} (hε : ε ≠ 0) (z : ℂ) (v : s ⊕ f → ℂ)
    (hv : fastSlowMatrix A B C D ε *ᵥ v = z • v) :
    A *ᵥ (v ∘ Sum.inl) + B *ᵥ (v ∘ Sum.inr) = z • (v ∘ Sum.inl) ∧
      C *ᵥ (v ∘ Sum.inl) + D *ᵥ (v ∘ Sum.inr) =
        (ε * z) • (v ∘ Sum.inr) := by
  constructor
  · funext i
    have hi := congrArg (fun w : s ⊕ f → ℂ => w (Sum.inl i)) hv
    simpa [fastSlowMatrix, Matrix.fromBlocks_mulVec] using hi
  · have hraw :
        ε⁻¹ • (C *ᵥ (v ∘ Sum.inl) + D *ᵥ (v ∘ Sum.inr)) =
          z • (v ∘ Sum.inr) := by
      funext i
      have hi := congrArg (fun w : s ⊕ f → ℂ => w (Sum.inr i)) hv
      simpa [fastSlowMatrix, Matrix.fromBlocks_mulVec,
        Matrix.smul_mulVec, smul_add, mul_add] using hi
    have h := congrArg (fun w : f → ℂ => ε • w) hraw
    simpa [smul_smul, hε] using h

/-- Any nonstable eigenvector of the full fast/slow matrix has a nonzero
slow component satisfying the exact spectral Schur equation. -/
theorem fastSlowMatrix_nonnegative_eigen_schur
    {s f : Type*} [Fintype s] [Fintype f] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0)
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) (hz : 0 ≤ z.re)
    (v : s ⊕ f → ℂ) (hv0 : v ≠ 0)
    (hv : fastSlowMatrix A B C D (ε : ℂ) *ᵥ v = z • v) :
    (v ∘ Sum.inl) ≠ 0 ∧
      (A + B * (fastSlowResolventMatrix D (ε : ℂ) z)⁻¹ * C) *ᵥ
        (v ∘ Sum.inl) = z • (v ∘ Sum.inl) := by
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hε
  obtain ⟨hs, hf⟩ :=
    fastSlowMatrix_eigen_blocks A B C D hεc z v hv
  obtain ⟨hy, hschur⟩ :=
    fastSlow_eigen_eliminate A B C D (ε : ℂ) z
      (v ∘ Sum.inl) (v ∘ Sum.inr) hs hf
      (fastSlowResolventMatrix_isUnit_det_of_hurwitz D hD hε z hz)
  constructor
  · intro hx
    have hy0 : v ∘ Sum.inr = 0 := by
      rw [hy, hx]
      simp
    apply hv0
    funext i
    cases i with
    | inl j => simpa using congrFun hx j
    | inr j => simpa using congrFun hy0 j
  · exact hschur

/-- The slow component of any nonstable full-matrix eigenvector gives the
same eigenvalue for the spectral Schur matrix. -/
theorem fastSlowMatrix_nonnegative_eigen_schur_spectrum
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0)
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) (hz : 0 ≤ z.re)
    (v : s ⊕ f → ℂ) (hv0 : v ≠ 0)
    (hv : fastSlowMatrix A B C D (ε : ℂ) *ᵥ v = z • v) :
    z ∈ spectrum ℂ
      (A + B * (fastSlowResolventMatrix D (ε : ℂ) z)⁻¹ * C) := by
  obtain ⟨hx, heig⟩ :=
    fastSlowMatrix_nonnegative_eigen_schur A B C D hD hε z hz v hv0 hv
  exact matrix_mem_spectrum_of_mulVec_eq_smul _ z _ hx heig

end
end PhosphorylationStableCapacity
