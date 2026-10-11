module
public import proofs.PhosphorylationStableCapacity.SplitSlowComplexIsolation
public import proofs.PhosphorylationStableCapacity.SplitHurwitzAssembly
public import proofs.PhosphorylationStableCapacity.SplitDeterminantTransfer
public import proofs.PhosphorylationStableCapacity.FastBindingHurwitz
public import proofs.PhosphorylationStableCapacity.LoadedJacobianBlockMatrix
public import Mathlib.Analysis.Polynomial.Order

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial PhosphorylationSharpness

/-- A monic real polynomial with one simple real root and all other
complex roots in the open left half-plane has a positive complementary
constant term. Its own constant term has the opposite sign of that root. -/
theorem monic_simple_root_constant_sign
    (P q : ℝ[X]) (lam : ℝ)
    (hP : P.Monic)
    (hfactor : P = (X-C lam)*q)
    (hsimple : q.eval lam ≠ 0)
    (hleft : ∀ z : ℂ,
      (P.map (algebraMap ℝ ℂ)).IsRoot z →
        z.re < 0 ∨ z = (lam : ℂ)) :
    0 < q.eval 0 ∧ (0 < P.eval 0 ↔ lam < 0) := by
  have hqmonic : q.Monic := by
    rw [hfactor] at hP
    exact Monic.of_mul_monic_left (monic_X_sub_C lam) hP
  have hroots : ∀ y : ℝ, q.IsRoot y → y < 0 := by
    intro y hy
    by_contra hnot
    have hy0 : 0 ≤ y := le_of_not_gt hnot
    have hyP : P.IsRoot y := by
      change q.eval y = 0 at hy
      rw [hfactor]
      simp [IsRoot, hy]
    have hyPC : (P.map (algebraMap ℝ ℂ)).IsRoot (y : ℂ) :=
      Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) hyP
    rcases hleft (y : ℂ) hyPC with hneg | heq
    · have : y < 0 := by simpa using hneg
      exact (not_lt_of_ge hy0) this
    · have hyeq : y = lam := by exact_mod_cast heq
      exact hsimple (by simpa [hyeq] using hy)
  have hq0 : 0 < q.eval 0 :=
    zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg hroots
      (by rw [hqmonic.leadingCoeff]; norm_num)
  refine ⟨hq0, ?_⟩
  have hP0 : P.eval 0 = -lam*q.eval 0 := by
    rw [hfactor]
    simp [eval_mul, eval_sub, eval_X, eval_C]
  rw [hP0]
  constructor <;> intro h <;> nlinarith

/-- The complex simplicity certificate supplies the nonvanishing
complementary factor needed by the real sign theorem. -/
theorem monic_simple_root_constant_sign_of_derivative
    (P : ℝ[X]) (lam : ℝ)
    (hP : P.Monic) (hroot : P.IsRoot lam)
    (hsimple : ((P.map (algebraMap ℝ ℂ)).derivative).eval
      (lam : ℂ) ≠ 0)
    (hleft : ∀ z : ℂ,
      (P.map (algebraMap ℝ ℂ)).IsRoot z →
        z.re < 0 ∨ z = (lam : ℂ)) :
    0 < P.eval 0 ↔ lam < 0 := by
  let q := P /ₘ (X-C lam)
  have hfactor : P = (X-C lam)*q := by
    exact (mul_divByMonic_eq_iff_isRoot).2 hroot |>.symm
  have hfactorC : P.map (algebraMap ℝ ℂ) =
      (X-C (lam : ℂ))*(q.map (algebraMap ℝ ℂ)) := by
    simp [hfactor]
  have hderiv (Q : ℂ[X]) (z : ℂ) :
      ((X-C z)*Q).derivative.eval z = Q.eval z := by
    rw [derivative_mul]
    simp
  have hqC : (q.map (algebraMap ℝ ℂ)).eval (lam : ℂ) ≠ 0 := by
    rw [hfactorC, hderiv] at hsimple
    exact hsimple
  have hq : q.eval lam ≠ 0 := by
    intro hz
    apply hqC
    change (q.map (algebraMap ℝ ℂ)).eval
      ((algebraMap ℝ ℂ) lam) = 0
    rw [eval_map_apply, hz]
    simp
  exact (monic_simple_root_constant_sign P q lam hP hfactor hq hleft).2

/-- The determinant parity converts the characteristic constant term to
the sign of the unique real slow eigenvalue. -/
theorem real_matrix_simple_slow_det_sign
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (lam : ℝ)
    (hroot : A.charpoly.IsRoot lam)
    (hsimple : (((A.map (algebraMap ℝ ℂ)).charpoly).derivative).eval
      (lam : ℂ) ≠ 0)
    (hleft : ∀ z : ℂ,
      (A.charpoly.map (algebraMap ℝ ℂ)).IsRoot z →
        z.re < 0 ∨ z = (lam : ℂ)) :
    (0 < (-1 : ℝ)^Fintype.card ι * A.det ↔ lam < 0) := by
  have hconst : A.charpoly.eval 0 =
      (-1 : ℝ)^Fintype.card ι * A.det := by
    simp [Matrix.eval_charpoly, Matrix.det_neg]
  have hsign := monic_simple_root_constant_sign_of_derivative
    A.charpoly lam (Matrix.charpoly_monic A) hroot
    (by simpa only [Matrix.charpoly_map] using hsimple) hleft
  rwa [hconst] at hsign

/-- A real Hurwitz matrix has a positive parity-adjusted determinant.
This also covers empty index types, where the determinant is one. -/
theorem isHurwitz_parity_det_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : IsHurwitz A) :
    0 < (-1 : ℝ)^Fintype.card ι * A.det := by
  have hroots : ∀ y : ℝ, A.charpoly.IsRoot y → y < 0 := by
    intro y hy
    have hyC : ((A.map (algebraMap ℝ ℂ)).charpoly).IsRoot
        (y : ℂ) := by
      simpa only [Matrix.charpoly_map, ← Complex.coe_algebraMap] using
        (Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) hy)
    simpa using hA (y : ℂ) hyC
  have hconst : A.charpoly.eval 0 =
      (-1 : ℝ)^Fintype.card ι * A.det := by
    simp [Matrix.eval_charpoly, Matrix.det_neg]
  rw [← hconst]
  exact zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg hroots
    (by rw [A.charpoly_monic.leadingCoeff]; norm_num)

/-- The literal fast complex-balance elimination block has positive
determinant at every positive equilibrium with positive rates. -/
theorem loaded_source_fast_block_det_pos {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    (hk : k.Positive)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u)) :
    0 < (LinearMap.toMatrix (fastBasis n) (fastBasis n)
      (loadedBlockD ET FT ST k u).toLinearMap).det := by
  let x := stateFromLoaded ET FT ST u
  let rho : Fin n → ℝ := fun i => k.a i*x.S i.castSucc*x.E
  let sigma : Fin n → ℝ := fun i => k.alpha i*x.S i.succ*x.F
  have hρ : ∀ i, 0 < rho i := by
    intro i
    exact mul_pos (mul_pos (hk i).1 (hpos.1 i.castSucc)) hpos.2.1
  have hσ : ∀ i, 0 < sigma i := by
    intro i
    exact mul_pos (mul_pos (hk i).2.2.2.1 (hpos.1 i.succ)) hpos.2.2.1
  rw [loadedBlockD_toMatrix_eq_fastBinding ET FT ST k u hpos heq]
  have hhurwitz : IsHurwitz (fastBindingMatrix n x rho sigma) :=
    fastBindingMatrix_hurwitz x hpos rho sigma hρ hσ
  have hsign := isHurwitz_parity_det_pos
    (fastBindingMatrix n x rho sigma) hhurwitz
  simpa [Fintype.card_sum, pow_add] using hsign

/-- Dock the generic determinant-sign theorem to the actual retuned
class Jacobian and its one-slow-mode certificate. -/
theorem splitSlowModeCertificate_det_sign
    (m : ℕ) (r τ δ ε : ℝ)
    (j : Fin (2*(m+1)+1)) (ρ : ℝ)
    (hcert : SplitSlowModeCertificate m r τ δ ε j ρ) :
    let A := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (splitRetunedRates m r τ δ ε)
      (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))
    ∃ x : ℝ, |x| < ρ ∧ A.charpoly.IsRoot x ∧
      (0 < (-1 : ℝ)^Fintype.card
        (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) * A.det ↔ x < 0) ∧
      (IsHurwitz A ↔ x < 0) := by
  dsimp only
  obtain ⟨x, hx, hroot, hderiv, hrest⟩ := hcert
  let A := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
    (splitRetunedRates m r τ δ ε)
    (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))
  have hleft : ∀ z : ℂ,
      (A.charpoly.map (algebraMap ℝ ℂ)).IsRoot z →
        z.re < 0 ∨ z = (x : ℂ) := by
    intro z hz
    have hzspec : z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) := by
      apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
      simpa only [Matrix.charpoly_map] using hz
    exact hrest z hzspec
  have hhurwitz : IsHurwitz A ↔ x < 0 := by
    unfold IsHurwitz
    constructor
    · intro hstable
      simpa using hstable (x : ℂ) (by
        simpa only [A, Matrix.charpoly_map, ← Complex.coe_algebraMap,
          Polynomial.IsRoot] using
          (Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) hroot))
    · intro hxneg z hz
      have hzspec : z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) :=
        Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hz
      rcases hrest z hzspec with hzleft | heq
      · exact hzleft
      · rw [heq]
        simpa using hxneg
  exact ⟨x, hx, hroot,
    real_matrix_simple_slow_det_sign A x hroot hderiv hleft,
    hhurwitz⟩

theorem splitSlowModeCertificate_hurwitz_iff_det_positive
    (m : ℕ) (r τ δ ε : ℝ)
    (j : Fin (2*(m+1)+1)) (ρ : ℝ)
    (hcert : SplitSlowModeCertificate m r τ δ ε j ρ) :
    let A := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (splitRetunedRates m r τ δ ε)
      (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))
    IsHurwitz A ↔ 0 < (-1 : ℝ)^Fintype.card
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) * A.det := by
  obtain ⟨x, _, _, hdet, hhurwitz⟩ :=
    splitSlowModeCertificate_det_sign m r τ δ ε j ρ hcert
  exact hhurwitz.trans hdet.symm

/-- With the simple slow-mode certificates in hand, the only remaining
attainment-specific premise is positivity of the parity-adjusted literal
determinant at the even-indexed states. -/
theorem split_even_det_positive_attains (m : ℕ) (r τ δ ε : ℝ)
    (hr : 0 < r)
    (hadm : SplitRetunedFamilyAdmissible m r τ δ ε)
    (ρ : Fin (2*(m+1)+1) → ℝ)
    (hcert : ∀ j, SplitSlowModeCertificate m r τ δ ε j (ρ j))
    (hdet : ∀ i : Fin (m+2),
      let A := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (splitRetunedRates m r τ δ ε)
        (toCoordinateSpace (chart
          (splitFiniteState (m+1) r δ (splitEvenIndex m i))))
      0 < (-1 : ℝ)^Fintype.card
        (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) * A.det) :
    LinearlyStableClassAttains (m+2) (m+2) := by
  apply split_even_hurwitz_attains m r τ δ ε hr hadm
  intro i
  exact (splitSlowModeCertificate_hurwitz_iff_det_positive
    m r τ δ ε (splitEvenIndex m i) (ρ (splitEvenIndex m i))
    (hcert (splitEvenIndex m i))).2 (hdet i)

/-- Positive edge scaling and binding relaxation preserve the sign of
the parity-adjusted determinant, as well as the ordinary determinant. -/
theorem splitRetunedJacobian_parity_det_sign (m : ℕ)
    (r τ δ ε : ℝ) (j : Fin (2*(m+1)+1))
    (hτ : 0 < τ) (hε : 0 < ε) :
    let exponent := Fintype.card
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2)))
    0 < (-1 : ℝ)^exponent *
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (splitRetunedRates m r τ δ ε)
        (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).det ↔
    0 < (-1 : ℝ)^exponent *
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (splitFiniteRates (m+1) r δ)
        (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).det := by
  dsimp only
  rw [splitRetunedJacobian_det_factor m r τ δ ε j hε]
  have hw : ∀ i : Fin (m+2), 0 < coalescedFinalCurrentWeights m τ i := by
    intro i
    by_cases hi : i = Fin.last (m+1)
    · simp [coalescedFinalCurrentWeights, hi, hτ]
    · simp [coalescedFinalCurrentWeights, hi]
  have hfactor : 0 < (ε⁻¹) ^ (2*(m+2)) *
      (∏ i : Fin (m+2), coalescedFinalCurrentWeights m τ i) ^ 3 :=
    mul_pos (pow_pos (inv_pos.mpr hε) _)
      (pow_pos (Finset.prod_pos (fun i _ => hw i)) _)
  rw [show (-1 : ℝ)^Fintype.card
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) *
      ((ε⁻¹) ^ (2*(m+2)) *
        (∏ i : Fin (m+2), coalescedFinalCurrentWeights m τ i) ^ 3 *
          (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (splitFiniteRates (m+1) r δ)
            (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).det) =
      ((ε⁻¹) ^ (2*(m+2)) *
        (∏ i : Fin (m+2), coalescedFinalCurrentWeights m τ i) ^ 3) *
        ((-1 : ℝ)^Fintype.card
          (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) *
          (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (splitFiniteRates (m+1) r δ)
            (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).det)
    from by ring]
  exact mul_pos_iff_of_pos_left hfactor

/-- All spectral, kinetic, indexing, and fixed-class steps now reduce
the all-size attainment theorem to one source-Jacobian sign premise at
the even prescribed roots. -/
theorem split_even_source_det_positive_attains
    (m : ℕ) (r τ δ ε : ℝ)
    (hr : 0 < r) (hτ : 0 < τ) (hε : 0 < ε)
    (hadm : SplitRetunedFamilyAdmissible m r τ δ ε)
    (ρ : Fin (2*(m+1)+1) → ℝ)
    (hcert : ∀ j, SplitSlowModeCertificate m r τ δ ε j (ρ j))
    (hsource : ∀ i : Fin (m+2),
      let A := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (splitFiniteRates (m+1) r δ)
        (toCoordinateSpace (chart
          (splitFiniteState (m+1) r δ (splitEvenIndex m i))))
      0 < (-1 : ℝ)^Fintype.card
        (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) * A.det) :
    LinearlyStableClassAttains (m+2) (m+2) := by
  apply split_even_det_positive_attains m r τ δ ε hr hadm ρ hcert
  intro i
  exact (splitRetunedJacobian_parity_det_sign m r τ δ ε
    (splitEvenIndex m i) hτ hε).2 (hsource i)

end
end PhosphorylationStableCapacity
