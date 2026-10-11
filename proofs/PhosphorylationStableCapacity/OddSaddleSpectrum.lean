module
public import proofs.PhosphorylationStableCapacity.OddSaddleOrientation
public import proofs.PhosphorylationStableCapacity.StrongCapacity435
public import proofs.PhosphorylationStableCapacity.SourceJacobianAugmentedOrientation

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Polynomial Matrix

/-- Nonzero physical augmented determinant makes the actual fixed-class
Jacobian nonsingular at a positive equilibrium. -/
theorem equilibrium_restricted_jacobian_det_ne_zero_of_augmented
    {n : ℕ} (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive) (heq : Equilibrium k x)
    (haug : (sourceAugmentedCurrentMatrix k x).det ≠ 0) :
    (restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
      k (toCoordinateSpace (chart x))).det ≠ 0 := by
  let u := loadedCoordOfState x
  have hback : stateFromLoaded (totalE x) (totalF x) (totalS x) u = x :=
    stateFromLoaded_loadedCoordOfState _ _ _ x ⟨rfl, rfl, rfl⟩
  have hcoord : fromLoadedCoord u = toCoordinateSpace (chart x) := by
    simp [u, loadedCoordOfState, from_toLoadedCoord]
  obtain ⟨hfast, hfactor⟩ :=
    source_jacobian_det_eq_positive_fast_mul_schur
      (totalE x) (totalF x) (totalS x) k u hk
      (by rw [hback]; exact hx) (by rw [hback]; exact heq)
  have hconstrained :
      (sourceConstrainedCurrentDerivative k x).det ≠ 0 := by
    intro hz
    apply haug
    rw [sourceAugmentedCurrentMatrix_det_eq_pivot_mul_constrained
      k x hx, hz, mul_zero]
  have hchain := congrArg Matrix.det
    (equilibrium_sourceCurrentResponse_mul_constrainedMass k x hk hx heq)
  rw [Matrix.det_mul] at hchain
  have hcurrent :
      (sourceCurrentResponseMatrix (totalE x) (totalF x) (totalS x)
        k u).det ≠ 0 := by
    intro hz
    apply hconstrained
    rw [← hchain, hz, zero_mul]
  have hslow :
      (sourceSlowSchurMatrix (totalE x) (totalF x) (totalS x)
        k u).det ≠ 0 := by
    rw [sourceSlowSchurMatrix_det_eq_current_response_det]
    exact hcurrent
  rw [hcoord] at hfactor
  rw [hfactor]
  exact mul_ne_zero (ne_of_gt hfast) hslow

/-- Exactly one simple real eigenvalue is positive; all remaining
class-Jacobian eigenvalues lie strictly in the left half-plane. -/
def IsOneUnstableSaddle {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) : Prop :=
  let A := restrictedJacobianMatrix ET FT ST k u
  ∃ x : ℝ,
    0 < x ∧ A.charpoly.IsRoot x ∧
    ((A.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
    ∀ z : ℂ, z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) →
      z.re < 0 ∨ z = (x : ℂ)

/-- The odd members of the common retuned split family each have one
unstable real direction and a strictly stable transverse spectrum. -/
theorem split_odd_is_one_unstable_saddle
    (m : ℕ) (r τ δ ε : ℝ)
    (hr : 0 < r) (hτ : 0 < τ) (hε : 0 < ε) (hδ : 0 < δ)
    (hD : DensePositive (splitRawD (m+1) r δ) (m+1))
    (hB : DensePositive (splitRawB (m+1) r δ) (m+1))
    (hv : ∀ j : Fin (2*(m+1)+1),
      0 < r-ratio (splitRoot δ j.val))
    (ρ : Fin (2*(m+1)+1) → ℝ)
    (hcert : ∀ j, SplitSlowModeCertificate m r τ δ ε j (ρ j))
    (j : Fin (2*(m+1)+1)) (hodd : Odd j.val) :
    IsOneUnstableSaddle (2*r) 2 (2*(r+1))
      (splitRetunedRates m r τ δ ε)
      (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j))) := by
  let y := splitFiniteState (m+1) r δ j
  let k₀ := splitFiniteRates (m+1) r δ
  let A₀ := restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k₀
    (toCoordinateSpace (chart y))
  let A := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
    (splitRetunedRates m r τ δ ε) (toCoordinateSpace (chart y))
  obtain ⟨hk₀, hy, heq, hET, hFT, hST⟩ :=
    splitFiniteState_source_of_conversion_positive
      (m+1) r δ hδ.le hD hB j
  have haug : (-1 : ℝ)^(m+2) *
      (sourceAugmentedCurrentMatrix k₀ y).det < 0 := by
    simpa only [k₀, y, Nat.add_assoc] using
      split_odd_source_augmented_current_det_neg
        (m+1) r δ j hr hδ hD hB (hv j) hodd
  have hsrcne : A₀.det ≠ 0 := by
    have h := equilibrium_restricted_jacobian_det_ne_zero_of_augmented
      k₀ y hk₀ hy heq (by
        intro hz
        rw [hz, mul_zero] at haug
        linarith)
    change totalE y = 2*r at hET
    change totalF y = 2 at hFT
    change totalS y = 2*(r+1) at hST
    rw [hET, hFT, hST] at h
    exact h
  have hpow : (-1 : ℝ)^Fintype.card
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) =
      (-1 : ℝ)^(m+2) := by
    have hcard : Fintype.card
        (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) =
        (m+2) + 2*(m+2) := by simp; omega
    rw [hcard, pow_add, pow_mul]
    norm_num
  have hsrcnotpos : ¬ 0 < (-1 : ℝ)^Fintype.card
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) * A₀.det := by
    intro hsrcpos
    have haugpos :=
      (equilibrium_restricted_jacobian_parity_det_pos_iff_augmented
        k₀ y hk₀ hy heq).1 (by
          change totalE y = 2*r at hET
          change totalF y = 2 at hFT
          change totalS y = 2*(r+1) at hST
          simpa only [hET, hFT, hST, hpow] using hsrcpos)
    linarith
  have hretne : A.det ≠ 0 := by
    have hsign := splitRetunedJacobian_det_sign
      m r τ δ ε j hτ hε
    rcases lt_trichotomy A₀.det 0 with hneg | hzero | hpos
    · exact ne_of_lt (hsign.1.mpr hneg)
    · exact False.elim (hsrcne hzero)
    · exact ne_of_gt (hsign.2.mpr hpos)
  have hretnotpos : ¬ 0 < (-1 : ℝ)^Fintype.card
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) * A.det := by
    intro hpos
    exact hsrcnotpos ((splitRetunedJacobian_parity_det_sign
      m r τ δ ε j hτ hε).1 hpos)
  obtain ⟨x, hxsmall, hroot, hsimple, hrest⟩ := hcert j
  have hleft : ∀ z : ℂ,
      (A.charpoly.map (algebraMap ℝ ℂ)).IsRoot z →
        z.re < 0 ∨ z = (x : ℂ) := by
    intro z hz
    apply hrest z
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    simpa only [Matrix.charpoly_map] using hz
  have hdetiff :
      (0 < (-1 : ℝ)^Fintype.card
        (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) * A.det) ↔
      x < 0 :=
    real_matrix_simple_slow_det_sign A x hroot hsimple hleft
  have hxnonneg : 0 ≤ x := le_of_not_gt (fun hxneg =>
    hretnotpos (hdetiff.mpr hxneg))
  have hxne : x ≠ 0 := by
    intro hxzero
    have heval : A.charpoly.eval 0 = 0 := by
      simpa only [hxzero, Polynomial.IsRoot] using hroot
    have hdetzero : A.det = 0 := by
      simpa [Matrix.eval_charpoly, Matrix.det_neg] using heval
    exact hretne hdetzero
  have hxpos : 0 < x := by
    rcases hxnonneg.eq_or_lt with heq | hpos
    · exact False.elim (hxne heq.symm)
    · exact hpos
  exact ⟨x, hxpos, hroot, hsimple, hrest⟩

end
end PhosphorylationStableCapacity
