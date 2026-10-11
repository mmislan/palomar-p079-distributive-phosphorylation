module
public import proofs.PhosphorylationStableCapacity.Jacobian
public import proofs.PhosphorylationStableCapacity.ScaledIntegerMatrixCertificates
public import proofs.PhosphorylationStableCapacity.PositiveDefiniteLyapunovHurwitz

public import Mathlib.Logic.Encodable.Pi
public import Mathlib.Data.Rat.Encodable

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

/-- A wholly rational exact diagonal-congruence witness for the Lyapunov
alternative in Remark 9's ordered search. The right inverses make both
congruence factors injective; the diagonal entries certify strict positivity. This structure
records one finite certificate, not termination of the full nested search. -/
structure RationalLyapunovLDLCertificate {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℚ) where
  P : Matrix ι ι ℚ
  Q : Matrix ι ι ℚ
  LP : Matrix ι ι ℚ
  RP : Matrix ι ι ℚ
  LQ : Matrix ι ι ℚ
  RQ : Matrix ι ι ℚ
  dP : ι → ℚ
  dQ : ι → ℚ
  positiveP : ∀ i, 0 < dP i
  positiveQ : ∀ i, 0 < dQ i
  inverseP : LP * RP = 1
  inverseQ : LQ * RQ = 1
  factorP : P = LP * Matrix.diagonal dP * LP.transpose
  factorQ : Q = LQ * Matrix.diagonal dQ * LQ.transpose
  lyapunov : A.transpose * P + P * A = -Q

/-- Raw finite rational entries, suitable for a decidable exact test. -/
structure RationalLyapunovLDLData (ι : Type*) [Fintype ι]
    [DecidableEq ι] where
  P : Matrix ι ι ℚ
  Q : Matrix ι ι ℚ
  LP : Matrix ι ι ℚ
  RP : Matrix ι ι ℚ
  LQ : Matrix ι ι ℚ
  RQ : Matrix ι ι ℚ
  dP : ι → ℚ
  dQ : ι → ℚ


/-- The finite rational data are encoded without depending on deriving-handler
internals. The local index encoding is fixed by the given finite type. -/
noncomputable instance rationalLyapunovLDLDataEncodable
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Encodable (RationalLyapunovLDLData ι) := by
  letI : Encodable ι := Fintype.toEncodable ι
  letI : Encodable (ι → ℚ) := inferInstance
  letI : Encodable (Matrix ι ι ℚ) :=
    inferInstanceAs (Encodable (ι → ι → ℚ))
  let e : RationalLyapunovLDLData ι ≃
      (Matrix ι ι ℚ × Matrix ι ι ℚ × Matrix ι ι ℚ ×
        Matrix ι ι ℚ × Matrix ι ι ℚ × Matrix ι ι ℚ ×
        (ι → ℚ) × (ι → ℚ)) := {
    toFun := fun C => ⟨C.P, C.Q, C.LP, C.RP, C.LQ, C.RQ, C.dP, C.dQ⟩
    invFun := fun x => {
      P := x.1, Q := x.2.1, LP := x.2.2.1, RP := x.2.2.2.1,
      LQ := x.2.2.2.2.1, RQ := x.2.2.2.2.2.1,
      dP := x.2.2.2.2.2.2.1, dQ := x.2.2.2.2.2.2.2 }
    left_inv := by intro C; cases C; rfl
    right_inv := by
      intro x
      rcases x with ⟨P, Q, LP, RP, LQ, RQ, dP, dQ⟩
      rfl }
  exact Encodable.ofEquiv _ e


/-- An exact rational-arithmetic test for a proposed pair of LDL factors.
The finite search may enumerate these data, but the acceptance proof still
needs a separate completeness theorem to establish termination. -/
def rationalLyapunovLDLAccepts {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι ℚ)
    (C : RationalLyapunovLDLData ι) : Bool :=
  decide ((∀ i, 0 < C.dP i) ∧ (∀ i, 0 < C.dQ i) ∧
    C.LP * C.RP = 1 ∧ C.LQ * C.RQ = 1 ∧
    C.P = C.LP * Matrix.diagonal C.dP * C.LP.transpose ∧
    C.Q = C.LQ * Matrix.diagonal C.dQ * C.LQ.transpose ∧
    A.transpose * C.P + C.P * A = -C.Q)

def rationalLyapunovLDLAccepts_sound {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℚ}
    (C : RationalLyapunovLDLData ι)
    (h : rationalLyapunovLDLAccepts A C = true) :
    RationalLyapunovLDLCertificate A := by
  simp only [rationalLyapunovLDLAccepts, decide_eq_true_eq] at h
  rcases h with ⟨hp, hq, hiP, hiQ, hfP, hfQ, hlyap⟩
  exact {
    P := C.P, Q := C.Q, LP := C.LP, RP := C.RP,
    LQ := C.LQ, RQ := C.RQ, dP := C.dP, dQ := C.dQ,
    positiveP := hp, positiveQ := hq,
    inverseP := hiP, inverseQ := hiQ,
    factorP := hfP, factorQ := hfQ, lyapunov := hlyap }

namespace RationalLyapunovLDLCertificate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℚ}

/-- The rational LDL fields become an exact real positive definite
certificate after the canonical embedding. -/
private theorem cast_posDef
    (P L R : Matrix ι ι ℚ) (d : ι → ℚ)
    (hd : ∀ i, 0 < d i) (hLR : L * R = 1)
    (hP : P = L * Matrix.diagonal d * L.transpose) :
    (P.map (algebraMap ℚ ℝ)).PosDef := by
  let f := algebraMap ℚ ℝ
  let DR : Matrix ι ι ℝ := Matrix.diagonal (fun i => (d i : ℝ))
  have hDR : DR.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    exact_mod_cast hd i
  have hLRreal : (L.map f) * (R.map f) = 1 := by
    calc
      (L.map f) * (R.map f) = (L * R).map f := by rw [Matrix.map_mul]
      _ = 1 := by rw [hLR]; simp
  have hPreal : P.map f = (L.map f) * DR * (L.map f).transpose := by
    have h := congrArg (fun M : Matrix ι ι ℚ => M.map f) hP
    simpa [DR, Matrix.map_mul, Matrix.transpose_map,
      Matrix.diagonal_map (map_zero f)] using h
  exact posDef_of_ldl_with_right_inverse
    (P.map f) (L.map f) DR (R.map f) hDR hLRreal hPreal

/-- Soundness of one accepted exact rational LDL test. This is the
mathematical half needed before any ordered parameter search can use it. -/
theorem isHurwitz (C : RationalLyapunovLDLCertificate A) :
    IsHurwitz (A.map (algebraMap ℚ ℝ)) := by
  let f := algebraMap ℚ ℝ
  have hP := cast_posDef C.P C.LP C.RP C.dP
    C.positiveP C.inverseP C.factorP
  have hQ := cast_posDef C.Q C.LQ C.RQ C.dQ
    C.positiveQ C.inverseQ C.factorQ
  have hLyap :
      (A.map f).transpose * (C.P.map f) +
        (C.P.map f) * (A.map f) = -(C.Q.map f) := by
    have h := congrArg (fun M : Matrix ι ι ℚ => M.map f) C.lyapunov
    simpa [Matrix.map_add, Matrix.map_mul, Matrix.map_neg,
      Matrix.transpose_map] using h
  exact hurwitz_of_posDef_lyapunov
    (A.map f) (C.P.map f) (C.Q.map f) hP hQ hLyap

end RationalLyapunovLDLCertificate

/-- A successful finite rational LDL test certifies the original real
Jacobian's strict Hurwitz spectrum. -/
theorem rationalLyapunovLDLAccepts_hurwitz {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (C : RationalLyapunovLDLData ι)
    (h : rationalLyapunovLDLAccepts A C = true) :
    IsHurwitz (A.map (algebraMap ℚ ℝ)) :=
  (rationalLyapunovLDLAccepts_sound C h).isHurwitz

end
end PhosphorylationStableCapacity
