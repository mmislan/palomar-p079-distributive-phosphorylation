module
public import proofs.PhosphorylationStableCapacity.FiniteRouthLDLSearchDefinition

public import proofs.PhosphorylationStableCapacity.RationalEulerLyapunovCertificate
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic

public import Mathlib.Logic.Encodable.Pi
public import Lean.Elab.Tactic.Omega

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

open Filter

/-- The paper's first exact-design loop, which doubles a rational `r`,
eventually exceeds every fixed geometric threshold. This is the cofinality
fact needed to move an eventual spectral theorem onto the actual loop. -/
theorem rational_doubling_exceeds (R : ℚ) :
    ∃ k : ℕ, R < (2 : ℚ)^k := by
  have hlim : Tendsto (fun k : ℕ => (2 : ℚ)^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  exact (hlim.eventually (eventually_gt_atTop R)).exists

/-- Each subsequent exact-design loop, which halves its rational parameter,
eventually enters every positive interval about zero. This does not alone
prove that the slow, coalesced, or full Jacobian passes its spectral test. -/
theorem rational_halving_below (η : ℚ) (hη : 0 < η) :
    ∃ k : ℕ, (1/2 : ℚ)^k < η := by
  exact exists_pow_lt_of_lt_one hη (by norm_num)

noncomputable section

private instance rationalLDLOptionCertificateDecidable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (candidate : Option (RationalLyapunovLDLData ι)) :
    Decidable (match candidate with
      | none => False
      | some C => rationalLyapunovLDLAccepts A C = true) := by
  cases candidate with
  | none => exact inferInstance
  | some C => exact inferInstance

/-- Stage `N` scans finitely many codes for exact rational Lyapunov LDL
data. Each decoded candidate is checked by `rationalLyapunovLDLAccepts`.
This is a complete semidecision for stable rational matrices, distinct from the
paper's more specific ordered parameter-loop policy. -/
def rationalLyapunovLDLSearchAccepts {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (N : ℕ) : Bool := by
  let : Encodable ι := Fintype.toEncodable ι
  let certificate : Fin N → Prop := fun code =>
    match Encodable.decode (α := RationalLyapunovLDLData ι) code.val with
    | none => False
    | some C => rationalLyapunovLDLAccepts A C = true
  letI : Decidable (∃ code : Fin N, certificate code) :=
    @Fintype.decidableExistsFintype (Fin N) certificate
      (fun code => rationalLDLOptionCertificateDecidable A
        (Encodable.decode (α := RationalLyapunovLDLData ι) code.val)) (Fin.fintype N)
  exact decide (∃ code : Fin N, certificate code)

/-- The completeness interface independent of the particular code order:
every rational Hurwitz matrix has finite rational data accepted by the exact
checker. -/
theorem isHurwitz_exists_rationalLyapunovLDLData {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℚ)
    (hA : IsHurwitz (A.map (algebraMap ℚ ℝ))) :
    ∃ D : RationalLyapunovLDLData ι,
      rationalLyapunovLDLAccepts A D = true := by
  obtain ⟨h, m, hcert⟩ :=
    isHurwitz_exists_rational_euler_power_certificate A hA
  let C := hcert.toLDLCertificate
  let D : RationalLyapunovLDLData ι := {
    P := C.P, Q := C.Q, LP := C.LP, RP := C.RP,
    LQ := C.LQ, RQ := C.RQ, dP := C.dP, dQ := C.dQ }
  refine ⟨D, ?_⟩
  simp only [rationalLyapunovLDLAccepts, decide_eq_true_eq]
  exact ⟨C.positiveP, C.positiveQ,
    C.inverseP, C.inverseQ, C.factorP, C.factorQ, C.lyapunov⟩

/-- A positive result from one finite stage is a genuine Hurwitz proof. -/
theorem rationalLyapunovLDLSearch_sound {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (N : ℕ)
    (h : rationalLyapunovLDLSearchAccepts A N = true) :
    IsHurwitz (A.map (algebraMap ℚ ℝ)) := by
  let : Encodable ι := Fintype.toEncodable ι
  unfold rationalLyapunovLDLSearchAccepts at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨code, hcode⟩ := h
  cases hdecode : Encodable.decode (α := RationalLyapunovLDLData ι) code.val with
  | none => simp only [hdecode] at hcode
  | some C =>
    simp only [hdecode] at hcode
    exact rationalLyapunovLDLAccepts_hurwitz A C hcode

/-- Every rational Hurwitz matrix supplies a finite accepted LDL stage:
Euler contraction gives rational P and Q, and the rational orthogonal-basis
theorem gives exact positive diagonal congruence factors for both. -/
theorem rationalLyapunovLDLSearch_eventually_accepts {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℚ)
    (hA : IsHurwitz (A.map (algebraMap ℚ ℝ))) :
    ∃ N : ℕ, rationalLyapunovLDLSearchAccepts A N = true := by
  let : Encodable ι := Fintype.toEncodable ι
  obtain ⟨D, hD⟩ := isHurwitz_exists_rationalLyapunovLDLData A hA
  let N := Encodable.encode D + 1
  refine ⟨N, ?_⟩
  unfold rationalLyapunovLDLSearchAccepts
  simp only [decide_eq_true_eq]
  refine ⟨⟨Encodable.encode D, by omega⟩, ?_⟩
  simpa only [Encodable.encodek] using hD

/-- A stable rational matrix's exact LDL scan has a first successful finite
stage, and every earlier finite stage has rejected. -/
theorem rationalLyapunovLDLSearch_first_acceptance {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℚ)
    (hA : IsHurwitz (A.map (algebraMap ℚ ℝ))) :
    ∃ N : ℕ, rationalLyapunovLDLSearchAccepts A N = true ∧
      ∀ K < N, rationalLyapunovLDLSearchAccepts A K = false := by
  have hex := rationalLyapunovLDLSearch_eventually_accepts A hA
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro K hK
  have hnot := Nat.find_min hex hK
  cases hval : rationalLyapunovLDLSearchAccepts A K with
  | false => rfl
  | true => exact False.elim (hnot hval)

/-- The same bounded rational scan can dovetail a countable sequence of
rational matrices. A stage checks only parameters and data codes below N. -/
def rationalLyapunovLDLFamilySearchAccepts {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A : ℕ → Matrix ι ι ℚ) (N : ℕ) : Bool := by
  let : Encodable ι := Fintype.toEncodable ι
  let certificate : Fin N → Fin N → Prop := fun parameter code =>
    match Encodable.decode (α := RationalLyapunovLDLData ι) code.val with
    | none => False
    | some C => rationalLyapunovLDLAccepts (A parameter.val) C = true
  let parameterDecidable (parameter : Fin N) :
      Decidable (∃ code : Fin N, certificate parameter code) :=
    @Fintype.decidableExistsFintype (Fin N) (certificate parameter)
      (fun code => rationalLDLOptionCertificateDecidable (A parameter.val)
        (Encodable.decode (α := RationalLyapunovLDLData ι) code.val)) (Fin.fintype N)
  letI : Decidable (∃ parameter : Fin N, ∃ code : Fin N, certificate parameter code) :=
    @Fintype.decidableExistsFintype (Fin N)
      (fun parameter => ∃ code : Fin N, certificate parameter code)
      parameterDecidable (Fin.fintype N)
  exact decide (∃ parameter : Fin N, ∃ code : Fin N, certificate parameter code)

/-- An accepted family stage identifies a tested stable parameter. -/
theorem rationalLyapunovLDLFamilySearch_sound {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A : ℕ → Matrix ι ι ℚ) (N : ℕ)
    (h : rationalLyapunovLDLFamilySearchAccepts A N = true) :
    ∃ k < N, IsHurwitz ((A k).map (algebraMap ℚ ℝ)) := by
  let : Encodable ι := Fintype.toEncodable ι
  unfold rationalLyapunovLDLFamilySearchAccepts at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨parameter, code, hcode⟩ := h
  cases hdecode : Encodable.decode (α := RationalLyapunovLDLData ι) code.val with
  | none => simp only [hdecode] at hcode
  | some C =>
    simp only [hdecode] at hcode
    exact ⟨parameter.val, parameter.isLt,
      rationalLyapunovLDLAccepts_hurwitz (A parameter.val) C hcode⟩

/-- If one member is Hurwitz, the dovetailed family scan accepts at
a first accepting stage with all earlier finite stages rejected. -/
theorem rationalLyapunovLDLFamilySearch_first_acceptance {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : ℕ → Matrix ι ι ℚ)
    (hA : ∃ k : ℕ, IsHurwitz ((A k).map (algebraMap ℚ ℝ))) :
    ∃ N : ℕ, rationalLyapunovLDLFamilySearchAccepts A N = true ∧
      (∀ K < N, rationalLyapunovLDLFamilySearchAccepts A K = false) ∧
      ∃ k < N, IsHurwitz ((A k).map (algebraMap ℚ ℝ)) := by
  let : Encodable ι := Fintype.toEncodable ι
  obtain ⟨k, hk⟩ := hA
  obtain ⟨D, hD⟩ := isHurwitz_exists_rationalLyapunovLDLData (A k) hk
  have hex : ∃ N : ℕ, rationalLyapunovLDLFamilySearchAccepts A N = true := by
    let N := k + Encodable.encode D + 1
    refine ⟨N, ?_⟩
    unfold rationalLyapunovLDLFamilySearchAccepts
    simp only [decide_eq_true_eq]
    refine ⟨⟨k, by omega⟩, ⟨Encodable.encode D, by omega⟩, ?_⟩
    simpa only [Encodable.encodek] using hD
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_, ?_⟩
  · intro K hK
    have hnot := Nat.find_min hex hK
    cases hval : rationalLyapunovLDLFamilySearchAccepts A K with
    | false => rfl
    | true => exact False.elim (hnot hval)
  · exact rationalLyapunovLDLFamilySearch_sound A (Nat.find hex)
      (Nat.find_spec hex)

end

end PhosphorylationStableCapacity
