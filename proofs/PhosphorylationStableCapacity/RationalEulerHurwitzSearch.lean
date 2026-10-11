module
public import proofs.PhosphorylationStableCapacity.SchurFrobeniusPowerContract
public import proofs.PhosphorylationStableCapacity.DyadicEventuallySelection
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Data.Rat.Encodable

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

open Matrix WithLp
open scoped Matrix.Norms.Frobenius
open Filter
open scoped Topology

/-- A finite certificate involving only rational arithmetic. The Euler
power has squared Frobenius norm less than one. -/
def RationalEulerPowerCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (h : ℚ) (m : ℕ) : Prop :=
  0 < h ∧ 0 < m ∧
    (∑ i, ∑ j, ((((1 : Matrix ι ι ℚ) + h • A)^m) i j)^2) < 1

instance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (h : ℚ) (m : ℕ) :
    Decidable (RationalEulerPowerCertificate A h m) :=
  inferInstanceAs (Decidable (0 < h ∧ 0 < m ∧
    (∑ i, ∑ j, ((((1 : Matrix ι ι ℚ) + h • A)^m) i j)^2) < 1))

private instance rationalEulerOptionCertificateDecidable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (m : ℕ) (step : Option ℚ) :
    Decidable (match step with
      | none => False
      | some h => RationalEulerPowerCertificate A h m) := by
  cases step with
  | none => exact inferInstance
  | some h => exact inferInstance

/-- Stage N tests the finitely many decoded rational steps and powers
with codes below N. The predicate is decidable in rational arithmetic. -/
def rationalEulerSearchAccepts {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (N : ℕ) : Bool := by
  let certificate : Fin N → Fin N → Prop := fun code exponent =>
    match Encodable.decode (α := ℚ) code.val with
    | none => False
    | some h => RationalEulerPowerCertificate A h exponent.val
  let codeDecidable (code : Fin N) : Decidable (∃ exponent, certificate code exponent) :=
    @Fintype.decidableExistsFintype (Fin N) (certificate code)
      (fun exponent => rationalEulerOptionCertificateDecidable A exponent.val
        (Encodable.decode (α := ℚ) code.val)) (Fin.fintype N)
  letI : Decidable (∃ code, ∃ exponent, certificate code exponent) :=
    @Fintype.decidableExistsFintype (Fin N)
      (fun code => ∃ exponent, certificate code exponent) codeDecidable (Fin.fintype N)
  exact decide (∃ code, ∃ exponent, certificate code exponent)

/-- Dovetail parameter indices, rational step codes, and exponents.
Every stage performs finitely many rational tests. -/
def rationalEulerFamilySearchAccepts {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A : ℕ → Matrix ι ι ℚ) (N : ℕ) : Bool := by
  let certificate : Fin N → Fin N → Fin N → Prop := fun parameter code exponent =>
    match Encodable.decode (α := ℚ) code.val with
    | none => False
    | some h => RationalEulerPowerCertificate (A parameter.val) h exponent.val
  let codeDecidable (parameter code : Fin N) :
      Decidable (∃ exponent, certificate parameter code exponent) :=
    @Fintype.decidableExistsFintype (Fin N) (certificate parameter code)
      (fun exponent => rationalEulerOptionCertificateDecidable (A parameter.val) exponent.val
        (Encodable.decode (α := ℚ) code.val)) (Fin.fintype N)
  let parameterDecidable (parameter : Fin N) :
      Decidable (∃ code, ∃ exponent, certificate parameter code exponent) :=
    @Fintype.decidableExistsFintype (Fin N)
      (fun code => ∃ exponent, certificate parameter code exponent)
      (codeDecidable parameter) (Fin.fintype N)
  letI : Decidable (∃ parameter, ∃ code, ∃ exponent, certificate parameter code exponent) :=
    @Fintype.decidableExistsFintype (Fin N)
      (fun parameter => ∃ code, ∃ exponent, certificate parameter code exponent)
      parameterDecidable (Fin.fintype N)
  exact decide (∃ parameter, ∃ code, ∃ exponent, certificate parameter code exponent)

noncomputable section

private theorem real_frobenius_norm_sq {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℝ) :
    ‖B‖^2 = ∑ i, ∑ j, (B i j)^2 := by
  have hnonneg : 0 ≤ ∑ i, ∑ j, (B i j)^2 :=
    Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hnorm : ‖B‖ = Real.sqrt (∑ i, ∑ j, (B i j)^2) := by
    rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp [Real.norm_eq_abs]
  rw [hnorm]
  exact Real.sq_sqrt hnonneg

private theorem rational_euler_power_cast {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (h : ℚ) (m : ℕ) :
    (((1 : Matrix ι ι ℚ) + h • A)^m).map (algebraMap ℚ ℝ) =
      ((1 : Matrix ι ι ℝ) + (h : ℝ) • A.map (algebraMap ℚ ℝ))^m := by
  rw [Matrix.map_pow]
  congr 1
  ext i j
  by_cases hij : i = j <;>
    simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, hij]

/-- Every rational Hurwitz matrix has a finite rational Euler certificate.
This is certificate completeness, not merely certificate soundness. -/
theorem isHurwitz_exists_rational_euler_power_certificate
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℚ)
    (hA : IsHurwitz (A.map (algebraMap ℚ ℝ))) :
    ∃ h : ℚ, ∃ m : ℕ, RationalEulerPowerCertificate A h m := by
  let AR := A.map (algebraMap ℚ ℝ)
  obtain ⟨h₀, hh₀, m, hm, hcontract⟩ :=
    isHurwitz_exists_real_frobenius_contracting_power AR hA
  have hcont : Continuous (fun h : ℝ =>
      ‖((1 : Matrix ι ι ℝ) + h • AR)^m‖) := by
    fun_prop
  let U : Set ℝ := {h | 0 < h ∧
    ‖((1 : Matrix ι ι ℝ) + h • AR)^m‖ < 1}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_id).inter
      (isOpen_lt hcont continuous_const)
  obtain ⟨h, hh, hnorm⟩ :=
    Rat.denseRange_cast.exists_mem_open hU ⟨h₀, hh₀, hcontract⟩
  have hhQ : (0 : ℚ) < h := by exact_mod_cast hh
  have hsquared :
      ∑ i, ∑ j,
        ((((1 : Matrix ι ι ℝ) + (h : ℝ) • AR)^m) i j)^2 < 1 := by
    rw [← real_frobenius_norm_sq]
    nlinarith [norm_nonneg (((1 : Matrix ι ι ℝ) + (h : ℝ) • AR)^m)]
  have hcast := rational_euler_power_cast A h m
  change ∑ i, ∑ j,
    ((((1 : Matrix ι ι ℝ) + (h : ℝ) •
      A.map (algebraMap ℚ ℝ))^m) i j)^2 < 1 at hsquared
  rw [← hcast] at hsquared
  change ∑ i, ∑ j,
    (((((1 : Matrix ι ι ℚ) + h • A)^m) i j : ℚ) : ℝ)^2 < 1 at hsquared
  refine ⟨h, m, hhQ, hm, ?_⟩
  exact_mod_cast hsquared

private theorem complex_frobenius_mulVec_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (v : ι → ℂ) :
    ‖toLp 2 (B *ᵥ v)‖ ≤ ‖B‖ * ‖toLp 2 v‖ := by
  calc
    ‖toLp 2 (B *ᵥ v)‖ = ‖Matrix.replicateCol Unit (B *ᵥ v)‖ := by simp
    _ = ‖B * Matrix.replicateCol Unit v‖ := by
      rw [Matrix.replicateCol_mulVec]
    _ ≤ ‖B‖ * ‖Matrix.replicateCol Unit v‖ :=
      Matrix.frobenius_norm_mul B _
    _ = ‖B‖ * ‖toLp 2 v‖ := by simp

/-- A contracting positive Euler power excludes every nonnegative real
part in the original spectrum. No numerical eigenvalue calculation is used. -/
theorem isHurwitz_of_real_euler_frobenius_power
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (h : ℝ) (m : ℕ)
    (hh : 0 < h) (_hm : 0 < m)
    (hcontract : ‖((1 : Matrix ι ι ℝ) + h • A)^m‖ < 1) :
    IsHurwitz A := by
  intro z hz
  let AC := A.map (algebraMap ℝ ℂ)
  have heig : Module.End.HasEigenvalue (Matrix.toLin' AC) z := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
    exact hz
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  have hev : AC *ᵥ v = z • v := hv.apply_eq_smul
  let BR : Matrix ι ι ℝ := 1 + h • A
  let BC := BR.map (algebraMap ℝ ℂ)
  let w : ℂ := 1 + (h : ℂ) * z
  have hstep : BC = 1 + (h : ℂ) • AC := by
    ext i j
    by_cases hij : i = j <;>
      simp [BC, BR, AC, Matrix.map_apply, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, hij]
  have hvstep : BC *ᵥ v = w • v := by
    rw [hstep, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, hev]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w]
    ring
  have hvpower (k : ℕ) : BC^k *ᵥ v = w^k • v := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hvstep,
        Matrix.mulVec_smul, ih, smul_smul, pow_succ]
      rw [mul_comm w]
  have hnorm : ‖BC^m‖ = ‖BR^m‖ := by
    rw [← Matrix.map_pow]
    exact Matrix.frobenius_norm_map_eq (BR^m)
      (algebraMap ℝ ℂ) (fun a => Complex.norm_real a)
  have hvnorm : 0 < ‖toLp 2 v‖ := by
    apply norm_pos_iff.mpr
    simpa using hv.2
  have hbound := complex_frobenius_mulVec_bound (BC^m) v
  rw [hvpower, toLp_smul, norm_smul, norm_pow] at hbound
  have hwpow : ‖w‖^m < 1 :=
    lt_of_le_of_lt (le_of_mul_le_mul_right hbound hvnorm)
      (by rw [hnorm]; exact hcontract)
  have hw : ‖w‖ < 1 := by
    by_contra hnot
    have hbase : 1 ≤ ‖w‖ := le_of_not_gt hnot
    have hp : 1 ≤ ‖w‖^m := one_le_pow₀ hbase
    linarith
  have hsq : Complex.normSq w < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  have hformula : Complex.normSq w =
      1 + 2*h*z.re + h^2*Complex.normSq z := by
    simp [w, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im]
    ring
  rw [hformula] at hsq
  have hnonneg : 0 ≤ h^2 * Complex.normSq z :=
    mul_nonneg (sq_nonneg h) (Complex.normSq_nonneg z)
  by_contra hnot
  have hre : 0 ≤ z.re := le_of_not_gt hnot
  have hprod : 0 ≤ 2*h*z.re := mul_nonneg (by positivity) hre
  linarith

/-- The rational finite certificate is a sound literal Hurwitz test. -/
theorem RationalEulerPowerCertificate.isHurwitz
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℚ} {h : ℚ} {m : ℕ}
    (hcert : RationalEulerPowerCertificate A h m) :
    IsHurwitz (A.map (algebraMap ℚ ℝ)) := by
  obtain ⟨hh, hm, hsum⟩ := hcert
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hsumR :
      ∑ i, ∑ j,
        (((((1 : Matrix ι ι ℚ) + h • A)^m) i j : ℚ) : ℝ)^2 < 1 := by
    exact_mod_cast hsum
  have hcast := rational_euler_power_cast A h m
  have hnormsq :
      ‖((1 : Matrix ι ι ℝ) + (h : ℝ) • A.map (algebraMap ℚ ℝ))^m‖^2 < 1 := by
    rw [real_frobenius_norm_sq, ← hcast]
    change ∑ i, ∑ j,
      (((((1 : Matrix ι ι ℚ) + h • A)^m) i j : ℚ) : ℝ)^2 < 1
    exact hsumR
  apply isHurwitz_of_real_euler_frobenius_power _ (h : ℝ) m hhR hm
  exact (sq_lt_sq₀ (norm_nonneg _) (by norm_num)).mp
    (by simpa using hnormsq)

/-- Every stable rational matrix is accepted after finitely many finite
search stages. The search enumerates certificates, not floating roots. -/
theorem rationalEulerSearch_eventually_accepts
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℚ)
    (hA : IsHurwitz (A.map (algebraMap ℚ ℝ))) :
    ∃ N : ℕ, rationalEulerSearchAccepts A N = true := by
  obtain ⟨h, m, hcert⟩ :=
    isHurwitz_exists_rational_euler_power_certificate A hA
  let N := Encodable.encode h + m + 1
  refine ⟨N, ?_⟩
  simp only [rationalEulerSearchAccepts, decide_eq_true_eq]
  refine ⟨⟨Encodable.encode h, by omega⟩, ⟨m, by omega⟩, ?_⟩
  simpa only [Encodable.encodek] using hcert

/-- Every accepted finite stage is spectrally sound. -/
theorem rationalEulerSearch_sound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (N : ℕ)
    (haccept : rationalEulerSearchAccepts A N = true) :
    IsHurwitz (A.map (algebraMap ℚ ℝ)) := by
  simp only [rationalEulerSearchAccepts, decide_eq_true_eq] at haccept
  obtain ⟨code, exponent, hcert⟩ := haccept
  cases hdecode : Encodable.decode (α := ℚ) code.val with
  | none => simp only [hdecode] at hcert
  | some h =>
    simp only [hdecode] at hcert
    exact hcert.isHurwitz

/-- A first accepted finite bound exists, with every earlier bound rejected.
This supplies structural termination for the explicit finite enumeration. -/
theorem rationalEulerSearch_first_acceptance
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℚ)
    (hA : IsHurwitz (A.map (algebraMap ℚ ℝ))) :
    ∃ N : ℕ, rationalEulerSearchAccepts A N = true ∧
      ∀ K < N, rationalEulerSearchAccepts A K = false := by
  have hex := rationalEulerSearch_eventually_accepts A hA
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro K hK
  have hnot := Nat.find_min hex hK
  cases hval : rationalEulerSearchAccepts A K with
  | false => rfl
  | true => exact False.elim (hnot hval)

/-- One stable member suffices for termination of the explicit dovetailed
family search. Each previous stage has genuinely finished and rejected. -/
theorem rationalEulerFamilySearch_first_acceptance
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : ℕ → Matrix ι ι ℚ)
    (hA : ∃ k : ℕ, IsHurwitz ((A k).map (algebraMap ℚ ℝ))) :
    ∃ N : ℕ, rationalEulerFamilySearchAccepts A N = true ∧
      (∀ K < N, rationalEulerFamilySearchAccepts A K = false) ∧
      ∃ k < N, IsHurwitz ((A k).map (algebraMap ℚ ℝ)) := by
  obtain ⟨k, hk⟩ := hA
  obtain ⟨h, m, hcert⟩ :=
    isHurwitz_exists_rational_euler_power_certificate (A k) hk
  have hex : ∃ N : ℕ, rationalEulerFamilySearchAccepts A N = true := by
    let N := k + Encodable.encode h + m + 1
    refine ⟨N, ?_⟩
    simp only [rationalEulerFamilySearchAccepts, decide_eq_true_eq]
    refine ⟨⟨k, by omega⟩, ⟨Encodable.encode h, by omega⟩,
      ⟨m, by omega⟩, ?_⟩
    simpa only [Encodable.encodek] using hcert
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_, ?_⟩
  · intro K hK
    have hnot := Nat.find_min hex hK
    cases hval : rationalEulerFamilySearchAccepts A K with
    | false => rfl
    | true => exact False.elim (hnot hval)
  · have hwitness (N : ℕ) (haccept : rationalEulerFamilySearchAccepts A N = true) :
        ∃ parameter : Fin N, ∃ code : Fin N, ∃ exponent : Fin N,
          match Encodable.decode (α := ℚ) code.val with
          | none => False
          | some h => RationalEulerPowerCertificate (A parameter.val) h exponent.val := by
      simp only [rationalEulerFamilySearchAccepts, decide_eq_true_eq] at haccept
      obtain ⟨parameter, code, exponent, hcert⟩ := haccept
      refine ⟨parameter, code, exponent, ?_⟩
      cases hdecode : Encodable.decode (α := ℚ) code.val with
      | none => simp only [hdecode] at hcert
      | some h => simpa only [hdecode] using hcert
    obtain ⟨parameter, code, exponent, hcert⟩ :=
      hwitness (Nat.find hex) (Nat.find_spec hex)
    refine ⟨parameter.val, parameter.isLt, ?_⟩
    cases hdecode : Encodable.decode (α := ℚ) code.val with
    | none => simp only [hdecode] at hcert
    | some h =>
      simp only [hdecode] at hcert
      exact hcert.isHurwitz

/-- Eventual stability of a literal rational dyadic family gives a first
accepted finite certificate stage for that same family. The cast identity
keeps the tested rational matrices tied to the actual real Jacobians. -/
theorem rationalEulerDyadicFamilySearch_first_acceptance
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (AR : ℝ → Matrix ι ι ℝ) (AQ : ℚ → Matrix ι ι ℚ)
    (hcast : ∀ d : ℕ,
      (AQ ((1/2 : ℚ)^d)).map (algebraMap ℚ ℝ) = AR ((1/2 : ℝ)^d))
    (hstable : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), IsHurwitz (AR δ)) :
    ∃ N : ℕ,
      rationalEulerFamilySearchAccepts (fun d => AQ ((1/2 : ℚ)^d)) N = true ∧
      (∀ K < N,
        rationalEulerFamilySearchAccepts (fun d => AQ ((1/2 : ℚ)^d)) K = false) ∧
      ∃ d < N, IsHurwitz (AR ((1/2 : ℝ)^d)) := by
  obtain ⟨d, hd⟩ := eventually_right_has_halving_index _ hstable
  have hex : ∃ d : ℕ,
      IsHurwitz ((AQ ((1/2 : ℚ)^d)).map (algebraMap ℚ ℝ)) :=
    ⟨d, by rw [hcast]; exact hd⟩
  obtain ⟨N, hN, hfirst, d, hdN, hcert⟩ :=
    rationalEulerFamilySearch_first_acceptance
      (fun d => AQ ((1/2 : ℚ)^d)) hex
  exact ⟨N, hN, hfirst, d, hdN, by simpa only [hcast] using hcert⟩

end
end PhosphorylationStableCapacity
