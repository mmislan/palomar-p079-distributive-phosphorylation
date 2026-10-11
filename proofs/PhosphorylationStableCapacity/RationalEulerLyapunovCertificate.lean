module
public import proofs.PhosphorylationStableCapacity.RationalEulerHurwitzSearch
public import proofs.PhosphorylationStableCapacity.FiniteRouthLDLSearchDefinition

public import proofs.PhosphorylationStableCapacity.RationalFrobeniusGramPosDef

public import proofs.PhosphorylationStableCapacity.RationalPosDefCongruence
public import Mathlib.Tactic.NoncommRing
public import Lean.Elab.Tactic.Omega

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

/-- The exact rational Euler step used to construct a continuous-time
Lyapunov matrix. -/
def rationalEulerStep {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (h : ℚ) : Matrix ι ι ℚ := 1 + h • A

/-- A finite rational Gram matrix. The `k=0` summand is exactly the
identity, so it is positive definite whenever `m>0`. -/
def rationalEulerGram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℚ) (m : ℕ) : Matrix ι ι ℚ :=
  ∑ k ∈ Finset.range m, (T^k).transpose * T^k

/-- The finite Gram matrix is positive definite over the rationals: its
first summand is `I`, and each remaining summand is a Gram square. -/
theorem rationalEulerGram_posDef {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℚ) (m : ℕ) (hm : 0 < m) :
    (rationalEulerGram T m).PosDef := by
  cases m with
  | zero => omega
  | succ k =>
    unfold rationalEulerGram
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Matrix.transpose_one, Matrix.one_mul]
    rw [add_comm _ (1 : Matrix ι ι ℚ)]
    apply Matrix.PosDef.add_posSemidef Matrix.PosDef.one
    apply Matrix.posSemidef_sum
    intro i hi
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self (T^(i+1))

private theorem rationalEulerGram_cast {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℚ) (m : ℕ) :
    (rationalEulerGram T m).map (algebraMap ℚ ℝ) =
      ∑ k ∈ Finset.range m,
        ((T.map (algebraMap ℚ ℝ))^k).transpose *
          (T.map (algebraMap ℚ ℝ))^k := by
  change ((algebraMap ℚ ℝ).mapMatrix : Matrix ι ι ℚ →+* Matrix ι ι ℝ)
      (∑ k ∈ Finset.range m, (T^k).transpose * T^k) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change ((T^k).transpose * T^k).map (algebraMap ℚ ℝ) = _
  rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_pow]

/-- The same finite rational Gram certificate remains strictly positive
as a real matrix, which is the input of the real Lyapunov converse. -/
theorem rationalEulerGram_cast_posDef {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℚ) (m : ℕ) (hm : 0 < m) :
    ((rationalEulerGram T m).map (algebraMap ℚ ℝ)).PosDef := by
  rw [rationalEulerGram_cast]
  cases m with
  | zero => omega
  | succ k =>
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Matrix.transpose_one, Matrix.one_mul]
    rw [add_comm _ (1 : Matrix ι ι ℝ)]
    apply Matrix.PosDef.add_posSemidef Matrix.PosDef.one
    apply Matrix.posSemidef_sum
    intro i hi
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self
        ((T.map (algebraMap ℚ ℝ))^(i+1))

private theorem rationalEulerGram_succ {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℚ) (m : ℕ) :
    rationalEulerGram T (m+1) =
      rationalEulerGram T m + (T^m).transpose * T^m := by
  simp only [rationalEulerGram, Finset.sum_range_succ]

private theorem rationalEulerGram_term_succ {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℚ) (m : ℕ) :
    T.transpose * ((T^m).transpose * T^m) * T =
      (T^(m+1)).transpose * T^(m+1) := by
  rw [pow_succ, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- Finite telescoping; no matrix inverse or infinite sum is needed.
This is the algebraic bridge from a rational Euler contraction to a
rational continuous-time Lyapunov equation. -/
theorem rationalEulerGram_telescope {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℚ) (m : ℕ) :
    T.transpose * rationalEulerGram T m * T - rationalEulerGram T m =
      (T^m).transpose * T^m - 1 := by
  induction m with
  | zero => simp [rationalEulerGram]
  | succ m ih =>
    rw [rationalEulerGram_succ]
    calc
      T.transpose * (rationalEulerGram T m + (T^m).transpose * T^m) * T -
          (rationalEulerGram T m + (T^m).transpose * T^m) =
        (T.transpose * rationalEulerGram T m * T - rationalEulerGram T m) +
          (T.transpose * ((T^m).transpose * T^m) * T -
            (T^m).transpose * T^m) := by
              simp only [Matrix.mul_add, Matrix.add_mul]
              abel
      _ = ((T^m).transpose * T^m - 1) +
          ((T^(m+1)).transpose * T^(m+1) - (T^m).transpose * T^m) := by
            rw [ih, rationalEulerGram_term_succ]
      _ = (T^(m+1)).transpose * T^(m+1) - 1 := by abel

/-- Explicit rational Lyapunov candidate for the original rational
matrix `A`, derived from one finite Euler certificate. -/
def rationalEulerLyapunovP {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (h : ℚ) (m : ℕ) : Matrix ι ι ℚ :=
  rationalEulerGram (rationalEulerStep A h) m

def rationalEulerLyapunovQ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (h : ℚ) (m : ℕ) : Matrix ι ι ℚ :=
  -(A.transpose * rationalEulerLyapunovP A h m +
    rationalEulerLyapunovP A h m * A)

theorem rationalEulerLyapunov_equation {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (h : ℚ) (m : ℕ) :
    A.transpose * rationalEulerLyapunovP A h m +
      rationalEulerLyapunovP A h m * A =
        -rationalEulerLyapunovQ A h m := by
  simp only [rationalEulerLyapunovQ, neg_neg]

/-- The exact rational loss identity behind the finite Gram construction.
For a contracting Euler power, `I - (T^m)ᵀ(T^m)` is strictly positive;
the final summand is positive semidefinite. -/
theorem rationalEulerLyapunov_loss_identity {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (h : ℚ) (m : ℕ) :
    h • rationalEulerLyapunovQ A h m =
      1 - ((rationalEulerStep A h)^m).transpose *
        (rationalEulerStep A h)^m +
      (h^2) • (A.transpose * rationalEulerLyapunovP A h m * A) := by
  let T := rationalEulerStep A h
  let P := rationalEulerLyapunovP A h m
  have htel : T.transpose * P * T - P =
      (T^m).transpose * T^m - 1 :=
    rationalEulerGram_telescope T m
  have hexpand : T.transpose * P * T - P =
      h • (A.transpose * P + P * A) +
        (h^2) • (A.transpose * P * A) := by
    simp only [T, rationalEulerStep, Matrix.transpose_add,
      Matrix.transpose_one, Matrix.transpose_smul,
      Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
    noncomm_ring
  rw [hexpand] at htel
  change h • (-(A.transpose * P + P * A)) =
    1 - (T^m).transpose * T^m +
      (h^2) • (A.transpose * P * A)
  rw [smul_neg]
  rw [eq_sub_of_add_eq htel]
  abel

/-- The finite rational Frobenius certificate gives a strictly positive
continuous-time Lyapunov loss over `ℚ`.  In particular, this construction
does not rely on finding a rational approximation to a real Lyapunov
solution. -/
theorem rationalEulerLyapunovQ_posDef {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (h : ℚ) (m : ℕ)
    (hcert : RationalEulerPowerCertificate A h m) :
    (rationalEulerLyapunovQ A h m).PosDef := by
  obtain ⟨hh, hm, hcontract⟩ := hcert
  let T := rationalEulerStep A h
  let P := rationalEulerLyapunovP A h m
  let Q := rationalEulerLyapunovQ A h m
  have hP : P.PosDef := rationalEulerGram_posDef T m hm
  have hbase : (1 - (T^m).transpose * T^m).PosDef := by
    exact rational_one_sub_gram_posDef (T^m) hcontract
  have hgram : (A.transpose * P * A).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hP.posSemidef.conjTranspose_mul_mul_same A
  have hscaled : (h • Q).PosDef := by
    rw [show h • Q = 1 - (T^m).transpose * T^m +
        (h^2) • (A.transpose * P * A) from
      rationalEulerLyapunov_loss_identity A h m]
    exact hbase.add_posSemidef (hgram.smul (sq_nonneg h))
  have hinv : 0 < h⁻¹ := inv_pos.mpr hh
  have hback := hscaled.smul hinv
  have hid : h⁻¹ • (h • Q) = Q := by
    rw [smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
  rw [hid] at hback
  exact hback

/-- A finite rational Euler power certificate can be converted to the
exact rational positive diagonal congruence data checked by the P079 LDL
alternative. Both the Lyapunov matrix and its loss use the same `A,h,m`. -/
noncomputable def RationalEulerPowerCertificate.toLDLCertificate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℚ} {h : ℚ} {m : ℕ}
    (hcert : RationalEulerPowerCertificate A h m) :
    RationalLyapunovLDLCertificate A := by
  have hP : (rationalEulerLyapunovP A h m).PosDef :=
    rationalEulerGram_posDef (rationalEulerStep A h) m hcert.2.1
  have hQ : (rationalEulerLyapunovQ A h m).PosDef :=
    rationalEulerLyapunovQ_posDef A h m hcert
  let factorP := rational_posDef_has_congruence_factor
    (rationalEulerLyapunovP A h m) hP
  let LP := Classical.choose factorP
  let RP := Classical.choose (Classical.choose_spec factorP)
  let dP := Classical.choose (Classical.choose_spec (Classical.choose_spec factorP))
  have hPdata := Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec factorP))
  let factorQ := rational_posDef_has_congruence_factor
    (rationalEulerLyapunovQ A h m) hQ
  let LQ := Classical.choose factorQ
  let RQ := Classical.choose (Classical.choose_spec factorQ)
  let dQ := Classical.choose (Classical.choose_spec (Classical.choose_spec factorQ))
  have hQdata := Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec factorQ))
  exact {
    P := rationalEulerLyapunovP A h m
    Q := rationalEulerLyapunovQ A h m
    LP := LP, RP := RP, LQ := LQ, RQ := RQ
    dP := dP, dQ := dQ
    positiveP := hPdata.1, positiveQ := hQdata.1
    inverseP := hPdata.2.1, inverseQ := hQdata.2.1
    factorP := hPdata.2.2, factorQ := hQdata.2.2
    lyapunov := rationalEulerLyapunov_equation A h m }

end
end PhosphorylationStableCapacity
