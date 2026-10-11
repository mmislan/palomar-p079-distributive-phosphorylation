module
public import proofs.PhosphorylationStableCapacity.CoalescedSourceLogConcavity

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial PhosphorylationSharpness

noncomputable section

def CoeffStrictLogConcave (p : ℝ[X]) (m : ℕ) : Prop :=
  ∀ i : ℕ, 0 < i → i < m →
    p.coeff (i - 1) * p.coeff (i + 1) < p.coeff i ^ 2

theorem positive_linear_step_strict_of_prev
    (r aPrevPrev aPrev aNow aNext : ℝ) (hr : 0 ≤ r)
    (hprev : aPrevPrev * aNow < aPrev ^ 2)
    (hnow : aPrev * aNext ≤ aNow ^ 2)
    (hcross : aPrevPrev * aNext ≤ aPrev * aNow) :
    (r * aPrev + aPrevPrev) * (r * aNext + aNow) <
      (r * aNow + aPrev) ^ 2 := by
  have h₁ : 0 ≤ r ^ 2 * (aNow ^ 2 - aPrev * aNext) :=
    mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hnow)
  have h₂ : 0 ≤ r * (aPrev * aNow - aPrevPrev * aNext) :=
    mul_nonneg hr (sub_nonneg.mpr hcross)
  have h₃ : 0 < aPrev ^ 2 - aPrevPrev * aNow :=
    sub_pos.mpr hprev
  nlinarith [h₁, h₂, h₃]

theorem positiveLinearStep_strictLogConcave {p : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hlc : CoeffLogConcave p m)
    (hs : CoeffStrictLogConcave p m)
    {r : ℝ} (hr : 0 < r) :
    CoeffStrictLogConcave (positiveLinearStep r p) (m + 1) := by
  intro i hi0 him
  cases i with
  | zero => omega
  | succ k =>
    cases k with
    | zero =>
      have hm : 1 ≤ m := by omega
      have hnow : p.coeff 0 * p.coeff 2 ≤ p.coeff 1 ^ 2 := by
        by_cases hinner : 1 < m
        · exact hlc 1 (by omega) hinner
        · rw [hp.2 2 (by omega)]
          nlinarith
      have hcross : 0 * p.coeff 2 ≤ p.coeff 0 * p.coeff 1 := by
        simpa using mul_nonneg (le_of_lt (hp.1 0 (by omega)))
          (le_of_lt (hp.1 1 hm))
      have hfac := positive_linear_step_strict_of_prev r 0
        (p.coeff 0) (p.coeff 1) (p.coeff 2)
        hr.le (by nlinarith [hp.1 0 (by omega)]) hnow hcross
      change (positiveLinearStep r p).coeff 0 *
        (positiveLinearStep r p).coeff 2 <
          (positiveLinearStep r p).coeff 1 ^ 2
      rw [positiveLinearStep_coeff_zero,
        positiveLinearStep_coeff_succ r p 0,
        positiveLinearStep_coeff_succ r p 1]
      simpa using hfac
    | succ k =>
      have hindex : k + 2 ≤ m := by omega
      have hprev : p.coeff k * p.coeff (k + 2) <
          p.coeff (k + 1) ^ 2 := by
        simpa [Nat.add_assoc] using
          hs (k + 1) (by omega) (by omega)
      have hnow : p.coeff (k + 1) * p.coeff (k + 3) ≤
          p.coeff (k + 2) ^ 2 := by
        by_cases hinner : k + 2 < m
        · simpa [Nat.add_assoc] using
            hlc (k + 2) (by omega) hinner
        · rw [hp.2 (k + 3) (by omega)]
          nlinarith
      have hcross : p.coeff k * p.coeff (k + 3) ≤
          p.coeff (k + 1) * p.coeff (k + 2) := by
        by_cases hinner : k + 2 < m
        · exact positive_logconcave_two_step
            (p.coeff k) (p.coeff (k + 1))
            (p.coeff (k + 2)) (p.coeff (k + 3))
            (hp.1 (k + 1) (by omega))
            (hp.1 (k + 2) hindex)
            (hp.1 (k + 3) (by omega)) hprev.le hnow
        · rw [hp.2 (k + 3) (by omega)]
          simpa using mul_nonneg (hp.1 (k + 1) (by omega)).le
            (hp.1 (k + 2) hindex).le
      have hfac := positive_linear_step_strict_of_prev r
        (p.coeff k) (p.coeff (k + 1))
        (p.coeff (k + 2)) (p.coeff (k + 3))
        hr.le hprev hnow hcross
      change (positiveLinearStep r p).coeff (k + 1) *
        (positiveLinearStep r p).coeff (k + 3) <
          (positiveLinearStep r p).coeff (k + 2) ^ 2
      rw [show k + 3 = (k + 2) + 1 by omega,
        show k + 2 = (k + 1) + 1 by omega,
        positiveLinearStep_coeff_succ r p k,
        positiveLinearStep_coeff_succ r p (k + 1),
        positiveLinearStep_coeff_succ r p (k + 2)]
      simpa [Nat.add_assoc] using hfac

end
end PhosphorylationStableCapacity
