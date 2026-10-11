module
public import proofs.PhosphorylationStableCapacity.PositiveLinearFactorStep

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial PhosphorylationSharpness

noncomputable section

def CoeffLogConcave (p : ℝ[X]) (m : ℕ) : Prop :=
  ∀ i : ℕ, 0 < i → i < m →
    p.coeff (i - 1) * p.coeff (i + 1) ≤ p.coeff i ^ 2

/-- Multiplication by a positive linear factor preserves adjacent
coefficient log-concavity for a densely positive finite polynomial. -/
theorem positiveLinearStep_logconcave {p : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hlc : CoeffLogConcave p m)
    {r : ℝ} (hr : 0 < r) :
    CoeffLogConcave (positiveLinearStep r p) (m + 1) := by
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
      have hfac := positive_linear_step_logconcave r 0
        (p.coeff 0) (p.coeff 1) (p.coeff 2)
        hr.le (by nlinarith) hnow hcross
      change (positiveLinearStep r p).coeff 0 *
        (positiveLinearStep r p).coeff 2 ≤
          (positiveLinearStep r p).coeff 1 ^ 2
      rw [positiveLinearStep_coeff_zero,
        positiveLinearStep_coeff_succ r p 0,
        positiveLinearStep_coeff_succ r p 1]
      simpa using hfac
    | succ k =>
      have hindex : k + 2 ≤ m := by omega
      have hprev : p.coeff k * p.coeff (k + 2) ≤
          p.coeff (k + 1) ^ 2 := by
        simpa [Nat.add_assoc] using
          hlc (k + 1) (by omega) (by omega)
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
            (hp.1 (k + 3) (by omega)) hprev hnow
        · rw [hp.2 (k + 3) (by omega)]
          simpa using mul_nonneg (hp.1 (k + 1) (by omega)).le
            (hp.1 (k + 2) hindex).le
      have hfac := positive_linear_step_logconcave r
        (p.coeff k) (p.coeff (k + 1))
        (p.coeff (k + 2)) (p.coeff (k + 3))
        hr.le hprev hnow hcross
      change (positiveLinearStep r p).coeff (k + 1) *
        (positiveLinearStep r p).coeff (k + 3) ≤
          (positiveLinearStep r p).coeff (k + 2) ^ 2
      rw [show k + 3 = (k + 2) + 1 by omega,
        show k + 2 = (k + 1) + 1 by omega,
        positiveLinearStep_coeff_succ r p k,
        positiveLinearStep_coeff_succ r p (k + 1),
        positiveLinearStep_coeff_succ r p (k + 2)]
      simpa [Nat.add_assoc] using hfac

end
end PhosphorylationStableCapacity
