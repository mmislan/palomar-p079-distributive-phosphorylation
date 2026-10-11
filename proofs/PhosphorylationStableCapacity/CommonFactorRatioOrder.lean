module
public import proofs.PhosphorylationStableCapacity.FactorReplacementRatioOrder

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial PhosphorylationSharpness

noncomputable section

theorem coeffRatioMono_cross {p q : ℝ[X]} {m i : ℕ}
    (hp : DensePositive p m) (hm : CoeffRatioMono p q m)
    (hi : i < m) :
    q.coeff i * p.coeff (i + 1) ≤
      q.coeff (i + 1) * p.coeff i := by
  exact (div_le_div_iff₀ (hp.1 i (by omega))
    (hp.1 (i + 1) (by omega))).mp (hm i hi)

/-- Multiplying both sides of a coefficient-ratio order by one common
positive linear factor preserves that order. -/
theorem commonFactor_coeffRatioMono {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m)
    (hm : CoeffRatioMono p q m)
    {r : ℝ} (hr : 0 < r) :
    CoeffRatioMono (positiveLinearStep r p)
      (positiveLinearStep r q) (m + 1) := by
  intro i hi
  have hd := positiveLinearStep_dense hp hr
  have hden0 := hd.1 i (by omega)
  have hden1 := hd.1 (i + 1) (by omega)
  cases i with
  | zero =>
      have hright : q.coeff 0 * p.coeff 1 ≤
          q.coeff 1 * p.coeff 0 := by
        by_cases hm0 : 0 < m
        · exact coeffRatioMono_cross hp hm hm0
        · rw [hp.2 1 (by omega), hq.2 1 (by omega)]
          norm_num
      have h := common_factor_ratio_mono r 0
        (p.coeff 0) (p.coeff 1) 0
        (q.coeff 0) (q.coeff 1) hr.le
        (by norm_num) (by norm_num) hright
        (by simpa [positiveLinearStep_coeff_zero] using hden0)
        (by simpa [positiveLinearStep_coeff_succ] using hden1)
      simpa [positiveLinearStep_coeff_zero,
        positiveLinearStep_coeff_succ] using h
  | succ j =>
      have hleft : q.coeff j * p.coeff (j + 1) ≤
          q.coeff (j + 1) * p.coeff j :=
        coeffRatioMono_cross hp hm (by omega)
      have hmiddle : q.coeff j * p.coeff (j + 2) ≤
          q.coeff (j + 2) * p.coeff j := by
        by_cases hinner : j + 1 < m
        · have htrans : q.coeff j / p.coeff j ≤
              q.coeff (j + 2) / p.coeff (j + 2) := by
            have h₁ := hm j (by omega)
            have h₂ := hm (j + 1) hinner
            simpa [Nat.add_assoc] using le_trans h₁ h₂
          exact (div_le_div_iff₀ (hp.1 j (by omega))
            (hp.1 (j + 2) (by omega))).mp htrans
        · rw [hp.2 (j + 2) (by omega), hq.2 (j + 2) (by omega)]
          norm_num
      have hright : q.coeff (j + 1) * p.coeff (j + 2) ≤
          q.coeff (j + 2) * p.coeff (j + 1) := by
        by_cases hinner : j + 1 < m
        · exact coeffRatioMono_cross hp hm hinner
        · rw [hp.2 (j + 2) (by omega), hq.2 (j + 2) (by omega)]
          norm_num
      have h := common_factor_ratio_mono r
        (p.coeff j) (p.coeff (j + 1)) (p.coeff (j + 2))
        (q.coeff j) (q.coeff (j + 1)) (q.coeff (j + 2))
        hr.le hleft hmiddle hright
        (by simpa [positiveLinearStep_coeff_succ] using hden0)
        (by simpa [positiveLinearStep_coeff_succ] using hden1)
      simpa [positiveLinearStep_coeff_succ, Nat.add_assoc] using h

end
end PhosphorylationStableCapacity
