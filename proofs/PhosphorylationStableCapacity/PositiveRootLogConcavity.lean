module
public import proofs.PhosphorylationStableCapacity.CoalescedSourceFactorization

@[expose] public section

namespace PhosphorylationStableCapacity

/-- Two adjacent positive log-concavity inequalities imply the two-step
cross inequality needed when one positive linear factor is added. -/
theorem positive_logconcave_two_step
    (a b c d : ℝ) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hleft : a * c ≤ b ^ 2) (hright : b * d ≤ c ^ 2) :
    a * d ≤ b * c := by
  have h₁ : a / b ≤ b / c :=
    (div_le_div_iff₀ hb hc).2 (by nlinarith [hleft])
  have h₂ : b / c ≤ c / d :=
    (div_le_div_iff₀ hc hd).2 (by nlinarith [hright])
  simpa only [mul_comm] using
    (div_le_div_iff₀ hb hd).1 (le_trans h₁ h₂)

/-- The coefficient-level algebra for multiplying a log-concave sequence
by a positive linear factor. The four assumptions correspond to the two
adjacent minors and their two-step consequence. -/
theorem positive_linear_step_logconcave
    (r aPrevPrev aPrev aNow aNext : ℝ) (hr : 0 ≤ r)
    (hprev : aPrevPrev * aNow ≤ aPrev ^ 2)
    (hnow : aPrev * aNext ≤ aNow ^ 2)
    (hcross : aPrevPrev * aNext ≤ aPrev * aNow) :
    (r * aPrev + aPrevPrev) * (r * aNext + aNow) ≤
      (r * aNow + aPrev) ^ 2 := by
  have h₁ : 0 ≤ r ^ 2 * (aNow ^ 2 - aPrev * aNext) :=
    mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hnow)
  have h₂ : 0 ≤ r * (aPrev * aNow - aPrevPrev * aNext) :=
    mul_nonneg hr (sub_nonneg.mpr hcross)
  have h₃ : 0 ≤ aPrev ^ 2 - aPrevPrev * aNow :=
    sub_nonneg.mpr hprev
  nlinarith [h₁, h₂, h₃]

end PhosphorylationStableCapacity
