module
public import proofs.PhosphorylationStableCapacity.SplitFirstOrderQuotient

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial

/-- The exact characteristic-polynomial constant term and first-order
    numerator/denominator bounds give the paper's multiplicative `O(δ)`
    error for a simple slow root. The network proof supplies `c`, while
    `constantTermSecant` carries the transverse characteristic factor. -/
theorem quantitative_slow_root_of_factored_constant_term
    (P : ℝ → ℝ[X]) (c : ℝ → ℝ)
    (N : ℕ) (gap c₀ p₁ A B δ lam : ℝ)
    (hc₀ : 0 < c₀) (hp₁ : 0 < p₁)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hδ : δ ≠ 0) (hgap : gap ≠ 0)
    (hconst : (P δ).eval 0 = c δ * δ^N * gap)
    (hroot : (P δ).IsRoot lam)
    (hsecant : p₁ / 2 ≤ (constantTermSecant (P δ)).eval lam)
    (hc : |c δ - c₀| ≤ A * |δ|)
    (hq : |(constantTermSecant (P δ)).eval lam - p₁| ≤ B * |δ|) :
    |lam / (-(c₀/p₁) * δ^N * gap) - 1| ≤
      ((A * p₁ + |c₀| * B) / (p₁^2/2)) /
        (c₀/p₁) * |δ| := by
  let q := (constantTermSecant (P δ)).eval lam
  let a := c₀ / p₁
  have hapos : 0 < a := div_pos hc₀ hp₁
  have hqpos : 0 < q := by dsimp [q] at *; linarith
  have hratio : lam / (-(c₀/p₁) * δ^N * gap) =
      (c δ / q) / (c₀/p₁) := by
    have hid := constantTermSecant_eval_identity (P δ) lam
    rw [hconst, hroot.eq_zero] at hid
    dsimp [q, a] at *
    field_simp [hδ, hgap, ne_of_gt hp₁, ne_of_gt hqpos, ne_of_gt hapos]
    nlinarith
  have hbound := first_order_quotient_bound
    (c δ) q c₀ p₁ A B |δ| hp₁ hsecant hA hB (abs_nonneg δ)
    hc hq
  rw [hratio]
  have hnorm : |(c δ / q) / a - 1| = |c δ / q - a| / a := by
    have hident : (c δ / q) / a - 1 = (c δ / q - a) / a := by
      field_simp [ne_of_gt hapos]
    rw [hident, abs_div, abs_of_pos hapos]
  rw [hnorm]
  calc
    |c δ / q - a| / a ≤
        ((A * p₁ + |c₀| * B) * |δ| / (p₁^2/2)) / a := by
          dsimp [a]
          exact div_le_div_of_nonneg_right hbound hapos.le
    _ = ((A * p₁ + |c₀| * B) / (p₁^2/2)) / a * |δ| := by ring

end
end PhosphorylationStableCapacity
