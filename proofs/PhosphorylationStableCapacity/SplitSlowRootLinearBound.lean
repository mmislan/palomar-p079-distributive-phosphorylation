module
public import proofs.PhosphorylationStableCapacity.SplitFirstOrderBound

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial

/-- A nonvanishing secant quotient converts the exact constant-term
    factorization into a linear bound on the slow eigenvalue. For the
    manuscript exponent `N=2n−2≥1`, `|δ|^N≤|δ|` near zero. -/
theorem slow_root_linear_bound_of_factored_constant_term
    (P : ℝ → ℝ[X]) (c : ℝ → ℝ)
    (N : ℕ) (gap cmax p₁ δ lam : ℝ)
    (hcmax : 0 ≤ cmax) (hp₁ : 0 < p₁)
    (hconst : (P δ).eval 0 = c δ * δ^N * gap)
    (hroot : (P δ).IsRoot lam)
    (hsecant : p₁ / 2 ≤ (constantTermSecant (P δ)).eval lam)
    (hc : |c δ| ≤ cmax)
    (hpow : |δ|^N ≤ |δ|) :
    |lam| ≤ (2*cmax*|gap|/p₁) * |δ| := by
  let q := (constantTermSecant (P δ)).eval lam
  have hqpos : 0 < q := by dsimp [q] at *; linarith
  have hid : lam * q = -(c δ * δ^N * gap) := by
    have heq := constantTermSecant_eval_identity (P δ) lam
    rw [hconst, hroot.eq_zero] at heq
    dsimp [q]
    linarith
  have habs : |lam| * q = |c δ| * |δ|^N * |gap| := by
    calc
      |lam| * q = |lam * q| := by rw [abs_mul, abs_of_pos hqpos]
      _ = |-(c δ * δ^N * gap)| := congrArg abs hid
      _ = |c δ| * |δ|^N * |gap| := by
        rw [abs_neg, abs_mul, abs_mul, abs_pow]
  have hnum : |c δ| * |δ|^N * |gap| ≤
      cmax * |δ| * |gap| := by
    calc
      |c δ| * |δ|^N * |gap| ≤
          cmax * |δ|^N * |gap| := by gcongr
      _ ≤ cmax * |δ| * |gap| := by gcongr
  have hmul : |lam| * (p₁/2) ≤ cmax * |δ| * |gap| := by
    have hleft : |lam| * (p₁/2) ≤ |lam| * q := by gcongr
    exact hleft.trans (habs.le.trans hnum)
  have hmain : |lam| * p₁ ≤ 2*cmax*|gap| * |δ| := by
    nlinarith [hmul]
  calc
    |lam| ≤ (2*cmax*|gap| * |δ|)/p₁ :=
      (le_div_iff₀ hp₁).2 hmain
    _ = (2*cmax*|gap|/p₁) * |δ| := by ring

end
end PhosphorylationStableCapacity
