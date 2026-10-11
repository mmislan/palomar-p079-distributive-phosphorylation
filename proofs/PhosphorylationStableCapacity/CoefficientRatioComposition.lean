module
public import proofs.PhosphorylationStableCapacity.CoefficientRatioTransport

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial PhosphorylationSharpness

noncomputable section

def CoeffRatioMono (p q : ℝ[X]) (m : ℕ) : Prop :=
  ∀ i < m, q.coeff i / p.coeff i ≤
    q.coeff (i + 1) / p.coeff (i + 1)

theorem positive_ratio_mono_compose
    (a0 a1 b0 b1 c0 c1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hb0 : 0 < b0) (hb1 : 0 < b1)
    (hc1 : 0 < c1)
    (hba : b0 / a0 ≤ b1 / a1)
    (hcb : c0 / b0 ≤ c1 / b1) :
    c0 / a0 ≤ c1 / a1 := by
  have hfirst := mul_le_mul_of_nonneg_right hcb
    (div_nonneg hb0.le ha0.le)
  have hsecond := mul_le_mul_of_nonneg_left hba
    (div_nonneg hc1.le hb1.le)
  calc
    c0 / a0 = (c0 / b0) * (b0 / a0) := by
      field_simp [ne_of_gt hb0, ne_of_gt ha0]
    _ ≤ (c1 / b1) * (b0 / a0) := hfirst
    _ ≤ (c1 / b1) * (b1 / a1) := hsecond
    _ = c1 / a1 := by
      field_simp [ne_of_gt hb1, ne_of_gt ha1]

theorem coeffRatioMono_compose {p q r : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m)
    (hr : DensePositive r m)
    (hpq : CoeffRatioMono p q m) (hqr : CoeffRatioMono q r m) :
    CoeffRatioMono p r m := by
  intro i hi
  exact positive_ratio_mono_compose
    (p.coeff i) (p.coeff (i + 1))
    (q.coeff i) (q.coeff (i + 1))
    (r.coeff i) (r.coeff (i + 1))
    (hp.1 i (by omega)) (hp.1 (i + 1) (by omega))
    (hq.1 i (by omega)) (hq.1 (i + 1) (by omega))
    (hr.1 (i + 1) (by omega))
    (hpq i hi) (hqr i hi)

end
end PhosphorylationStableCapacity
