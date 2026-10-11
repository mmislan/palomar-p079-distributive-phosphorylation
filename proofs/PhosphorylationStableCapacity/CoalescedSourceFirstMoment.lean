module
public import proofs.PhosphorylationStableCapacity.CoalescedFiniteSource
public import proofs.PhosphorylationStableCapacity.CoalescedMomentInduction

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial PhosphorylationSharpness Filter

noncomputable section

/-- Differentiating the exact quotient identity at the source point one.
This identity keeps the finite source parameter and does not use a limit. -/
theorem quotient_deriv_eval_one (p q : ℝ[X]) (r : ℝ) :
    (quotient p q r).eval 1 +
      (1 - r) * (derivative (quotient p q r)).eval 1 =
      q.eval r * (p.eval 1 + (derivative p).eval 1) -
        r * p.eval r * (derivative q).eval 1 := by
  have h := congrArg (fun f : ℝ[X] => (derivative f).eval 1)
    (quotient_identity p q r)
  simp [conversionNumerator, derivative_mul, derivative_sub] at h
  linear_combination h

/-- Evaluation at one of the undifferentiated quotient identity. -/
theorem quotient_eval_one (p q : ℝ[X]) (r : ℝ) :
    (1 - r) * (quotient p q r).eval 1 =
      q.eval r * p.eval 1 - r * p.eval r * q.eval 1 := by
  have h := congrArg (fun f : ℝ[X] => f.eval 1)
    (quotient_identity p q r)
  simpa [conversionNumerator, sub_mul] using h

/-- Only the equal source values and their first-derivative difference are
needed for the finite first-moment identity of the converted rate data. -/
theorem rawB_deriv_eval_one_of_moments (p q : ℝ[X]) (r z : ℝ)
    (hp : p.eval 1 = z) (hq : q.eval 1 = z)
    (hdiff : (derivative p).eval 1 - (derivative q).eval 1 =
      -(2 / 3 : ℝ) * z) :
    (derivative (rawB p q r)).eval 1 =
      (2 * r - 1) * (derivative (rawD p q r)).eval 1 -
        (2 * r + 1) / 3 * (rawD p q r).eval 1 := by
  have hD0 : (rawD p q r).eval 1 =
      4 * (quotient p q r).eval 1 := by
    simp [rawD]
  have hD1 : (derivative (rawD p q r)).eval 1 =
      4 * (derivative (quotient p q r)).eval 1 := by
    simp [rawD, derivative_mul]
  have hDval : (1 - r) * (rawD p q r).eval 1 =
      4 * z * (q.eval r - r * p.eval r) := by
    rw [hD0]
    have h := quotient_eval_one p q r
    rw [hp, hq] at h
    linear_combination 4 * h
  have hDder : (rawD p q r).eval 1 +
      (1 - r) * (derivative (rawD p q r)).eval 1 =
      4 * (q.eval r * (z + (derivative p).eval 1) -
        r * p.eval r * (derivative q).eval 1) := by
    rw [hD0, hD1]
    have h := quotient_deriv_eval_one p q r
    rw [hp] at h
    linear_combination 4 * h
  have hBder : (derivative (rawB p q r)).eval 1 =
      r * (derivative (rawD p q r)).eval 1 +
        (4 * r * p.eval r - 2 * q.eval r) *
          (derivative p).eval 1 -
          2 * q.eval r * (derivative q).eval 1 := by
    simp [rawB, derivative_mul, derivative_add, derivative_sub]
  have hdiffmul := congrArg
    (fun t : ℝ => (2 * q.eval r + 4 * r * p.eval r) * t) hdiff
  nlinarith [hDval, hDder, hBder, hdiffmul]

/-- The literal all-size equal-root source satisfies the exact finite
first-moment relation required for the zero slow-current mode. -/
theorem coalescedRawB_deriv_eval_one (m : ℕ) (r : ℝ) :
    (derivative (coalescedRawB (m + 1) r)).eval 1 =
      (2 * r - 1) *
        (derivative (coalescedRawD (m + 1) r)).eval 1 -
      (2 * r + 1) / 3 * (coalescedRawD (m + 1) r).eval 1 := by
  let p := (coalescedPair (m + 1)).1
  let q := (coalescedPair (m + 1)).2
  let z : ℝ := 36 ^ (m + 1)
  have hval := coalescedPair_eval_one (m + 1)
  have hder := coalescedPair_deriv_eval_one m
  have hdiff : (derivative p).eval 1 -
      (derivative q).eval 1 = -(2 / 3 : ℝ) * z := by
    dsimp [p, q, z]
    rw [hder.1, hder.2]
    ring
  exact rawB_deriv_eval_one_of_moments p q r z hval.1 hval.2 hdiff

/-- Candidate zeroth feedback moment of the literal source, before its
identification with the finite binding complex levels. -/
def coalescedSourceH0 (r : ℝ) : ℝ := (1 - r) / (2 * r)

/-- Candidate first feedback moment from the converted polynomials. -/
def coalescedSourceH1 (m : ℕ) (r : ℝ) : ℝ :=
  let D := coalescedRawD (m + 1) r
  let B := coalescedRawB (m + 1) r
  (D.eval 1 + (derivative D).eval 1) / (2 * D.eval 1) -
    (derivative B).eval 1 / (2 * r * D.eval 1)

/-- Candidate zeroth total-row moment of the loaded mass. -/
def coalescedSourceT0 (r : ℝ) : ℝ := (7 * r - 1) / (2 * r)

/-- Candidate first total-row moment of the loaded mass. -/
def coalescedSourceT1 (m : ℕ) (r : ℝ) : ℝ :=
  let D := coalescedRawD (m + 1) r
  let B := coalescedRawB (m + 1) r
  (3 * D.eval 1 + 5 * (derivative D).eval 1) /
      (2 * D.eval 1) +
    (derivative B).eval 1 / (2 * r * D.eval 1)

/-- The exact finite source polynomial moments satisfy the scalar
determinant-zero identity. The literal mass/current moment bridge is next. -/
theorem coalescedSourceMomentDet_zero (m : ℕ) (r : ℝ)
    (hr : r ≠ 0)
    (hD : (coalescedRawD (m + 1) r).eval 1 ≠ 0) :
    coalescedSourceT0 r * (coalescedSourceH1 m r - 1) -
      coalescedSourceT1 m r * coalescedSourceH0 r = 0 := by
  have hB := coalescedRawB_deriv_eval_one m r
  simp only [coalescedSourceT0, coalescedSourceT1,
    coalescedSourceH0, coalescedSourceH1]
  rw [hB]
  field_simp [hr, hD]
  ring

/-- The coalesced source eventually satisfies the exact scalar zero-mode
moment condition without any nonzero premises in the conclusion. -/
theorem coalescedSourceMomentDet_eventually_zero (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      coalescedSourceT0 r * (coalescedSourceH1 m r - 1) -
        coalescedSourceT1 m r * coalescedSourceH0 r = 0 := by
  have hsource := conversion_eventually_positive
    (coalescedPair_dense (m + 1)).1
    (coalescedPair_dense (m + 1)).2
  filter_upwards [hsource, eventually_gt_atTop (0 : ℝ)]
    with r hpositive hr
  apply coalescedSourceMomentDet_zero m r (ne_of_gt hr)
  exact ne_of_gt (hpositive.1.eval_pos (by norm_num))

end
end PhosphorylationStableCapacity
