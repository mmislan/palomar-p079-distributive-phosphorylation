module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

/-- Rational intervals used by the finite operational certificate. -/
structure RationalInterval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

namespace RationalInterval

def Contains (I : RationalInterval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def point (q : ℚ) : RationalInterval := ⟨q, q⟩
def add (I J : RationalInterval) : RationalInterval := ⟨I.lo + J.lo, I.hi + J.hi⟩
def neg (I : RationalInterval) : RationalInterval := ⟨-I.hi, -I.lo⟩
def sub (I J : RationalInterval) : RationalInterval := add I (neg J)
def mul (I J : RationalInterval) : RationalInterval :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩
def magnitude (I : RationalInterval) : ℚ := max |I.lo| |I.hi|
def centered (q radius : ℚ) : RationalInterval := ⟨q - radius, q + radius⟩
def relative (q radius : ℚ) : RationalInterval :=
  ⟨q * (1 - radius), q * (1 + radius)⟩

theorem point_contains (q : ℚ) : (point q).Contains (q : ℝ) := ⟨le_rfl, le_rfl⟩

theorem centered_contains_of_abs_sub_le (q radius : ℚ) (x : ℝ)
    (hx : |x - (q : ℝ)| ≤ (radius : ℝ)) : (centered q radius).Contains x := by
  rw [abs_le] at hx
  simp only [Contains, centered, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith

theorem relative_contains_of_abs_sub_le (q radius : ℚ) (x : ℝ)
    (hx : |x - (q : ℝ)| ≤ (radius : ℝ) * (q : ℝ)) :
    (relative q radius).Contains x := by
  rw [abs_le] at hx
  simp only [Contains, relative, Rat.cast_mul, Rat.cast_sub, Rat.cast_add, Rat.cast_one]
  constructor <;> nlinarith

theorem relative_lo_pos (q radius : ℚ) (hq : 0 < q) (hr : radius < 1) :
    (0 : ℝ) < (relative q radius).lo :=
  Rat.cast_pos.mpr (mul_pos hq (sub_pos.mpr hr))

theorem contains_pos {I : RationalInterval} {x : ℝ}
    (hlo : (0 : ℝ) < I.lo) (hx : I.Contains x) : 0 < x := hlo.trans_le hx.1

theorem add_contains {I J : RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (add I J).Contains (x + y) := by
  constructor
  · simpa [add] using add_le_add hx.1 hy.1
  · simpa [add] using add_le_add hx.2 hy.2

theorem neg_contains {I : RationalInterval} {x : ℝ}
    (hx : I.Contains x) : (neg I).Contains (-x) := by
  constructor
  · simpa [neg] using neg_le_neg hx.2
  · simpa [neg] using neg_le_neg hx.1

theorem sub_contains {I J : RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (sub I J).Contains (x - y) := by
  simpa [sub, sub_eq_add_neg] using add_contains hx (neg_contains hy)

private theorem bounded_linear_product {a b x t L U : ℝ}
    (hax : a ≤ x) (hxb : x ≤ b)
    (hLa : L ≤ a*t) (hLb : L ≤ b*t)
    (haU : a*t ≤ U) (hbU : b*t ≤ U) : L ≤ x*t ∧ x*t ≤ U := by
  by_cases ht : 0 ≤ t
  · exact ⟨hLa.trans (mul_le_mul_of_nonneg_right hax ht),
      (mul_le_mul_of_nonneg_right hxb ht).trans hbU⟩
  · have ht' : t ≤ 0 := le_of_lt (lt_of_not_ge ht)
    exact ⟨hLb.trans (mul_le_mul_of_nonpos_right hxb ht'),
      (mul_le_mul_of_nonpos_right hax ht').trans haU⟩

theorem mul_contains {I J : RationalInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (mul I J).Contains (x*y) := by
  let L : ℝ := min (min ((I.lo : ℝ)*J.lo) ((I.lo : ℝ)*J.hi))
    (min ((I.hi : ℝ)*J.lo) ((I.hi : ℝ)*J.hi))
  let U : ℝ := max (max ((I.lo : ℝ)*J.lo) ((I.lo : ℝ)*J.hi))
    (max ((I.hi : ℝ)*J.lo) ((I.hi : ℝ)*J.hi))
  have h00 : L ≤ (I.lo : ℝ)*J.lo ∧ (I.lo : ℝ)*J.lo ≤ U :=
    ⟨(min_le_left _ _).trans (min_le_left _ _),
      (le_max_left _ _).trans (le_max_left _ _)⟩
  have h01 : L ≤ (I.lo : ℝ)*J.hi ∧ (I.lo : ℝ)*J.hi ≤ U :=
    ⟨(min_le_left _ _).trans (min_le_right _ _),
      (le_max_right _ _).trans (le_max_left _ _)⟩
  have h10 : L ≤ (I.hi : ℝ)*J.lo ∧ (I.hi : ℝ)*J.lo ≤ U :=
    ⟨(min_le_right _ _).trans (min_le_left _ _),
      (le_max_left _ _).trans (le_max_right _ _)⟩
  have h11 : L ≤ (I.hi : ℝ)*J.hi ∧ (I.hi : ℝ)*J.hi ≤ U :=
    ⟨(min_le_right _ _).trans (min_le_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  have hlo : L ≤ (I.lo : ℝ)*y ∧ (I.lo : ℝ)*y ≤ U := by
    have h := bounded_linear_product (t := (I.lo : ℝ)) (L := L) (U := U)
      hy.1 hy.2 (by simpa only [mul_comm] using h00.1)
      (by simpa only [mul_comm] using h01.1)
      (by simpa only [mul_comm] using h00.2)
      (by simpa only [mul_comm] using h01.2)
    simpa only [mul_comm] using h
  have hhi : L ≤ (I.hi : ℝ)*y ∧ (I.hi : ℝ)*y ≤ U := by
    have h := bounded_linear_product (t := (I.hi : ℝ)) (L := L) (U := U)
      hy.1 hy.2 (by simpa only [mul_comm] using h10.1)
      (by simpa only [mul_comm] using h11.1)
      (by simpa only [mul_comm] using h10.2)
      (by simpa only [mul_comm] using h11.2)
    simpa only [mul_comm] using h
  have h := bounded_linear_product hx.1 hx.2 hlo.1 hhi.1 hlo.2 hhi.2
  simpa [Contains, mul, L, U, Rat.cast_min, Rat.cast_max] using h

theorem abs_le_magnitude {I : RationalInterval} {x : ℝ} (hx : I.Contains x) :
    |x| ≤ (I.magnitude : ℝ) := by
  rw [abs_le]
  have hlo : -(I.magnitude : ℝ) ≤ (I.lo : ℝ) := by
    have h := neg_abs_le (I.lo : ℝ)
    have hmag : |(I.lo : ℝ)| ≤ (I.magnitude : ℝ) := by
      simp [magnitude]
    linarith
  have hhi : (I.hi : ℝ) ≤ (I.magnitude : ℝ) := by
    have hmag : |(I.hi : ℝ)| ≤ (I.magnitude : ℝ) := by
      simp [magnitude]
    exact (le_abs_self _).trans hmag
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

end RationalInterval
end PhosphorylationStableCapacity
