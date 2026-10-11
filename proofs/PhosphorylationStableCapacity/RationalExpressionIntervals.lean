module
public import proofs.PhosphorylationStableCapacity.RationalIntervalSoundness
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace PhosphorylationStableCapacity

/-- Polynomial expressions in independent real parameters and state coordinates.
Evaluation uses exact rational constants; the interval checker uses the same tree. -/
inductive RationalExpression (σ : Type*) where
  | const : ℚ → RationalExpression σ
  | var : σ → RationalExpression σ
  | add : RationalExpression σ → RationalExpression σ → RationalExpression σ
  | neg : RationalExpression σ → RationalExpression σ
  | mul : RationalExpression σ → RationalExpression σ → RationalExpression σ

namespace RationalExpression

def eval {σ : Type*} (v : σ → ℝ) : RationalExpression σ → ℝ
  | .const q => q
  | .var i => v i
  | .add e f => eval v e + eval v f
  | .neg e => -eval v e
  | .mul e f => eval v e * eval v f

def enclose {σ : Type*} (I : σ → RationalInterval) :
    RationalExpression σ → RationalInterval
  | .const q => RationalInterval.point q
  | .var i => I i
  | .add e f => RationalInterval.add (enclose I e) (enclose I f)
  | .neg e => RationalInterval.neg (enclose I e)
  | .mul e f => RationalInterval.mul (enclose I e) (enclose I f)

/-- Every computed rational enclosure covers evaluation at every real point
in the independent input box. This theorem supplies checker soundness. -/
theorem eval_mem_enclose {σ : Type*} (I : σ → RationalInterval) (v : σ → ℝ)
    (hv : ∀ i, (I i).Contains (v i)) (e : RationalExpression σ) :
    (enclose I e).Contains (eval v e) := by
  induction e with
  | const q => exact RationalInterval.point_contains q
  | var i => exact hv i
  | add e f he hf => exact RationalInterval.add_contains he hf
  | neg e he => exact RationalInterval.neg_contains he
  | mul e f he hf => exact RationalInterval.mul_contains he hf

theorem abs_eval_le {σ : Type*} (I : σ → RationalInterval) (v : σ → ℝ)
    (hv : ∀ i, (I i).Contains (v i)) (e : RationalExpression σ) :
    |eval v e| ≤ ((enclose I e).magnitude : ℝ) :=
  RationalInterval.abs_le_magnitude (eval_mem_enclose I v hv e)

end RationalExpression

namespace RationalInterval

def IsSubinterval (I J : RationalInterval) : Prop := J.lo ≤ I.lo ∧ I.hi ≤ J.hi

instance (I J : RationalInterval) : Decidable (IsSubinterval I J) :=
  inferInstanceAs (Decidable (J.lo ≤ I.lo ∧ I.hi ≤ J.hi))

theorem contains_of_subinterval {I J : RationalInterval} (hIJ : I.IsSubinterval J)
    {x : ℝ} (hx : I.Contains x) : J.Contains x := by
  have hlo : (J.lo : ℝ) ≤ I.lo := Rat.cast_le.mpr hIJ.1
  have hhi : (I.hi : ℝ) ≤ J.hi := Rat.cast_le.mpr hIJ.2
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

end RationalInterval

/-- A finite exact rational enclosure certificate implies a real uniform bound.
The certificate is checked by the kernel; no numerical oracle is used. -/
theorem rational_expression_bound_of_certificate {σ : Type*}
    (I : σ → RationalInterval) (e : RationalExpression σ) (B : RationalInterval)
    (hcheck : (e.enclose I).IsSubinterval B)
    (v : σ → ℝ) (hv : ∀ i, (I i).Contains (v i)) :
    B.Contains (e.eval v) :=
  RationalInterval.contains_of_subinterval hcheck (e.eval_mem_enclose I v hv)

/-- An exact row certificate bounds the real absolute row sums uniformly
throughout the independent parameter and state box. -/
theorem rational_expression_row_bound_of_certificate
    {σ ι κ : Type*} [Fintype κ]
    (I : σ → RationalInterval) (e : ι → κ → RationalExpression σ)
    (B : ℚ)
    (hcheck : ∀ i, (∑ j, ((e i j).enclose I).magnitude) ≤ B)
    (v : σ → ℝ) (hv : ∀ i, (I i).Contains (v i)) (i : ι) :
    (∑ j, |(e i j).eval v|) ≤ (B : ℝ) := by
  calc
    _ ≤ ∑ j, (((e i j).enclose I).magnitude : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact RationalExpression.abs_eval_le I v hv (e i j)
    _ = ((∑ j, ((e i j).enclose I).magnitude : ℚ) : ℝ) := by
      exact (map_sum (Rat.castHom ℝ) (fun j => ((e i j).enclose I).magnitude) Finset.univ).symm
    _ ≤ (B : ℝ) := Rat.cast_le.mpr (hcheck i)

end PhosphorylationStableCapacity
