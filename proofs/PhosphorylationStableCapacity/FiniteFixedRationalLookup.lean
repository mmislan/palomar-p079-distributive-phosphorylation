module
public import proofs.PhosphorylationStableCapacity.FiniteRationalJacobianAction
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedFamily
public import proofs.PhosphorylationStableCapacity.FiniteFixedPolynomialLookup
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedCoefficients
public import proofs.PhosphorylationStableCapacity.FiniteCoalescedCoefficientBridge
public import Mathlib.Data.Rat.BigOperators

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Polynomial

/-- Exact rational coefficient data for one printed fixed size. Each field
is independently checked against the manuscript construction in Lean. -/
structure FixedRationalLookup (m : ℕ) where
  spacing : ℚ
  inventory : Fin (m + 2) → ℚ
  binding : Fin (m + 1) → ℚ
  release : Fin (m + 1) → ℚ
  coalescedRelease : Fin (m + 1) → ℚ

def FixedRationalLookup.rawRates {m : ℕ}
    (q : FixedRationalLookup m) : RationalSiteRates (m + 1) where
  a i := 2 * q.release i / q.inventory i.castSucc
  b i := q.release i / q.binding i
  c i := q.release i / q.binding i
  alpha i := 2 * q.release i / q.inventory i.succ
  beta _ := 1
  gamma _ := 1

def FixedRationalLookup.coalescedCoordinate {m : ℕ}
    (q : FixedRationalLookup m) (i : Fin (m+1)) : ℚ :=
  q.coalescedRelease i / ∑ k : Fin (m+1), q.coalescedRelease k

def FixedRationalLookup.rates {m : ℕ}
    (q : FixedRationalLookup m) : RationalSiteRates (m + 1) where
  a i := (1 + (1 / q.coalescedCoordinate i) * (q.rawRates.c i)) *
    q.rawRates.a i / (q.rawRates.b i + q.rawRates.c i)
  b _ := 1
  c i := (1 / q.coalescedCoordinate i) * q.rawRates.c i
  alpha i := (1 + (1 / q.coalescedCoordinate i) * q.rawRates.gamma i) *
    q.rawRates.alpha i / (q.rawRates.beta i + q.rawRates.gamma i)
  beta _ := 1
  gamma i := (1 / q.coalescedCoordinate i) * q.rawRates.gamma i

def FixedRationalLookup.root {m : ℕ} (q : FixedRationalLookup m)
    (j : Fin (2 * m + 1)) : ℚ :=
  3 + q.spacing * ((j.val : ℚ) - m)

def FixedRationalLookup.ratio {m : ℕ} (q : FixedRationalLookup m)
    (j : Fin (2 * m + 1)) : ℚ :=
  ((q.root j) ^ 2 - 1) / 8

def FixedRationalLookup.releaseEval {m : ℕ}
    (q : FixedRationalLookup m) (u : ℚ) : ℚ :=
  ∑ i : Fin (m + 1), q.release i * u ^ i.val

def FixedRationalLookup.coordinate {m : ℕ}
    (q : FixedRationalLookup m) (j : Fin (2 * m + 1)) :
    RationalSiteCoordinate (m + 1) :=
  let x := q.root j
  let u := q.ratio j
  let s := (x - 1) / (2 * u * q.releaseEval u)
  let f := 4 / (x + 1)
  ((fun i => q.inventory i.succ * u ^ (i.val + 1) * s),
    ((fun i => q.binding i * u ^ (i.val + 1) * s * f),
      (fun i => q.release i * u ^ (i.val + 1) * s * f)))

/-- The rational release evaluation is the real source polynomial evaluation
once the finite coefficient table and its tail theorem have been checked. -/
theorem FixedRationalLookup.releaseEval_cast {m : ℕ}
    (q : FixedRationalLookup m) (p : ℝ[X])
    (htail : ∀ i : ℕ, m < i → p.coeff i = 0)
    (hcoeff : ∀ i : Fin (m + 1), p.coeff i.val = (q.release i : ℝ))
    (u : ℚ) :
    (q.releaseEval u : ℝ) = p.eval (u : ℝ) := by
  rw [polynomial_eval_of_finite_lookup m p
    (fun i => (q.release i : ℝ)) htail hcoeff]
  simp only [FixedRationalLookup.releaseEval, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_pow]

/-- The source inventory is obtained by multiplying the D polynomial by
`1+X`; the coefficient table makes this a single finite identity. -/
theorem FixedRationalLookup.inventory_cast_of_coeff {m : ℕ}
    (q : FixedRationalLookup m) (p : ℝ[X])
    (h0 : (q.inventory 0 : ℝ) = p.coeff 0)
    (hsucc : ∀ i : Fin (m + 1),
      (q.inventory i.succ : ℝ) = p.coeff (i.val + 1) + p.coeff i.val) :
    ∀ i : Fin (m + 2),
      (q.inventory i : ℝ) = ((1 + X) * p).coeff i.val := by
  intro i
  induction i using Fin.cases with
  | zero => simpa only [Fin.val_zero, one_add_X_mul_coeff_zero] using h0
  | succ i => simpa only [Fin.val_succ, one_add_X_mul_coeff_succ] using hsucc i

/-- Casting exact rational source coefficients commutes with the literal
rate reconstruction. -/
theorem FixedRationalLookup.rawRates_cast {m : ℕ}
    (q : FixedRationalLookup m) :
    q.rawRates.toReal = realize
      (fun i => (q.inventory i : ℝ))
      (fun i => (q.binding i : ℝ))
      (fun i => (q.release i : ℝ)) := by
  unfold FixedRationalLookup.rawRates RationalSiteRates.toReal realize
  congr 1 <;> funext i <;> push_cast <;> rfl

/-- The retuning uses normalized reference coordinates, rather than raw
polynomial coefficients. -/
theorem FixedRationalLookup.rates_cast {m : ℕ}
    (q : FixedRationalLookup m) :
    q.rates.toReal = retune q.rawRates.toReal
      (fun i => 1 / (q.coalescedCoordinate i : ℝ))
      (fun _ => 1) (fun _ => 1) := by
  unfold FixedRationalLookup.rates RationalSiteRates.toReal retune
  congr 1 <;> funext i <;> push_cast <;> rfl

/-- One coefficient/evaluation interface identifies the entire rational
chart family with the actual printed state family. -/
theorem FixedRationalLookup.coordinate_cast {m : ℕ}
    (q : FixedRationalLookup m) (j : Fin (2*m+1)) :
    (q.coordinate j).toReal =
      toCoordinateSpace (chart (reconstruct
        (fun i => (q.inventory i : ℝ))
        (fun i => (q.binding i : ℝ))
        (fun i => (q.release i : ℝ))
        (q.ratio j : ℝ)
        (((q.root j : ℝ)-1) / (2*(q.ratio j : ℝ)*(q.releaseEval (q.ratio j) : ℝ)))
        (4/((q.root j : ℝ)+1)))) := by
  ext i <;>
    simp only [FixedRationalLookup.coordinate, RationalSiteCoordinate.toReal,
      toCoordinateSpace, chart, reconstruct, Rat.cast_div, Rat.cast_mul,
      Rat.cast_sub, Rat.cast_add, Rat.cast_pow, Rat.cast_ofNat,
      Rat.cast_one, Fin.val_succ]

theorem FixedRationalLookup.coalescedCoordinate_cast {m : ℕ}
    (q : FixedRationalLookup m)
    (hcoeff : ∀ i : Fin (m+1),
      (coalescedRawD m (finiteFixedRadius m)).coeff i = (q.coalescedRelease i : ℝ))
    (i : Fin (m+1)) :
    (q.coalescedCoordinate i : ℝ) =
      (coalescedFiniteState m (finiteFixedRadius m)).D i := by
  obtain ⟨hp, hq⟩ := coalescedPair_dense m
  have htail (k : ℕ) (hk : m < k) :
      (coalescedRawD m (finiteFixedRadius m)).coeff k = 0 :=
    (raw_support hp hq (finiteFixedRadius m) k hk).1
  rw [coalescedFiniteState_D_eq_coeff_div_eval,
    polynomial_eval_of_finite_lookup m _ (fun k => (q.coalescedRelease k : ℝ))
      htail hcoeff 1]
  simp only [FixedRationalLookup.coalescedCoordinate, Rat.cast_div,
    Rat.cast_sum, hcoeff, one_pow, mul_one]

/-- A checked coefficient table binds a rational lookup to the printed
construction without unfolding the polynomial recurrence per state. -/
structure FixedRationalLookup.Valid {m : ℕ} (q : FixedRationalLookup m) : Prop where
  spacing : (q.spacing : ℝ) = finiteFixedSpacing m
  inventory : ∀ i : Fin (m+2), (q.inventory i : ℝ) =
    ((1+X)*arbitrarySplitRawD m (finiteFixedOffset m)
      (finiteFixedRadius m) (finiteFixedSpacing m)).coeff i
  binding : ∀ i : Fin (m+1), (q.binding i : ℝ) =
    (arbitrarySplitRawB m (finiteFixedOffset m)
      (finiteFixedRadius m) (finiteFixedSpacing m)).coeff i
  release : ∀ i : Fin (m+1), (q.release i : ℝ) =
    (arbitrarySplitRawD m (finiteFixedOffset m)
      (finiteFixedRadius m) (finiteFixedSpacing m)).coeff i
  releaseTail : ∀ i : ℕ, m < i →
    (arbitrarySplitRawD m (finiteFixedOffset m)
      (finiteFixedRadius m) (finiteFixedSpacing m)).coeff i = 0
  coalesced : ∀ i : Fin (m+1), (q.coalescedCoordinate i : ℝ) =
    (coalescedFiniteState m (finiteFixedRadius m)).D i

theorem FixedRationalLookup.Valid.rates_cast {m : ℕ}
    {q : FixedRationalLookup m} (h : q.Valid) :
    q.rates.toReal = finiteFixedPrintedRates m := by
  rw [FixedRationalLookup.rates_cast, FixedRationalLookup.rawRates_cast]
  have ht := funext h.inventory
  have hb := funext h.binding
  have hd := funext h.release
  rw [ht, hb, hd]
  simp only [h.coalesced]
  rfl

theorem FixedRationalLookup.Valid.coordinate_cast {m : ℕ}
    {q : FixedRationalLookup m} (h : q.Valid) (j : Fin (2*m+1)) :
    (q.coordinate j).toReal =
      toCoordinateSpace (chart (finiteFixedPrintedState m j)) := by
  have hx : (q.root j : ℝ) =
      offsetSplitRoot (finiteFixedOffset m) (finiteFixedSpacing m) j.val := by
    dsimp [FixedRationalLookup.root]
    push_cast
    rw [h.spacing]
    rfl
  have hu : (q.ratio j : ℝ) = PhosphorylationSharpness.ratio
      (offsetSplitRoot (finiteFixedOffset m) (finiteFixedSpacing m) j.val) := by
    dsimp [FixedRationalLookup.ratio]
    push_cast
    rw [hx]
    rfl
  have heval := FixedRationalLookup.releaseEval_cast q
    (arbitrarySplitRawD m (finiteFixedOffset m)
      (finiteFixedRadius m) (finiteFixedSpacing m))
    h.releaseTail (fun i => (h.release i).symm) (q.ratio j)
  rw [hu] at heval
  rw [FixedRationalLookup.coordinate_cast]
  rw [funext h.inventory, funext h.binding, funext h.release, hx, hu, heval]
  rfl

end
end PhosphorylationStableCapacity
