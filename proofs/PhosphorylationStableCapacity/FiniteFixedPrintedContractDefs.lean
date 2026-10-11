module
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedFamily
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.LocalAsymptoticStability
public import proofs.PhosphorylationStableCapacity.RationalSplitWitnessAlgebra

@[expose] public section

namespace PhosphorylationStableCapacity.P079PrintedContract
noncomputable section
open PhosphorylationSharpness Polynomial

def paperFixedRadius (m : ℕ) : ℝ :=
  if m = 1 then 2 else if m ≤ 3 then 4 else 8

def paperFixedSpacing (m : ℕ) : ℝ :=
  if m ≤ 3 then 1 / 2 else 1 / 4

def paperFixedRoot (m : ℕ) (δ : ℝ) (j : ℕ) : ℝ :=
  3 + δ * ((j : ℝ) - m)

def paperFixedNextN (a b : ℝ) (p q : ℝ[X]) : ℝ[X] :=
  Polynomial.C ((a + 1) * (b + 1)) * p +
    Polynomial.C 8 * (Polynomial.X * p) +
      Polynomial.C (2 * (a + b)) * q

def paperFixedNextJ (a b : ℝ) (p q : ℝ[X]) : ℝ[X] :=
  Polynomial.C ((a - 1) * (b - 1)) * q +
    Polynomial.C 8 * (Polynomial.X * q) +
      Polynomial.C (4 * (a + b)) * (Polynomial.X * p)

def paperFixedPairAt (M : ℕ) : (depth : ℕ) → ℝ → ℝ[X] × ℝ[X]
  | 0, δ => (1, Polynomial.C ((paperFixedRoot M δ 0 - 1) / 2))
  | depth + 1, δ =>
      let pq := paperFixedPairAt M depth δ
      (paperFixedNextN (paperFixedRoot M δ (2 * depth + 1))
          (paperFixedRoot M δ (2 * depth + 2)) pq.1 pq.2,
        paperFixedNextJ (paperFixedRoot M δ (2 * depth + 1))
          (paperFixedRoot M δ (2 * depth + 2)) pq.1 pq.2)

def paperFixedPair (m : ℕ) (δ : ℝ) : ℝ[X] × ℝ[X] :=
  paperFixedPairAt m m δ

def paperFixedRatio (x : ℝ) : ℝ := (x ^ 2 - 1) / 8
def paperFixedRootS (x d : ℝ) : ℝ :=
  (x - 1) / (2 * paperFixedRatio x * d)
def paperFixedRootF (x : ℝ) : ℝ := 4 / (x + 1)

def paperFixedRawD (m : ℕ) (r δ : ℝ) : ℝ[X] :=
  let pq := paperFixedPair m δ
  Polynomial.C 4 *
    ((Polynomial.C (pq.2.eval r) * (Polynomial.X * pq.1) -
        Polynomial.C (r * pq.1.eval r) * pq.2) /ₘ
      (Polynomial.X - Polynomial.C r))

def paperFixedRawB (m : ℕ) (r δ : ℝ) : ℝ[X] :=
  let pq := paperFixedPair m δ
  let D := paperFixedRawD m r δ
  Polynomial.C r * D +
    Polynomial.C (4 * r * pq.1.eval r - 2 * pq.2.eval r) * pq.1 -
      Polynomial.C (2 * pq.2.eval r) * pq.2

def paperFixedT (m : ℕ) (r δ : ℝ) (i : Fin (m + 2)) : ℝ :=
  (((1 : ℝ[X]) + Polynomial.X) * paperFixedRawD m r δ).coeff i

def paperFixedBaseRates (m : ℕ) (r δ : ℝ) : Rates (m + 1) :=
  let B := paperFixedRawB m r δ
  let D := paperFixedRawD m r δ
  let t := paperFixedT m r δ
  { a := fun i => 2 * D.coeff i / t i.castSucc
    b := fun i => D.coeff i / B.coeff i
    c := fun i => D.coeff i / B.coeff i
    alpha := fun i => 2 * D.coeff i / t i.succ
    beta := fun _ => 1
    gamma := fun _ => 1 }

def paperFixedCoalescedD (m : ℕ) (i : Fin (m + 1)) : ℝ :=
  let D := paperFixedRawD m (paperFixedRadius m) 0
  D.coeff i * paperFixedRatio 3 ^ (i.val + 1) *
    paperFixedRootS 3 (D.eval (paperFixedRatio 3)) * paperFixedRootF 3

def paperFixedRates (m : ℕ) : Rates (m + 1) :=
  let k := paperFixedBaseRates m (paperFixedRadius m) (paperFixedSpacing m)
  let l := fun i : Fin (m + 1) => 1 / paperFixedCoalescedD m i
  { a := fun i => (1 + l i * k.c i) * k.a i / (k.b i + k.c i)
    b := fun _ => 1
    c := fun i => l i * k.c i
    alpha := fun i => (1 + l i * k.gamma i) * k.alpha i /
      (k.beta i + k.gamma i)
    beta := fun _ => 1
    gamma := fun i => l i * k.gamma i }

def paperFixedState (m : ℕ) (j : Fin (2 * m + 1)) : State (m + 1) :=
  let r := paperFixedRadius m
  let δ := paperFixedSpacing m
  let x := paperFixedRoot m δ j.val
  let D := paperFixedRawD m r δ
  let B := paperFixedRawB m r δ
  let u := paperFixedRatio x
  let s := paperFixedRootS x (D.eval u)
  let f := paperFixedRootF x
  { S := fun i => paperFixedT m r δ i * u ^ i.val * s
    E := u * f
    F := f
    C := fun i => B.coeff i * u ^ (i.val + 1) * s * f
    D := fun i => D.coeff i * u ^ (i.val + 1) * s * f }

def PaperFixedFiniteTable : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ 6 →
    let k := paperFixedRates m
    let x := paperFixedState m
    let ET := 2 * paperFixedRadius m
    let FT : ℝ := 2
    let ST := 2 * (paperFixedRadius m + 1)
    RationalRates k ∧ k.Positive ∧
      (∀ j : Fin (2 * m + 1),
        RationalState (x j) ∧ (x j).Positive ∧
          Equilibrium k (x j) ∧ InClass ET FT ST (x j)) ∧
      Function.Injective x ∧
      {y : State (m + 1) |
        y.Positive ∧ Equilibrium k y ∧ InClass ET FT ST y} =
          Set.range x ∧
      {y : State (m + 1) |
        y.Positive ∧ Equilibrium k y ∧ InClass ET FT ST y}.ncard =
          2 * m + 1 ∧
      (∀ j : Fin (2 * m + 1),
        if Even j.val then
          IsLinearlyStable ET FT ST k (toCoordinateSpace (chart (x j))) ∧
            IsLocallyAsymptoticallyStableClass ET FT ST k
              (toCoordinateSpace (chart (x j)))
        else
          IsOneUnstableSaddle ET FT ST k
            (toCoordinateSpace (chart (x j))))
end
end PhosphorylationStableCapacity.P079PrintedContract
