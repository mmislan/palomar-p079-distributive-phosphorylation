module
public import proofs.PhosphorylationStableCapacity.FiniteAllSiteJacobianActionFormula
public import proofs.PhosphorylationStableCapacity.ScaledIntegerMatrixCertificates

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Exact rational input data for one class-chart Jacobian. -/
structure RationalSiteRates (n : ℕ) where
  a : Fin n → ℚ
  b : Fin n → ℚ
  c : Fin n → ℚ
  alpha : Fin n → ℚ
  beta : Fin n → ℚ
  gamma : Fin n → ℚ

abbrev RationalSiteCoordinate (n : ℕ) :=
  (Fin n → ℚ) × ((Fin n → ℚ) × (Fin n → ℚ))

def RationalSiteRates.toReal {n : ℕ} (k : RationalSiteRates n) : Rates n where
  a := fun i => (k.a i : ℝ)
  b := fun i => (k.b i : ℝ)
  c := fun i => (k.c i : ℝ)
  alpha := fun i => (k.alpha i : ℝ)
  beta := fun i => (k.beta i : ℝ)
  gamma := fun i => (k.gamma i : ℝ)

def RationalSiteCoordinate.toReal {n : ℕ}
    (u : RationalSiteCoordinate n) : CoordinateSpace n :=
  ((fun i => (u.1 i : ℝ)),
    ((fun i => (u.2.1 i : ℝ)), (fun i => (u.2.2 i : ℝ))))

def rationalSiteS {n : ℕ} (ST : ℚ) (u : RationalSiteCoordinate n) :
    Fin (n + 1) → ℚ :=
  Fin.cases (ST - ∑ i, u.1 i - ∑ i, u.2.1 i - ∑ i, u.2.2 i) u.1

def rationalSiteE {n : ℕ} (ET : ℚ) (u : RationalSiteCoordinate n) : ℚ :=
  ET - ∑ i, u.2.1 i

def rationalSiteF {n : ℕ} (FT : ℚ) (u : RationalSiteCoordinate n) : ℚ :=
  FT - ∑ i, u.2.2 i

def rationalDirectionS {n : ℕ} (v : RationalSiteCoordinate n) :
    Fin (n + 1) → ℚ :=
  Fin.cases (-(∑ i, v.1 i) - ∑ i, v.2.1 i - ∑ i, v.2.2 i) v.1

def rationalDirectionE {n : ℕ} (v : RationalSiteCoordinate n) : ℚ :=
  -(∑ i, v.2.1 i)

def rationalDirectionF {n : ℕ} (v : RationalSiteCoordinate n) : ℚ :=
  -(∑ i, v.2.2 i)

def rationalKinaseDirection {n : ℕ} (ET ST : ℚ)
    (k : RationalSiteRates n) (u v : RationalSiteCoordinate n)
    (i : Fin n) : ℚ :=
  k.a i * (rationalSiteE ET u * rationalDirectionS v i.castSucc +
    rationalSiteS ST u i.castSucc * rationalDirectionE v) - k.b i * v.2.1 i

def rationalPhosphataseDirection {n : ℕ} (FT ST : ℚ)
    (k : RationalSiteRates n) (u v : RationalSiteCoordinate n)
    (i : Fin n) : ℚ :=
  k.alpha i * (rationalSiteF FT u * rationalDirectionS v i.succ +
    rationalSiteS ST u i.succ * rationalDirectionF v) - k.beta i * v.2.2 i

/-- A finite rational evaluator with the same block order as the class chart. -/
def rationalJacobianAction {n : ℕ} (ET FT ST : ℚ)
    (k : RationalSiteRates n) (u v : RationalSiteCoordinate n) :
    RationalSiteCoordinate n :=
  ((fun j => ∑ i : Fin n, (
      (if i.castSucc = j.succ then
        -rationalKinaseDirection ET ST k u v i + k.gamma i * v.2.2 i else 0) +
      (if i.succ = j.succ then
        k.c i * v.2.1 i - rationalPhosphataseDirection FT ST k u v i else 0))),
    (fun i => rationalKinaseDirection ET ST k u v i - k.c i * v.2.1 i),
    (fun i => rationalPhosphataseDirection FT ST k u v i - k.gamma i * v.2.2 i))

def rationalCoordinateRead {n : ℕ}
    (i : Fin n ⊕ (Fin n ⊕ Fin n)) (u : RationalSiteCoordinate n) : ℚ :=
  match i with
  | .inl j => u.1 j
  | .inr (.inl j) => u.2.1 j
  | .inr (.inr j) => u.2.2 j

def rationalCoordinateUnit {n : ℕ}
    (j : Fin n ⊕ (Fin n ⊕ Fin n)) : RationalSiteCoordinate n :=
  match j with
  | .inl i => (Pi.single i 1, (0, 0))
  | .inr (.inl i) => (0, (Pi.single i 1, 0))
  | .inr (.inr i) => (0, (0, Pi.single i 1))

def rationalJacobianMatrix {n : ℕ} (ET FT ST : ℚ)
    (k : RationalSiteRates n) (u : RationalSiteCoordinate n) :
    Matrix (Fin (3 * n)) (Fin (3 * n)) ℚ :=
  Matrix.of fun i j =>
    rationalCoordinateRead ((allSiteIndexEquiv n).symm i)
      (rationalJacobianAction ET FT ST k u
        (rationalCoordinateUnit ((allSiteIndexEquiv n).symm j)))

def ScaledIntegerMatrix.ratMatrix {ι κ : Type*}
    (A : ScaledIntegerMatrix ι κ) : Matrix ι κ ℚ :=
  (A.denominator : ℚ)⁻¹ • A.entries.map (Int.castRingHom ℚ)

private theorem rationalSiteS_cast {n : ℕ} (ST : ℚ)
    (u : RationalSiteCoordinate n) (i : Fin (n + 1)) :
    (rationalSiteS ST u i : ℝ) =
      allSiteClassS (ST : ℝ) u.toReal i := by
  cases i using Fin.cases with
  | zero => simp [rationalSiteS, allSiteClassS,
      RationalSiteCoordinate.toReal]
  | succ i => rfl

private theorem rationalDirectionS_cast {n : ℕ}
    (v : RationalSiteCoordinate n) (i : Fin (n + 1)) :
    (rationalDirectionS v i : ℝ) =
      allSiteDirectionS v.toReal i := by
  cases i using Fin.cases with
  | zero => simp [rationalDirectionS, allSiteDirectionS,
      RationalSiteCoordinate.toReal]
  | succ i => rfl

private theorem rationalKinaseDirection_cast {n : ℕ} (ET ST : ℚ)
    (k : RationalSiteRates n) (u v : RationalSiteCoordinate n)
    (i : Fin n) :
    (rationalKinaseDirection ET ST k u v i : ℝ) =
      allSiteKinaseDirection (ET : ℝ) (ST : ℝ) k.toReal
        u.toReal v.toReal i := by
  simp [rationalKinaseDirection, allSiteKinaseDirection,
    rationalSiteS_cast, rationalDirectionS_cast,
    rationalSiteE, rationalDirectionE,
    allSiteClassE, allSiteDirectionE,
    RationalSiteCoordinate.toReal, RationalSiteRates.toReal]

private theorem rationalPhosphataseDirection_cast {n : ℕ} (FT ST : ℚ)
    (k : RationalSiteRates n) (u v : RationalSiteCoordinate n)
    (i : Fin n) :
    (rationalPhosphataseDirection FT ST k u v i : ℝ) =
      allSitePhosphataseDirection (FT : ℝ) (ST : ℝ) k.toReal
        u.toReal v.toReal i := by
  simp [rationalPhosphataseDirection, allSitePhosphataseDirection,
    rationalSiteS_cast, rationalDirectionS_cast,
    rationalSiteF, rationalDirectionF,
    allSiteClassF, allSiteDirectionF,
    RationalSiteCoordinate.toReal, RationalSiteRates.toReal]

theorem rationalJacobianAction_cast {n : ℕ} (ET FT ST : ℚ)
    (k : RationalSiteRates n) (u v : RationalSiteCoordinate n) :
    (rationalJacobianAction ET FT ST k u v).toReal =
      allSiteJacobianActionFormula (ET : ℝ) (FT : ℝ) (ST : ℝ)
        k.toReal u.toReal v.toReal := by
  apply Prod.ext
  · funext j
    simp [RationalSiteCoordinate.toReal, rationalJacobianAction,
      allSiteJacobianActionFormula, rationalKinaseDirection_cast,
      rationalPhosphataseDirection_cast, RationalSiteRates.toReal]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h1 : x.castSucc = j.succ
    · by_cases h2 : x = j
      · subst x
        by_cases hk : j.castSucc = j.succ <;>
          simp [hk, rationalKinaseDirection_cast,
            rationalPhosphataseDirection_cast,
            RationalSiteRates.toReal, RationalSiteCoordinate.toReal]
      · simp [h1, h2, rationalKinaseDirection_cast,
          RationalSiteRates.toReal, RationalSiteCoordinate.toReal]
    · by_cases h2 : x = j
      · subst x
        by_cases hk : j.castSucc = j.succ <;>
          simp [hk, rationalKinaseDirection_cast,
            rationalPhosphataseDirection_cast,
            RationalSiteRates.toReal, RationalSiteCoordinate.toReal]
      · simp [h1, h2]
  · apply Prod.ext
    · funext i
      simp [RationalSiteCoordinate.toReal, rationalJacobianAction,
        allSiteJacobianActionFormula, rationalKinaseDirection_cast,
        RationalSiteRates.toReal]
    · funext i
      simp [RationalSiteCoordinate.toReal, rationalJacobianAction,
        allSiteJacobianActionFormula, rationalPhosphataseDirection_cast,
        RationalSiteRates.toReal]

private theorem rationalCoordinateRead_cast {n : ℕ}
    (i : Fin n ⊕ (Fin n ⊕ Fin n))
    (u : RationalSiteCoordinate n) :
    (rationalCoordinateRead i u : ℝ) =
      allSiteCoordinateRead i u.toReal := by
  rcases i with i | i
  · rfl
  rcases i with i | i <;> rfl

private theorem rationalCoordinateUnit_cast {n : ℕ}
    (j : Fin n ⊕ (Fin n ⊕ Fin n)) :
    (rationalCoordinateUnit j).toReal = allSiteCoordinateUnit j := by
  rcases j with j | j
  · simp only [rationalCoordinateUnit, allSiteCoordinateUnit,
      RationalSiteCoordinate.toReal, Prod.mk.injEq]
    constructor
    · funext i; by_cases h : i = j <;> simp [h]
    · constructor <;> funext i <;> simp
  rcases j with j | j
  · simp only [rationalCoordinateUnit, allSiteCoordinateUnit,
      RationalSiteCoordinate.toReal, Prod.mk.injEq]
    constructor
    · funext i; simp
    · constructor
      · funext i; by_cases h : i = j <;> simp [h]
      · funext i; simp
  · simp only [rationalCoordinateUnit, allSiteCoordinateUnit,
      RationalSiteCoordinate.toReal, Prod.mk.injEq]
    constructor
    · funext i; simp
    · constructor
      · funext i; simp
      · funext i; by_cases h : i = j <;> simp [h]

/-- The rational evaluator, after the canonical embedding, is the actual
restricted class Jacobian in the finite chart order. -/
theorem rationalJacobianMatrix_cast {n : ℕ} (ET FT ST : ℚ)
    (k : RationalSiteRates n) (u : RationalSiteCoordinate n) :
    (rationalJacobianMatrix ET FT ST k u).map (algebraMap ℚ ℝ) =
      allSiteExplicitFinMatrix (ET : ℝ) (FT : ℝ) (ST : ℝ)
        k.toReal u.toReal := by
  ext i j
  rw [allSiteExplicitFinMatrix_entry_actionFormula]
  change
    (rationalCoordinateRead ((allSiteIndexEquiv n).symm i)
      (rationalJacobianAction ET FT ST k u
        (rationalCoordinateUnit ((allSiteIndexEquiv n).symm j))) : ℝ) = _
  rw [rationalCoordinateRead_cast, rationalJacobianAction_cast,
    rationalCoordinateUnit_cast]

theorem ScaledIntegerMatrix.ratMatrix_cast {ι κ : Type*}
    (A : ScaledIntegerMatrix ι κ) :
    A.ratMatrix.map (algebraMap ℚ ℝ) = A.realMatrix := by
  ext i j
  simp [ScaledIntegerMatrix.ratMatrix, ScaledIntegerMatrix.realMatrix]

end
end PhosphorylationStableCapacity
