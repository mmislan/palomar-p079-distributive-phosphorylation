module
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Tactic.FunProp
public import proofs.PhosphorylationStableCapacity.Compatibility
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness
open Module

/-- A normed real coordinate space for the `3n` free class variables. -/
abbrev CoordinateSpace (n : ℕ) :=
  (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)

def toCoordinateSpace {n : ℕ} (u : ClassCoord n) : CoordinateSpace n :=
  (u.S, u.C, u.D)

def ofCoordinateSpace {n : ℕ} (u : CoordinateSpace n) : ClassCoord n where
  S := u.1
  C := u.2.1
  D := u.2.2

theorem of_toCoordinateSpace {n : ℕ} (u : ClassCoord n) :
    ofCoordinateSpace (toCoordinateSpace u) = u := by
  cases u
  rfl

theorem to_ofCoordinateSpace {n : ℕ} (u : CoordinateSpace n) :
    toCoordinateSpace (ofCoordinateSpace u) = u := by
  rfl

/-- The literal mass-action field restricted to one class, in a normed chart. -/
def restrictedFieldEuclid {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) : CoordinateSpace n :=
  toCoordinateSpace (restrictedField ET FT ST k (ofCoordinateSpace u))

theorem restrictedFieldEuclid_eq_zero_iff {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) :
    restrictedFieldEuclid ET FT ST k u = 0 ↔
      Equilibrium k (unChart ET FT ST (ofCoordinateSpace u)) := by
  rw [equilibrium_iff_restricted]
  simp only [restrictedFieldEuclid, toCoordinateSpace, Prod.mk_eq_zero]
  constructor
  · rintro ⟨hS, hCD⟩
    rcases hCD with ⟨hC, hD⟩
    exact ⟨fun i => congrFun hS i, fun i => congrFun hC i,
      fun i => congrFun hD i⟩
  · rintro ⟨hS, hC, hD⟩
    exact ⟨funext hS, ⟨funext hC, funext hD⟩⟩

@[fun_prop] private theorem differentiable_ite_fixed {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p : Prop) [Decidable p]
    {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun x => if p then f x else g x) := by
  by_cases hp : p <;> simp [hp, hf, hg]

@[fun_prop] private theorem differentiable_fin_cases_fixed {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (i : Fin (n + 1)) {f : E → ℝ} {g : E → (Fin n → ℝ)}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun x => Fin.cases (motive := fun _ => ℝ) (f x) (g x) i) := by
  cases i using Fin.cases with
  | zero => simpa using hf
  | succ j => simpa using (differentiable_pi.mp hg) j

/-- The class-restricted field is a polynomial map in the free coordinates. -/
theorem differentiable_restrictedFieldEuclid {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) : Differentiable ℝ (restrictedFieldEuclid ET FT ST k) := by
  classical
  unfold restrictedFieldEuclid restrictedField toCoordinateSpace chart field
    unChart ofCoordinateSpace kinaseNet phosphataseNet
  dsimp
  fun_prop

/-- The class-restricted Jacobian, as the Fréchet derivative in the affine chart. -/
def restrictedJacobian {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) : CoordinateSpace n →L[ℝ] CoordinateSpace n :=
  fderiv ℝ (restrictedFieldEuclid ET FT ST k) u

/-- The standard basis, ordered by substrate, kinase complex, phosphatase complex. -/
def coordinateBasis (n : ℕ) :
    Basis (Fin n ⊕ (Fin n ⊕ Fin n)) ℝ (CoordinateSpace n) :=
  (Pi.basisFun ℝ (Fin n)).prod
    ((Pi.basisFun ℝ (Fin n)).prod (Pi.basisFun ℝ (Fin n)))

/-- Matrix of the actual class-restricted Fréchet derivative. -/
def restrictedJacobianMatrix {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) :
    Matrix (Fin n ⊕ (Fin n ⊕ Fin n))
      (Fin n ⊕ (Fin n ⊕ Fin n)) ℝ :=
  LinearMap.toMatrix (coordinateBasis n) (coordinateBasis n)
    (restrictedJacobian ET FT ST k u).toLinearMap

/-- Every complex root of the characteristic polynomial lies in the open left half-plane. -/
def IsHurwitz {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Prop :=
  ∀ z : ℂ, ((A.map (algebraMap ℝ ℂ)).charpoly).eval z = 0 → z.re < 0

/-- Linear stability is tested only after restriction to the fixed compatibility class. -/
def IsLinearlyStable {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) : Prop :=
  IsHurwitz (restrictedJacobianMatrix ET FT ST k u)

end
end PhosphorylationStableCapacity
