module
public meta import Lean.Elab.Command
public meta import Lean.Meta.Tactic.AuxLemma
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Set.Card
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.LinearAlgebra.Complex.Module
@[expose] public section
/- Retain the original early Mathlib instance choices outside the original defining modules that use the later C-star, inner-product, or module topology routes. -/
attribute [-instance] CommCStarAlgebra.toNormedCommRing
attribute [-instance] InnerProductSpace.toNormedSpace
attribute [-instance] IsModuleTopology.toContinuousSMul
/- Independent contract assembly. This command only switches elaborator auxiliary-proof caches; it creates or replaces no mathematical declarations. Dormant caches use tagged metadata keys in the existing cache. A string literal, or a string literal applied to a type, cannot be a valid proposition type and therefore cannot collide with a real auxiliary-proof cache key. The actual cache keys and lemma names/universe parameters are preserved. -/
elab "challengeAuxModule " label:str : command => do
  let env ← Lean.getEnv
  let cache := (Lean.Meta.auxLemmasExt.getState env).lemmas
  let marker : Lean.Meta.AuxLemmaKey := {
    type := Lean.mkStrLit "_p079_aux_current_module", isPrivate := false, defeq := false }
  let previous := match cache.find? marker with
    | some (.str .anonymous text, _) => text
    | _ => ""
  let requested := label.getString
  if previous == requested then return
  let mut stored : Lean.PHashMap Lean.Meta.AuxLemmaKey (Lean.Name × List Lean.Name) := {}
  for (key, value) in cache.toList do
    if key == marker then continue
    match key.type with
    | .app (.lit (.strVal _)) _ =>
      stored := stored.insert key value
    | _ => pure ()
  -- Copy dormant entries first, then overwrite them with the newest active
  -- entries. Hash-map iteration order must not select an older cache value.
  for (key, value) in cache.toList do
    if key == marker then continue
    match key.type with
    | .app (.lit (.strVal _)) _ => pure ()
    | _ =>
      if previous != "" then
        stored := stored.insert
          { key with type := Lean.mkApp (Lean.mkStrLit previous) key.type } value
  let mut current := stored
  for (key, value) in stored.toList do
    match key.type with
    | .app (.lit (.strVal owner)) type =>
      if owner == requested then
        current := current.insert { key with type := type } value
    | _ => pure ()
  current := current.insert marker (.str .anonymous requested, [])
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env
    (fun _ => { lemmas := current })
-- Recreate only the proved numeral auxiliaries shared with omitted, unused definitions.
elab "challengeNumeralAux " n:ident k:num : command => do
  let predecessor := Lean.quote (k.getNat - 1)
  Lean.Elab.Command.elabCommand (← `(set_option linter.auxLemma false in theorem $n : Nat.AtLeastTwo ($predecessor + 1) := Nat.instAtLeastTwoHAddOfNat $predecessor))
  let name := (← Lean.getCurrNamespace) ++ n.getId
  let info ← Lean.getConstInfo name
  let key : Lean.Meta.AuxLemmaKey := { type := info.type, isPrivate := false, defeq := false }
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env
    (fun s => { lemmas := s.lemmas.insert key (name, info.levelParams) })
namespace PhosphorylationSharpness
noncomputable section
open scoped BigOperators
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationSharpness/Source.lean"
structure State (n : ℕ) where
  S : Fin (n+1) → ℝ
  E : ℝ
  F : ℝ
  C : Fin n → ℝ
  D : Fin n → ℝ
structure Rates (n : ℕ) where
  a : Fin n → ℝ
  b : Fin n → ℝ
  c : Fin n → ℝ
  alpha : Fin n → ℝ
  beta : Fin n → ℝ
  gamma : Fin n → ℝ
def Rates.Positive {n : ℕ} (k : Rates n) : Prop := ∀ i, 0 < k.a i ∧ 0 < k.b i ∧ 0 < k.c i ∧ 0 < k.alpha i ∧ 0 < k.beta i ∧ 0 < k.gamma i
def State.Positive {n : ℕ} (x : State n) : Prop := (∀ i, 0 < x.S i) ∧ 0 < x.E ∧ 0 < x.F ∧ (∀ i, 0 < x.C i) ∧ (∀ i, 0 < x.D i)
def kinaseNet {n : ℕ} (k : Rates n) (x : State n) (i : Fin n) : ℝ := k.a i*x.S i.castSucc*x.E-k.b i*x.C i
def phosphataseNet {n : ℕ} (k : Rates n) (x : State n) (i : Fin n) : ℝ := k.alpha i*x.S i.succ*x.F-k.beta i*x.D i
def field {n : ℕ} (k : Rates n) (x : State n) : State n where
  S j := ∑ i : Fin n, (
    (if i.castSucc = j then -kinaseNet k x i+k.gamma i*x.D i else 0) +
    (if i.succ = j then k.c i*x.C i-phosphataseNet k x i else 0))
  E := ∑ i, (-kinaseNet k x i+k.c i*x.C i)
  F := ∑ i, (-phosphataseNet k x i+k.gamma i*x.D i)
  C i := kinaseNet k x i-k.c i*x.C i
  D i := phosphataseNet k x i-k.gamma i*x.D i
def Equilibrium {n : ℕ} (k : Rates n) (x : State n) : Prop := (∀ i, (field k x).S i=0) ∧ (field k x).E=0 ∧ (field k x).F=0 ∧ (∀ i, (field k x).C i=0) ∧ (∀ i, (field k x).D i=0)
def totalE {n : ℕ} (x : State n) : ℝ := x.E+∑ i, x.C i
def totalF {n : ℕ} (x : State n) : ℝ := x.F+∑ i, x.D i
def totalS {n : ℕ} (x : State n) : ℝ := (∑ i, x.S i)+(∑ i, x.C i)+(∑ i, x.D i)
end
end PhosphorylationSharpness
namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Filter Module
open scoped Topology BigOperators
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/Compatibility.lean"
def InClass {n : ℕ} (ET FT ST : ℝ) (x : State n) : Prop := totalE x = ET ∧ totalF x = FT ∧ totalS x = ST
structure ClassCoord (n : ℕ) where
  S : Fin n → ℝ
  C : Fin n → ℝ
  D : Fin n → ℝ
def chart {n : ℕ} (x : State n) : ClassCoord n where
  S i := x.S i.succ
  C := x.C
  D := x.D
def unChart {n : ℕ} (ET FT ST : ℝ) (u : ClassCoord n) : State n where
  S := Fin.cases (ST - (∑ i, u.S i) - (∑ i, u.C i) - (∑ i, u.D i)) u.S
  E := ET - ∑ i, u.C i
  F := FT - ∑ i, u.D i
  C := u.C
  D := u.D
def restrictedField {n : ℕ} (ET FT ST : ℝ) (k : Rates n) (u : ClassCoord n) : ClassCoord n := chart (field k (unChart ET FT ST u))
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/Jacobian.lean"
abbrev CoordinateSpace (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)
def toCoordinateSpace {n : ℕ} (u : ClassCoord n) : CoordinateSpace n := (u.S, u.C, u.D)
def ofCoordinateSpace {n : ℕ} (u : CoordinateSpace n) : ClassCoord n where
  S := u.1
  C := u.2.1
  D := u.2.2
def restrictedFieldEuclid {n : ℕ} (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) : CoordinateSpace n := toCoordinateSpace (restrictedField ET FT ST k (ofCoordinateSpace u))
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/LocalAsymptoticStability.lean"
section
/- Match the already verified definition's original Mathlib instances. -/
attribute [local instance 2000] IsModuleTopology.toContinuousSMul
attribute [local instance 2001] instContinuousSMulForall
attribute [local instance 2001] Prod.continuousSMul
def IsForwardClassCurve {n : ℕ} (f : CoordinateSpace n → CoordinateSpace n) (y : CoordinateSpace n) (γ : ℝ → CoordinateSpace n) : Prop := γ 0 = y ∧ ∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt γ (f (γ t)) (Set.Ici (0 : ℝ)) t
end
def IsLocallyAsymptoticallyStableClassField {n : ℕ} (f : CoordinateSpace n → CoordinateSpace n) (x : CoordinateSpace n) : Prop := f x = 0 ∧ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y : CoordinateSpace n, dist y x < δ →
  ∀ γ, IsForwardClassCurve f y γ → ∀ t : ℝ, 0 ≤ t → dist (γ t) x < ε) ∧ (∃ δ : ℝ, 0 < δ ∧ ∀ y : CoordinateSpace n, dist y x < δ → ∀ γ, IsForwardClassCurve f y γ → Tendsto γ atTop (𝓝 x)) ∧ (∃ δ : ℝ, 0 < δ ∧
  ∀ y : CoordinateSpace n, dist y x < δ → ∃ γ, IsForwardClassCurve f y γ)
def IsLocallyAsymptoticallyStableClass {n : ℕ} (ET FT ST : ℝ) (k : Rates n) (x : CoordinateSpace n) : Prop := IsLocallyAsymptoticallyStableClassField (restrictedFieldEuclid ET FT ST k) x
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/NonlinearAttainmentTarget.lean"
def NonlinearlyStableClassAttains (n count : ℕ) : Prop := ∃ (k : Rates n) (ET FT ST : ℝ) (u : Fin count → CoordinateSpace n), k.Positive ∧ 0 < ET ∧ 0 < FT ∧ 0 < ST ∧ Function.Injective u ∧
  ∀ j, (unChart ET FT ST (ofCoordinateSpace (u j))).Positive ∧ IsLocallyAsymptoticallyStableClass ET FT ST k (u j)
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/LocalStableEquilibriumBudget.lean"
def locallyStablePositiveStates {n : ℕ} (ET FT ST : ℝ) (k : Rates n) : Set (State n) := {x | x.Positive ∧ InClass ET FT ST x ∧ IsLocallyAsymptoticallyStableClass ET FT ST k (toCoordinateSpace (chart x))}
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/ExactNonlinearCapacityTarget.lean"
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/ExactCapacity435.lean"
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/Jacobian.lean"
def restrictedJacobian {n : ℕ} (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) : CoordinateSpace n →L[ℝ] CoordinateSpace n := fderiv ℝ (restrictedFieldEuclid ET FT ST k) u
def coordinateBasis (n : ℕ) : Basis (Fin n ⊕ (Fin n ⊕ Fin n)) ℝ (CoordinateSpace n) := (Pi.basisFun ℝ (Fin n)).prod ((Pi.basisFun ℝ (Fin n)).prod (Pi.basisFun ℝ (Fin n)))
def restrictedJacobianMatrix {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) :
    Matrix (Fin n ⊕ (Fin n ⊕ Fin n))
      (Fin n ⊕ (Fin n ⊕ Fin n)) ℝ :=
  LinearMap.toMatrix (coordinateBasis n) (coordinateBasis n)
    (restrictedJacobian ET FT ST k u).toLinearMap
section
/- Match the already verified definition's original Mathlib instances. -/
attribute [local instance 2000] Algebra.complexToReal
def IsHurwitz {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) : Prop := ∀ z : ℂ, ((A.map (algebraMap ℝ ℂ)).charpoly).eval z = 0 → z.re < 0
end
def IsLinearlyStable {n : ℕ} (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) : Prop := IsHurwitz (restrictedJacobianMatrix ET FT ST k u)
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/OddSaddleSpectrum.lean"
section
/- Match the already verified definition's original Mathlib instances. -/
attribute [local instance 2000] CommCStarAlgebra.toNormedCommRing
def IsOneUnstableSaddle {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) : Prop :=
  let A := restrictedJacobianMatrix ET FT ST k u
  ∃ x : ℝ,
    0 < x ∧ A.charpoly.IsRoot x ∧
    ((A.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
    ∀ z : ℂ, z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) →
      z.re < 0 ∨ z = (x : ℂ)
end
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/RationalSplitWitnessAlgebra.lean"
def RationalReal (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x
def RationalRates {n : ℕ} (k : Rates n) : Prop := ∀ i, RationalReal (k.a i) ∧ RationalReal (k.b i) ∧ RationalReal (k.c i) ∧ RationalReal (k.alpha i) ∧ RationalReal (k.beta i) ∧ RationalReal (k.gamma i)
def RationalState {n : ℕ} (x : State n) : Prop := (∀ i, RationalReal (x.S i)) ∧ RationalReal x.E ∧ RationalReal x.F ∧ (∀ i, RationalReal (x.C i)) ∧ (∀ i, RationalReal (x.D i))
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/SplitJacobianContinuity.lean"
abbrev RateVector (n : ℕ) := Fin 6 → Fin n → ℝ
def ratesFromVector {n : ℕ} (v : RateVector n) : Rates n where
  a := v 0
  b := v 1
  c := v 2
  alpha := v 3
  beta := v 4
  gamma := v 5
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/OpenParameterPersistence.lean"
abbrev CapacityParameter (n : ℕ) := RateVector n × (ℝ × ℝ × ℝ)
def capacityParameterField {n : ℕ}
    (q : CapacityParameter n × CoordinateSpace n) : CoordinateSpace n :=
  restrictedFieldEuclid q.1.2.1 q.1.2.2.1 q.1.2.2.2
    (ratesFromVector q.1.1) q.2
section
/- Match the already verified definition's original Mathlib instances. -/
attribute [local instance 2000] CommCStarAlgebra.toNormedCommRing
def IsHyperbolicMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) : Prop := ∀ z : ℂ, z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) → z.re ≠ 0
end
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/StrongCapacity435.lean"
def HyperbolicNonlinearClassAttains (n count : ℕ) : Prop := ∃ (k : Rates n) (ET FT ST : ℝ) (u : Fin count → CoordinateSpace n), k.Positive ∧ 0 < ET ∧ 0 < FT ∧ 0 < ST ∧ Function.Injective u ∧
  ∀ j, (unChart ET FT ST (ofCoordinateSpace (u j))).Positive ∧ restrictedFieldEuclid ET FT ST k (u j) = 0 ∧ IsLinearlyStable ET FT ST k (u j) ∧ IsLocallyAsymptoticallyStableClass ET FT ST k (u j)
def FullFamilyWithHyperbolicSinks (n : ℕ) : Prop := ∃ (k : Rates n) (ET FT ST : ℝ) (u : Fin (2*n-1) → CoordinateSpace n), k.Positive ∧ 0 < ET ∧ 0 < FT ∧ 0 < ST ∧ Function.Injective u ∧
  (∀ j, (unChart ET FT ST (ofCoordinateSpace (u j))).Positive ∧ restrictedFieldEuclid ET FT ST k (u j) = 0) ∧ ∀ i : Fin n, ∃ j : Fin (2*n-1), j.val = 2*i.val ∧ IsLinearlyStable ET FT ST k (u j) ∧
  IsLocallyAsymptoticallyStableClass ET FT ST k (u j)
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/RationalConfiguration435.lean"
def RationalFullFamilyWithSinksAndSaddles (n : ℕ) : Prop := ∃ (k : Rates n) (ET FT ST : ℝ) (u : Fin (2*n-1) → CoordinateSpace n), RationalRates k ∧ RationalReal ET ∧ RationalReal FT ∧ RationalReal ST ∧
  k.Positive ∧ 0 < ET ∧ 0 < FT ∧ 0 < ST ∧ Function.Injective u ∧ (∀ j, RationalState (unChart ET FT ST (ofCoordinateSpace (u j))) ∧ (unChart ET FT ST (ofCoordinateSpace (u j))).Positive ∧
  restrictedFieldEuclid ET FT ST k (u j) = 0) ∧ (∀ i : Fin n, ∃ j : Fin (2*n-1), j.val = 2*i.val ∧ IsLinearlyStable ET FT ST k (u j) ∧ IsLocallyAsymptoticallyStableClass ET FT ST k (u j)) ∧
  (∀ j : Fin (2*n-1), Odd j.val → IsOneUnstableSaddle ET FT ST k (u j)) ∧ {x : State n | x.Positive ∧ Equilibrium k x ∧ InClass ET FT ST x} = Set.range (fun j : Fin (2*n-1) =>
  unChart ET FT ST (ofCoordinateSpace (u j))) ∧ {x : State n | x.Positive ∧ Equilibrium k x ∧ InClass ET FT ST x}.ncard = 2*n-1
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/OpenParameterPersistence.lean"
def OpenFullHyperbolicFamily (n : ℕ) : Prop := ∃ s : Set (CapacityParameter n), IsOpen s ∧ (∃ p₀ ∈ s, RationalRates (ratesFromVector p₀.1) ∧ RationalReal p₀.2.1 ∧ RationalReal p₀.2.2.1 ∧ RationalReal p₀.2.2.2 ∧
  ∃ x₀ : Fin (2*n-1) → CoordinateSpace n, Function.Injective x₀ ∧ (∀ j, RationalState (unChart p₀.2.1 p₀.2.2.1 p₀.2.2.2 (ofCoordinateSpace (x₀ j))) ∧ (unChart p₀.2.1 p₀.2.2.1 p₀.2.2.2
  (ofCoordinateSpace (x₀ j))).Positive ∧ capacityParameterField (p₀, x₀ j) = 0) ∧ (∀ j : Fin (2*n-1), Odd j.val → IsOneUnstableSaddle p₀.2.1 p₀.2.2.1 p₀.2.2.2 (ratesFromVector p₀.1) (x₀ j))) ∧ ∀ p ∈ s,
  ((ratesFromVector p.1).Positive ∧ 0 < p.2.1 ∧ 0 < p.2.2.1 ∧ 0 < p.2.2.2) ∧ ∃ x : Fin (2*n-1) → CoordinateSpace n, Function.Injective x ∧ (∀ j, (unChart p.2.1 p.2.2.1 p.2.2.2 (ofCoordinateSpace (x j))).Positive ∧
  capacityParameterField (p, x j) = 0 ∧ IsHyperbolicMatrix (restrictedJacobianMatrix p.2.1 p.2.2.1 p.2.2.2 (ratesFromVector p.1) (x j)) ∧ (Even j.val → IsLinearlyStable p.2.1 p.2.2.1 p.2.2.2 (ratesFromVector p.1) (x j) ∧
  IsLocallyAsymptoticallyStableClass p.2.1 p.2.2.1 p.2.2.2 (ratesFromVector p.1) (x j)) ∧ (Odd j.val → IsOneUnstableSaddle p.2.1 p.2.2.1 p.2.2.2 (ratesFromVector p.1) (x j))) ∧ {y : State n | y.Positive ∧
  Equilibrium (ratesFromVector p.1) y ∧ InClass p.2.1 p.2.2.1 p.2.2.2 y} = Set.range (fun j : Fin (2*n-1) => unChart p.2.1 p.2.2.1 p.2.2.2 (ofCoordinateSpace (x j))) ∧ {y : State n | y.Positive ∧
  Equilibrium (ratesFromVector p.1) y ∧ InClass p.2.1 p.2.2.1 p.2.2.2 y}.ncard = 2*n-1
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/StrongCapacity435.lean"
def ExactCapacityWithHyperbolicAttainment (n : ℕ) : Prop := HyperbolicNonlinearClassAttains n n ∧ ∀ (ET FT ST : ℝ), 0 < ET → 0 < FT → 0 < ST → ∀ (k : Rates n), k.Positive →
  (locallyStablePositiveStates ET FT ST k).Finite ∧ (locallyStablePositiveStates ET FT ST k).ncard ≤ n
end
end PhosphorylationStableCapacity
namespace PhosphorylationStableCapacity
noncomputable section
open Matrix PhosphorylationSharpness Set
open scoped BigOperators
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/ScaledIntegerMatrixCertificates.lean"
structure ScaledIntegerMatrix (ι κ : Type*) where
  denominator : ℕ
  entries : Matrix ι κ ℤ
def ScaledIntegerMatrix.realMatrix {ι κ : Type*} (A : ScaledIntegerMatrix ι κ) : Matrix ι κ ℝ := (A.denominator : ℝ)⁻¹ • A.entries.map (Int.castRingHom ℝ)
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/OperationalCoordinateMaps.lean"
def operationalUnpack (q : Fin 9 → ℝ) : CoordinateSpace 3 := (![q 0,q 1,q 2], (![q 3,q 4,q 5], ![q 6,q 7,q 8]))
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/OperationalCoordinateMaps.lean"
def operationalFlatten (u : CoordinateSpace 3) : Fin 9 → ℝ := ![u.1 0,u.1 1,u.1 2,u.2.1 0,u.2.1 1,u.2.1 2, u.2.2 0,u.2.2 1,u.2.2 2]
def operationalProjection (i : Fin 9) : (Fin 9 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
def operationalLift (s : Fin 9 → ℝ) : (Fin 9 → ℝ) →L[ℝ] CoordinateSpace 3 := (ContinuousLinearMap.pi ![s 0 • operationalProjection 0, s 1 • operationalProjection 1,s 2 • operationalProjection 2]).prod ((ContinuousLinearMap.pi ![s 3 • operationalProjection 3, s 4 • operationalProjection 4,s 5 • operationalProjection 5]).prod (ContinuousLinearMap.pi ![s 6 • operationalProjection 6, s 7 • operationalProjection 7,s 8 • operationalProjection 8]))
def operationalReadS (i : Fin 3) : CoordinateSpace 3 →L[ℝ] ℝ := ((ContinuousLinearMap.proj i) : (Fin 3 → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) ((Fin 3 → ℝ) × (Fin 3 → ℝ)))
def operationalReadC (i : Fin 3) : CoordinateSpace 3 →L[ℝ] ℝ := ((ContinuousLinearMap.proj i) : (Fin 3 → ℝ) →L[ℝ] ℝ).comp ((ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) (Fin 3 → ℝ)).comp (ContinuousLinearMap.snd ℝ (Fin 3 → ℝ) ((Fin 3 → ℝ) × (Fin 3 → ℝ))))
def operationalReadD (i : Fin 3) : CoordinateSpace 3 →L[ℝ] ℝ := ((ContinuousLinearMap.proj i) : (Fin 3 → ℝ) →L[ℝ] ℝ).comp ((ContinuousLinearMap.snd ℝ (Fin 3 → ℝ) (Fin 3 → ℝ)).comp (ContinuousLinearMap.snd ℝ (Fin 3 → ℝ) ((Fin 3 → ℝ) × (Fin 3 → ℝ))))
def operationalRead (s : Fin 9 → ℝ) : CoordinateSpace 3 →L[ℝ] (Fin 9 → ℝ) := ContinuousLinearMap.pi ![ (s 0)⁻¹ • operationalReadS 0,(s 1)⁻¹ • operationalReadS 1,(s 2)⁻¹ • operationalReadS 2, (s 3)⁻¹ • operationalReadC 0,(s 4)⁻¹ • operationalReadC 1,(s 5)⁻¹ • operationalReadC 2, (s 6)⁻¹ • operationalReadD 0,(s 7)⁻¹ • operationalReadD 1,(s 8)⁻¹ • operationalReadD 2]
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/FiniteThreeSiteFieldFormula.lean"
def threeSiteFreeS0 (ST : ℝ) (u : CoordinateSpace 3) : ℝ := ST - u.1 0 - u.1 1 - u.1 2 - u.2.1 0 - u.2.1 1 - u.2.1 2 - u.2.2 0 - u.2.2 1 - u.2.2 2
def threeSiteFreeE (ET : ℝ) (u : CoordinateSpace 3) : ℝ := ET - u.2.1 0 - u.2.1 1 - u.2.1 2
def threeSiteFreeF (FT : ℝ) (u : CoordinateSpace 3) : ℝ := FT - u.2.2 0 - u.2.2 1 - u.2.2 2
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/OperationalAffineExpressions.lean"
def operationalSpeciesLinear (s : Fin 9 → ℚ) : Matrix (Fin 12) (Fin 9) ℚ := Matrix.of ![![-s 0,-s 1,-s 2,-s 3,-s 4,-s 5,-s 6,-s 7,-s 8], ![s 0,0,0,0,0,0,0,0,0], ![0,s 1,0,0,0,0,0,0,0], ![0,0,s 2,0,0,0,0,0,0], ![0,0,0,-s 3,-s 4,-s 5,0,0,0], ![0,0,0,0,0,0,-s 6,-s 7,-s 8], ![0,0,0,s 3,0,0,0,0,0], ![0,0,0,0,s 4,0,0,0,0], ![0,0,0,0,0,s 5,0,0,0], ![0,0,0,0,0,0,s 6,0,0], ![0,0,0,0,0,0,0,s 7,0], ![0,0,0,0,0,0,0,0,s 8]]
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/OperationalReactionExpressions.lean"
def operationalReactionFirst : Fin 18 → Fin 12 := ![0,6,6,1,9,9,1,7,7,2,10,10,2,8,8,3,11,11]
def operationalReactionSecond : Fin 18 → Option (Fin 12) := ![some 4,none,none,some 5,none,none, some 4,none,none,some 5,none,none, some 4,none,none,some 5,none,none]
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/OperationalWeightedCoordinates.lean"
def operationalParameterRates (θ : Fin 21 → ℝ) : Rates 3 where
  a := ![θ 0,θ 6,θ 12]
  b := ![θ 1,θ 7,θ 13]
  c := ![θ 2,θ 8,θ 14]
  alpha := ![θ 3,θ 9,θ 15]
  beta := ![θ 4,θ 10,θ 16]
  gamma := ![θ 5,θ 11,θ 17]
def operationalWeightedField (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) : Fin 9 → ℝ := operationalRead s (restrictedFieldEuclid (θ 18) (θ 19) (θ 20) (operationalParameterRates θ) (operationalUnpack q+operationalLift s w))
def operationalWeightedJacobian (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) : (Fin 9 → ℝ) →L[ℝ] (Fin 9 → ℝ) := (operationalRead s).comp ((restrictedJacobian (θ 18) (θ 19) (θ 20) (operationalParameterRates θ) (operationalUnpack q+operationalLift s w)).comp (operationalLift s))
def operationalSpecies (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ)
    (w : Fin 9 → ℝ) : Fin 12 → ℝ :=
  let u := operationalUnpack q + operationalLift s w
  ![threeSiteFreeS0 (θ 20) u, u.1 0, u.1 1, u.1 2,
    threeSiteFreeE (θ 18) u, threeSiteFreeF (θ 19) u,
    u.2.1 0, u.2.1 1, u.2.1 2, u.2.2 0, u.2.2 1, u.2.2 2]
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/OperationalWeightedCoordinates.lean"
def operationalStoichiometry : Matrix (Fin 9) (Fin 18) ℚ := Matrix.of ![![0,0,1,-1,1,0,-1,1,0,0,0,1,0,0,0,0,0,0], ![0,0,0,0,0,0,0,0,1,-1,1,0,-1,1,0,0,0,1], ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,1,0], ![1,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], ![0,0,0,0,0,0,1,-1,-1,0,0,0,0,0,0,0,0,0], ![0,0,0,0,0,0,0,0,0,0,0,0,1,-1,-1,0,0,0], ![0,0,0,1,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0], ![0,0,0,0,0,0,0,0,0,1,-1,-1,0,0,0,0,0,0], ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,-1]]
def operationalReactionDerivative (θ : Fin 21 → ℝ) (x : Fin 12 → ℝ)
    (T : Matrix (Fin 12) (Fin 9) ℝ) (a : Fin 18) (j : Fin 9) : ℝ :=
  let rate := θ (Fin.castAdd 3 a)
  let first := operationalReactionFirst a
  match operationalReactionSecond a with
  | none => rate*T first j
  | some b => rate*(x first*T b j+x b*T first j)
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/OperationalWeightedCoordinates.lean"
def operationalWeightedStoichiometry (s : Fin 9 → ℝ) : Matrix (Fin 9) (Fin 18) ℝ := fun i a => (operationalStoichiometry i a : ℝ) / s i
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/OperationalCertificateAlgebra.lean"
def matrixSupContinuousMap {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℝ) : (κ → ℝ) →L[ℝ] (ι → ℝ) := ContinuousLinearMap.pi (fun i => ∑ j, M i j • (ContinuousLinearMap.proj j : (κ → ℝ) →L[ℝ] ℝ))
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/FiniteEuclideanLength.lean"
def finiteEuclideanLength {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ := Real.sqrt (∑ i, v i^2)
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/OperationalCertifiedModel.lean"
section
/- Match the already verified definition's original Mathlib instances. -/
attribute [local instance 2000] IsModuleTopology.toContinuousSMul
attribute [local instance 2001] instContinuousSMulForall
attribute [local instance 2001] Prod.continuousSMul
def IsOperationalPhysicalCurve (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ) (initial : Fin 9 → ℝ) (γ : ℝ → Fin 9 → ℝ) : Prop := γ 0 = initial ∧ ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt γ ((1/10 : ℝ) • operationalWeightedField q s θ (γ t)) (Ici (0 : ℝ)) t
end
def operationalPhysicalParameters (θ : Fin 21 → ℝ) : Fin 21 → ℝ := fun i => if i.val < 18 ∧ i.val % 3 = 0 then θ i else θ i/10
def operationalReactionJacobian (q s : Fin 9 → ℚ) (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) : Matrix (Fin 9) (Fin 9) ℝ := operationalWeightedStoichiometry (fun i => (s i : ℝ)) * (Matrix.of fun a j => operationalReactionDerivative θ (operationalSpecies (fun i => (q i : ℝ)) (fun i => (s i : ℝ)) θ w) (fun i j => (operationalSpeciesLinear s i j : ℝ)) a j)
def operationalPhysicalState (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ)
    (w : Fin 9 → ℝ) : State 3 :=
  let φ := operationalPhysicalParameters θ
  unChart (φ 18) (φ 19) (φ 20)
    (ofCoordinateSpace (operationalUnpack (fun i => q i/10)+
      operationalLift (fun i => s i/10) w))
def operationalPhysicalReadout (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ)
    (w : Fin 9 → ℝ) : ℝ :=
  let x := unChart (θ 18) (θ 19) (θ 20)
    (ofCoordinateSpace (operationalUnpack q+operationalLift s w))
  (1/10 : ℝ)*(x.S 3+x.D 2)
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/OperationalSinkOutcome.lean"
section
/- Match the already verified definition's original Mathlib instances. -/
attribute [local instance 2000] InnerProductSpace.toNormedSpace
attribute [local instance 2000] RCLike.toInnerProductSpaceReal
structure OperationalNominalLyapunovData (q s : Fin 9 → ℚ) (nominal : Fin 21 → ℚ)
    (P Q Qinv : Matrix (Fin 9) (Fin 9) ℝ) (c loss : ℝ) : Prop where
  actual_nominal_form : Q =
    -((operationalReactionJacobian q s (fun i => (nominal i : ℝ)) 0).transpose*P +
      P*operationalReactionJacobian q s (fun i => (nominal i : ℝ)) 0)
  positive_definite : Q.PosDef
  exact_inverse : Q*Qinv = 1
  decay_formula : c = 1/‖matrixSupContinuousMap Qinv‖-loss
  decay_positive : 0 < c
end
def OperationalRecoveryConclusion (equilibrium : Fin 9 → ℝ) (ρ c M recoveryTime : ℝ) (γ : ℝ → Fin 9 → ℝ) : Prop := (∀ t : ℝ, 0 ≤ t → ‖γ t‖ < ρ) ∧ (∀ t : ℝ, 0 ≤ t → finiteEuclideanLength (γ t-equilibrium) ≤ (ρ/2)*Real.exp (-(c/(2*M))*(t/10))) ∧ (∀ t : ℝ, recoveryTime ≤ t → finiteEuclideanLength (γ t-equilibrium) < ρ/20)
section
/- Match the already verified definition's original Mathlib instances. -/
attribute [local instance 2000] InnerProductSpace.toNormedSpace
attribute [local instance 2000] RCLike.toInnerProductSpaceReal
structure OperationalSinkOutcome (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ)
    (P : Matrix (Fin 9) (Fin 9) ℝ) (ρ ρin p c M recoveryTime lower upper : ℝ)
    (equilibrium : Fin 9 → ℝ) : Prop where
  physical_parameters_positive : ∀ i, 0 < operationalPhysicalParameters θ i
  physical_species_positive_in_box : ∀ w : Fin 9 → ℝ, ‖w‖ ≤ ρ →
    (operationalPhysicalState q s θ w).Positive
  positive_definite : P.PosDef
  rational_matrix : ∀ i j, ∃ a : ℚ, (a : ℝ) = P i j
  operator_norm : ‖matrixSupContinuousMap P‖ = M
  lower_constant_positive : 0 < p
  decay_positive : 0 < c
  quadratic_lower : ∀ v : Fin 9 → ℝ, p*(∑ i, v i^2) ≤ v ⬝ᵥ (P *ᵥ v)
  quadratic_upper : ∀ v : Fin 9 → ℝ, v ⬝ᵥ (P *ᵥ v) ≤ M*(∑ i, v i^2)
  actual_uniform_dissipation : ∀ w : Fin 9 → ℝ, ‖w‖ ≤ ρ →
    ∀ v : Fin 9 → ℝ, 2*(v ⬝ᵥ (P *ᵥ (operationalWeightedJacobian q s θ w v))) ≤
      -c*(∑ i, v i^2)
  shift : ‖equilibrium‖ ≤ ρ/4
  zero : operationalWeightedField q s θ equilibrium = 0
  positive : (operationalPhysicalState q s θ equilibrium).Positive
  physical_equilibrium : Equilibrium
    (operationalParameterRates (operationalPhysicalParameters θ))
      (operationalPhysicalState q s θ equilibrium)
  physical_class : InClass (operationalPhysicalParameters θ 18)
    (operationalPhysicalParameters θ 19) (operationalPhysicalParameters θ 20)
    (operationalPhysicalState q s θ equilibrium)
  unique_in_box : ∀ v : Fin 9 → ℝ, ‖v‖ ≤ ρ →
    operationalWeightedField q s θ v = 0 → v = equilibrium
  measured_readout : ∀ measurement : ℝ, |measurement| ≤ (1/1000 : ℝ) →
    lower ≤ operationalPhysicalReadout q s θ equilibrium+measurement ∧
      operationalPhysicalReadout q s θ equilibrium+measurement ≤ upper
  inner_recovery : ∀ initial : Fin 9 → ℝ,
    (∑ i, (initial i-equilibrium i)^2) ≤ ρin^2 →
    (∃ γ : ℝ → Fin 9 → ℝ, IsOperationalPhysicalCurve q s θ initial γ) ∧
    ∀ γ : ℝ → Fin 9 → ℝ, IsOperationalPhysicalCurve q s θ initial γ →
      OperationalRecoveryConclusion equilibrium ρ c M recoveryTime γ
  closed_ellipsoid_recovery : ∀ initial : Fin 9 → ℝ,
    (initial-equilibrium) ⬝ᵥ (P *ᵥ (initial-equilibrium)) ≤ p*(ρ/2)^2 →
    (∃ γ : ℝ → Fin 9 → ℝ, IsOperationalPhysicalCurve q s θ initial γ) ∧
    ∀ γ : ℝ → Fin 9 → ℝ, IsOperationalPhysicalCurve q s θ initial γ →
      (∀ t : ℝ, 0 ≤ t → (γ t-equilibrium) ⬝ᵥ
        (P *ᵥ (γ t-equilibrium)) ≤ p*(ρ/2)^2) ∧
      OperationalRecoveryConclusion equilibrium ρ c M recoveryTime γ
end
def OperationalPrintedSinkOutcome (q s : Fin 9 → ℚ) (nominal : Fin 21 → ℚ) (θ : Fin 21 → ℝ) (P : Matrix (Fin 9) (Fin 9) ℝ) (ρ ρin p c M recoveryTime lower upper loss : ℝ) (equilibrium : Fin 9 → ℝ) : Prop := ∃ Q Qinv : Matrix (Fin 9) (Fin 9) ℝ, OperationalNominalLyapunovData q s (fun i => nominal i) P Q Qinv c loss ∧ OperationalSinkOutcome (fun i => (q i : ℝ)) (fun i => (s i : ℝ)) θ P ρ ρin p c M recoveryTime lower upper equilibrium
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/OperationalLiteralPhysicalRecovery.lean"
section
/- Keep pointwise/product continuity above the scalar module-topology route. -/
attribute [local instance 2000] IsModuleTopology.toContinuousSMul
attribute [local instance 2001] instContinuousSMulForall
attribute [local instance 2001] Prod.continuousSMul
def IsOperationalLiteralPhysicalCurve (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ) (initial : Fin 9 → ℝ) (γ : ℝ → Fin 9 → ℝ) : Prop := γ 0 = initial ∧ ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt γ (operationalWeightedField (fun i => q i/10) (fun i => s i/10) (operationalPhysicalParameters θ) (γ t)) (Ici (0 : ℝ)) t
end
def OperationalLiteralPhysicalRecovery (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ) (P : Matrix (Fin 9) (Fin 9) ℝ) (ρ ρin p c M recoveryTime : ℝ) (equilibrium : Fin 9 → ℝ) : Prop := (∀ initial : Fin 9 → ℝ, (∑ i, (initial i-equilibrium i)^2) ≤ ρin^2 → (∃ γ : ℝ → Fin 9 → ℝ, IsOperationalLiteralPhysicalCurve q s θ initial γ) ∧ ∀ γ : ℝ → Fin 9 → ℝ, IsOperationalLiteralPhysicalCurve q s θ initial γ → OperationalRecoveryConclusion equilibrium ρ c M recoveryTime γ) ∧ (∀ initial : Fin 9 → ℝ, (initial-equilibrium) ⬝ᵥ (P *ᵥ (initial-equilibrium)) ≤ p*(ρ/2)^2 → (∃ γ : ℝ → Fin 9 → ℝ, IsOperationalLiteralPhysicalCurve q s θ initial γ) ∧ ∀ γ : ℝ → Fin 9 → ℝ, IsOperationalLiteralPhysicalCurve q s θ initial γ → (∀ t : ℝ, 0 ≤ t → (γ t-equilibrium) ⬝ᵥ (P *ᵥ (γ t-equilibrium)) ≤ p*(ρ/2)^2) ∧ OperationalRecoveryConclusion equilibrium ρ c M recoveryTime γ)
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/BenchmarkOperationalIntervalZero.lean"
def operationalZeroIntervalNominal : Fin 30 → ℚ := ![(2/1 : ℚ), (2561356061/42962538673466 : ℚ), (23614054870423099379/1196662741996490128512 : ℚ), (7051250727309545389200260/41021787130284170515591497 : ℚ), (32243543687792426/75463699179943029 : ℚ), (42833130699194/21481269336733 : ℚ), (1850056872394595934523465378312/989996000917120571045749950607 : ℚ), (1562760173497930/199539510868912837 : ℚ), (47508880452187522835105892/291467450611351315929492199 : ℚ), (235395971596073829481109385678/117918371998374931344888363875 : ℚ), (50075904370247184/186779636882893435 : ℚ), (376304202426012366/196059545236362091 : ℚ), (27607712325255743002783032/126732220442230611250455425 : ℚ), (206960131084861/1632576469591708 : ℚ), (34120037836851215351993/89038971023625546753883 : ℚ), (1888280435603197004985/944140432152952132667 : ℚ), (26718975290670014/210323108075952803 : ℚ), (180608615618770229/96429418052594437 : ℚ), (18/1 : ℚ), (2/1 : ℚ), (20/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ)]
def operationalZeroIntervalCoordinates : Fin 9 → ℚ := ![(543596293/469538300 : ℚ), (8300517/18781532 : ℚ), (1700253/117384575 : ℚ), (37138176/3353845 : ℚ), (1486627189/234769150 : ℚ), (11080308/117384575 : ℚ), (100237/914685 : ℚ), (63125631/117384575 : ℚ), (2267004/117384575 : ℚ)]
def operationalZeroIntervalScales : Fin 9 → ℚ := ![(543596293/469538300 : ℚ), (8300517/18781532 : ℚ), (1700253/117384575 : ℚ), (37138176/3353845 : ℚ), (1486627189/234769150 : ℚ), (11080308/117384575 : ℚ), (100237/914685 : ℚ), (63125631/117384575 : ℚ), (2267004/117384575 : ℚ)]
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/BenchmarkOperationalInverseZero.lean"
def operationalZeroP : ScaledIntegerMatrix (Fin 9) (Fin 9) where
  denominator := 1000000
  entries := ![ ![112661611, 51349347, 1965123, -103222912, 655446676, 12661935, 3232380, 60139597, 2533344], ![51349347, 24111614, 973359, -51142596, 298749342, 6578792, 1447892, 27844250, 1203443], ![1965123, 973359, 316435, -2624815, 11095595, 555891, 64127, 1111065, 170196], ![-103222912, -51142596, -2624815, 144160577, -599986329, -19358117, -2786361, -57837682, -2882712], ![655446676, 298749342, 11095595, -599986329, 3827390024, 70251111, 18267626, 350334111, 14590590], ![12661935, 6578792, 555891, -19358117, 70251111, 3970105, 425507, 7217955, 468240], ![3232380, 1447892, 64127, -2786361, 18267626, 425507, 282121, 1665299, 69179], ![60139597, 27844250, 1111065, -57837682, 350334111, 7217955, 1665299, 32552476, 1366907], ![2533344, 1203443, 170196, -2882712, 14590590, 468240, 69179, 1366907, 319373] ]
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/BenchmarkOperationalNormZero.lean"
def operationalZeroPRowBound : ℚ := (1461527851/250000 : ℚ)
def operationalZeroDecayMargin : ℚ := (145328706557919795738200856652951977017906713348296860215415578415070659372549966905706916126497068518796501570986655871171030380578575525468020010699522030388281656686731039503788471774227646587932242542009158882939856627805511725142898028807245900895900601403855446869234183163639600499077498724723533291287783039058223737167908907669692425427927980479981305315509520136641719800106586798633287/147518187717985264629029662871450618248297804654867439360424533064196965264232620940555528919100246603253139536304228791805554875655870391721042474498140050757606931496157285101009613438702403145840099756586334344176951797052448987570758761747296683351880455610313709240839881864807535774833312099179458870266117962264125303783964746002232474758026570409199588515600429133437337600000000000000000 : ℚ)
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/BenchmarkOperationalIntervalTwo.lean"
def operationalTwoIntervalNominal : Fin 30 → ℚ := ![(2/1 : ℚ), (2561356061/42962538673466 : ℚ), (23614054870423099379/1196662741996490128512 : ℚ), (7051250727309545389200260/41021787130284170515591497 : ℚ), (32243543687792426/75463699179943029 : ℚ), (42833130699194/21481269336733 : ℚ), (1850056872394595934523465378312/989996000917120571045749950607 : ℚ), (1562760173497930/199539510868912837 : ℚ), (47508880452187522835105892/291467450611351315929492199 : ℚ), (235395971596073829481109385678/117918371998374931344888363875 : ℚ), (50075904370247184/186779636882893435 : ℚ), (376304202426012366/196059545236362091 : ℚ), (27607712325255743002783032/126732220442230611250455425 : ℚ), (206960131084861/1632576469591708 : ℚ), (34120037836851215351993/89038971023625546753883 : ℚ), (1888280435603197004985/944140432152952132667 : ℚ), (26718975290670014/210323108075952803 : ℚ), (180608615618770229/96429418052594437 : ℚ), (18/1 : ℚ), (2/1 : ℚ), (20/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ)]
def operationalTwoIntervalCoordinates : Fin 9 → ℚ := ![(1087192586/1988871157 : ℚ), (3320206800/1988871157 : ℚ), (870529536/1988871157 : ℚ), (742763520/284124451 : ℚ), (23786035024/1988871157 : ℚ), (2836558848/1988871157 : ℚ), (22052140/852373353 : ℚ), (2020020192/1988871157 : ℚ), (580353024/1988871157 : ℚ)]
def operationalTwoIntervalScales : Fin 9 → ℚ := ![(1087192586/1988871157 : ℚ), (3320206800/1988871157 : ℚ), (870529536/1988871157 : ℚ), (742763520/284124451 : ℚ), (23786035024/1988871157 : ℚ), (2836558848/1988871157 : ℚ), (22052140/852373353 : ℚ), (2020020192/1988871157 : ℚ), (580353024/1988871157 : ℚ)]
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/BenchmarkOperationalInverseTwo.lean"
def operationalTwoP : ScaledIntegerMatrix (Fin 9) (Fin 9) where
  denominator := 1000000
  entries := ![ ![714443230, 2487094744, 721894679, -15062441, 15907920873, 2223936565, 8856741, 1472319032, 476128347], ![2487094744, 8663740980, 2515385139, -53079367, 55390959819, 7747805978, 30541579, 5128138423, 1658984104], ![721894679, 2515385139, 731070774, -15512806, 16077668458, 2250046521, 8861199, 1488837653, 481935877], ![-15062441, -53079367, -15512806, 565834, -337271974, -47574567, -144485, -31352295, -10226525], ![15907920873, 55390959819, 16077668458, -337271974, 354278237925, 49527627430, 195741624, 32789965605, 10604491898], ![2223936565, 7747805978, 2250046521, -47574567, 49527627430, 6930347023, 27384264, 4585861205, 1483823612], ![8856741, 30541579, 8861199, -144485, 195741624, 27384264, 309023, 18038610, 5817781], ![1472319032, 5128138423, 1488837653, -31352295, 32789965605, 4585861205, 18038610, 3035645517, 981872044], ![476128347, 1658984104, 481935877, -10226525, 10604491898, 1483823612, 5817781, 981872044, 317961835] ]
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/BenchmarkOperationalNormTwo.lean"
def operationalTwoPRowBound : ℚ := (267554942803/500000 : ℚ)
def operationalTwoDecayMargin : ℚ := (2313420339089540192561208978756556878652132333783377953977603237309733852100519015643643880949575727617939337589710945882233864690643091334453384923329461471309539060259439463862583634237265311178207991671970124297000712496016409172492231098762644568365016468017855760446206638257993793024276551843986844268013585858308908996828547066676913655720639507834006074512307335229863958871689631417751859416013479/2371834886972293759807356663340487578848094772830564478699949075620927899269630752084563379314149251945105737883692422216313142888340473333639154054712602729861383804113812612901146974517873148383968023918225436596139463664037998797598263048494918468334179369652401438989145016876614416422302191863415327731624349350418221107831806668042560930943823284832902024714881512569532020809741107200000000000000000 : ℚ)
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/BenchmarkOperationalIntervalFour.lean"
def operationalFourIntervalNominal : Fin 30 → ℚ := ![(2/1 : ℚ), (2561356061/42962538673466 : ℚ), (23614054870423099379/1196662741996490128512 : ℚ), (7051250727309545389200260/41021787130284170515591497 : ℚ), (32243543687792426/75463699179943029 : ℚ), (42833130699194/21481269336733 : ℚ), (1850056872394595934523465378312/989996000917120571045749950607 : ℚ), (1562760173497930/199539510868912837 : ℚ), (47508880452187522835105892/291467450611351315929492199 : ℚ), (235395971596073829481109385678/117918371998374931344888363875 : ℚ), (50075904370247184/186779636882893435 : ℚ), (376304202426012366/196059545236362091 : ℚ), (27607712325255743002783032/126732220442230611250455425 : ℚ), (206960131084861/1632576469591708 : ℚ), (34120037836851215351993/89038971023625546753883 : ℚ), (1888280435603197004985/944140432152952132667 : ℚ), (26718975290670014/210323108075952803 : ℚ), (180608615618770229/96429418052594437 : ℚ), (18/1 : ℚ), (2/1 : ℚ), (20/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ), (0/1 : ℚ)]
def operationalFourIntervalCoordinates : Fin 9 → ℚ := ![(543596293/2004214940 : ℚ), (124507755/57263284 : ℚ), (107115939/71579105 : ℚ), (12379392/14315821 : ℚ), (1486627189/143158210 : ℚ), (232686468/71579105 : ℚ), (1102607/128842389 : ℚ), (63125631/71579105 : ℚ), (47607084/71579105 : ℚ)]
def operationalFourIntervalScales : Fin 9 → ℚ := ![(543596293/2004214940 : ℚ), (124507755/57263284 : ℚ), (107115939/71579105 : ℚ), (12379392/14315821 : ℚ), (1486627189/143158210 : ℚ), (232686468/71579105 : ℚ), (1102607/128842389 : ℚ), (63125631/71579105 : ℚ), (47607084/71579105 : ℚ)]
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/BenchmarkOperationalInverseFour.lean"
def operationalFourP : ScaledIntegerMatrix (Fin 9) (Fin 9) where
  denominator := 1000000
  entries := ![ ![130811439, 1181735963, 882694257, -67163, 5047759858, 1820946261, 1083228, 466064535, 391749829], ![1181735963, 10690408277, 7988266277, -745824, 45634178032, 16474214264, 9252308, 4215299411, 3545532666], ![882694257, 7988266277, 5971974963, -589163, 34087425345, 12311859574, 6873156, 3149605682, 2650392573], ![-67163, -745824, -589163, 74077, -3018679, -1160464, 6900, -284799, -266187], ![5047759858, 45634178032, 34087425345, -3018679, 194915140609, 70314902063, 39813928, 17996615672, 15129638847], ![1820946261, 16474214264, 12311859574, -1160464, 70314902063, 25389534202, 14356741, 6495751337, 5464339804], ![1083228, 9252308, 6873156, 6900, 39813928, 14356741, 212520, 3613580, 2979683], ![466064535, 4215299411, 3149605682, -284799, 17996615672, 6495751337, 3613580, 1662355817, 1397843498], ![391749829, 3545532666, 2650392573, -266187, 15129638847, 5464339804, 2979683, 1397843498, 1176481752] ]
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/BenchmarkOperationalNormFour.lean"
def operationalFourPRowBound : ℚ := (383168493033/1000000 : ℚ)
def operationalFourDecayMargin : ℚ := (390391618960160560848407330506436102114539076028171632905800972471658874124172427557686801503784664104351904762226836122673373930778307533649171765975183222533224810177025240176172054706813283787235201336323362346879785134133858998951511585538531590850128524479152036179478524190177139141100505093626053667549304744618008693609886598680472583430200524459893820003559169405399541797046566680347643819/397905262913780449054944299661547063862403588391038724741018604082590549329007434883146588782394115748134894419481894824607627478457439971670653869033010226804262120084226044390136808097138614088760037713211328967275899787021273788293864738683900976805929970791949664238890281526317678471063484088179828894023803261912877092341144466099570260741641883465218500370410610597023029657600000000000000000 : ℚ)
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/FiniteThreeSiteOperationalNominalBridge.lean"
def benchmarkThreeSiteOperationalNominal : Fin 21 → ℝ := fun i => (operationalZeroIntervalNominal (Fin.castAdd 9 i) : ℝ)
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/BenchmarkOperationalFullCertificate.lean"
def InOperationalParameterBox (θ : Fin 21 → ℝ) : Prop := ∀ i, |θ i-benchmarkThreeSiteOperationalNominal i| ≤ (1/671088640000 : ℝ)*benchmarkThreeSiteOperationalNominal i
def operationalPhysicalRestrictedSink (q s : Fin 9 → ℚ) (θ : Fin 21 → ℝ) (e : Fin 9 → ℝ) : Prop := IsHurwitz (restrictedJacobianMatrix (operationalPhysicalParameters θ 18) (operationalPhysicalParameters θ 19) (operationalPhysicalParameters θ 20) (operationalParameterRates (operationalPhysicalParameters θ)) (operationalUnpack (fun i => ((q i / 10 : ℚ) : ℝ)) + operationalLift (fun i => ((s i / 10 : ℚ) : ℝ)) e))
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/BenchmarkOperationalInverseZero.lean"
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/BenchmarkOperationalFullCertificate.lean"
challengeNumeralAux operationalZeroFullOutcome._proof_3 8192000
challengeNumeralAux operationalZeroFullOutcome._proof_4 16384000000
challengeNumeralAux operationalZeroFullOutcome._proof_5 100
challengeNumeralAux operationalZeroFullOutcome._proof_6 357000
challengeNumeralAux operationalZeroFullOutcome._proof_7 23797
challengeNumeralAux operationalZeroFullOutcome._proof_8 10000000
challengeNumeralAux operationalZeroFullOutcome._proof_9 437971
challengeNumeralAux operationalZeroFullOutcome._proof_10 100000000
challengeNumeralAux operationalZeroFullOutcome._proof_1 218764808329051461578859664168415574856896977253299942183080347793378744494716931669151270266485111504209
challengeNumeralAux operationalZeroFullOutcome._proof_2 14787547339777033195991071424383892203979741648460352142542874901487227497663485514140876800000000000000000
challengeNumeralAux operationalTwoFullOutcome._proof_3 16384000
challengeNumeralAux operationalTwoFullOutcome._proof_4 327680000000
challengeNumeralAux operationalTwoFullOutcome._proof_5 32918000
challengeNumeralAux operationalTwoFullOutcome._proof_6 1439001
challengeNumeralAux operationalTwoFullOutcome._proof_7 20000000
challengeNumeralAux operationalTwoFullOutcome._proof_8 3697503
challengeNumeralAux operationalTwoFullOutcome._proof_9 50000000
challengeNumeralAux operationalTwoFullOutcome._proof_1 489688143626661270927230150387757428988666312583057387523196772556661289010094942204927686144971255286670470601623
challengeNumeralAux operationalTwoFullOutcome._proof_2 19940451679071769213046230667604449464772368013801095203005229248592935834727757199382838188284313600000000000000000
challengeNumeralAux operationalFourFullOutcome._proof_3 2048000
challengeNumeralAux operationalFourFullOutcome._proof_4 40960000000
challengeNumeralAux operationalFourFullOutcome._proof_5 23433000
challengeNumeralAux operationalFourFullOutcome._proof_6 10757833
challengeNumeralAux operationalFourFullOutcome._proof_7 2714459
challengeNumeralAux operationalFourFullOutcome._proof_8 12500000
challengeNumeralAux operationalFourFullOutcome._proof_1 4599501469907009612464002751315450826328711932522883905127728262836218206833047661497370341089714584554295941
challengeNumeralAux operationalFourFullOutcome._proof_2 245291609798590978623041458588212757858564254475582332674050107111671862729092679484239878553600000000000000000
def operationalZeroPrintedOutcome (θ : Fin 21 → ℝ) (e : Fin 9 → ℝ) : Prop := OperationalPrintedSinkOutcome operationalZeroIntervalCoordinates operationalZeroIntervalScales (fun i : Fin 21 => operationalZeroIntervalNominal (Fin.castAdd 9 i)) θ operationalZeroP.realMatrix (1/8192000) (1/16384000000) (1/100) (operationalZeroDecayMargin : ℝ) (operationalZeroPRowBound : ℝ) (357000) (23797/10000000) (437971/100000000) (218764808329051461578859664168415574856896977253299942183080347793378744494716931669151270266485111504209/14787547339777033195991071424383892203979741648460352142542874901487227497663485514140876800000000000000000 : ℝ) e ∧ operationalPhysicalRestrictedSink operationalZeroIntervalCoordinates operationalZeroIntervalScales θ e ∧ OperationalLiteralPhysicalRecovery (fun i => (operationalZeroIntervalCoordinates i : ℝ)) (fun i => (operationalZeroIntervalScales i : ℝ)) θ operationalZeroP.realMatrix (1/8192000) (1/16384000000) (1/100) (operationalZeroDecayMargin : ℝ) (operationalZeroPRowBound : ℝ) (357000) e
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/BenchmarkOperationalInverseTwo.lean"
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/BenchmarkOperationalFullCertificate.lean"
def operationalTwoPrintedOutcome (θ : Fin 21 → ℝ) (e : Fin 9 → ℝ) : Prop := OperationalPrintedSinkOutcome operationalTwoIntervalCoordinates operationalTwoIntervalScales (fun i : Fin 21 => operationalTwoIntervalNominal (Fin.castAdd 9 i)) θ operationalTwoP.realMatrix (1/16384000) (1/327680000000) (1/100) (operationalTwoDecayMargin : ℝ) (operationalTwoPRowBound : ℝ) (32918000) (1439001/20000000) (3697503/50000000) (489688143626661270927230150387757428988666312583057387523196772556661289010094942204927686144971255286670470601623/19940451679071769213046230667604449464772368013801095203005229248592935834727757199382838188284313600000000000000000 : ℝ) e ∧ operationalPhysicalRestrictedSink operationalTwoIntervalCoordinates operationalTwoIntervalScales θ e ∧ OperationalLiteralPhysicalRecovery (fun i => (operationalTwoIntervalCoordinates i : ℝ)) (fun i => (operationalTwoIntervalScales i : ℝ)) θ operationalTwoP.realMatrix (1/16384000) (1/327680000000) (1/100) (operationalTwoDecayMargin : ℝ) (operationalTwoPRowBound : ℝ) (32918000) e
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/BenchmarkOperationalInverseFour.lean"
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/BenchmarkOperationalFullCertificate.lean"
def operationalFourPrintedOutcome (θ : Fin 21 → ℝ) (e : Fin 9 → ℝ) : Prop := OperationalPrintedSinkOutcome operationalFourIntervalCoordinates operationalFourIntervalScales (fun i : Fin 21 => operationalFourIntervalNominal (Fin.castAdd 9 i)) θ operationalFourP.realMatrix (1/2048000) (1/40960000000) (1/100) (operationalFourDecayMargin : ℝ) (operationalFourPRowBound : ℝ) (23433000) (10757833/50000000) (2714459/12500000) (4599501469907009612464002751315450826328711932522883905127728262836218206833047661497370341089714584554295941/245291609798590978623041458588212757858564254475582332674050107111671862729092679484239878553600000000000000000 : ℝ) e ∧ operationalPhysicalRestrictedSink operationalFourIntervalCoordinates operationalFourIntervalScales θ e ∧ OperationalLiteralPhysicalRecovery (fun i => (operationalFourIntervalCoordinates i : ℝ)) (fun i => (operationalFourIntervalScales i : ℝ)) θ operationalFourP.realMatrix (1/2048000) (1/40960000000) (1/100) (operationalFourDecayMargin : ℝ) (operationalFourPRowBound : ℝ) (23433000) e
challengeAuxModule "CHALLENGE_ONLY_CONTRACT"
open Polynomial Filter
open scoped Topology
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/PaperFixedBindingChallengeResearchDefs.lean"
def paperNextN (a b : ℝ) (p q : ℝ[X]) : ℝ[X] := C ((a+1)*(b+1))*p + C 8*(X*p) + C (2*(a+b))*q
def paperNextJ (a b : ℝ) (p q : ℝ[X]) : ℝ[X] := C ((a-1)*(b-1))*q + C 8*(X*q) + C (4*(a+b))*(X*p)
def paperCoalescedPair : ℕ → ℝ[X] × ℝ[X]
  | 0 => (1, 1)
  | m+1 =>
      let pq := paperCoalescedPair m
      (paperNextN 3 3 pq.1 pq.2, paperNextJ 3 3 pq.1 pq.2)
def paperOffsetRoot (ξ : ℕ → ℝ) (δ : ℝ) (j : ℕ) : ℝ := 3+δ*ξ j
def paperSplitPair : ℕ → (ℕ → ℝ) → ℝ → ℝ[X] × ℝ[X]
  | 0, ξ, δ => (1, C ((paperOffsetRoot ξ δ 0-1)/2))
  | m+1, ξ, δ =>
      let pq := paperSplitPair m ξ δ
      (paperNextN (paperOffsetRoot ξ δ (2*m+1))
        (paperOffsetRoot ξ δ (2*m+2)) pq.1 pq.2,
       paperNextJ (paperOffsetRoot ξ δ (2*m+1))
        (paperOffsetRoot ξ δ (2*m+2)) pq.1 pq.2)
def paperRatio (x : ℝ) : ℝ := (x^2-1)/8
def paperQuotient (p q : ℝ[X]) (r : ℝ) : ℝ[X] := (C (q.eval r)*(X*p)-C (r*p.eval r)*q) /ₘ (X-C r)
def paperRawD (p q : ℝ[X]) (r : ℝ) : ℝ[X] := C 4*paperQuotient p q r
def paperRawB (p q : ℝ[X]) (r : ℝ) : ℝ[X] := C r*paperRawD p q r+C (4*r*p.eval r-2*q.eval r)*p-C (2*q.eval r)*q
def paperSplitD (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) : ℝ[X] := paperRawD (paperSplitPair m ξ δ).1 (paperSplitPair m ξ δ).2 r
def paperSplitB (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) : ℝ[X] := paperRawB (paperSplitPair m ξ δ).1 (paperSplitPair m ξ δ).2 r
def paperCoalescedD (m : ℕ) (r : ℝ) : ℝ[X] := paperRawD (paperCoalescedPair m).1 (paperCoalescedPair m).2 r
def paperCoalescedB (m : ℕ) (r : ℝ) : ℝ[X] := paperRawB (paperCoalescedPair m).1 (paperCoalescedPair m).2 r
def paperRealize {n : ℕ}
    (T : Fin (n+1) → ℝ) (B D : Fin n → ℝ) : Rates n where
  a i := 2*D i/T i.castSucc
  b i := D i/B i
  c i := D i/B i
  alpha i := 2*D i/T i.succ
  beta _ := 1
  gamma _ := 1
def paperReconstruct {n : ℕ}
    (T : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (u s f : ℝ) : State n where
  S i := T i*u^i.val*s
  E := u*f
  F := f
  C i := B i*u^(i.val+1)*s*f
  D i := D i*u^(i.val+1)*s*f
def paperSourceRates (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) : Rates (m+2) := paperRealize (fun i : Fin (m+3) => ((1+X)*paperSplitD (m+1) ξ r δ).coeff i) (fun i : Fin (m+2) => (paperSplitB (m+1) ξ r δ).coeff i)
  (fun i : Fin (m+2) => (paperSplitD (m+1) ξ r δ).coeff i)
def paperSourceState (m : ℕ) (ξ : ℕ → ℝ)
    (r δ : ℝ) (j : Fin (2*(m+1)+1)) : State (m+2) :=
  let x := paperOffsetRoot ξ δ j.val
  let D := paperSplitD (m+1) ξ r δ
  paperReconstruct
    (fun i : Fin (m+3) => ((1+X)*D).coeff i)
    (fun i : Fin (m+2) => (paperSplitB (m+1) ξ r δ).coeff i)
    (fun i : Fin (m+2) => D.coeff i)
    (paperRatio x) ((x-1)/(2*paperRatio x*D.eval (paperRatio x)))
    (4/(x+1))
def paperCoalescedState (m : ℕ) (r : ℝ) : State (m+2) :=
  let D := paperCoalescedD (m+1) r
  paperReconstruct
    (fun i : Fin (m+3) => ((1+X)*D).coeff i)
    (fun i : Fin (m+2) => (paperCoalescedB (m+1) r).coeff i)
    (fun i : Fin (m+2) => D.coeff i)
    (paperRatio 3) ((3-1)/(2*paperRatio 3*D.eval (paperRatio 3)))
    (4/(3+1))
def paperScaleRates {n : ℕ}
    (w : Fin n → ℝ) (k : Rates n) : Rates n where
  a i := w i*k.a i
  b i := w i*k.b i
  c i := w i*k.c i
  alpha i := w i*k.alpha i
  beta i := w i*k.beta i
  gamma i := w i*k.gamma i
def paperFixBinding {n : ℕ} (k : Rates n) : Rates n where
  a i := (1+k.c i)*(k.a i/(k.b i+k.c i))
  b _ := 1
  c := k.c
  alpha i := (1+k.gamma i)*(k.alpha i/(k.beta i+k.gamma i))
  beta _ := 1
  gamma := k.gamma
def paperRelax {n : ℕ} (k : Rates n) (ε : ℝ) : Rates n where
  a i := k.a i/ε
  b i := (k.b i+k.c i)/ε-k.c i
  c := k.c
  alpha i := k.alpha i/ε
  beta i := (k.beta i+k.gamma i)/ε-k.gamma i
  gamma := k.gamma
def paperRates (m : ℕ) (ξ : ℕ → ℝ) (r δ ε : ℝ) (w : Fin (m+2) → ℝ) : Rates (m+2) := paperRelax (paperFixBinding (paperScaleRates w (paperSourceRates m ξ r δ))) ε
def paperFiniteGap {N : ℕ} (x : Fin N → ℝ) (j : Fin N) : ℝ :=
  ∏ i ∈ (Finset.univ : Finset (Fin N)).erase j, (x j-x i)
section
/- Match the already verified definition's original Mathlib instances. -/
attribute [local instance 2000] CommCStarAlgebra.toNormedCommRing
def PaperFixedBindingSignedLawAt
    (m : ℕ) (x : Fin (2*(m+1)+1) → ℝ) (ξ : ℕ → ℝ)
    (r δ ε A α K : ℝ) (w : Fin (m+2) → ℝ)
    (lam : Fin (2*(m+1)+1) → ℝ → ℝ) : Prop :=
  let k := paperRates m ξ r δ ε w
  let z := paperSourceState m ξ r δ
  k.Positive ∧ Function.Injective z ∧
    {s : State (m+2) | s.Positive ∧ Equilibrium k s ∧
      InClass (2*r) 2 (2*(r+1)) s} = Set.range z ∧
    {s : State (m+2) | s.Positive ∧ Equilibrium k s ∧
      InClass (2*r) 2 (2*(r+1)) s}.ncard = 2*(m+1)+1 ∧
    ∀ j : Fin (2*(m+1)+1),
      let s := z j
      let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k
        (toCoordinateSpace (chart s))
      s.Positive ∧ Equilibrium k s ∧ InClass (2*r) 2 (2*(r+1)) s ∧
      Real.sqrt (1+8*s.E/s.F)=3+δ*x j ∧ J.charpoly.IsRoot (lam j δ) ∧
      ((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval ((lam j δ) : ℂ) ≠ 0 ∧
      (∀ ζ : ℂ, ζ ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
        ζ = ((lam j δ) : ℂ) ∨ ζ.re ≤ -α) ∧
      |lam j δ/(-A*δ^(2*(m+1))*paperFiniteGap x j)-1| ≤ K*|δ| ∧
      (∃ err : ℝ, |err| ≤ 2*K*|δ| ∧
        1/|lam j δ|=(1+err)/(A*|paperFiniteGap x j| *δ^(2*(m+1)))) ∧
      (Even j.val → lam j δ < 0) ∧ (Odd j.val → 0 < lam j δ) ∧
      (Even j.val → IsLinearlyStable (2*r) 2 (2*(r+1)) k
        (toCoordinateSpace (chart s)) ∧
        IsLocallyAsymptoticallyStableClass (2*r) 2 (2*(r+1)) k
          (toCoordinateSpace (chart s))) ∧
      (Odd j.val → IsOneUnstableSaddle (2*r) 2 (2*(r+1)) k
        (toCoordinateSpace (chart s)))
end
section
/- Match the already verified definition's original Mathlib instances. -/
attribute [local instance 2000] InnerProductSpace.toNormedSpace
attribute [local instance 2000] RCLike.toInnerProductSpaceReal
def PaperFixedBindingFamilyData (m : ℕ) (ξ : ℕ → ℝ)
    (r t ε : ℝ) (w : Fin (m+2) → ℝ) : Prop :=
  let X₀ := paperCoalescedState m r
  let kUnrelaxed := paperFixBinding (paperScaleRates w (paperSourceRates m ξ r 0))
  let k₀ := paperRates m ξ r 0 ε w
  (3*(m+2 : ℝ))/2 ≤ r ∧ 0 < t ∧
    (∀ i : Fin (m+2), kUnrelaxed.b i=1 ∧ kUnrelaxed.beta i=1) ∧
    (∀ i : Fin (m+1), k₀.gamma i.castSucc*X₀.D i.castSucc=1) ∧
    k₀.gamma (Fin.last (m+1))*X₀.D (Fin.last (m+1))=t ∧
    (∀ j, paperSourceState m ξ r 0 j = X₀) ∧
    (∀ i : Fin (m+2),
      AnalyticAt ℝ (fun δ => (paperRates m ξ r δ ε w).a i) 0 ∧
      AnalyticAt ℝ (fun δ => (paperRates m ξ r δ ε w).b i) 0 ∧
      AnalyticAt ℝ (fun δ => (paperRates m ξ r δ ε w).c i) 0 ∧
      AnalyticAt ℝ (fun δ => (paperRates m ξ r δ ε w).alpha i) 0 ∧
      AnalyticAt ℝ (fun δ => (paperRates m ξ r δ ε w).beta i) 0 ∧
      AnalyticAt ℝ (fun δ => (paperRates m ξ r δ ε w).gamma i) 0) ∧
    (∀ j : Fin (2*(m+1)+1),
      (∀ i : Fin (m+3), AnalyticAt ℝ
        (fun δ => (paperSourceState m ξ r δ j).S i) 0) ∧
      AnalyticAt ℝ (fun δ => (paperSourceState m ξ r δ j).E) 0 ∧
      AnalyticAt ℝ (fun δ => (paperSourceState m ξ r δ j).F) 0 ∧
      (∀ i : Fin (m+2), AnalyticAt ℝ
        (fun δ => (paperSourceState m ξ r δ j).C i) 0) ∧
      (∀ i : Fin (m+2), AnalyticAt ℝ
        (fun δ => (paperSourceState m ξ r δ j).D i) 0))
end
section
/- Match the already verified definition's original Mathlib instances. -/
attribute [local instance 2000] CommCStarAlgebra.toNormedCommRing
attribute [local instance 2000] InnerProductSpace.toNormedSpace
attribute [local instance 2000] RCLike.toInnerProductSpaceReal
def PaperFixedBindingSelectedLaw
    (m : ℕ) (x : Fin (2*(m+1)+1) → ℝ) (ξ : ℕ → ℝ)
    (r ε A α K : ℝ) (w : Fin (m+2) → ℝ)
    (lam : Fin (2*(m+1)+1) → ℝ → ℝ) : Prop :=
  let X₀ := paperCoalescedState m r
  let k₀ := paperRates m ξ r 0 ε w
  (∀ j, AnalyticAt ℝ (lam j) 0 ∧ lam j 0=0) ∧
    0 < A ∧ 0 < α ∧ 0 < K ∧
    (A =
      let J₀ := restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k₀
        (toCoordinateSpace (chart X₀))
      let Θ₀ : ℂ := ((J₀.map (algebraMap ℝ ℂ)).charpoly.roots.erase 0).prod
      let P := paperCoalescedPair (m+1)
      let D := paperCoalescedD (m+1) r
      let B := paperCoalescedB (m+1) r
      let C := 2*r*P.1.eval r+P.2.eval r
      let M := (B.eval 1-D.eval 1)/D.coeff 0
      (4*C*M/((r-1)*D.eval 1*‖Θ₀‖))*
        (∏ i : Fin (m+2), (k₀.b i+k₀.c i)*k₀.alpha i*k₀.gamma i)) ∧
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      PaperFixedBindingSignedLawAt m x ξ r δ ε A α K w lam
end
def PaperFixedBindingFiniteLaw
    (m : ℕ) (x : Fin (2*(m+1)+1) → ℝ) : Prop :=
  StrictMono x → ∃ ξ : ℕ → ℝ, StrictMono ξ ∧
    (∀ j : Fin (2*(m+1)+1), ξ j.val=x j) ∧ ∃ a b c : ℕ,
      let r : ℝ := 2^a; let t : ℝ := (1/2)^b; let ε : ℝ := (1/2)^c
      let X₀ := paperCoalescedState m r
      let w : Fin (m+2) → ℝ := Fin.lastCases (t/X₀.D (Fin.last (m+1)))
        (fun i => 1/X₀.D i.castSucc)
      PaperFixedBindingFamilyData m ξ r t ε w ∧
      ∃ lam : Fin (2*(m+1)+1) → ℝ → ℝ, ∃ A α K : ℝ,
        PaperFixedBindingSelectedLaw m x ξ r ε A α K w lam
def PaperFixedBindingRationalAttainment (m : ℕ) : Prop :=
  ∃ a b c : ℕ,
    let r : ℝ := 2^a; let t : ℝ := (1/2)^b; let ε : ℝ := (1/2)^c
    let X₀ := paperCoalescedState m r
    let w : Fin (m+2) → ℝ := Fin.lastCases (t/X₀.D (Fin.last (m+1)))
      (fun i => 1/X₀.D i.castSucc)
    let ξ : ℕ → ℝ := fun j => (j : ℝ)
    let x : Fin (2*(m+1)+1) → ℝ := fun j => (j.val : ℝ)
    PaperFixedBindingFamilyData m ξ r t ε w ∧
    ∃ lam : Fin (2*(m+1)+1) → ℝ → ℝ, ∃ A α K : ℝ,
      PaperFixedBindingSelectedLaw m x ξ r ε A α K w lam ∧
      ∃ d : ℕ, let δ : ℝ := (1/2)^d
        RationalRates (paperRates m ξ r δ ε w) ∧
        (∀ j, RationalState (paperSourceState m ξ r δ j)) ∧
        PaperFixedBindingSignedLawAt m x ξ r δ ε A α K w lam
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/PaperCompactChallengeResearchDefs.lean"
abbrev PaperPositivePrefixCurrents (m : ℕ) := {ω : Fin (m+1) → ℝ // ∀ i, 0 < ω i}
def paperReadout (m : ℕ) (s : State (m+2)) : ℝ := s.S (Fin.last (m+2)) + s.D (Fin.last (m+1))
def paperReadoutScalar (m : ℕ) (D : ℝ[X]) (x : ℝ) : ℝ :=
  (D.coeff (m+1)/2) * ((paperRatio x)^(m+1)/D.eval (paperRatio x)) *
    ((x-1)*(x+5)/(x+1))
section
/- Match the already verified definition's original Mathlib instances. -/
attribute [local instance 2000] CommCStarAlgebra.toNormedCommRing
attribute [local instance 2000] InnerProductSpace.toNormedSpace
attribute [local instance 2000] RCLike.toInnerProductSpaceReal
def PaperCompactActualCurrentLaw
    (m : ℕ) (x : Fin (2*(m+1)+1) → ℝ) : Prop :=
  StrictMono x →
    ∃ ξ : ℕ → ℝ, StrictMono ξ ∧ (∀ j, ξ j.val = x j) ∧
      ∀ᶠ r : ℝ in atTop,
        ∀ K : Set (PaperPositivePrefixCurrents m), IsCompact K →
          ∃ t ε α Kerr Cread : ℝ,
            0 < t ∧ 0 < ε ∧ ε ≤ 1 ∧ 0 < α ∧ 0 < Kerr ∧ 0 < Cread ∧
            let X₀ := paperCoalescedState m r
            let z := fun δ => paperSourceState m ξ r δ
            let w := fun ω : PaperPositivePrefixCurrents m =>
              Fin.lastCases (t/X₀.D (Fin.last (m+1)))
                (fun i => ω.val i/X₀.D i.castSucc)
            let k := fun ω δ => paperRates m ξ r δ ε (w ω)
            ∃ lam : PaperPositivePrefixCurrents m → Fin (2*(m+1)+1) → ℝ → ℝ,
              ∃ A : PaperPositivePrefixCurrents m → ℝ,
                (∀ ω ∈ K, 0 < A ω ∧
                  (∀ j, AnalyticAt ℝ (lam ω j) 0 ∧ lam ω j 0 = 0) ∧
                  (∀ i, (k ω 0).gamma i.castSucc*X₀.D i.castSucc = ω.val i) ∧
                  (k ω 0).gamma (Fin.last (m+1))*X₀.D (Fin.last (m+1)) = t ∧
                  (A ω =
                    let J₀ := restrictedJacobianMatrix (2*r) 2 (2*(r+1)) (k ω 0)
                      (toCoordinateSpace (chart X₀))
                    let Θ₀ : ℂ :=
                      ((J₀.map (algebraMap ℝ ℂ)).charpoly.roots.erase 0).prod
                    let P := paperCoalescedPair (m+1)
                    let D := paperCoalescedD (m+1) r
                    let B := paperCoalescedB (m+1) r
                    let C := 2*r*P.1.eval r+P.2.eval r
                    let M := (B.eval 1-D.eval 1)/D.coeff 0
                    (4*C*M/((r-1)*D.eval 1*‖Θ₀‖))*
                      (∏ i : Fin (m+2),
                        ((k ω 0).b i+(k ω 0).c i)*(k ω 0).alpha i*(k ω 0).gamma i))) ∧
                ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
                  (∀ j l : Fin (2*(m+1)+1),
                    |(paperReadout m (z δ j)-paperReadout m (z δ l)) -
                      (x j-x l)*deriv (paperReadoutScalar m (paperCoalescedD (m+1) r)) 3*δ|
                      ≤ Cread*δ^2) ∧
                  StrictMono (fun j => paperReadout m (z δ j)) ∧
                  ∀ ω ∈ K,
                    (k ω δ).Positive ∧ Function.Injective (z δ) ∧
                    {s : State (m+2) | s.Positive ∧ Equilibrium (k ω δ) s ∧
                      InClass (2*r) 2 (2*(r+1)) s} = Set.range (z δ) ∧
                    {s : State (m+2) | s.Positive ∧ Equilibrium (k ω δ) s ∧
                      InClass (2*r) 2 (2*(r+1)) s}.ncard = 2*(m+1)+1 ∧
                    ∀ j : Fin (2*(m+1)+1),
                      let s := z δ j
                      let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1)) (k ω δ)
                        (toCoordinateSpace (chart s))
                      s.Positive ∧ Equilibrium (k ω δ) s ∧
                      InClass (2*r) 2 (2*(r+1)) s ∧
                      Real.sqrt (1+8*s.E/s.F) = 3+δ*x j ∧
                      J.charpoly.IsRoot (lam ω j δ) ∧
                      ((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
                        ((lam ω j δ) : ℂ) ≠ 0 ∧
                      (∀ ζ : ℂ, ζ ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
                        ζ = ((lam ω j δ) : ℂ) ∨ ζ.re ≤ -α) ∧
                      |lam ω j δ/(-A ω*δ^(2*(m+1))*paperFiniteGap x j)-1| ≤ Kerr*|δ| ∧
                      (∃ err : ℝ, |err| ≤ 2*Kerr*|δ| ∧
                        1/|lam ω j δ| = (1+err)/
                          (A ω * |paperFiniteGap x j| * δ^(2*(m+1)))) ∧
                      (Even j.val → lam ω j δ < 0) ∧
                      (Odd j.val → 0 < lam ω j δ) ∧
                      (Even j.val → IsLinearlyStable (2*r) 2 (2*(r+1)) (k ω δ)
                        (toCoordinateSpace (chart s)) ∧
                        IsLocallyAsymptoticallyStableClass (2*r) 2 (2*(r+1)) (k ω δ)
                          (toCoordinateSpace (chart s))) ∧
                      (Odd j.val → IsOneUnstableSaddle (2*r) 2 (2*(r+1)) (k ω δ)
                        (toCoordinateSpace (chart s)))
end
namespace P079PrintedContract
noncomputable section
open PhosphorylationSharpness Polynomial
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/FiniteFixedPrintedContractDefs.lean"
def paperFixedRadius (m : ℕ) : ℝ := if m = 1 then 2 else if m ≤ 3 then 4 else 8
def paperFixedSpacing (m : ℕ) : ℝ := if m ≤ 3 then 1 / 2 else 1 / 4
def paperFixedRoot (m : ℕ) (δ : ℝ) (j : ℕ) : ℝ := 3 + δ * ((j : ℝ) - m)
def paperFixedNextN (a b : ℝ) (p q : ℝ[X]) : ℝ[X] := Polynomial.C ((a + 1) * (b + 1)) * p + Polynomial.C 8 * (Polynomial.X * p) + Polynomial.C (2 * (a + b)) * q
def paperFixedNextJ (a b : ℝ) (p q : ℝ[X]) : ℝ[X] := Polynomial.C ((a - 1) * (b - 1)) * q + Polynomial.C 8 * (Polynomial.X * q) + Polynomial.C (4 * (a + b)) * (Polynomial.X * p)
def paperFixedPairAt (M : ℕ) : (depth : ℕ) → ℝ → ℝ[X] × ℝ[X]
  | 0, δ => (1, Polynomial.C ((paperFixedRoot M δ 0 - 1) / 2))
  | depth + 1, δ =>
      let pq := paperFixedPairAt M depth δ
      (paperFixedNextN (paperFixedRoot M δ (2 * depth + 1))
          (paperFixedRoot M δ (2 * depth + 2)) pq.1 pq.2,
        paperFixedNextJ (paperFixedRoot M δ (2 * depth + 1))
          (paperFixedRoot M δ (2 * depth + 2)) pq.1 pq.2)
def paperFixedPair (m : ℕ) (δ : ℝ) : ℝ[X] × ℝ[X] := paperFixedPairAt m m δ
def paperFixedRatio (x : ℝ) : ℝ := (x ^ 2 - 1) / 8
def paperFixedRootS (x d : ℝ) : ℝ := (x - 1) / (2 * paperFixedRatio x * d)
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
def paperFixedT (m : ℕ) (r δ : ℝ) (i : Fin (m + 2)) : ℝ := (((1 : ℝ[X]) + Polynomial.X) * paperFixedRawD m r δ).coeff i
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
end P079PrintedContract
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/FiniteThreeSiteBenchmarkData.lean"
def benchmarkThreeSiteRates : Rates 3 where
  a := ![(2 : ℝ), (1850056872394595934523465378312 : ℝ) / 989996000917120571045749950607, (27607712325255743002783032 : ℝ) / 126732220442230611250455425]
  b := ![(2561356061 : ℝ) / 42962538673466, (1562760173497930 : ℝ) / 199539510868912837, (206960131084861 : ℝ) / 1632576469591708]
  c := ![(23614054870423099379 : ℝ) / 1196662741996490128512, (47508880452187522835105892 : ℝ) / 291467450611351315929492199, (34120037836851215351993 : ℝ) / 89038971023625546753883]
  alpha := ![(7051250727309545389200260 : ℝ) / 41021787130284170515591497, (235395971596073829481109385678 : ℝ) / 117918371998374931344888363875, (1888280435603197004985 : ℝ) / 944140432152952132667]
  beta := ![(32243543687792426 : ℝ) / 75463699179943029, (50075904370247184 : ℝ) / 186779636882893435, (26718975290670014 : ℝ) / 210323108075952803]
  gamma := ![(42833130699194 : ℝ) / 21481269336733, (376304202426012366 : ℝ) / 196059545236362091, (180608615618770229 : ℝ) / 96429418052594437]
def benchmarkThreeSiteStates : Fin 5 → State 3 := ![
  { S := ![(200474 : ℝ) / 914685, (543596293 : ℝ) / 469538300, (8300517 : ℝ) / 18781532, (1700253 : ℝ) / 117384575], E := (1 : ℝ) / 2, F := (4 : ℝ) / 3, C := ![(37138176 : ℝ) / 3353845, (1486627189 : ℝ) / 234769150, (11080308 : ℝ) / 117384575], D := ![(100237 : ℝ) / 914685, (63125631 : ℝ) / 117384575, (2267004 : ℝ) / 117384575] },
  { S := ![(5613272 : ℝ) / 138173535, (543596293 : ℝ) / 675515060, (622538775 : ℝ) / 540412048, (76511385 : ℝ) / 540412048], E := (5 : ℝ) / 4, F := (8 : ℝ) / 9, C := ![(173311488 : ℝ) / 33775753, (1486627189 : ℝ) / 135103012, (41551155 : ℝ) / 67551506], D := ![(1403318 : ℝ) / 27634707, (63125631 : ℝ) / 67551506, (8501265 : ℝ) / 67551506] },
  { S := ![(11026070 : ℝ) / 852373353, (1087192586 : ℝ) / 1988871157, (3320206800 : ℝ) / 1988871157, (870529536 : ℝ) / 1988871157], E := (2 : ℝ), F := (2 : ℝ) / 3, C := ![(742763520 : ℝ) / 284124451, (23786035024 : ℝ) / 1988871157, (2836558848 : ℝ) / 1988871157], D := ![(22052140 : ℝ) / 852373353, (2020020192 : ℝ) / 1988871157, (580353024 : ℝ) / 1988871157] },
  { S := ![(5613272 : ℝ) / 1071365415, (543596293 : ℝ) / 1428487220, (2282642175 : ℝ) / 1142789776, (1028653065 : ℝ) / 1142789776], E := (11 : ℝ) / 4, F := (8 : ℝ) / 15, C := ![(519934464 : ℝ) / 357121805, (16352899079 : ℝ) / 1428487220, (335179317 : ℝ) / 142848722], D := ![(15436498 : ℝ) / 1071365415, (694381941 : ℝ) / 714243610, (68576871 : ℝ) / 142848722] },
  { S := ![(2205214 : ℝ) / 901896723, (543596293 : ℝ) / 2004214940, (124507755 : ℝ) / 57263284, (107115939 : ℝ) / 71579105], E := (7 : ℝ) / 2, F := (4 : ℝ) / 9, C := ![(12379392 : ℝ) / 14315821, (1486627189 : ℝ) / 143158210, (232686468 : ℝ) / 71579105], D := ![(1102607 : ℝ) / 128842389, (63125631 : ℝ) / 71579105, (47607084 : ℝ) / 71579105] }
  ]
def benchmarkThreeSiteCoord (j : Fin 5) : CoordinateSpace 3 := toCoordinateSpace (chart (benchmarkThreeSiteStates j))
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/BenchmarkFullConfiguration435.lean"
def PaperBenchmarkFullConfiguration : Prop := benchmarkThreeSiteRates.Positive ∧ Function.Injective benchmarkThreeSiteStates ∧ {s : State 3 | s.Positive ∧ Equilibrium benchmarkThreeSiteRates s ∧ InClass 18 2 20 s} = Set.range benchmarkThreeSiteStates ∧ {s : State 3 | s.Positive ∧ Equilibrium benchmarkThreeSiteRates s ∧ InClass 18 2 20 s}.ncard = 5 ∧ ∀ j : Fin 5, (benchmarkThreeSiteStates j).Positive ∧ Equilibrium benchmarkThreeSiteRates (benchmarkThreeSiteStates j) ∧ InClass 18 2 20 (benchmarkThreeSiteStates j) ∧ (Even j.val → IsLinearlyStable 18 2 20 benchmarkThreeSiteRates (benchmarkThreeSiteCoord j) ∧ IsLocallyAsymptoticallyStableClass 18 2 20 benchmarkThreeSiteRates (benchmarkThreeSiteCoord j)) ∧ (Odd j.val → IsOneUnstableSaddle 18 2 20 benchmarkThreeSiteRates (benchmarkThreeSiteCoord j))
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/FiniteTwoSiteManuscriptWitness.lean"
def manuscriptTwoSiteRates : Rates 2 where
  a := ![(19782 : ℝ)/1375, (311808 : ℝ)/192049]
  b := ![1, 1]
  c := ![(625 : ℝ)/1573, (4065 : ℝ)/2431]
  alpha := ![(147000 : ℝ)/124267, (79 : ℝ)/34]
  beta := ![1, 1]
  gamma := ![(45 : ℝ)/11, (45 : ℝ)/34]
def manuscriptTwoSiteStates : Fin 3 → State 2 := ![ { S := ![(250 : ℝ)/693, (1027 : ℝ)/1008, (271 : ℝ)/528], E := 3/4, F := 8/7, C := ![(39 : ℝ)/14, (13 : ℝ)/28], D := ![(125 : ℝ)/462, (271 : ℝ)/462] }, { S := ![(2625 : ℝ)/11297, 1, (8672 : ℝ)/11297], E := 1, F := 1, C := ![(189 : ℝ)/79, (48 : ℝ)/79], D := ![(2625 : ℝ)/11297, (8672 : ℝ)/11297] }, { S := ![(350 : ℝ)/2223, (869 : ℝ)/912, (4065 : ℝ)/3952], E := 5/4, F := 8/9, C := ![(77 : ℝ)/38, (55 : ℝ)/76], D := ![(875 : ℝ)/4446, (1355 : ℝ)/1482] } ]
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/FiniteTwoSitePaperTailGap.lean"
def OneDominantTailGap {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) : Prop := ∃ x : ℝ, -2 < x ∧ A.charpoly.IsRoot x ∧ ((A.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧ ∀ z : ℂ, z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) → z.re < -2 ∨ z = (x : ℂ)
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/PaperTwoSiteTailTarget.lean"
def PaperTwoSiteTailLaw : Prop := ∀ j : Fin 3, OneDominantTailGap (restrictedJacobianMatrix 4 2 6 manuscriptTwoSiteRates (toCoordinateSpace (chart (manuscriptTwoSiteStates j))))
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/PaperCompactActualCurrentInterval435.lean"
section
/- Match the already verified definition's original Mathlib instances. -/
attribute [local instance 2000] CommCStarAlgebra.toNormedCommRing
attribute [local instance 2000] InnerProductSpace.toNormedSpace
attribute [local instance 2000] RCLike.toInnerProductSpaceReal
def PaperCompactActualCurrentIntervalLaw
    (m : ℕ) (x : Fin (2*(m+1)+1) → ℝ) : Prop :=
  StrictMono x →
    ∃ ξ : ℕ → ℝ, StrictMono ξ ∧ (∀ j, ξ j.val = x j) ∧
      ∀ᶠ r : ℝ in atTop,
        ∀ K : Set (PaperPositivePrefixCurrents m), IsCompact K →
          ∃ t ε α Kerr Cread : ℝ,
            0 < t ∧ 0 < ε ∧ ε ≤ 1 ∧ 0 < α ∧ 0 < Kerr ∧ 0 < Cread ∧
            0 < deriv (paperReadoutScalar m (paperCoalescedD (m+1) r)) 3 ∧
            let X₀ := paperCoalescedState m r
            let z := fun δ => paperSourceState m ξ r δ
            let w := fun ω : PaperPositivePrefixCurrents m =>
              Fin.lastCases (t/X₀.D (Fin.last (m+1)))
                (fun i => ω.val i/X₀.D i.castSucc)
            let k := fun ω δ => paperRates m ξ r δ ε (w ω)
            ∃ lam : PaperPositivePrefixCurrents m → Fin (2*(m+1)+1) → ℝ → ℝ,
              ∃ A : PaperPositivePrefixCurrents m → ℝ,
                (∀ ω ∈ K, 0 < A ω ∧
                  (∀ j, AnalyticAt ℝ (lam ω j) 0 ∧ lam ω j 0 = 0) ∧
                  (∀ i, (k ω 0).gamma i.castSucc*X₀.D i.castSucc = ω.val i) ∧
                  (k ω 0).gamma (Fin.last (m+1))*X₀.D (Fin.last (m+1)) = t ∧
                  (A ω =
                    let J₀ := restrictedJacobianMatrix (2*r) 2 (2*(r+1)) (k ω 0)
                      (toCoordinateSpace (chart X₀))
                    let Θ₀ : ℂ :=
                      ((J₀.map (algebraMap ℝ ℂ)).charpoly.roots.erase 0).prod
                    let P := paperCoalescedPair (m+1)
                    let D := paperCoalescedD (m+1) r
                    let B := paperCoalescedB (m+1) r
                    let C := 2*r*P.1.eval r+P.2.eval r
                    let M := (B.eval 1-D.eval 1)/D.coeff 0
                    (4*C*M/((r-1)*D.eval 1*‖Θ₀‖))*
                      (∏ i : Fin (m+2),
                        ((k ω 0).b i+(k ω 0).c i)*(k ω 0).alpha i*(k ω 0).gamma i))) ∧
                ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
                  (∀ j l : Fin (2*(m+1)+1),
                    |(paperReadout m (z δ j)-paperReadout m (z δ l)) -
                      (x j-x l)*deriv (paperReadoutScalar m (paperCoalescedD (m+1) r)) 3*δ|
                      ≤ Cread*δ^2) ∧
                  StrictMono (fun j => paperReadout m (z δ j)) ∧
                  ∀ ω ∈ K,
                    (k ω δ).Positive ∧ Function.Injective (z δ) ∧
                    {s : State (m+2) | s.Positive ∧ Equilibrium (k ω δ) s ∧
                      InClass (2*r) 2 (2*(r+1)) s} = Set.range (z δ) ∧
                    {s : State (m+2) | s.Positive ∧ Equilibrium (k ω δ) s ∧
                      InClass (2*r) 2 (2*(r+1)) s}.ncard = 2*(m+1)+1 ∧
                    ∀ j : Fin (2*(m+1)+1),
                      let s := z δ j
                      let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1)) (k ω δ)
                        (toCoordinateSpace (chart s))
                      s.Positive ∧
                      0 < ∑ i : Fin (m+2), (k ω δ).gamma i*s.D i ∧
                      Equilibrium (k ω δ) s ∧
                      InClass (2*r) 2 (2*(r+1)) s ∧
                      Real.sqrt (1+8*s.E/s.F) = 3+δ*x j ∧
                      J.charpoly.IsRoot (lam ω j δ) ∧
                      ((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
                        ((lam ω j δ) : ℂ) ≠ 0 ∧
                      (∀ ζ : ℂ, ζ ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
                        ζ = ((lam ω j δ) : ℂ) ∨ ζ.re ≤ -α) ∧
                      |lam ω j δ/(-A ω*δ^(2*(m+1))*paperFiniteGap x j)-1| ≤ Kerr*|δ| ∧
                      (∃ err : ℝ, |err| ≤ 2*Kerr*|δ| ∧
                        1/|lam ω j δ| = (1+err)/
                          (A ω*|paperFiniteGap x j| *δ^(2*(m+1)))) ∧
                      (Even j.val → lam ω j δ < 0) ∧
                      (Odd j.val → 0 < lam ω j δ) ∧
                      (Even j.val → IsLinearlyStable (2*r) 2 (2*(r+1)) (k ω δ)
                        (toCoordinateSpace (chart s)) ∧
                        IsLocallyAsymptoticallyStableClass (2*r) 2 (2*(r+1)) (k ω δ)
                          (toCoordinateSpace (chart s))) ∧
                      (Odd j.val → IsOneUnstableSaddle (2*r) 2 (2*(r+1)) (k ω δ)
                        (toCoordinateSpace (chart s)))
end
theorem all_size_exact_capacity_with_hyperbolic_attainment_435 (n : ℕ) (hn : 1 ≤ n) : ExactCapacityWithHyperbolicAttainment n := by sorry
theorem all_size_full_family_with_hyperbolic_sinks (n : ℕ) (hn : 2 ≤ n) : FullFamilyWithHyperbolicSinks n := by sorry
theorem all_size_rational_full_family_with_sinks_and_saddles (n : ℕ) (hn : 2 ≤ n) : RationalFullFamilyWithSinksAndSaddles n := by sorry
theorem positive_equilibria_finite_and_ncard_le_two_n_sub_one {n : ℕ} (hn : 0 < n) (k : Rates n) (hk : k.Positive) (ET FT ST : ℝ) (hET : 0 < ET) (hFT : 0 < FT) (hST : 0 < ST) : let E : Set (State n) := {x | x.Positive ∧ Equilibrium k x ∧ InClass ET FT ST x}; E.Finite ∧ E.ncard ≤ 2*n-1 := by sorry
theorem all_positive_sizes_rational_full_family_with_sinks_and_saddles (n : ℕ) (hn : 1 ≤ n) : RationalFullFamilyWithSinksAndSaddles n := by sorry
theorem all_positive_sizes_open_full_hyperbolic_family (n : ℕ) (hn : 1 ≤ n) : OpenFullHyperbolicFamily n := by sorry
theorem three_site_printed_operational_submission (φ : Fin 21 → ℝ) (hφ : ∀ i, |φ i-operationalPhysicalParameters benchmarkThreeSiteOperationalNominal i| ≤ (1/671088640000 : ℝ)*operationalPhysicalParameters benchmarkThreeSiteOperationalNominal i) : ∃ θ : Fin 21 → ℝ, operationalPhysicalParameters θ = φ ∧ InOperationalParameterBox θ ∧ ∃ e0 e2 e4 : Fin 9 → ℝ, operationalZeroPrintedOutcome θ e0 ∧ operationalTwoPrintedOutcome θ e2 ∧ operationalFourPrintedOutcome θ e4 ∧ operationalPhysicalState (fun i => (operationalZeroIntervalCoordinates i : ℝ)) (fun i => (operationalZeroIntervalScales i : ℝ)) θ e0 ≠ operationalPhysicalState (fun i => (operationalTwoIntervalCoordinates i : ℝ)) (fun i => (operationalTwoIntervalScales i : ℝ)) θ e2 ∧ operationalPhysicalState (fun i => (operationalTwoIntervalCoordinates i : ℝ)) (fun i => (operationalTwoIntervalScales i : ℝ)) θ e2 ≠ operationalPhysicalState (fun i => (operationalFourIntervalCoordinates i : ℝ)) (fun i => (operationalFourIntervalScales i : ℝ)) θ e4 ∧ operationalPhysicalState (fun i => (operationalZeroIntervalCoordinates i : ℝ)) (fun i => (operationalZeroIntervalScales i : ℝ)) θ e0 ≠ operationalPhysicalState (fun i => (operationalFourIntervalCoordinates i : ℝ)) (fun i => (operationalFourIntervalScales i : ℝ)) θ e4 := by sorry
theorem paper_fixed_binding_finite_law (m : ℕ) (x : Fin (2*(m+1)+1) → ℝ) : PaperFixedBindingFiniteLaw m x := by sorry
theorem paper_fixed_binding_rational_attainment (m : ℕ) : PaperFixedBindingRationalAttainment m := by sorry
theorem paper_compact_actual_current_law (m : ℕ) (x : Fin (2*(m+1)+1) → ℝ) : PaperCompactActualCurrentLaw m x := by sorry
theorem P079PrintedContract.paper_fixed_finite_table : P079PrintedContract.PaperFixedFiniteTable := by sorry
theorem three_site_benchmark_full_configuration : PaperBenchmarkFullConfiguration := by sorry
theorem two_site_literal_dominant_tail_gap : PaperTwoSiteTailLaw := by sorry
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/OperationalMeasuredReadoutSeparation.lean"
/-- The literal readout in physical concentration units, including one
independent measurement error for the first sink. -/
def operationalZeroMeasuredReadout (θ : Fin 21 → ℝ)
    (e : Fin 9 → ℝ) (error : ℝ) : ℝ :=
  operationalPhysicalReadout
    (fun i => (operationalZeroIntervalCoordinates i : ℝ))
    (fun i => (operationalZeroIntervalScales i : ℝ)) θ e + error
/-- The literal physical readout for the second sink. -/
def operationalTwoMeasuredReadout (θ : Fin 21 → ℝ)
    (e : Fin 9 → ℝ) (error : ℝ) : ℝ :=
  operationalPhysicalReadout
    (fun i => (operationalTwoIntervalCoordinates i : ℝ))
    (fun i => (operationalTwoIntervalScales i : ℝ)) θ e + error
/-- The literal physical readout for the third sink. -/
def operationalFourMeasuredReadout (θ : Fin 21 → ℝ) (e : Fin 9 → ℝ) (error : ℝ) : ℝ := operationalPhysicalReadout (fun i => (operationalFourIntervalCoordinates i : ℝ))
  (fun i => (operationalFourIntervalScales i : ℝ)) θ e + error
theorem three_site_printed_operational_submission_with_measured_separation (φ : Fin 21 → ℝ) (hφ : ∀ i, |φ i-operationalPhysicalParameters benchmarkThreeSiteOperationalNominal i| ≤ (1/671088640000 : ℝ)* operationalPhysicalParameters benchmarkThreeSiteOperationalNominal i) : ∃ θ : Fin 21 → ℝ, operationalPhysicalParameters θ = φ ∧ InOperationalParameterBox θ ∧ ∃ e0 e2 e4 : Fin 9 → ℝ, operationalZeroPrintedOutcome θ e0 ∧ operationalTwoPrintedOutcome θ e2 ∧ operationalFourPrintedOutcome θ e4 ∧ operationalPhysicalState (fun i => (operationalZeroIntervalCoordinates i : ℝ)) (fun i => (operationalZeroIntervalScales i : ℝ)) θ e0 ≠ operationalPhysicalState (fun i => (operationalTwoIntervalCoordinates i : ℝ)) (fun i => (operationalTwoIntervalScales i : ℝ)) θ e2 ∧ operationalPhysicalState (fun i => (operationalTwoIntervalCoordinates i : ℝ)) (fun i => (operationalTwoIntervalScales i : ℝ)) θ e2 ≠ operationalPhysicalState (fun i => (operationalFourIntervalCoordinates i : ℝ)) (fun i => (operationalFourIntervalScales i : ℝ)) θ e4 ∧ operationalPhysicalState (fun i => (operationalZeroIntervalCoordinates i : ℝ)) (fun i => (operationalZeroIntervalScales i : ℝ)) θ e0 ≠ operationalPhysicalState (fun i => (operationalFourIntervalCoordinates i : ℝ)) (fun i => (operationalFourIntervalScales i : ℝ)) θ e4 ∧ ∀ error0 error2 error4 : ℝ, |error0| ≤ (1/1000 : ℝ) → |error2| ≤ (1/1000 : ℝ) → |error4| ≤ (1/1000 : ℝ) → operationalZeroMeasuredReadout θ e0 error0 < operationalTwoMeasuredReadout θ e2 error2 ∧ operationalTwoMeasuredReadout θ e2 error2 < operationalFourMeasuredReadout θ e4 error4 := by sorry
theorem paper_compact_actual_current_interval_law (m : ℕ) (x : Fin (2*(m+1)+1) → ℝ) : PaperCompactActualCurrentIntervalLaw m x := by sorry
challengeAuxModule "E:/Palomar-Submissions/proofs/PhosphorylationStableCapacity/PaperGlobalSubmissionEndpoints435.lean"
def PaperCoefficientDense (p : ℝ[X]) (m : ℕ) : Prop := (∀ i ≤ m, 0 < p.coeff i) ∧ ∀ i, m < i → p.coeff i = 0
theorem paper_global_conversion_quotient_and_D_positive (m : ℕ) (ξ : ℕ → ℝ) (δ r : ℝ) (hr : 0 < r) (hroot : ∀ j, j ≤ 2*m → 1 < paperOffsetRoot ξ δ j) : PaperCoefficientDense (paperQuotient (paperSplitPair m ξ δ).1 (paperSplitPair m ξ δ).2 r) m ∧ PaperCoefficientDense (paperSplitD m ξ r δ) m := by sorry
theorem paper_global_conversion_B_positive (m : ℕ) (ξ : ℕ → ℝ) (δ r : ℝ) (hr : 0 < r) (hroot : ∀ j, j ≤ 2*m → 1 < paperOffsetRoot ξ δ j) (hfar : ∀ j, j ≤ 2*m → paperOffsetRoot ξ δ j < Real.sqrt (1+8*r)) (hsum : (∑ j ∈ Finset.range (2*m+1), paperOffsetRoot ξ δ j) ≤ 4*r+Real.sqrt (1+8*r)) : PaperCoefficientDense (paperSplitB m ξ r δ) m := by sorry
theorem paper_global_readout_strict_order (m : ℕ) (D : ℝ[X]) (hD : PaperCoefficientDense D m) : StrictMonoOn (fun x : ℝ => (D.coeff m/2)*((paperRatio x)^m/D.eval (paperRatio x))*((x-1)*(x+5)/(x+1))) (Set.Ioi 1) := by sorry
theorem paper_global_interlacing_partial_fractions_and_ratios (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ) (hroot : ∀ j, j ≤ 2*m → 1 < paperOffsetRoot ξ δ j) : let p := (paperSplitPair m ξ δ).1; let q := (paperSplitPair m ξ δ).2; ∃ ν ζ σ τ : Fin m → ℝ, StrictAnti ν ∧ StrictAnti ζ ∧ (∀ i, ν i < ζ i ∧ ζ i < 0 ∧ 0 < σ i ∧ 0 < τ i ∧ p.eval (ν i) = 0 ∧ q.eval (ζ i) = 0 ∧ p.derivative.eval (ν i) ≠ 0 ∧ q.derivative.eval (ζ i) ≠ 0 ∧ σ i = p.eval (ζ i)/q.derivative.eval (ζ i) ∧ τ i = -q.eval (ν i)/p.derivative.eval (ν i)) ∧ (∀ i j, i < j → ζ j < ν i) ∧ p = C (p.coeff m)*(∏ i, (X-C (ν i))) ∧ q = C (q.coeff m)*(∏ i, (X-C (ζ i))) ∧ (∀ u, (∀ i, u ≠ ζ i) → p.eval u/q.eval u = p.coeff m/q.coeff m + ∑ i, σ i/(u-ζ i)) ∧ (∀ u, (∀ i, u ≠ ν i) → q.eval u/p.eval u = q.coeff m/p.coeff m - ∑ i, τ i/(u-ν i)) ∧ StrictMonoOn (fun i : ℕ => (if i = 0 then 0 else q.coeff (i-1))/q.coeff i) (Set.Iic m) ∧ (∀ i < m, q.coeff i/p.coeff i ≤ q.coeff (i+1)/p.coeff (i+1)) := by sorry
end
end PhosphorylationStableCapacity
