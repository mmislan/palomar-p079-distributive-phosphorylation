module
public import proofs.PhosphorylationStableCapacity.Jacobian
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

@[expose] public section
namespace P079UnstableWorkbench
open PhosphorylationStableCapacity PhosphorylationSharpness
open scoped BigOperators

noncomputable section

def substrateCoordinate {n : ℕ} (i : Fin n) : CoordinateSpace n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ((Fin n → ℝ) × (Fin n → ℝ)))

def kinaseComplexCoordinate {n : ℕ} (i : Fin n) : CoordinateSpace n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)).comp
      (ContinuousLinearMap.snd ℝ (Fin n → ℝ) ((Fin n → ℝ) × (Fin n → ℝ))))

def phosphataseComplexCoordinate {n : ℕ} (i : Fin n) : CoordinateSpace n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)).comp
      (ContinuousLinearMap.snd ℝ (Fin n → ℝ) ((Fin n → ℝ) × (Fin n → ℝ))))

def freeSubstrateCoordinate {n : ℕ} (i : Fin (n+1)) : CoordinateSpace n →L[ℝ] ℝ :=
  Fin.cases (-(∑ j : Fin n, (substrateCoordinate j + kinaseComplexCoordinate j +
    phosphataseComplexCoordinate j))) substrateCoordinate i

def freeKinaseCoordinate (n : ℕ) : CoordinateSpace n →L[ℝ] ℝ :=
  -(∑ i : Fin n, kinaseComplexCoordinate i)

def freePhosphataseCoordinate (n : ℕ) : CoordinateSpace n →L[ℝ] ℝ :=
  -(∑ i : Fin n, phosphataseComplexCoordinate i)

def constantSubstrate {n : ℕ} (ST : ℝ) (i : Fin (n+1)) : ℝ :=
  Fin.cases ST (fun _ => 0) i

def bilinearPi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (B : Fin n → E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] (Fin n → ℝ) :=
  (ContinuousLinearMap.piEquivL ℝ E (fun _ : Fin n => ℝ)).toContinuousLinearMap.comp
    (ContinuousLinearMap.pi B)

def bilinearProd {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] E →L[ℝ] F) (C : E →L[ℝ] E →L[ℝ] G) :
    E →L[ℝ] E →L[ℝ] (F × G) :=
  (ContinuousLinearMap.prodL ℝ :
    ((E →L[ℝ] F) × (E →L[ℝ] G)) ≃L[ℝ] (E →L[ℝ] F × G)).toContinuousLinearMap.comp
      (B.prod C)

def bindingQuadraticE {n : ℕ} (k : Rates n) (i : Fin n) :
    CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ :=
  k.a i • (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
    (freeSubstrateCoordinate i.castSucc) (freeKinaseCoordinate n)

def bindingQuadraticF {n : ℕ} (k : Rates n) (i : Fin n) :
    CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ :=
  k.alpha i • (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
    (freeSubstrateCoordinate i.succ) (freePhosphataseCoordinate n)

/-- The actual homogeneous quadratic term is built from bounded bilinear
binding reactions and literal class-coordinate projections. -/
def classFieldQuadratic {n : ℕ} (k : Rates n) :
    CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] CoordinateSpace n :=
  bilinearProd
    (bilinearPi (fun j : Fin n => ∑ i : Fin n,
      ((if i.castSucc = j.succ then -bindingQuadraticE k i else 0) +
      (if i.succ = j.succ then -bindingQuadraticF k i else 0))))
    (bilinearProd (bilinearPi (bindingQuadraticE k)) (bilinearPi (bindingQuadraticF k)))

def bindingLinearE {n : ℕ} (ET ST : ℝ) (k : Rates n) (i : Fin n) :
    CoordinateSpace n →L[ℝ] ℝ :=
  k.a i • (ET • freeSubstrateCoordinate i.castSucc +
    constantSubstrate ST i.castSucc • freeKinaseCoordinate n) -
      k.b i • kinaseComplexCoordinate i

def bindingLinearF {n : ℕ} (FT ST : ℝ) (k : Rates n) (i : Fin n) :
    CoordinateSpace n →L[ℝ] ℝ :=
  k.alpha i • (FT • freeSubstrateCoordinate i.succ +
    constantSubstrate ST i.succ • freePhosphataseCoordinate n) -
      k.beta i • phosphataseComplexCoordinate i

def classFieldLinear {n : ℕ} (ET FT ST : ℝ) (k : Rates n) :
    CoordinateSpace n →L[ℝ] CoordinateSpace n :=
  (ContinuousLinearMap.pi (fun j : Fin n => ∑ i : Fin n,
    ((if i.castSucc = j.succ then
      -bindingLinearE ET ST k i + k.gamma i • phosphataseComplexCoordinate i else 0) +
    (if i.succ = j.succ then
      k.c i • kinaseComplexCoordinate i - bindingLinearF FT ST k i else 0)))).prod
  ((ContinuousLinearMap.pi (fun i : Fin n => bindingLinearE ET ST k i -
    k.c i • kinaseComplexCoordinate i)).prod
   (ContinuousLinearMap.pi (fun i : Fin n => bindingLinearF FT ST k i -
    k.gamma i • phosphataseComplexCoordinate i)))

theorem unChart_substrate_affine {n : ℕ} (ET FT ST : ℝ) (u : CoordinateSpace n)
    (i : Fin (n+1)) :
    (unChart ET FT ST (ofCoordinateSpace u)).S i =
      constantSubstrate ST i + freeSubstrateCoordinate i u := by
  cases i using Fin.cases with
  | zero =>
      simp [unChart, ofCoordinateSpace, constantSubstrate, freeSubstrateCoordinate,
        substrateCoordinate, kinaseComplexCoordinate, phosphataseComplexCoordinate,
        Finset.sum_add_distrib]
      ring
  | succ i =>
      simp [unChart, ofCoordinateSpace, constantSubstrate, freeSubstrateCoordinate,
        substrateCoordinate]

theorem unChart_kinase_affine {n : ℕ} (ET FT ST : ℝ) (u : CoordinateSpace n) :
    (unChart ET FT ST (ofCoordinateSpace u)).E = ET + freeKinaseCoordinate n u := by
  simp [unChart, ofCoordinateSpace, freeKinaseCoordinate, kinaseComplexCoordinate,
    sub_eq_add_neg]

theorem unChart_phosphatase_affine {n : ℕ} (ET FT ST : ℝ) (u : CoordinateSpace n) :
    (unChart ET FT ST (ofCoordinateSpace u)).F = FT + freePhosphataseCoordinate n u := by
  simp [unChart, ofCoordinateSpace, freePhosphataseCoordinate, phosphataseComplexCoordinate,
    sub_eq_add_neg]

theorem actual_classField_constant_linear_quadratic {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    restrictedFieldEuclid ET FT ST k u = restrictedFieldEuclid ET FT ST k 0 +
      classFieldLinear ET FT ST k u + classFieldQuadratic k u u := by
  have hS := unChart_substrate_affine (n := n) ET FT ST
  have hE := unChart_kinase_affine (n := n) ET FT ST
  have hF := unChart_phosphatase_affine (n := n) ET FT ST
  have hC (w : CoordinateSpace n) (i : Fin n) :
      (unChart ET FT ST (ofCoordinateSpace w)).C i = w.2.1 i := rfl
  have hD (w : CoordinateSpace n) (i : Fin n) :
      (unChart ET FT ST (ofCoordinateSpace w)).D i = w.2.2 i := rfl
  apply Prod.ext
  · funext j
    simp only [restrictedFieldEuclid, restrictedField, toCoordinateSpace, chart, field,
      kinaseNet, phosphataseNet, Prod.fst_add]
    simp_rw [hS, hE, hF, hC, hD]
    simp [classFieldLinear, classFieldQuadratic, bilinearProd, bilinearPi,
      bindingLinearE, bindingLinearF, bindingQuadraticE, bindingQuadraticF,
      kinaseComplexCoordinate, phosphataseComplexCoordinate,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp only [add_apply, sub_apply, neg_apply, smul_apply,
      zero_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.mul_apply',
      smul_eq_mul] <;> ring
  · apply Prod.ext <;> funext i
    · simp only [restrictedFieldEuclid, restrictedField, toCoordinateSpace, chart, field,
        kinaseNet, Prod.snd_add, Prod.fst_add]
      simp_rw [hS, hE, hC]
      simp [classFieldLinear, classFieldQuadratic, bilinearProd, bilinearPi,
        bindingLinearE, bindingQuadraticE, kinaseComplexCoordinate,
        add_apply, sub_apply, smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.mul_apply',
        smul_eq_mul]
      ring
    · simp only [restrictedFieldEuclid, restrictedField, toCoordinateSpace, chart, field,
        phosphataseNet, Prod.snd_add]
      simp_rw [hS, hF, hD]
      simp [classFieldLinear, classFieldQuadratic, bilinearProd, bilinearPi,
        bindingLinearF, bindingQuadraticF, phosphataseComplexCoordinate,
        add_apply, sub_apply, smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.coe_snd',
        ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.mul_apply',
        smul_eq_mul]
      ring

/-- The literal nonlinear remainder at any class coordinate is exactly the
same bounded quadratic term; the linear term is the actual Fréchet Jacobian. -/
theorem actual_classField_exact_quadratic_remainder {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u w : CoordinateSpace n) :
    restrictedFieldEuclid ET FT ST k (u+w) = restrictedFieldEuclid ET FT ST k u +
      restrictedJacobian ET FT ST k u w + classFieldQuadratic k w w := by
  let L := classFieldLinear ET FT ST k
  let Q := classFieldQuadratic k
  have hquad := Q.hasFDerivAt_of_bilinear (hasFDerivAt_id u) (hasFDerivAt_id u)
  have hderiv : HasFDerivAt (restrictedFieldEuclid ET FT ST k)
      (L + (Q.precompR (CoordinateSpace n) u (.id ℝ _)+
        Q.precompL (CoordinateSpace n) (.id ℝ _) u)) u := by
    have h := ((L.hasFDerivAt).fun_add hquad).const_add (restrictedFieldEuclid ET FT ST k 0)
    convert h using 1
    · funext x
      rw [actual_classField_constant_linear_quadratic]
      simp only [L, Q, id_eq, add_assoc]
    · rfl
  have hA : restrictedJacobian ET FT ST k u =
      L + (Q.precompR (CoordinateSpace n) u (.id ℝ _)+
        Q.precompL (CoordinateSpace n) (.id ℝ _) u) := hderiv.fderiv
  rw [actual_classField_constant_linear_quadratic ET FT ST k (u+w),
    actual_classField_constant_linear_quadratic ET FT ST k u, hA]
  simp only [L, Q, map_add, add_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]
  abel

end
end P079UnstableWorkbench
