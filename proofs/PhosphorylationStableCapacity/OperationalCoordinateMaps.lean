module
public import proofs.PhosphorylationStableCapacity.Jacobian
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

def operationalUnpack (q : Fin 9 → ℝ) : CoordinateSpace 3 :=
  (![q 0,q 1,q 2], (![q 3,q 4,q 5], ![q 6,q 7,q 8]))

def operationalFlatten (u : CoordinateSpace 3) : Fin 9 → ℝ :=
  ![u.1 0,u.1 1,u.1 2,u.2.1 0,u.2.1 1,u.2.1 2,
    u.2.2 0,u.2.2 1,u.2.2 2]

theorem operationalFlatten_unpack (q : Fin 9 → ℝ) :
    operationalFlatten (operationalUnpack q) = q := by
  ext i
  fin_cases i <;> rfl

theorem operationalUnpack_flatten (u : CoordinateSpace 3) :
    operationalUnpack (operationalFlatten u) = u := by
  ext i <;> fin_cases i <;> rfl

def operationalProjection (i : Fin 9) : (Fin 9 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj i

def operationalLift (s : Fin 9 → ℝ) : (Fin 9 → ℝ) →L[ℝ] CoordinateSpace 3 :=
  (ContinuousLinearMap.pi ![s 0 • operationalProjection 0,
    s 1 • operationalProjection 1,s 2 • operationalProjection 2]).prod
    ((ContinuousLinearMap.pi ![s 3 • operationalProjection 3,
      s 4 • operationalProjection 4,s 5 • operationalProjection 5]).prod
      (ContinuousLinearMap.pi ![s 6 • operationalProjection 6,
        s 7 • operationalProjection 7,s 8 • operationalProjection 8]))

def operationalReadS (i : Fin 3) : CoordinateSpace 3 →L[ℝ] ℝ :=
  ((ContinuousLinearMap.proj i) : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) ((Fin 3 → ℝ) × (Fin 3 → ℝ)))
def operationalReadC (i : Fin 3) : CoordinateSpace 3 →L[ℝ] ℝ :=
  ((ContinuousLinearMap.proj i) : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
    ((ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) (Fin 3 → ℝ)).comp
      (ContinuousLinearMap.snd ℝ (Fin 3 → ℝ) ((Fin 3 → ℝ) × (Fin 3 → ℝ))))
def operationalReadD (i : Fin 3) : CoordinateSpace 3 →L[ℝ] ℝ :=
  ((ContinuousLinearMap.proj i) : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
    ((ContinuousLinearMap.snd ℝ (Fin 3 → ℝ) (Fin 3 → ℝ)).comp
      (ContinuousLinearMap.snd ℝ (Fin 3 → ℝ) ((Fin 3 → ℝ) × (Fin 3 → ℝ))))

def operationalRead (s : Fin 9 → ℝ) : CoordinateSpace 3 →L[ℝ] (Fin 9 → ℝ) :=
  ContinuousLinearMap.pi ![
    (s 0)⁻¹ • operationalReadS 0,(s 1)⁻¹ • operationalReadS 1,(s 2)⁻¹ • operationalReadS 2,
    (s 3)⁻¹ • operationalReadC 0,(s 4)⁻¹ • operationalReadC 1,(s 5)⁻¹ • operationalReadC 2,
    (s 6)⁻¹ • operationalReadD 0,(s 7)⁻¹ • operationalReadD 1,(s 8)⁻¹ • operationalReadD 2]

theorem operationalLift_apply (s v : Fin 9 → ℝ) :
    operationalLift s v = operationalUnpack (fun i => s i*v i) := by
  ext i <;> fin_cases i <;> rfl

theorem operationalRead_apply (s : Fin 9 → ℝ) (u : CoordinateSpace 3) (i : Fin 9) :
    operationalRead s u i = operationalFlatten u i / s i := by
  fin_cases i <;> simp [operationalRead, operationalReadS, operationalReadC,
    operationalReadD, operationalFlatten, div_eq_mul_inv, mul_comm]

theorem operationalRead_lift (s : Fin 9 → ℝ) (hs : ∀ i, s i ≠ 0) (v : Fin 9 → ℝ) :
    operationalRead s (operationalLift s v) = v := by
  ext i
  rw [operationalRead_apply, operationalLift_apply, operationalFlatten_unpack]
  exact mul_div_cancel_left₀ (v i) (hs i)

theorem operationalLift_read (s : Fin 9 → ℝ) (hs : ∀ i, s i ≠ 0)
    (u : CoordinateSpace 3) : operationalLift s (operationalRead s u) = u := by
  rw [operationalLift_apply]
  have h : (fun i => s i * operationalRead s u i) = operationalFlatten u := by
    funext i
    rw [operationalRead_apply]
    field_simp [hs i]
  rw [h, operationalUnpack_flatten]

theorem operationalRead_injective (s : Fin 9 → ℝ) (hs : ∀ i, s i ≠ 0) :
    Function.Injective (operationalRead s) := by
  intro u v h
  calc
    u = operationalLift s (operationalRead s u) := (operationalLift_read s hs u).symm
    _ = operationalLift s (operationalRead s v) := congrArg (operationalLift s) h
    _ = v := operationalLift_read s hs v

theorem operationalLift_injective (s : Fin 9 → ℝ) (hs : ∀ i, s i ≠ 0) :
    Function.Injective (operationalLift s) := by
  intro u v h
  calc
    u = operationalRead s (operationalLift s u) := (operationalRead_lift s hs u).symm
    _ = operationalRead s (operationalLift s v) := congrArg (operationalRead s) h
    _ = v := operationalRead_lift s hs v

end
end PhosphorylationStableCapacity
