module
import all proofs.PhosphorylationStableCapacity.Jacobian
public import proofs.PhosphorylationStableCapacity.Jacobian

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Literal species as a normed real vector space, preserving all components. -/
abbrev FullSpace (n : ℕ) :=
  (Fin (n+1) → ℝ) × (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ))

def toFullSpace {n : ℕ} (x : State n) : FullSpace n :=
  (x.S, (x.E, x.F), (x.C, x.D))

def ofFullSpace {n : ℕ} (x : FullSpace n) : State n where
  S := x.1
  E := x.2.1.1
  F := x.2.1.2
  C := x.2.2.1
  D := x.2.2.2

theorem of_toFullSpace {n : ℕ} (x : State n) :
    ofFullSpace (toFullSpace x) = x := by
  cases x
  rfl

theorem to_ofFullSpace {n : ℕ} (x : FullSpace n) :
    toFullSpace (ofFullSpace x) = x := by
  rfl

/-- The full literal mass-action field on a normed species space. -/
def fullFieldEuclid {n : ℕ} (k : Rates n) (x : FullSpace n) : FullSpace n :=
  toFullSpace (field k (ofFullSpace x))

/-- The affine inclusion of one compatibility class in the full species space. -/
def classEmbedding {n : ℕ} (ET FT ST : ℝ)
    (u : CoordinateSpace n) : FullSpace n :=
  toFullSpace (unChart ET FT ST (ofCoordinateSpace u))

/-- Projection of a full species vector onto the `3n` free class coordinates. -/
def classProjection {n : ℕ} (x : FullSpace n) : CoordinateSpace n :=
  toCoordinateSpace (chart (ofFullSpace x))

theorem projection_embedding {n : ℕ} (ET FT ST : ℝ)
    (u : CoordinateSpace n) : classProjection (classEmbedding ET FT ST u) = u := by
  simp only [classProjection, classEmbedding, of_toFullSpace,
    chart_unChart, to_ofCoordinateSpace]

/-- The restricted field is exactly the full literal field composed with the chart. -/
theorem restricted_eq_project_full_embed {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) :
    restrictedFieldEuclid ET FT ST k u =
      classProjection (fullFieldEuclid k (classEmbedding ET FT ST u)) := by
  simp only [restrictedFieldEuclid, restrictedField, classProjection,
    fullFieldEuclid, classEmbedding, of_toFullSpace]

theorem differentiable_fullFieldEuclid {n : ℕ} (k : Rates n) :
    Differentiable ℝ (fullFieldEuclid k) := by
  classical
  unfold fullFieldEuclid toFullSpace ofFullSpace field kinaseNet phosphataseNet
  dsimp
  fun_prop

theorem differentiable_classEmbedding {n : ℕ} (ET FT ST : ℝ) :
    Differentiable ℝ (classEmbedding (n := n) ET FT ST) := by
  classical
  unfold classEmbedding toFullSpace unChart ofCoordinateSpace
  dsimp
  fun_prop

theorem differentiable_classProjection {n : ℕ} :
    Differentiable ℝ (classProjection (n := n)) := by
  unfold classProjection toCoordinateSpace chart ofFullSpace
  dsimp
  fun_prop

/-- The manuscript's `L (DV) T` relation for the literal full field, for every `n`. -/
theorem restrictedJacobian_chain {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) :
    restrictedJacobian ET FT ST k u =
      (fderiv ℝ classProjection (fullFieldEuclid k (classEmbedding ET FT ST u))).comp
        ((fderiv ℝ (fullFieldEuclid k) (classEmbedding ET FT ST u)).comp
          (fderiv ℝ (classEmbedding ET FT ST) u)) := by
  have hfield : restrictedFieldEuclid ET FT ST k =
      fun v => classProjection (fullFieldEuclid k (classEmbedding ET FT ST v)) := by
    funext v
    exact restricted_eq_project_full_embed ET FT ST k v
  have hinner : DifferentiableAt ℝ
      (fun v => fullFieldEuclid k (classEmbedding ET FT ST v)) u :=
    ((differentiable_fullFieldEuclid k).comp
      (differentiable_classEmbedding ET FT ST)).differentiableAt
  rw [restrictedJacobian, hfield]
  have hc₁ := fderiv_comp u
    (differentiable_classProjection.differentiableAt) hinner
  change fderiv ℝ (fun v => classProjection
    (fullFieldEuclid k (classEmbedding ET FT ST v))) u = _ at hc₁
  rw [hc₁]
  have hc₂ := fderiv_comp u (differentiable_fullFieldEuclid k).differentiableAt
    (differentiable_classEmbedding ET FT ST).differentiableAt
  change fderiv ℝ (fun v => fullFieldEuclid k
    (classEmbedding ET FT ST v)) u = _ at hc₂
  rw [hc₂]

/-- A class inclusion is affine with the same zero-total tangent map at every point. -/
theorem classEmbedding_add {n : ℕ} (ET FT ST : ℝ)
    (u v : CoordinateSpace n) :
    classEmbedding ET FT ST (u + v) =
      classEmbedding ET FT ST u + classEmbedding 0 0 0 v := by
  ext i <;> try cases i using Fin.cases <;>
    simp [classEmbedding, toFullSpace, unChart, ofCoordinateSpace,
      Finset.sum_add_distrib] <;> ring
  all_goals
    simp [classEmbedding, toFullSpace, unChart, ofCoordinateSpace,
      Finset.sum_add_distrib] <;> ring

/-- The free-coordinate projection is additive. -/
theorem classProjection_add {n : ℕ} (x y : FullSpace n) :
    classProjection (x + y) = classProjection x + classProjection y := by
  ext i <;> rfl

/-- The fixed tangent inclusion of the class chart. -/
def tangentMap (n : ℕ) : CoordinateSpace n →L[ℝ] FullSpace n :=
  fderiv ℝ (classEmbedding 0 0 0) 0

/-- The fixed projection of full velocities to the free class coordinates. -/
def projectionMap (n : ℕ) : FullSpace n →L[ℝ] CoordinateSpace n :=
  fderiv ℝ classProjection 0

theorem fderiv_classEmbedding {n : ℕ} (ET FT ST : ℝ)
    (u : CoordinateSpace n) :
    fderiv ℝ (classEmbedding ET FT ST) u = tangentMap n := by
  have hshift :
      (fun v => classEmbedding ET FT ST (u + v)) =
        (fun v => classEmbedding ET FT ST u + classEmbedding 0 0 0 v) := by
    funext v
    exact classEmbedding_add ET FT ST u v
  have h := (fderiv_comp_add_left (𝕜 := ℝ)
    (f := classEmbedding ET FT ST) (x := 0) u)
  rw [hshift, fderiv_const_add] at h
  simpa [tangentMap] using h.symm

theorem fderiv_classProjection {n : ℕ} (x : FullSpace n) :
    fderiv ℝ classProjection x = projectionMap n := by
  have hshift :
      (fun v => classProjection (x + v)) =
        (fun v => classProjection x + classProjection v) := by
    funext v
    exact classProjection_add x v
  have h := (fderiv_comp_add_left (𝕜 := ℝ)
    (f := classProjection) (x := 0) x)
  rw [hshift, fderiv_const_add] at h
  simpa [projectionMap] using h.symm

theorem restrictedJacobian_eq_LDT {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) :
    restrictedJacobian ET FT ST k u =
      (projectionMap n).comp
        ((fderiv ℝ (fullFieldEuclid k) (classEmbedding ET FT ST u)).comp
          (tangentMap n)) := by
  rw [restrictedJacobian_chain, fderiv_classProjection,
    fderiv_classEmbedding]

theorem classEmbedding_zero {n : ℕ} :
    classEmbedding (n := n) 0 0 0 0 = 0 := by
  ext i <;> try cases i using Fin.cases <;>
    simp [classEmbedding, toFullSpace, unChart, ofCoordinateSpace]
  all_goals simp [classEmbedding, toFullSpace, unChart, ofCoordinateSpace]

/-- The fixed projection is a left inverse of the fixed tangent inclusion. -/
theorem projection_tangent_id (n : ℕ) :
    (projectionMap n).comp (tangentMap n) =
      ContinuousLinearMap.id ℝ (CoordinateSpace n) := by
  have hfun :
      (fun u : CoordinateSpace n => classProjection (classEmbedding 0 0 0 u)) =
        id := by
    funext u
    exact projection_embedding 0 0 0 u
  have hchain := fderiv_comp (0 : CoordinateSpace n)
    (differentiable_classProjection.differentiableAt)
    (differentiable_classEmbedding 0 0 0).differentiableAt
  change fderiv ℝ (fun u => classProjection (classEmbedding 0 0 0 u)) 0 = _ at hchain
  rw [hfun, fderiv_id, classEmbedding_zero] at hchain
  simpa [projectionMap, tangentMap] using hchain.symm

/-- The full velocity is the fixed zero-total lift of the class velocity. -/
theorem fullField_embedding {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) :
    fullFieldEuclid k (classEmbedding ET FT ST u) =
      classEmbedding 0 0 0 (restrictedFieldEuclid ET FT ST k u) := by
  change toFullSpace (field k (unChart ET FT ST (ofCoordinateSpace u))) =
    toFullSpace (unChart 0 0 0
      (ofCoordinateSpace (toCoordinateSpace
        (restrictedField ET FT ST k (ofCoordinateSpace u)))))
  rw [of_toCoordinateSpace]
  exact congrArg toFullSpace
    (field_eq_unChart_restricted ET FT ST k (ofCoordinateSpace u))

/-- The full Jacobian preserves class tangents and intertwines with the restricted Jacobian. -/
theorem fullJacobian_tangent_intertwine {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) :
    (fderiv ℝ (fullFieldEuclid k) (classEmbedding ET FT ST u)).comp
        (tangentMap n) =
      (tangentMap n).comp (restrictedJacobian ET FT ST k u) := by
  have hfun :
      (fun v => fullFieldEuclid k (classEmbedding ET FT ST v)) =
        (fun v => classEmbedding 0 0 0
          (restrictedFieldEuclid ET FT ST k v)) := by
    funext v
    exact fullField_embedding ET FT ST k v
  have h := congrArg
    (fun g : CoordinateSpace n → FullSpace n => fderiv ℝ g u) hfun
  change fderiv ℝ (fun v => fullFieldEuclid k
    (classEmbedding ET FT ST v)) u =
    fderiv ℝ (fun v => classEmbedding 0 0 0
      (restrictedFieldEuclid ET FT ST k v)) u at h
  have hc₁ := fderiv_comp u (differentiable_fullFieldEuclid k).differentiableAt
    (differentiable_classEmbedding ET FT ST).differentiableAt
  change fderiv ℝ (fun v => fullFieldEuclid k
    (classEmbedding ET FT ST v)) u = _ at hc₁
  rw [hc₁] at h
  have hc₂ := fderiv_comp u (differentiable_classEmbedding 0 0 0).differentiableAt
    (differentiable_restrictedFieldEuclid ET FT ST k).differentiableAt
  change fderiv ℝ (fun v => classEmbedding 0 0 0
    (restrictedFieldEuclid ET FT ST k v)) u = _ at hc₂
  rw [hc₂] at h
  simpa [restrictedJacobian, fderiv_classEmbedding] using h

end
end PhosphorylationStableCapacity
