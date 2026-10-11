module
/-
Copyright (c) 2026 Michael Mislan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

This module is compiled in the separately authorized Lean 4.35 degree
environment. It is not part of the frozen Lean 4.30 project.
-/

public import DifferentialGeometry.Topology.LocalDegree.ClosedBall
public import DifferentialGeometry.Topology.ClosedBall.Extension
public import DifferentialGeometry.Topology.LocalDegree.Determinant
public import DifferentialGeometry.Topology.LocalDegree.FiniteAdditivity

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace PhosphorylationStableCapacity.Topology435

noncomputable section

open Set Metric DifferentialGeometry.LocalDegree
open DifferentialGeometry.Topology.ClosedBall
open scoped unitInterval Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {d : ℕ} {a : E} {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
  (A : E ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
  (hcover : ∀ x : closedBall a r, A x.val ∈ ball (A a) R)

/-- Extend a map from an arbitrary norm ball, then read it in Euclidean
coordinates on one strictly enclosing Euclidean ball. -/
def ambientEuclideanMap (f : C(closedBall a r, E)) :
    C(closedBall (A a) R, EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨fun y => A (extension a hr.le f (A.symm y.val)), by fun_prop⟩

theorem ambientEuclideanMap_boundary_nonzero
    (hcover : ∀ x : closedBall a r, A x.val ∈ ball (A a) R)
    (f : C(closedBall a r, E))
    (hb : ∀ x : closedBall a r, x.val ∈ sphere a r → f x ≠ 0) :
    ∀ y : closedBall (A a) R,
      y.val ∈ sphere (A a) R →
      ambientEuclideanMap hr A f y ≠ 0 := by
  intro y hy hz
  have hout : A.symm y.val ∉ closedBall a r := by
    intro hin
    have hball := hcover ⟨A.symm y.val, hin⟩
    simp only [ContinuousLinearEquiv.apply_symm_apply] at hball
    exact (ne_of_lt (mem_ball.mp hball)) (mem_sphere.mp hy)
  have hnonzero := extension_ne_zero_of_not_mem a hr.le f hb hout
  exact hnonzero (A.map_eq_zero_iff.mp hz)

/-- The genuine Euclidean degree of the radial extension. -/
def ambientBallDegree
    (hcover : ∀ x : closedBall a r, A x.val ∈ ball (A a) R)
    (f : C(closedBall a r, E))
    (hb : ∀ x : closedBall a r, x.val ∈ sphere a r → f x ≠ 0) : ℤ :=
  euclideanBallDegree hR (ambientEuclideanMap hr A f)
    (ambientEuclideanMap_boundary_nonzero hr A hcover f hb)

theorem ambientBallDegree_eq_of_homotopy
    (hcover : ∀ x : closedBall a r, A x.val ∈ ball (A a) R)
    (f g : C(closedBall a r, E))
    (hf : ∀ x : closedBall a r, x.val ∈ sphere a r → f x ≠ 0)
    (hg : ∀ x : closedBall a r, x.val ∈ sphere a r → g x ≠ 0)
    (H : f.Homotopy g)
    (hH : ∀ t : I, ∀ x : closedBall a r,
      x.val ∈ sphere a r → H (t, x) ≠ 0) :
    ambientBallDegree hr hR A hcover f hf =
      ambientBallDegree hr hR A hcover g hg := by
  let K : C(I × closedBall (A a) R,
      EuclideanSpace ℝ (Fin (d + 1))) :=
    ⟨fun p => A (H (p.1, retraction a hr.le (A.symm p.2.val))), by
      fun_prop⟩
  let HH : (ambientEuclideanMap hr A f).Homotopy
      (ambientEuclideanMap hr A g) := {
    toFun := K
    map_zero_left := by
      intro y
      change A (H (0, retraction a hr.le (A.symm y.val))) =
        A (f (retraction a hr.le (A.symm y.val)))
      exact congrArg A (H.map_zero_left (retraction a hr.le (A.symm y.val)))
    map_one_left := by
      intro y
      change A (H (1, retraction a hr.le (A.symm y.val))) =
        A (g (retraction a hr.le (A.symm y.val)))
      exact congrArg A (H.map_one_left (retraction a hr.le (A.symm y.val))) }
  change euclideanBallDegree hR (ambientEuclideanMap hr A f) _ =
    euclideanBallDegree hR (ambientEuclideanMap hr A g) _
  apply euclideanBallDegree_eq_of_homotopy hR
    (ambientEuclideanMap hr A f)
    (ambientEuclideanMap_boundary_nonzero hr A hcover f hf)
    (ambientEuclideanMap_boundary_nonzero hr A hcover g hg) HH
  intro t y hy
  have hout : A.symm y.val ∉ closedBall a r := by
    intro hin
    have hball := hcover ⟨A.symm y.val, hin⟩
    simp only [ContinuousLinearEquiv.apply_symm_apply] at hball
    exact (ne_of_lt (mem_ball.mp hball)) (mem_sphere.mp hy)
  have hsphere : (retraction a hr.le (A.symm y.val)).val ∈ sphere a r :=
    retraction_mem_sphere a hr.le (le_of_lt (lt_of_not_ge hout))
  intro hz
  exact hH t (retraction a hr.le (A.symm y.val)) hsphere
    (A.map_eq_zero_iff.mp hz)

/-- Linear conjugation preserves the derivative determinant, hence the
sign attached to a regular zero after changing coordinates. -/
theorem conjugate_fderiv_det
    (g : E → E) (x : E) (hg : DifferentiableAt ℝ g x) :
    LinearMap.det
      (fderiv ℝ (fun y => A (g (A.symm y))) (A x)).toLinearMap =
        LinearMap.det (fderiv ℝ g x).toLinearMap := by
  have h₁ : HasFDerivAt (fun y => g (A.symm y))
      ((fderiv ℝ g x).comp A.symm.toContinuousLinearMap) (A x) := by
    have hg' : HasFDerivAt g (fderiv ℝ g x) (A.symm (A x)) := by
      simpa using hg.hasFDerivAt
    have h := hg'.comp (A x) A.symm.hasFDerivAt
    simpa [Function.comp_def] using h
  have h₂ : HasFDerivAt (fun y => A (g (A.symm y)))
      (A.toContinuousLinearMap.comp
        ((fderiv ℝ g x).comp A.symm.toContinuousLinearMap)) (A x) := by
    simpa [Function.comp_def] using A.hasFDerivAt.comp (A x) h₁
  rw [h₂.fderiv]
  exact LinearMap.det_conj (fderiv ℝ g x).toLinearMap A.toLinearEquiv

theorem ambientBallDegree_center
    (hcover : ∀ x : closedBall a r, A x.val ∈ ball (A a) R) :
    ambientBallDegree hr hR A hcover
      ⟨fun y : closedBall a r => y.val - a, by fun_prop⟩
      (by
        intro y hy hz
        have hya : y.val = a := sub_eq_zero.mp hz
        rw [hya] at hy
        have : (0 : ℝ) = r := by simpa using (mem_sphere.mp hy)
        exact hr.ne' this.symm) = 1 := by
  let f : C(E, E) := ⟨fun z => z - a, by fun_prop⟩
  let F : C(closedBall a r, E) := f.restrict (closedBall a r)
  have hb : ∀ y : closedBall a r, y.val ∈ sphere a r → F y ≠ 0 := by
    intro y hy hz
    have hya : y.val = a := sub_eq_zero.mp hz
    rw [hya] at hy
    have : (0 : ℝ) = r := by simpa using (mem_sphere.mp hy)
    exact hr.ne' this.symm
  let G : EuclideanSpace ℝ (Fin (d + 1)) →
      EuclideanSpace ℝ (Fin (d + 1)) :=
    fun z => A (extension a hr.le F (A.symm z))
  have hGzero (z : EuclideanSpace ℝ (Fin (d + 1))) :
      G z = 0 ↔ z = A a := by
    constructor
    · intro hz
      have hz' : extension a hr.le F (A.symm z) = 0 :=
        A.map_eq_zero_iff.mp hz
      obtain ⟨hx, hh⟩ :=
        (extension_eq_iff a hr.le F hb (A.symm z)).mp hz'
      have heq : A.symm z = a := sub_eq_zero.mp hh
      calc
        z = A (A.symm z) := (A.apply_symm_apply z).symm
        _ = A a := by rw [heq]
    · intro hz
      subst z
      have ha : a ∈ closedBall a r := mem_closedBall_self hr.le
      change A (extension a hr.le F (A.symm (A a))) = 0
      rw [A.symm_apply_apply]
      have heq := extension_coe a hr.le F (⟨a, ha⟩ : closedBall a r)
      rw [heq]
      simp [F, f]
  have hS : {z ∈ closedBall (A a) R | G z = 0} = {A a} := by
    ext z
    constructor
    · intro hz
      exact (hGzero z).mp hz.2
    · intro hz
      rw [mem_singleton_iff] at hz
      subst z
      exact ⟨mem_closedBall_self hR.le, (hGzero (A a)).mpr rfl⟩
  have hfinite : {z ∈ closedBall (A a) R | G z = 0}.Finite := by
    rw [hS]
    exact finite_singleton _
  have hcont : ContinuousOn G (closedBall (A a) R) := by
    have hc : Continuous G := by fun_prop
    exact hc.continuousOn
  have hbG : ∀ z ∈ sphere (A a) R, G z ≠ 0 := by
    intro z hz
    exact ambientEuclideanMap_boundary_nonzero hr A hcover F hb
      ⟨z, sphere_subset_closedBall hz⟩ hz
  change euclideanBallDegree hR (ambientEuclideanMap hr A F)
      (ambientEuclideanMap_boundary_nonzero hr A hcover F hb) = 1
  change euclideanBallDegree hR
      (⟨fun y : closedBall (A a) R => G y.val, hcont.domRestrict⟩)
      (fun y hy => hbG y.val hy) = 1
  rw [euclideanBallDegree_eq_finsum_localDegrees hR hcont hfinite hbG]
  classical
  haveI : Fintype {z ∈ closedBall (A a) R | G z = 0} := hfinite.fintype
  let p₀ : {z ∈ closedBall (A a) R | G z = 0} :=
    ⟨A a, by rw [hS]; simp⟩
  have huniq (p : {z ∈ closedBall (A a) R | G z = 0}) : p = p₀ := by
    apply Subtype.ext
    have hp : p.val ∈ ({A a} : Set (EuclideanSpace ℝ (Fin (d + 1)))) := by
      rw [← hS]
      exact p.property
    simpa using hp
  have huniv : (Finset.univ : Finset {z ∈ closedBall (A a) R | G z = 0}) =
      {p₀} := by
    ext p
    simp [huniq p]
  rw [finsum_eq_sum_of_fintype, huniv, Finset.sum_singleton]
  have hevent : (G : EuclideanSpace ℝ (Fin (d + 1)) →
      EuclideanSpace ℝ (Fin (d + 1))) =ᶠ[𝓝 (A a)]
      (fun z => z - A a) := by
    have h₁ : (extension a hr.le F : E → E) =ᶠ[𝓝 a] f :=
      extension_restrict_eventuallyEq a hr.le f (mem_ball_self hr)
    have ht : Filter.Tendsto A.symm (𝓝 (A a)) (𝓝 a) := by
      have ht₀ := A.symm.continuous.continuousAt (x := A a)
      change Filter.Tendsto A.symm (𝓝 (A a)) (𝓝 (A.symm (A a))) at ht₀
      simpa using ht₀
    have h₂ := h₁.comp_tendsto ht
    filter_upwards [h₂] with z hz
    change A (extension a hr.le F (A.symm z)) = z - A a
    change (extension a hr.le F) (A.symm z) = f (A.symm z) at hz
    rw [hz]
    change A (A.symm z - a) = z - A a
    simp
  have hderiv : fderiv ℝ G (A a) =
      fderiv ℝ (fun z : EuclideanSpace ℝ (Fin (d + 1)) => z - A a) (A a) :=
    hevent.fderiv_eq
  have hdiff : DifferentiableAt ℝ G (A a) := by
    apply hevent.differentiableAt_iff.mpr
    show DifferentiableAt ℝ
      (fun z : EuclideanSpace ℝ (Fin (d + 1)) => z - A a) (A a)
    fun_prop
  change euclideanLocalDegree G (A a)
    (isolatedZero_of_finite_closedBall_zeroSet hcont hfinite hbG
      (mem_closedBall_self hR.le) ((hGzero (A a)).mpr rfl)) = 1
  rw [euclideanLocalDegree_eq_sign_det_fderiv _ hdiff]
  · simp [hderiv, fderiv_sub_const]
  · simp [hderiv, fderiv_sub_const]

/-- Regular-zero formula on an arbitrary finite-dimensional norm ball.
The zeros of the radial extension are exactly the original zeros, so
Euclidean finite additivity applies on the enclosing ball. -/
theorem ambientBallDegree_regular_zero_sum
    (hcover : ∀ x : closedBall a r, A x.val ∈ ball (A a) R)
    (g : E → E) (hg : Differentiable ℝ g)
    (Z : Finset E)
    (hZ : ∀ x : E, (x ∈ closedBall a r ∧ g x = 0) ↔ x ∈ Z)
    (hZint : ∀ x ∈ Z, x ∈ ball a r)
    (hdet : ∀ x ∈ Z, LinearMap.det (fderiv ℝ g x).toLinearMap ≠ 0) :
    ambientBallDegree hr hR A hcover
      ⟨fun y : closedBall a r => g y.val,
        hg.continuous.continuousOn.domRestrict⟩
      (by
        intro y hy hz
        have hxZ : y.val ∈ Z := (hZ y.val).mp
          ⟨sphere_subset_closedBall hy, hz⟩
        exact (ne_of_lt (hZint y.val hxZ)) (mem_sphere.mp hy)) =
      ∑ x ∈ Z,
        if 0 < LinearMap.det (fderiv ℝ g x).toLinearMap
        then (1 : ℤ) else -1 := by
  let f : C(E, E) := ⟨g, hg.continuous⟩
  let F : C(closedBall a r, E) := f.restrict (closedBall a r)
  have hb : ∀ y : closedBall a r, y.val ∈ sphere a r → F y ≠ 0 := by
    intro y hy hz
    have hxZ : y.val ∈ Z := (hZ y.val).mp
      ⟨sphere_subset_closedBall hy, hz⟩
    exact (ne_of_lt (hZint y.val hxZ)) (mem_sphere.mp hy)
  let G : EuclideanSpace ℝ (Fin (d + 1)) →
      EuclideanSpace ℝ (Fin (d + 1)) :=
    fun z => A (extension a hr.le F (A.symm z))
  have hGzero (z : EuclideanSpace ℝ (Fin (d + 1))) :
      G z = 0 ↔ A.symm z ∈ Z := by
    rw [show G z = 0 ↔ extension a hr.le F (A.symm z) = 0 from
      A.map_eq_zero_iff]
    rw [extension_eq_iff a hr.le F hb]
    exact ⟨fun ⟨hx, hz⟩ => (hZ _).mp ⟨hx, hz⟩,
      fun hz => ⟨(hZ _).mpr hz |>.1, (hZ _).mpr hz |>.2⟩⟩
  let S : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
    {z ∈ closedBall (A a) R | G z = 0}
  have hSfinite : S.Finite := by
    apply (Z.finite_toSet.image A).subset
    intro z hz
    exact ⟨A.symm z, (hGzero z).mp hz.2, A.apply_symm_apply z⟩
  have hcont : ContinuousOn G (closedBall (A a) R) := by
    have hc : Continuous G := by fun_prop
    exact hc.continuousOn
  have hbG : ∀ z ∈ sphere (A a) R, G z ≠ 0 := by
    intro z hz
    exact ambientEuclideanMap_boundary_nonzero hr A hcover F hb
      ⟨z, sphere_subset_closedBall hz⟩ hz
  change euclideanBallDegree hR (ambientEuclideanMap hr A F)
      (ambientEuclideanMap_boundary_nonzero hr A hcover F hb) = _
  change euclideanBallDegree hR
      (⟨fun y : closedBall (A a) R => G y.val, hcont.domRestrict⟩)
      (fun y hy => hbG y.val hy) = _
  rw [euclideanBallDegree_eq_finsum_localDegrees hR hcont hSfinite hbG]
  classical
  haveI : Fintype S := hSfinite.fintype
  rw [finsum_eq_sum_of_fintype]
  apply Finset.sum_bij (fun p _ => A.symm p.val)
  · intro p _
    exact (hGzero p.val).mp p.property.2
  · intro p _ q _ heq
    apply Subtype.ext
    exact A.symm.injective heq
  · intro x hx
    have hxball := hcover ⟨x, ball_subset_closedBall (hZint x hx)⟩
    let p : S := ⟨A x, ⟨ball_subset_closedBall hxball,
      (hGzero (A x)).mpr (by simpa using hx)⟩⟩
    exact ⟨p, Finset.mem_univ _, by simp [p]⟩
  · intro p _
    let x : E := A.symm p.val
    have hxZ : x ∈ Z := (hGzero p.val).mp p.property.2
    have hxball : x ∈ ball a r := hZint x hxZ
    have h₁ : (extension a hr.le F : E → E) =ᶠ[𝓝 x] f :=
      extension_restrict_eventuallyEq a hr.le f hxball
    have ht : Filter.Tendsto A.symm (𝓝 p.val) (𝓝 x) := by
      have ht₀ := A.symm.continuous.continuousAt (x := p.val)
      change Filter.Tendsto A.symm (𝓝 p.val) (𝓝 (A.symm p.val)) at ht₀
      exact ht₀
    have h₂ := h₁.comp_tendsto ht
    have hevent : G =ᶠ[𝓝 p.val] (fun z => A (g (A.symm z))) := by
      filter_upwards [h₂] with z hz
      exact congrArg A hz
    have hconjdiff : DifferentiableAt ℝ
        (fun z : EuclideanSpace ℝ (Fin (d + 1)) => A (g (A.symm z))) p.val := by
      have hgd : DifferentiableAt ℝ g (A.symm p.val) := hg _
      exact A.differentiableAt.comp _
        (hgd.comp _ A.symm.differentiableAt)
    have hGdiff : DifferentiableAt ℝ G p.val :=
      hevent.differentiableAt_iff.mpr hconjdiff
    have hGdet : LinearMap.det (fderiv ℝ G p.val).toLinearMap =
        LinearMap.det (fderiv ℝ g x).toLinearMap := by
      rw [hevent.fderiv_eq]
      simpa [x] using conjugate_fderiv_det A g x (hg x)
    have hdetG : LinearMap.det (fderiv ℝ G p.val).toLinearMap ≠ 0 := by
      rw [hGdet]
      exact hdet x hxZ
    rw [euclideanLocalDegree_eq_sign_det_fderiv _ hGdiff hdetG]
    rw [hGdet]
    change (SignType.sign (LinearMap.det (fderiv ℝ g x).toLinearMap) : ℤ) =
      if 0 < LinearMap.det (fderiv ℝ g x).toLinearMap then 1 else -1
    by_cases hpos : 0 < LinearMap.det (fderiv ℝ g x).toLinearMap
    · simp [hpos, sign_pos hpos]
    · have hneg : LinearMap.det (fderiv ℝ g x).toLinearMap < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpos) (hdet x hxZ)
      simp [hpos, sign_neg hneg]

/-- Totalize the ambient homological degree to match interfaces which
accept every set-theoretic map. Only admissible maps are used by its laws. -/
def totalAmbientDegree
    (hcover : ∀ x : closedBall a r, A x.val ∈ ball (A a) R)
    (f : closedBall a r → E) : ℤ := by
  classical
  exact if hf : Continuous f then
    if hb : ∀ y : closedBall a r,
        y.val ∈ sphere a r → f y ≠ 0 then
      ambientBallDegree hr hR A hcover ⟨f, hf⟩ hb
    else 0
  else 0

theorem totalAmbientDegree_eq
    (hcover : ∀ x : closedBall a r, A x.val ∈ ball (A a) R)
    (f : closedBall a r → E) (hf : Continuous f)
    (hb : ∀ y : closedBall a r,
      y.val ∈ sphere a r → f y ≠ 0) :
    totalAmbientDegree hr hR A hcover f =
      ambientBallDegree hr hR A hcover ⟨f, hf⟩ hb := by
  classical
  unfold totalAmbientDegree
  simp only [dite_eq_left hf, dite_eq_left hb]

theorem totalAmbientDegree_homotopy_Icc
    (hcover : ∀ x : closedBall a r, A x.val ∈ ball (A a) R)
    (H : ℝ → closedBall a r → E)
    (hcont : ContinuousOn
      (fun p : ℝ × closedBall a r => H p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ univ))
    (hb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      ∀ y : closedBall a r, dist y.val a = r → H t y ≠ 0) :
    totalAmbientDegree hr hR A hcover (H 0) =
      totalAmbientDegree hr hR A hcover (H 1) := by
  let k : I × closedBall a r → ℝ × closedBall a r :=
    fun p => (p.1.val, p.2)
  have hk : Continuous k := by fun_prop
  have hmaps : MapsTo k univ (Icc (0 : ℝ) 1 ×ˢ univ) := by
    intro p _
    exact ⟨p.1.property, mem_univ _⟩
  let h : C(I × closedBall a r, E) :=
    ⟨fun p => H p.1.val p.2, by
      apply continuousOn_univ.mp
      exact hcont.comp hk.continuousOn hmaps⟩
  let f : C(closedBall a r, E) :=
    ⟨fun y => h (0, y),
      h.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let g : C(closedBall a r, E) :=
    ⟨fun y => h (1, y),
      h.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hf : ∀ y : closedBall a r,
      y.val ∈ sphere a r → f y ≠ 0 :=
    fun y hy => hb 0 (by norm_num) y (mem_sphere.mp hy)
  have hg : ∀ y : closedBall a r,
      y.val ∈ sphere a r → g y ≠ 0 :=
    fun y hy => hb 1 (by norm_num) y (mem_sphere.mp hy)
  let hom : f.Homotopy g := {
    toFun := h
    map_zero_left := fun _ => rfl
    map_one_left := fun _ => rfl }
  change totalAmbientDegree hr hR A hcover f =
    totalAmbientDegree hr hR A hcover g
  rw [totalAmbientDegree_eq hr hR A hcover f f.continuous hf,
    totalAmbientDegree_eq hr hR A hcover g g.continuous hg]
  exact ambientBallDegree_eq_of_homotopy hr hR A hcover
    f g hf hg hom (fun t y hy => hb t.val t.property y (mem_sphere.mp hy))

theorem totalAmbientDegree_center
    (hcover : ∀ x : closedBall a r, A x.val ∈ ball (A a) R) :
    totalAmbientDegree hr hR A hcover
      (fun y : closedBall a r => y.val - a) = 1 := by
  have hcont : Continuous (fun y : closedBall a r => y.val - a) := by
    fun_prop
  have hb : ∀ y : closedBall a r,
      y.val ∈ sphere a r → y.val - a ≠ 0 := by
    intro y hy hz
    have hya : y.val = a := sub_eq_zero.mp hz
    rw [hya] at hy
    have : (0 : ℝ) = r := by simpa using (mem_sphere.mp hy)
    exact hr.ne' this.symm
  rw [totalAmbientDegree_eq hr hR A hcover _ hcont hb]
  exact ambientBallDegree_center hr hR A hcover

theorem totalAmbientDegree_regular_zero_sum
    (hcover : ∀ x : closedBall a r, A x.val ∈ ball (A a) R)
    (g : E → E) (hg : Differentiable ℝ g)
    (Z : Finset (closedBall a r))
    (hZ : ∀ y : closedBall a r, g y.val = 0 ↔ y ∈ Z)
    (hb : ∀ y : closedBall a r,
      dist y.val a = r → g y.val ≠ 0)
    (hdet : ∀ y ∈ Z,
      LinearMap.det (fderiv ℝ g y.val).toLinearMap ≠ 0) :
    totalAmbientDegree hr hR A hcover
      (fun y : closedBall a r => g y.val) =
      ∑ y ∈ Z,
        if 0 < LinearMap.det (fderiv ℝ g y.val).toLinearMap
        then (1 : ℤ) else -1 := by
  classical
  let ZE : Finset E := Z.image Subtype.val
  have hZE (x : E) : (x ∈ closedBall a r ∧ g x = 0) ↔ x ∈ ZE := by
    constructor
    · rintro ⟨hx, hgzero⟩
      exact Finset.mem_image.mpr
        ⟨⟨x, hx⟩, (hZ ⟨x, hx⟩).mp hgzero, rfl⟩
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨y.property, (hZ y).mpr hy⟩
  have hZEint : ∀ x ∈ ZE, x ∈ ball a r := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    apply Metric.mem_ball.mpr
    have hle : dist y.val a ≤ r := Metric.mem_closedBall.mp y.property
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact False.elim (hb y heq ((hZ y).mpr hy))
  have hdetE : ∀ x ∈ ZE,
      LinearMap.det (fderiv ℝ g x).toLinearMap ≠ 0 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hdet y hy
  have hcont : Continuous (fun y : closedBall a r => g y.val) :=
    hg.continuous.continuousOn.domRestrict
  have hbsphere : ∀ y : closedBall a r,
      y.val ∈ sphere a r → g y.val ≠ 0 :=
    fun y hy => hb y (mem_sphere.mp hy)
  rw [totalAmbientDegree_eq hr hR A hcover _ hcont hbsphere]
  calc
    _ = ∑ x ∈ ZE,
          if 0 < LinearMap.det (fderiv ℝ g x).toLinearMap
          then (1 : ℤ) else -1 :=
      ambientBallDegree_regular_zero_sum hr hR A hcover g hg
        ZE hZE hZEint hdetE
    _ = _ := by
      dsimp [ZE]
      rw [Finset.sum_image]
      intro x _ y _ hxy
      exact Subtype.val_injective hxy

end

end PhosphorylationStableCapacity.Topology435
