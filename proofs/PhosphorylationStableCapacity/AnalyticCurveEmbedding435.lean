module
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Topology.PartialHomeomorph.Basic
public import Mathlib.Topology.Constructions

@[expose] public section
namespace P079UnstableWorkbench
open scoped Topology
open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A genuinely nonzero tangent admits a continuous real coordinate functional.
Its construction uses Hahn--Banach, with no assumption on the nonlinear curve. -/
theorem nonzero_tangent_coordinate (v : E) (hv : v ≠ 0) :
    ∃ L : E →L[ℝ] ℝ, L v = 1 := by
  obtain ⟨L, -, hL⟩ := exists_dual_vector ℝ v (norm_ne_zero_iff.mpr hv)
  refine ⟨‖v‖⁻¹ • L, ?_⟩
  simp only [smul_apply, smul_eq_mul, hL]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)

/-- An analytic vector curve with a nonzero tangent is a true local topological
embedding, and remains an immersion on the same open parameter neighborhood.
This uses a scalar projection and the actual inverse function theorem. -/
theorem analyticCurve_open_embedding
    (h : ℝ → E) (v : E) (ha : AnalyticAt ℝ h 0)
    (hv : v ≠ 0) (hderiv : fderiv ℝ h 0 1 = v) :
    ∃ U : Set ℝ, IsOpen U ∧ 0 ∈ U ∧
      Topology.IsEmbedding (fun s : U => h s) ∧
      ∀ s ∈ U, fderiv ℝ h s 1 ≠ 0 := by
  obtain ⟨L, hL⟩ := nonzero_tangent_coordinate v hv
  let g : ℝ → ℝ := fun s => L (h s)
  have hga : AnalyticAt ℝ g 0 := (L.analyticAt (h 0)).comp ha
  have hgD : HasFDerivAt g (L.comp (fderiv ℝ h 0)) 0 :=
    L.hasFDerivAt.comp 0 ha.differentiableAt.hasFDerivAt
  have hgd : deriv g 0 = 1 := by
    rw [← fderiv_apply_one_eq_deriv, hgD.fderiv,
      ContinuousLinearMap.comp_apply, hderiv, hL]
  have hgstrict : HasStrictDerivAt g 1 0 := by
    simpa only [hgd] using hga.hasStrictDerivAt
  let hge := hgstrict.hasStrictFDerivAt_equiv one_ne_zero
  let e := hge.toOpenPartialHomeomorph g
  have he0 : 0 ∈ e.source := hge.mem_toOpenPartialHomeomorph_source
  have hdcont : ContinuousAt (fun s => fderiv ℝ h s 1) 0 :=
    ha.fderiv.continuousAt.clm_apply continuousAt_const
  have hdn : ∀ᶠ s in 𝓝 (0 : ℝ), fderiv ℝ h s 1 ≠ 0 := by
    have hn : {x : E | x ≠ 0} ∈ 𝓝 (fderiv ℝ h 0 1) :=
      isOpen_compl_singleton.mem_nhds (by simpa only [hderiv, Set.mem_compl_iff, Set.mem_singleton_iff] using hv)
    exact hdcont hn
  obtain ⟨V, hVsub, hVopen, hV0⟩ := mem_nhds_iff.mp
    (ha.eventually_continuousAt.and hdn)
  let U : Set ℝ := V ∩ e.source
  have hUsub : U ⊆ e.source := Set.inter_subset_right
  have hUcont : Continuous (fun s : U => h s) := by
    apply continuousOn_iff_continuous_domRestrict.mp
    intro s hs
    exact (hVsub hs.1).1.continuousWithinAt
  have hgembed : Topology.IsEmbedding (fun s : U => g s) := by
    have hemb := e.isEmbedding_restrict.comp (Topology.IsEmbedding.inclusion hUsub)
    change Topology.IsEmbedding (fun s : U => e s) at hemb
    simpa only [e, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using hemb
  refine ⟨U, hVopen.inter e.open_source, ⟨hV0, he0⟩,
    Topology.IsEmbedding.of_comp hUcont L.continuous hgembed, ?_⟩
  intro s hs
  exact (hVsub hs.1).2

end P079UnstableWorkbench
