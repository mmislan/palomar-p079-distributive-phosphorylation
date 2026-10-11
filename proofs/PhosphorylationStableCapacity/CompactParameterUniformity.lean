module
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Analysis.Normed.Group.Uniform

@[expose] public section

open Filter
open scoped Topology

namespace PhosphorylationStableCapacity

noncomputable section

/-- Joint continuity gives uniform control in a parameter over a
compact set of states. This is the quantitative tube-lemma input for
preserving zero-free boundaries under rate perturbations. -/
theorem continuous_family_uniform_near_compact
    {P X Y : Type*} [MetricSpace P] [TopologicalSpace X]
    [NormedAddCommGroup Y]
    (F : P → X → Y)
    (hF : Continuous (fun z : P × X => F z.1 z.2))
    (p₀ : P) (K : Set X) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ p : P, dist p p₀ < δ →
        ∀ x ∈ K, ‖F p x - F p₀ x‖ < ε := by
  let U : Set (P × X) :=
    {z | ‖F z.1 z.2 - F p₀ z.2‖ < ε}
  have hfixed : Continuous (fun z : P × X => F p₀ z.2) :=
    hF.comp (continuous_const.prodMk continuous_snd)
  have hU : IsOpen U :=
    isOpen_Iio.preimage ((hF.sub hfixed).norm)
  have hsubset : ({p₀} : Set P) ×ˢ K ⊆ U := by
    intro z hz
    rcases hz with ⟨hp, _⟩
    have hp₀ : z.1 = p₀ := Set.mem_singleton_iff.mp hp
    change ‖F z.1 z.2 - F p₀ z.2‖ < ε
    rw [hp₀, sub_self, norm_zero]
    exact hε
  obtain ⟨V, W, hV, _, hpV, hKW, hVW⟩ :=
    generalized_tube_lemma isCompact_singleton hK hU hsubset
  have hVnhds : V ∈ 𝓝 p₀ := hV.mem_nhds (hpV (Set.mem_singleton p₀))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hVnhds
  refine ⟨δ, hδ, ?_⟩
  intro p hp x hx
  have hz : (p, x) ∈ U :=
    hVW ⟨hball (Metric.mem_ball.mpr hp), hKW hx⟩
  exact hz

end
end PhosphorylationStableCapacity
