module
public import proofs.PhosphorylationStableCapacity.ContinuousNeutralMatrixFamily435
public import proofs.PhosphorylationStableCapacity.CompactLocalPersistence435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial Filter
open scoped Topology

/-- A compact family of simple-neutral real matrices has one common
perturbation interval on which every member retains exactly one simple
real slow eigenvalue and all other spectrum lies to its left. -/
theorem compact_jointNeutralMatrix_slowMode_eventually
    {α ι : Type*} [PseudoMetricSpace α]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (K : Set α) (hK : IsCompact K)
    (J : α × ℝ → Matrix ι ι ℝ)
    (hJ : ∀ a ∈ K, ContinuousAt J (a, 0))
    (hspec : ∀ a ∈ K, SimpleNeutralHurwitzComplement (J (a, 0))) :
    ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ a ∈ K, ∃ x : ℝ,
        (J (a, δ)).charpoly.IsRoot x ∧
          (((J (a, δ)).map (algebraMap ℝ ℂ)).charpoly).derivative.eval
            (x : ℂ) ≠ 0 ∧
          ∀ z : ℂ,
            z ∈ spectrum ℂ ((J (a, δ)).map (algebraMap ℝ ℂ)) →
              z.re < 0 ∨ z = (x : ℂ) := by
  let S : Set (α × ℝ) := {p | ∃ x : ℝ,
    (J p).charpoly.IsRoot x ∧
      (((J p).map (algebraMap ℝ ℂ)).charpoly).derivative.eval
        (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ,
        z ∈ spectrum ℂ ((J p).map (algebraMap ℝ ℂ)) →
          z.re < 0 ∨ z = (x : ℂ)}
  have hlocal : ∀ a ∈ K, S ∈ 𝓝 (a, 0) := by
    intro a ha
    obtain ⟨ρ, hρ, hlocal⟩ :=
      continuousNeutralMatrix_slowMode_eventually_at
        J (a, 0) (hJ a ha) (hspec a ha)
    filter_upwards [hlocal] with p hp
    obtain ⟨x, _, hroot, hsimple, hleft⟩ := hp
    exact ⟨x, hroot, hsimple, hleft⟩
  exact compact_eventually_of_local_neighborhoods K hK 0 S hlocal

end

end PhosphorylationStableCapacity
