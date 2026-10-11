module
public import proofs.PhosphorylationStableCapacity.RankOneMetzlerPerturbation
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.Analysis.Normed.Algebra.Spectrum

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open Filter Matrix
open scoped Topology Matrix.Norms.L2Operator
set_option maxHeartbeats 2000000

private theorem isOpen_hurwitz_matrices
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsOpen {A : Matrix ι ι ℝ | IsHurwitz A} := by
  classical
  apply isOpen_iff_mem_nhds.mpr
  intro A hA
  let U : Set ℂ := {z | z.re < 0}
  have hU : IsOpen U := isOpen_Iio.preimage Complex.continuous_re
  have hspec : spectrum ℂ (A.map (algebraMap ℝ ℂ)) ⊆ U := by
    intro z hz
    exact hA z ((Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz).eq_zero)
  have hnear :=
    (upperHemicontinuous_spectrum ℂ (Matrix ι ι ℂ)).forall_isOpen
      (A.map (algebraMap ℝ ℂ)) U hU hspec
  have hmap : Continuous (fun B : Matrix ι ι ℝ =>
      B.map (algebraMap ℝ ℂ)) := by
    apply continuous_matrix
    intro i j
    exact Complex.continuous_ofReal.comp (continuous_apply j |>.comp (continuous_apply i))
  apply Filter.mem_of_superset (hmap.continuousAt.tendsto.eventually hnear)
  intro B hB z hz
  exact hB ((Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    (Polynomial.IsRoot.def.mpr hz)))

/-- A jointly continuous matrix family that is Hurwitz above a compact
parameter set at zero stays Hurwitz there for one common small parameter. -/
theorem compact_continuous_matrixFamily_eventually_hurwitz
    {α ι : Type*} [TopologicalSpace α]
    [Fintype ι] [DecidableEq ι]
    (K : Set α) (hK : IsCompact K)
    (F : α × ℝ → Matrix ι ι ℝ)
    (hF : Continuous F)
    (h0 : ∀ a ∈ K, IsHurwitz (F (a, 0))) :
    ∀ᶠ τ : ℝ in 𝓝 0,
      ∀ a ∈ K,
        IsHurwitz (F (a, τ)) := by
  let S : Set (α × ℝ) := {p | IsHurwitz (F p)}
  have hSopen : IsOpen S := isOpen_hurwitz_matrices.preimage hF
  have hprod : K ×ˢ ({0} : Set ℝ) ⊆ S := by
    rintro ⟨a, t⟩ ⟨ha, ht⟩
    have ht0 : t = 0 := Set.mem_singleton_iff.mp ht
    subst t
    exact h0 a ha
  obtain ⟨U, V, _, hVopen, hKU, h0V, hUV⟩ :=
    generalized_tube_lemma hK isCompact_singleton hSopen hprod
  have hV : V ∈ 𝓝 (0 : ℝ) :=
    hVopen.mem_nhds (h0V (by simp))
  filter_upwards [hV] with τ hτ a ha
  exact hUV ⟨hKU ha, hτ⟩

/-- A compact family of Hurwitz prefix matrices admits one common small
rank-one shear parameter when the shear matrix is jointly continuous. -/
theorem compact_rankOneShear_eventually_hurwitz
    {α ι : Type*} [TopologicalSpace α]
    [Fintype ι] [DecidableEq ι]
    (K : Set α) (hK : IsCompact K)
    (A : α → Matrix ι ι ℝ) (u c : α → ι → ℝ)
    (hA : ∀ a ∈ K, IsHurwitz (A a))
    (hcont : Continuous (fun p : α × ℝ =>
      rankOneShearComplement (A p.1) (u p.1) (c p.1) p.2)) :
    ∀ᶠ τ : ℝ in 𝓝 0,
      ∀ a ∈ K,
        IsHurwitz (rankOneShearComplement (A a) (u a) (c a) τ) := by
  apply compact_continuous_matrixFamily_eventually_hurwitz K hK
    (fun p => rankOneShearComplement (A p.1) (u p.1) (c p.1) p.2) hcont
  intro a ha
  have hzeroeq :
      rankOneShearComplement (A a) (u a) (c a) 0 = A a := by
    ext i j
    simp [rankOneShearComplement]
  rw [hzeroeq]
  exact hA a ha

end

end PhosphorylationStableCapacity
