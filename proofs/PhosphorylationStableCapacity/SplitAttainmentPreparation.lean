module
public import proofs.PhosphorylationStableCapacity.SplitRetunedSource
public import proofs.PhosphorylationStableCapacity.CoalescedAdmissibleSpectralSource

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter PhosphorylationSharpness Polynomial Matrix
open scoped Topology

/-- A real matrix has one algebraically simple neutral characteristic
factor and a Hurwitz complementary factor. -/
def SimpleNeutralHurwitzComplement
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : Prop :=
  ∃ p : ℂ[X],
    ((M.map (algebraMap ℝ ℂ)).charpoly) = Polynomial.X * p ∧
      p.eval 0 ≠ 0 ∧
      ∀ z : ℂ, p.eval z = 0 → z.re < 0

/-- The full geometric split certificate at one common rate list. -/
def SplitRetunedFamilyAdmissible (m : ℕ) (r τ δ ε : ℝ) : Prop :=
  (splitRetunedRates m r τ δ ε).Positive ∧
    Function.Injective (splitFiniteState (m+1) r δ) ∧
    ∀ j : Fin (2*(m+1)+1),
      (splitFiniteState (m+1) r δ j).Positive ∧
      Equilibrium (splitRetunedRates m r τ δ ε)
        (splitFiniteState (m+1) r δ j) ∧
      totalE (splitFiniteState (m+1) r δ j) = 2*r ∧
      totalF (splitFiniteState (m+1) r δ j) = 2 ∧
      totalS (splitFiniteState (m+1) r δ j) = 2*(r+1)

/-- A fixed conversion parameter, final-edge weight, and binding scale
produce a near-coalescent family of `2m+3` distinct positive equilibria.
Every state uses the same retuned rate list and totals. This proves the
source geometry needed for attainment, but makes no stability claim for
the split states. -/
theorem splitRetunedSource_eventually_admissible
    (m : ℕ) (r τ ε : ℝ)
    (hr : 0 < r) (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1)) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      (splitRetunedRates m r τ δ ε).Positive ∧
        Function.Injective (splitFiniteState (m+1) r δ) ∧
        ∀ j : Fin (2*(m+1)+1),
          (splitFiniteState (m+1) r δ j).Positive ∧
          Equilibrium (splitRetunedRates m r τ δ ε)
            (splitFiniteState (m+1) r δ j) ∧
          totalE (splitFiniteState (m+1) r δ j) = 2*r ∧
          totalF (splitFiniteState (m+1) r δ j) = 2 ∧
          totalS (splitFiniteState (m+1) r δ j) = 2*(r+1) := by
  have hsplit := split_conversion_positive_near_zero (m+1) r
    (ne_of_gt hr) hD₀ hB₀
  have hδpos : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ :=
    self_mem_nhdsWithin
  filter_upwards [hsplit, hδpos] with δ hconv hδ
  have hroot : Function.Injective (splitFiniteState (m+1) r δ) :=
    splitFiniteState_injective (m+1) r hδ
  have hsource (j : Fin (2*(m+1)+1)) :=
    splitRetunedState_source_of_conversion_positive m r τ δ ε
      hτ hδ.le hε hε1 hconv.1 hconv.2 j
  exact ⟨(hsource 0).1, hroot, fun j => (hsource j).2⟩

/-- The neutral spectral source and the near-coalescent positive split family
can be chosen with the *same* `r`, final-edge weight, binding scale, and
chemical realization. The missing attainment step is spectral transport to
the split states and classification of their one small eigenvalue. -/
theorem coalescedSpectral_and_splitFamily_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        ∀ᶠ ε : ℝ in 𝓝 0,
          0 < ε → ε ≤ 1 →
            SimpleNeutralHurwitzComplement
              (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
                (splitRetunedRates m r τ 0 ε)
                (fromLoadedCoord
                  (loadedCoordOfState (coalescedFiniteState (m+1) r)))) ∧
            ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
              SplitRetunedFamilyAdmissible m r τ δ ε := by
  obtain ⟨hp, hq⟩ := coalescedPair_dense (m+1)
  have hconv := conversion_eventually_positive hp hq
  have hrpos : ∀ᶠ r : ℝ in atTop, 0 < r := eventually_gt_atTop 0
  filter_upwards [coalescedAdmissibleSpectralSource_eventually m,
    hconv, hrpos] with r hsource hconv hr
  have hτpos : ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), 0 < τ :=
    self_mem_nhdsWithin
  filter_upwards [hsource, hτpos] with τ hsource hτ
  filter_upwards [hsource] with ε hsource hε hε1
  rcases hsource hε hε1 with ⟨_, _, _, _, _, _, _, hspec⟩
  have hsplit := splitRetunedSource_eventually_admissible
    m r τ ε hr hτ hε hε1 hconv.1 hconv.2
  constructor
  · simpa only [SimpleNeutralHurwitzComplement,
      splitRetunedRates_zero_eq_coalesced] using hspec
  · simpa only [SplitRetunedFamilyAdmissible] using hsplit

end
end PhosphorylationStableCapacity
