module
public import proofs.PhosphorylationStableCapacity.SplitStableAttainment

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Filter
open scoped Topology

/-- Any property that holds sufficiently far along the positive real ray
holds at a rational point. -/
private theorem rational_of_eventually_atTop {P : ℝ → Prop}
    (h : ∀ᶠ r : ℝ in atTop, P r) : ∃ q : ℚ, P (q : ℝ) := by
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.1 h
  obtain ⟨q, hq⟩ := exists_rat_gt b
  exact ⟨q, hb (q : ℝ) hq.le⟩

/-- Rational points meet every punctured right neighborhood of zero. -/
private theorem rational_of_eventually_pos {P : ℝ → Prop}
    (h : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), P x) :
    ∃ q : ℚ, 0 < (q : ℝ) ∧ P (q : ℝ) := by
  have h' := eventually_nhdsWithin_iff.1 h
  obtain ⟨a, b, ⟨ha, hb⟩, hab⟩ :=
    mem_nhds_iff_exists_Ioo_subset.1 h'
  obtain ⟨q, hq0, hqb⟩ := exists_rat_btwn hb
  refine ⟨q, hq0, ?_⟩
  exact hab ⟨lt_trans ha hq0, hqb⟩ hq0

/-- Rational parameters can be selected from the same nested spectral,
conversion-positivity, and full-family admissibility conditions used for
the simultaneous hyperbolic-sink construction. -/
theorem rational_split_spectral_parameters (m : ℕ) :
    ∃ r τ δ ε : ℚ,
      (1 : ℝ) < (r : ℝ) ∧
      0 < (τ : ℝ) ∧ 0 < (δ : ℝ) ∧
      0 < (ε : ℝ) ∧ (ε : ℝ) ≤ 1 ∧
      DensePositive (splitRawD (m+1) (r : ℝ) (δ : ℝ)) (m+1) ∧
      DensePositive (splitRawB (m+1) (r : ℝ) (δ : ℝ)) (m+1) ∧
      (∀ j : Fin (2*(m+1)+1),
        0 < (r : ℝ)-ratio (splitRoot (δ : ℝ) j.val)) ∧
      ∃ ρ : Fin (2*(m+1)+1) → ℝ,
        SplitRetunedFamilyAdmissible m (r : ℝ) (τ : ℝ) (δ : ℝ) (ε : ℝ) ∧
        ∀ j, SplitSlowModeCertificate m (r : ℝ) (τ : ℝ)
          (δ : ℝ) (ε : ℝ) j (ρ j) := by
  obtain ⟨hp, hq⟩ := coalescedPair_dense (m+1)
  have hconv := conversion_eventually_positive hp hq
  have hr1 : ∀ᶠ r : ℝ in atTop, 1 < r := eventually_gt_atTop 1
  obtain ⟨r, ⟨hspec, hconv⟩, hr1⟩ :=
    rational_of_eventually_atTop
      (((coalescedSpectral_splitFamily_simpleSlow_eventually m).and hconv).and hr1)
  have hτpos : ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), 0 < τ := self_mem_nhdsWithin
  obtain ⟨τ, hτ, ⟨hspec, _⟩⟩ := rational_of_eventually_pos (hspec.and hτpos)
  have hεle : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 := by
    have hnear : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ε < 1 :=
      Iio_mem_nhds (by norm_num)
    exact (hnear.filter_mono nhdsWithin_le_nhds).mono (fun _ h => h.le)
  obtain ⟨ε, hε, ⟨hspec, hεle⟩⟩ :=
    rational_of_eventually_pos
      ((hspec.filter_mono nhdsWithin_le_nhds).and hεle)
  obtain ⟨ρ, _, hδspec⟩ := hspec hε hεle
  have hδconv := split_conversion_positive_near_zero (m+1) (r : ℝ)
    (by linarith : (r : ℝ) ≠ 0) hconv.1 hconv.2
  have hδhv := split_root_ratios_below_source_eventually
    (m+1) (r : ℝ) hr1
  obtain ⟨δ, hδ, ⟨⟨hspec, hconv⟩, hv⟩⟩ :=
    rational_of_eventually_pos ((hδspec.and hδconv).and hδhv)
  exact ⟨r, τ, δ, ε, hr1, hτ, hδ, hε, hεle,
    hconv.1, hconv.2, hv, ρ, hspec.1, hspec.2⟩

end
end PhosphorylationStableCapacity
