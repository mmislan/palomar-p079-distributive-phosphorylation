module
public import proofs.PhosphorylationStableCapacity.SplitAugmentedRootOrientation
public import proofs.PhosphorylationStableCapacity.SourceCurrentResponseChain
public import proofs.PhosphorylationStableCapacity.BaseCase

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness
open Filter
open scoped Topology

/-- At zero splitting every prescribed root has ratio one, so a
source parameter above one keeps all finitely many nearby roots in
the regular positive chart. -/
theorem split_root_ratios_below_source_eventually
    (m : ℕ) (r : ℝ) (hr : 1 < r) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j : Fin (2*m+1), 0 < r-ratio (splitRoot δ j.val) := by
  apply Filter.eventually_all.mpr
  intro j
  have hc : ContinuousAt
      (fun δ : ℝ => r-ratio (splitRoot δ j.val)) 0 := by
    unfold splitRoot ratio
    fun_prop
  have hzero : 0 < r-ratio (splitRoot 0 j.val) := by
    norm_num [splitRoot, ratio]
    linarith
  exact (hc.eventually (Ioi_mem_nhds hzero)).filter_mono
    nhdsWithin_le_nhds

/-- The physical split-root orientation closes the former augmented
determinant premise of the all-size stable-attainment assembly. -/
theorem split_even_stable_attains_of_uniform_spectral_certificate
    (m : ℕ) (r τ δ ε : ℝ)
    (hr : 0 < r) (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 < δ)
    (hD : DensePositive (splitRawD (m+1) r δ) (m+1))
    (hB : DensePositive (splitRawB (m+1) r δ) (m+1))
    (hv : ∀ j : Fin (2*(m+1)+1),
      0 < r-ratio (splitRoot δ j.val))
    (hadm : SplitRetunedFamilyAdmissible m r τ δ ε)
    (ρ : Fin (2*(m+1)+1) → ℝ)
    (hcert : ∀ j, SplitSlowModeCertificate m r τ δ ε j (ρ j)) :
    LinearlyStableClassAttains (m+2) (m+2) := by
  apply split_even_augmented_current_positive_attains
    m r τ δ ε hr hτ hε hδ.le hD hB hadm ρ hcert
  intro i
  have heven : Even (splitEvenIndex m i).val := by
    simp [splitEvenIndex]
  simpa only [Nat.add_assoc] using
    split_even_source_augmented_current_det_pos
      (m+1) r δ (splitEvenIndex m i) hr hδ hD hB
      (hv (splitEvenIndex m i)) heven

/-- The coalesced simple-slow spectral family, strict orientation at
each even split root, and finite chart positivity yield all-size
linear stable attainment for sufficiently near-coalescent parameters. -/
theorem coalescedSpectral_splitFamily_stable_eventually (m : ℕ) :
    ∀ᶠ _r : ℝ in atTop,
      ∀ᶠ _τ : ℝ in 𝓝[>] (0 : ℝ),
        ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
          0 < ε → ε ≤ 1 →
            ∀ᶠ _δ : ℝ in 𝓝[>] (0 : ℝ),
              LinearlyStableClassAttains (m+2) (m+2) := by
  obtain ⟨hp, hq⟩ := coalescedPair_dense (m+1)
  have hconv := conversion_eventually_positive hp hq
  have hr1 : ∀ᶠ r : ℝ in atTop, 1 < r := eventually_gt_atTop 1
  filter_upwards [coalescedSpectral_splitFamily_simpleSlow_eventually m,
    hconv, hr1] with r hspec hconv hr1
  have hτpos : ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), 0 < τ :=
    self_mem_nhdsWithin
  filter_upwards [hspec, hτpos] with τ hspec hτ
  filter_upwards [hspec] with ε hspec hε hε1
  obtain ⟨ρ, _, hδspec⟩ := hspec hε hε1
  have hδconv := split_conversion_positive_near_zero (m+1) r
    (by linarith : r ≠ 0) hconv.1 hconv.2
  have hδhv := split_root_ratios_below_source_eventually
    (m+1) r hr1
  have hδpos : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ :=
    self_mem_nhdsWithin
  filter_upwards [hδspec, hδconv, hδhv, hδpos]
    with δ hspec hconv hv hδ
  exact split_even_stable_attains_of_uniform_spectral_certificate
    m r τ δ ε (by linarith) hτ hε hδ
    hconv.1 hconv.2 hv hspec.1 ρ hspec.2

/-- Unconditional all-size linear stable-state attainment for every
chain with at least two phosphorylation sites. -/
theorem split_linearly_stable_capacity_attained (m : ℕ) :
    LinearlyStableClassAttains (m+2) (m+2) := by
  obtain ⟨r, hr⟩ := (coalescedSpectral_splitFamily_stable_eventually m).exists
  obtain ⟨τ, hτ⟩ := hr.exists
  have hεpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε :=
    self_mem_nhdsWithin
  have hεle : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 := by
    have hnear : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ε < 1 :=
      Iio_mem_nhds (by norm_num)
    exact (hnear.filter_mono nhdsWithin_le_nhds).mono
      (fun _ h => h.le)
  obtain ⟨ε, ⟨hε, hpos⟩, hle⟩ :=
    ((hτ.filter_mono nhdsWithin_le_nhds).and hεpos |>.and hεle).exists
  obtain ⟨δ, hstable⟩ := (hε hpos hle).exists
  exact hstable

/-- Every positive chain size attains its claimed Hurwitz lower bound
with one common rate list and one common compatibility class. -/
theorem all_size_linearly_stable_attainment (n : ℕ) (hn : 1 ≤ n) :
    LinearlyStableClassAttains n n := by
  cases n with
  | zero => omega
  | succ n =>
      cases n with
      | zero => simpa using one_site_linearly_stable_attainment
      | succ m =>
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
            split_linearly_stable_capacity_attained m

end
end PhosphorylationStableCapacity
