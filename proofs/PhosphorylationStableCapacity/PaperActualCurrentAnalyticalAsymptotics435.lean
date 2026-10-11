module
public import proofs.PhosphorylationStableCapacity.PaperActualCurrentAnalyticalTradeoff435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitRootGapNonzero
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Polynomial
open scoped Topology BigOperators

private theorem actualCurrent_tendsto_of_linear_error
    (f : ℝ → ℝ) (L C : ℝ)
    (hbound : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), |f δ-L| ≤ C*|δ|) :
    Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  have hid : Tendsto (fun δ : ℝ => δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hupper : Tendsto (fun δ : ℝ => C*|δ|)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [abs_zero, mul_zero] using
      (tendsto_const_nhds.mul hid.abs)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ hupper
  simpa only [Real.dist_eq] using hbound

private theorem actualCurrent_scaled_slow_limit
    (lam : ℝ → ℝ) (N : ℕ) (A gap K : ℝ)
    (hA : 0 < A) (hgap : gap ≠ 0)
    (hbound : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      |lam δ/(-A*δ^N*gap)-1| ≤ K*|δ|) :
    Tendsto (fun δ => lam δ/δ^N)
      (𝓝[>] (0 : ℝ)) (𝓝 (-A*gap)) := by
  have hratio := actualCurrent_tendsto_of_linear_error
    (fun δ => lam δ/(-A*δ^N*gap)) 1 K hbound
  have hprod : Tendsto (fun δ => (lam δ/(-A*δ^N*gap))*(-A*gap))
      (𝓝[>] (0 : ℝ)) (𝓝 (-A*gap)) := by
    simpa only [one_mul] using hratio.mul tendsto_const_nhds
  apply Tendsto.congr' _ hprod
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hp : δ^N ≠ 0 := pow_ne_zero _ (ne_of_gt hδ)
  field_simp [ne_of_gt hA, hgap, hp]

private theorem actualCurrent_scaled_reciprocal_limit
    (lam : ℝ → ℝ) (N : ℕ) (A gap : ℝ)
    (hA : 0 < A) (hgap : gap ≠ 0)
    (hslow : Tendsto (fun δ => lam δ/δ^N)
      (𝓝[>] (0 : ℝ)) (𝓝 (-A*gap))) :
    Tendsto (fun δ => δ^N/|lam δ|)
      (𝓝[>] (0 : ℝ)) (𝓝 (1/(A*|gap|))) := by
  have hnorm : Tendsto (fun δ => |lam δ/δ^N|)
      (𝓝[>] (0 : ℝ)) (𝓝 (A*|gap|)) := by
    simpa only [abs_mul, abs_neg, abs_of_pos hA] using hslow.abs
  have hden : A*|gap| ≠ 0 := mul_ne_zero (ne_of_gt hA) (abs_ne_zero.mpr hgap)
  have hrec : Tendsto (fun δ => 1/|lam δ/δ^N|)
      (𝓝[>] (0 : ℝ)) (𝓝 (1/(A*|gap|))) :=
    tendsto_const_nhds.div hnorm hden
  apply Tendsto.congr' _ hrec
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  simp only [abs_div, abs_of_pos (pow_pos hδ N), one_div, inv_div]

private theorem actualCurrent_reciprocal_diverges
    (lam : ℝ → ℝ) (N : ℕ) (hN : 1 ≤ N) (A gap : ℝ)
    (hA : 0 < A) (hgap : gap ≠ 0)
    (hslow : Tendsto (fun δ => lam δ/δ^N)
      (𝓝[>] (0 : ℝ)) (𝓝 (-A*gap))) :
    Tendsto lam (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Tendsto (fun δ => 1/|lam δ|) (𝓝[>] (0 : ℝ)) atTop := by
  have hid : Tendsto (fun δ : ℝ => δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hpow : Tendsto (fun δ : ℝ => δ^N)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow (by omega : N ≠ 0)] using hid.pow N
  have hprod : Tendsto (fun δ => (lam δ/δ^N)*δ^N)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hslow.mul hpow
  have hzero : Tendsto lam (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply Tendsto.congr' _ hprod
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact div_mul_cancel₀ _ (pow_ne_zero _ (ne_of_gt hδ))
  have hnorm : Tendsto (fun δ => |lam δ/δ^N|)
      (𝓝[>] (0 : ℝ)) (𝓝 (A*|gap|)) := by
    simpa only [abs_mul, abs_neg, abs_of_pos hA] using hslow.abs
  have hnormPos : 0 < A*|gap| := mul_pos hA (abs_pos.mpr hgap)
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < |lam δ| := by
    filter_upwards [hnorm.eventually (Ioi_mem_nhds hnormPos)] with δ hd
    apply abs_pos.mpr
    intro hz
    exact (lt_irrefl (0 : ℝ)) (by simpa only [hz, zero_div, abs_zero] using hd)
  have habs : Tendsto (fun δ => |lam δ|)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa only [abs_zero] using hzero.abs, hpos⟩
  refine ⟨hzero, ?_⟩
  simpa only [one_div, Function.comp_def] using tendsto_inv_nhdsGT_zero.comp habs

/-- Actual physical separation and reciprocal growth in the same selected
analytic family. The last limit eliminates the split parameter: physical
readout separation to the power `2n-2`, multiplied by the slow-mode
relaxation time, has its explicit nonzero limit whenever the readouts
are distinct. No separately chosen rate vector or eigenvalue is used. -/
def PaperActualCurrentAnalyticalAsymptotics
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε α K Cread : ℝ)
    (θ : Fin (m+1) → ℝ) (lam : Fin (2*(m+1)+1) → ℝ → ℝ) : Prop :=
  let N := 2*(m+1)
  let A := paperFixedBindingPrintedCoefficient m r τ ε θ
  let ρ := deriv (splitReadoutScalar (m+1) (coalescedRawD (m+1) r)) 3
  let R := fun δ j => fullyPhosphorylatedReadout (m+1)
    (arbitrarySplitFiniteState (m+1) ξ r δ j)
  let gap := fun j : Fin (2*(m+1)+1) =>
    ∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val, (ξ j.val-ξ i)
  0 < ρ ∧
    (∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      PaperFixedBindingCompletePoint m ξ r τ ε α K δ θ lam ∧
        ∀ j k, |(R δ j-R δ k)-(ξ j.val-ξ k.val)*ρ*δ| ≤ Cread*δ^2) ∧
    (∀ j k, Tendsto (fun δ => (R δ j-R δ k)/δ)
      (𝓝[>] (0 : ℝ)) (𝓝 ((ξ j.val-ξ k.val)*ρ))) ∧
    (∀ j k, Tendsto (fun δ => R δ j-R δ k)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) ∧
    (∀ j, Tendsto (fun δ => lam j δ/δ^N)
      (𝓝[>] (0 : ℝ)) (𝓝 (-A*gap j))) ∧
    (∀ j, Tendsto (fun δ => δ^N/|lam j δ|)
      (𝓝[>] (0 : ℝ)) (𝓝 (1/(A*|gap j|)))) ∧
    (∀ j, Tendsto (lam j) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Tendsto (fun δ => 1/|lam j δ|) (𝓝[>] (0 : ℝ)) atTop) ∧
    (∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), StrictMono (R δ)) ∧
    (∀ i j k : Fin (2*(m+1)+1), j ≠ k → 0 <
      |(ξ j.val-ξ k.val)*ρ|^N/(A*|gap i|)) ∧
    ∀ i j k, Tendsto (fun δ => |R δ j-R δ k|^N/|lam i δ|)
      (𝓝[>] (0 : ℝ))
      (𝓝 (|(ξ j.val-ξ k.val)*ρ|^N/(A*|gap i|)))

theorem paperActualCurrent_analytical_asymptotics
    (m : ℕ) (ξ : ℕ → ℝ) (hξ : StrictMono ξ) :
    ∃ a b c : ℕ,
      let r : ℝ := (2 : ℝ)^a
      let t : ℝ := (1/2 : ℝ)^b
      let ε : ℝ := (1/2 : ℝ)^c
      let x₀ := coalescedFiniteState (m+1) r
      let τ : ℝ := t/x₀.D (Fin.last (m+1))
      let θ : Fin (m+1) → ℝ := fun i => 1/x₀.D i.castSucc
      let k₀ := relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r (Fin.lastCases τ θ))) ε
      (3*(m+2 : ℝ))/2 ≤ r ∧ 0 < t ∧ 0 < ε ∧ ε ≤ 1 ∧
        (∀ i : Fin (m+1), k₀.gamma i.castSucc*x₀.D i.castSucc = 1) ∧
        k₀.gamma (Fin.last (m+1))*x₀.D (Fin.last (m+1)) = t ∧
        ∃ lam : Fin (2*(m+1)+1) → ℝ → ℝ,
          (∀ j, AnalyticAt ℝ (lam j) 0 ∧ lam j 0 = 0) ∧
          0 < paperFixedBindingPrintedCoefficient m r τ ε θ ∧
          ∃ α K Cread : ℝ, 0 < α ∧ 0 < K ∧ 0 < Cread ∧
            PaperActualCurrentAnalyticalAsymptotics m ξ r τ ε α K Cread θ lam := by
  obtain ⟨a, b, c, hr, ht, hε, hε1, hprefix, hfinal,
    lam, hanalytic, hA, α, K, Cread, hα, hK, hCread, hρ, hfamily⟩ :=
    paperActualCurrent_readout_relaxation_tradeoff m ξ hξ
  let r : ℝ := (2 : ℝ)^a
  let t : ℝ := (1/2 : ℝ)^b
  let ε : ℝ := (1/2 : ℝ)^c
  let x₀ := coalescedFiniteState (m+1) r
  let τ : ℝ := t/x₀.D (Fin.last (m+1))
  let θ : Fin (m+1) → ℝ := fun i => 1/x₀.D i.castSucc
  let N := 2*(m+1)
  let A := paperFixedBindingPrintedCoefficient m r τ ε θ
  let ρ := deriv (splitReadoutScalar (m+1) (coalescedRawD (m+1) r)) 3
  let R := fun δ j => fullyPhosphorylatedReadout (m+1)
    (arbitrarySplitFiniteState (m+1) ξ r δ j)
  let gap := fun j : Fin (2*(m+1)+1) =>
    ∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val, (ξ j.val-ξ i)
  have hgap (j : Fin (2*(m+1)+1)) : gap j ≠ 0 :=
    arbitrarySplit_root_gap_ne_zero (m+1) ξ hξ j
  have hread (j k : Fin (2*(m+1)+1)) :
      Tendsto (fun δ => (R δ j-R δ k)/δ)
        (𝓝[>] (0 : ℝ)) (𝓝 ((ξ j.val-ξ k.val)*ρ)) := by
    apply actualCurrent_tendsto_of_linear_error _ _ Cread
    filter_upwards [hfamily, self_mem_nhdsWithin] with δ hd hδ
    have hfrac : (R δ j-R δ k)/δ-(ξ j.val-ξ k.val)*ρ =
        ((R δ j-R δ k)-(ξ j.val-ξ k.val)*ρ*δ)/δ := by
      field_simp [ne_of_gt hδ]
    rw [hfrac, abs_div, abs_of_pos hδ]
    apply (div_le_iff₀ hδ).mpr
    simpa only [R, ρ, pow_two, mul_assoc] using hd.2 j k
  have hseparation (j k : Fin (2*(m+1)+1)) :
      Tendsto (fun δ => R δ j-R δ k)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun δ : ℝ => δ)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hprod : Tendsto (fun δ => ((R δ j-R δ k)/δ)*δ)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using (hread j k).mul hid
    apply Tendsto.congr' _ hprod
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact div_mul_cancel₀ _ (ne_of_gt hδ)
  have hslow (j : Fin (2*(m+1)+1)) :
      Tendsto (fun δ => lam j δ/δ^N)
        (𝓝[>] (0 : ℝ)) (𝓝 (-A*gap j)) := by
    apply actualCurrent_scaled_slow_limit (lam j) N A (gap j) K hA (hgap j)
    filter_upwards [hfamily] with δ hd
    obtain ⟨_, _, _, _, hj⟩ := hd.1
    obtain ⟨_, _, _, _, _, _, _, _, _, hrelative, _⟩ := hj j
    exact hrelative
  have hrec (j : Fin (2*(m+1)+1)) :
      Tendsto (fun δ => δ^N/|lam j δ|)
        (𝓝[>] (0 : ℝ)) (𝓝 (1/(A*|gap j|))) :=
    actualCurrent_scaled_reciprocal_limit (lam j) N A (gap j) hA (hgap j) (hslow j)
  have htime (j : Fin (2*(m+1)+1)) :
      Tendsto (lam j) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
        Tendsto (fun δ => 1/|lam j δ|) (𝓝[>] (0 : ℝ)) atTop :=
    actualCurrent_reciprocal_diverges (lam j) N (by dsimp [N]; omega)
      A (gap j) hA (hgap j) (hslow j)
  have horder : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), StrictMono (R δ) := by
    have hpair (j k : Fin (2*(m+1)+1)) :
        ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), j < k → R δ j < R δ k := by
      by_cases hjk : j < k
      · have hξjk : ξ j.val < ξ k.val := hξ hjk
        have hpositive : 0 < (ξ k.val-ξ j.val)*ρ := mul_pos (sub_pos.mpr hξjk) hρ
        filter_upwards [(hread k j).eventually (Ioi_mem_nhds hpositive),
          self_mem_nhdsWithin] with δ hd hδ _
        exact sub_pos.mp ((div_pos_iff_of_pos_right hδ).mp hd)
      · exact Eventually.of_forall fun _ h => (hjk h).elim
    have hall : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        ∀ j k : Fin (2*(m+1)+1), j < k → R δ j < R δ k :=
      Filter.eventually_all.mpr fun j => Filter.eventually_all.mpr (hpair j)
    exact hall
  have hlimitPos (i j k : Fin (2*(m+1)+1)) (hjk : j ≠ k) :
      0 < |(ξ j.val-ξ k.val)*ρ|^N/(A*|gap i|) := by
    have hoffset : ξ j.val-ξ k.val ≠ 0 := by
      apply sub_ne_zero.mpr
      intro hsame
      exact hjk (Fin.ext (hξ.injective hsame))
    have hnum : 0 < |(ξ j.val-ξ k.val)*ρ| :=
      abs_pos.mpr (mul_ne_zero hoffset (ne_of_gt hρ))
    exact div_pos (pow_pos hnum N) (mul_pos hA (abs_pos.mpr (hgap i)))
  have hdistance (i j k : Fin (2*(m+1)+1)) :
      Tendsto (fun δ => |R δ j-R δ k|^N/|lam i δ|)
        (𝓝[>] (0 : ℝ))
        (𝓝 (|(ξ j.val-ξ k.val)*ρ|^N/(A*|gap i|))) := by
    have hprod := ((hread j k).abs.pow N).mul (hrec i)
    have hprod' : Tendsto
        (fun δ => |(R δ j-R δ k)/δ|^N*(δ^N/|lam i δ|))
        (𝓝[>] (0 : ℝ))
        (𝓝 (|(ξ j.val-ξ k.val)*ρ|^N/(A*|gap i|))) := by
      simpa only [mul_one_div] using hprod
    apply Tendsto.congr' _ hprod'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [abs_div, abs_of_pos hδ, div_pow]
    exact div_mul_div_cancel₀ (pow_ne_zero N (ne_of_gt hδ))
  refine ⟨a, b, c, hr, ht, hε, hε1, hprefix, hfinal,
    lam, hanalytic, hA, α, K, Cread, hα, hK, hCread, ?_⟩
  exact ⟨hρ, hfamily, hread, hseparation, hslow, hrec, htime, horder,
    hlimitPos, hdistance⟩

end
end PhosphorylationStableCapacity
