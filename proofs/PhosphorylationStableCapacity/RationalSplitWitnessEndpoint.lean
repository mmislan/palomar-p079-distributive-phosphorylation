module
public import proofs.PhosphorylationStableCapacity.RationalSplitWitnessAlgebra
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.ExactSplitEquilibriumCount

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The separate one-site witness also has rational kinetic data and
literal concentrations. -/
theorem one_site_rational_rates_and_state :
    RationalRates oneRates ∧ RationalState oneState := by
  constructor
  · intro i
    exact ⟨⟨1, by simp [oneRates]⟩, ⟨1, by simp [oneRates]⟩,
      ⟨1, by simp [oneRates]⟩, ⟨1, by simp [oneRates]⟩,
      ⟨1, by simp [oneRates]⟩, ⟨1, by simp [oneRates]⟩⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i; exact ⟨1, by simp [oneState]⟩
    · exact ⟨1, by simp [oneState]⟩
    · exact ⟨1, by simp [oneState]⟩
    · intro i; exact ⟨1/2, by norm_num [oneState]⟩
    · intro i; exact ⟨1/2, by norm_num [oneState]⟩

/-- One explicitly parameterized rational system contains every member of
the full split equilibrium family. The even members are hyperbolic nonlinear
sinks, and each odd member has exactly one unstable eigenvalue. Rationality
is asserted for every literal species concentration and rate coordinate. -/
def RationalSplitFullFamilyWithSpectra (m : ℕ) : Prop :=
  ∃ r τ δ ε : ℚ,
    let k := splitRetunedRates m (r : ℝ) (τ : ℝ) (δ : ℝ) (ε : ℝ)
    let z := splitFiniteState (m+1) (r : ℝ) (δ : ℝ)
    (1 : ℝ) < (r : ℝ) ∧
    0 < (τ : ℝ) ∧ 0 < (δ : ℝ) ∧ 0 < (ε : ℝ) ∧
    k.Positive ∧ RationalRates k ∧ Function.Injective z ∧
    (∀ j : Fin (2*(m+1)+1),
      RationalState (z j) ∧ (z j).Positive ∧
      Equilibrium k (z j) ∧
      totalE (z j) = 2*(r : ℝ) ∧
      totalF (z j) = 2 ∧
      totalS (z j) = 2*((r : ℝ)+1)) ∧
    {x : State (m+2) |
      x.Positive ∧ Equilibrium k x ∧
        InClass (2*(r : ℝ)) 2 (2*((r : ℝ)+1)) x} = Set.range z ∧
    {x : State (m+2) |
      x.Positive ∧ Equilibrium k x ∧
        InClass (2*(r : ℝ)) 2 (2*((r : ℝ)+1)) x}.ncard =
      2*(m+1)+1 ∧
    (∀ i : Fin (m+2),
      let u := toCoordinateSpace (chart (z (splitEvenIndex m i)))
      IsLinearlyStable (2*(r : ℝ)) 2 (2*((r : ℝ)+1)) k u ∧
      IsLocallyAsymptoticallyStableClass
        (2*(r : ℝ)) 2 (2*((r : ℝ)+1)) k u) ∧
    (∀ j : Fin (2*(m+1)+1), Odd j.val →
      IsOneUnstableSaddle (2*(r : ℝ)) 2 (2*((r : ℝ)+1)) k
        (toCoordinateSpace (chart (z j))))

theorem rational_split_full_family_with_spectra (m : ℕ) :
    RationalSplitFullFamilyWithSpectra m := by
  obtain ⟨r, τ, δ, ε, hr, hτ, hδ, hε, hε1, hD, hB,
    hv, hkrational, hzrational, ρ, hadm, hcert⟩ :=
      rational_split_family_with_spectral_certificates m
  let k := splitRetunedRates m (r : ℝ) (τ : ℝ) (δ : ℝ) (ε : ℝ)
  let z := splitFiniteState (m+1) (r : ℝ) (δ : ℝ)
  have hfamily := hadm.2.2
  have hback (j : Fin (2*(m+1)+1)) :
      unChart (2*(r : ℝ)) 2 (2*((r : ℝ)+1))
        (ofCoordinateSpace (toCoordinateSpace (chart (z j)))) = z j := by
    rw [of_toCoordinateSpace]
    exact unChart_chart_of_inClass
      (2*(r : ℝ)) 2 (2*((r : ℝ)+1)) (z j)
      ⟨(hfamily j).2.2.1, (hfamily j).2.2.2.1,
        (hfamily j).2.2.2.2⟩
  have hfield (j : Fin (2*(m+1)+1)) :
      restrictedFieldEuclid (2*(r : ℝ)) 2 (2*((r : ℝ)+1)) k
        (toCoordinateSpace (chart (z j))) = 0 := by
    apply (restrictedFieldEuclid_eq_zero_iff
      (2*(r : ℝ)) 2 (2*((r : ℝ)+1)) k
      (toCoordinateSpace (chart (z j)))).2
    rw [hback]
    exact (hfamily j).2.1
  unfold RationalSplitFullFamilyWithSpectra
  refine ⟨r, τ, δ, ε, hr, hτ, hδ, hε,
    hadm.1, hkrational, hadm.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨hzrational j, (hfamily j).1, (hfamily j).2.1,
      (hfamily j).2.2.1, (hfamily j).2.2.2.1,
      (hfamily j).2.2.2.2⟩
  · exact splitRetuned_positive_equilibria_exact_family
      m (r : ℝ) (τ : ℝ) (δ : ℝ) (ε : ℝ)
      (by linarith) hτ hδ hε hε1 hD hB
  · exact splitRetuned_positive_equilibria_ncard
      m (r : ℝ) (τ : ℝ) (δ : ℝ) (ε : ℝ)
      (by linarith) hτ hδ hε hε1 hD hB
  · intro i
    have hstable := split_even_hurwitz_with_full_family
      m (r : ℝ) (τ : ℝ) (δ : ℝ) (ε : ℝ)
      (by linarith) hτ hε hδ hD hB hv ρ hcert i
    have hx : toCoordinateSpace (chart (z (splitEvenIndex m i))) ∈
        classPolytopeStrict (m+2)
          (2*(r : ℝ)) 2 (2*((r : ℝ)+1)) := by
      have hp := positive_state_mem_classPolytopeStrict
        (2*(r : ℝ)) 2 (2*((r : ℝ)+1))
        (unChart (2*(r : ℝ)) 2 (2*((r : ℝ)+1))
          (ofCoordinateSpace (toCoordinateSpace
            (chart (z (splitEvenIndex m i))))))
        (by rw [hback]; exact (hfamily (splitEvenIndex m i)).1)
        (unChart_inClass (2*(r : ℝ)) 2 (2*((r : ℝ)+1)) _)
      simpa only [chart_unChart, to_ofCoordinateSpace] using hp
    exact ⟨hstable,
      isLinearlyStable_locally_asymptotically_stable
        (by omega : 1 ≤ m+2)
        (2*(r : ℝ)) 2 (2*((r : ℝ)+1))
        (by positivity) k hadm.1 _ hx
        (hfield (splitEvenIndex m i)) hstable⟩
  · intro j hodd
    exact split_odd_is_one_unstable_saddle
      m (r : ℝ) (τ : ℝ) (δ : ℝ) (ε : ℝ)
      (by linarith) hτ hε hδ hD hB hv ρ hcert j hodd

end
end PhosphorylationStableCapacity
