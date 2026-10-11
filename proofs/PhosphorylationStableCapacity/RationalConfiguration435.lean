module
public import proofs.PhosphorylationStableCapacity.FullHyperbolicConfiguration435
public import proofs.PhosphorylationStableCapacity.RationalSplitWitnessEndpoint

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- An exact split configuration is attained with rational rates, totals,
and every listed physical equilibrium rational. All properties use one
common system and compatibility class. -/
def RationalFullFamilyWithSinksAndSaddles (n : ℕ) : Prop :=
  ∃ (k : Rates n) (ET FT ST : ℝ)
      (u : Fin (2*n-1) → CoordinateSpace n),
    RationalRates k ∧ RationalReal ET ∧ RationalReal FT ∧
      RationalReal ST ∧
    k.Positive ∧ 0 < ET ∧ 0 < FT ∧ 0 < ST ∧ Function.Injective u ∧
      (∀ j, RationalState
        (unChart ET FT ST (ofCoordinateSpace (u j))) ∧
        (unChart ET FT ST (ofCoordinateSpace (u j))).Positive ∧
        restrictedFieldEuclid ET FT ST k (u j) = 0) ∧
      (∀ i : Fin n, ∃ j : Fin (2*n-1), j.val = 2*i.val ∧
        IsLinearlyStable ET FT ST k (u j) ∧
        IsLocallyAsymptoticallyStableClass ET FT ST k (u j)) ∧
      (∀ j : Fin (2*n-1), Odd j.val →
        IsOneUnstableSaddle ET FT ST k (u j)) ∧
      {x : State n | x.Positive ∧ Equilibrium k x ∧
        InClass ET FT ST x} =
          Set.range (fun j : Fin (2*n-1) =>
            unChart ET FT ST (ofCoordinateSpace (u j))) ∧
      {x : State n | x.Positive ∧ Equilibrium k x ∧
        InClass ET FT ST x}.ncard = 2*n-1

theorem all_size_rational_full_family_with_sinks_and_saddles
    (n : ℕ) (hn : 2 ≤ n) :
    RationalFullFamilyWithSinksAndSaddles n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m+2 := ⟨n-2, by omega⟩
  obtain ⟨r, τ, δ, ε, hr, hτ, hδ, hε, hk, hkr,
    hinj, hstate, hexact, hcard, heven, hodd⟩ :=
      rational_split_full_family_with_spectra m
  let k := splitRetunedRates m (r : ℝ) (τ : ℝ) (δ : ℝ) (ε : ℝ)
  let z := splitFiniteState (m+1) (r : ℝ) (δ : ℝ)
  let u : Fin (2*(m+1)+1) → CoordinateSpace (m+2) :=
    fun j => toCoordinateSpace (chart (z j))
  have hback (j : Fin (2*(m+1)+1)) :
      unChart (2*(r : ℝ)) 2 (2*((r : ℝ)+1))
        (ofCoordinateSpace (u j)) = z j := by
    rw [show ofCoordinateSpace (u j) = chart (z j) by
      simp only [u, of_toCoordinateSpace]]
    exact unChart_chart_of_inClass
      (2*(r : ℝ)) 2 (2*((r : ℝ)+1)) (z j)
      ⟨(hstate j).2.2.2.1, (hstate j).2.2.2.2.1,
        (hstate j).2.2.2.2.2⟩
  have hfield (j : Fin (2*(m+1)+1)) :
      restrictedFieldEuclid (2*(r : ℝ)) 2 (2*((r : ℝ)+1))
        k (u j) = 0 := by
    apply (restrictedFieldEuclid_eq_zero_iff
      (2*(r : ℝ)) 2 (2*((r : ℝ)+1)) k (u j)).2
    rw [hback]
    exact (hstate j).2.2.1
  unfold RationalFullFamilyWithSinksAndSaddles
  refine ⟨k, 2*(r : ℝ), 2, 2*((r : ℝ)+1), u,
    hkr, ⟨2*r, by norm_num⟩, ⟨2, by norm_num⟩,
    ⟨2*(r+1), by norm_num⟩,
    hk, by linarith, by norm_num, by linarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    apply hinj
    change z a = z b
    rw [← hback a, ← hback b, hab]
  · intro j
    exact ⟨by rw [hback]; exact (hstate j).1,
      by rw [hback]; exact (hstate j).2.1,
      hfield j⟩
  · intro i
    exact ⟨splitEvenIndex m i, rfl, (heven i).1, (heven i).2⟩
  · intro j hj
    exact hodd j hj
  · rw [hexact]
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, hback j⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, (hback j).symm⟩
  · simpa only [k, show 2*(m+2)-1 = 2*(m+1)+1 by omega]
      using hcard

end
end PhosphorylationStableCapacity
