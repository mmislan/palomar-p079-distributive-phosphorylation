module
public import proofs.PhosphorylationStableCapacity.OneSiteNonlinearStability
public import proofs.PhosphorylationStableCapacity.SplitStableAttainment
public import proofs.PhosphorylationStableCapacity.HurwitzNonlinearStability

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- Attainment by genuinely locally asymptotically stable positive
equilibria of one literal fixed compatibility class. -/
def NonlinearlyStableClassAttains (n count : ℕ) : Prop :=
  ∃ (k : Rates n) (ET FT ST : ℝ) (u : Fin count → CoordinateSpace n),
    k.Positive ∧ 0 < ET ∧ 0 < FT ∧ 0 < ST ∧ Function.Injective u ∧
      ∀ j, (unChart ET FT ST (ofCoordinateSpace (u j))).Positive ∧
        IsLocallyAsymptoticallyStableClass ET FT ST k (u j)

/-- The exact positive unit-rate one-site witness attains one nonlinear
stable state under the full forward-curve stability predicate. -/
theorem one_site_nonlinear_stable_attainment :
    NonlinearlyStableClassAttains 1 1 := by
  refine ⟨oneRates, 3/2, 3/2, 3, (fun _ => oneCoord),
    oneRates_positive, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · intro i j _
    exact Subsingleton.elim i j
  · intro j
    constructor
    · rw [oneState_eq_unChart]
      exact oneState_positive
    · exact oneSite_locally_asymptotically_stable

/-- The exact missing all-size lower-bound interface: a uniform
Hurwitz-to-nonlinear-stability theorem would upgrade the already
verified common-class Hurwitz attainment construction. -/
theorem nonlinear_attainment_of_hurwitz_transfer
    (htransfer : ∀ (n : ℕ) (ET FT ST : ℝ) (k : Rates n)
      (u : CoordinateSpace n),
      restrictedFieldEuclid ET FT ST k u = 0 →
      IsLinearlyStable ET FT ST k u →
        IsLocallyAsymptoticallyStableClass ET FT ST k u)
    (n : ℕ) (hn : 1 ≤ n) :
    NonlinearlyStableClassAttains n n := by
  obtain ⟨k, ET, FT, ST, u, hk, hET, hFT, hST, hinj, hstates⟩ :=
    all_size_linearly_stable_attainment n hn
  exact ⟨k, ET, FT, ST, u, hk, hET, hFT, hST, hinj,
    fun j => ⟨(hstates j).1,
      htransfer n ET FT ST k (u j)
        (hstates j).2.1 (hstates j).2.2⟩⟩

/-- The literal all-size construction attains `n` genuinely nonlinear
locally asymptotically stable positive equilibria in one class. -/
theorem all_size_nonlinearly_stable_attainment
    (n : ℕ) (hn : 1 ≤ n) :
    NonlinearlyStableClassAttains n n := by
  obtain ⟨k, ET, FT, ST, u, hk, hET, hFT, hST, hinj, hstates⟩ :=
    all_size_linearly_stable_attainment n hn
  refine ⟨k, ET, FT, ST, u, hk, hET, hFT, hST, hinj, ?_⟩
  intro j
  refine ⟨(hstates j).1, ?_⟩
  have hx : u j ∈ classPolytopeStrict n ET FT ST := by
    have hp := positive_state_mem_classPolytopeStrict
      ET FT ST (unChart ET FT ST (ofCoordinateSpace (u j)))
      (hstates j).1 (unChart_inClass ET FT ST _)
    simpa only [chart_unChart, to_ofCoordinateSpace] using hp
  exact isLinearlyStable_locally_asymptotically_stable
    hn ET FT ST hET k hk (u j) hx
    (hstates j).2.1 (hstates j).2.2

end
end PhosphorylationStableCapacity
