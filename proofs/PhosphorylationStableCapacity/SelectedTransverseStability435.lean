module
public import proofs.PhosphorylationStableCapacity.SelectedTransverseRootChoice435
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.HurwitzNonlinearStability
public import proofs.PhosphorylationStableCapacity.ClassPolytopeTopology

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix Polynomial

/-- A negative selected mode and a strictly left transverse spectrum
make the whole literal class Jacobian Hurwitz. -/
theorem simpleTransverseRoot_hurwitz_of_negative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (α lam : ℝ)
    (hα : 0 < α) (hneg : lam < 0)
    (hselected : SimpleTransverseRoot J α lam) :
    IsHurwitz J := by
  intro z hz
  rcases hselected.2.2 z
      (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hz) with heq | hleft
  · rw [heq]
    simpa using hneg
  · linarith

/-- A positive selected mode and a strictly left transverse spectrum
give exactly one simple unstable real direction for the literal class
Jacobian. -/
theorem simpleTransverseRoot_oneUnstable_of_positive
    {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) (α lam : ℝ)
    (hα : 0 < α) (hpos : 0 < lam)
    (hselected : SimpleTransverseRoot
      (restrictedJacobianMatrix ET FT ST k u) α lam) :
    IsOneUnstableSaddle ET FT ST k u := by
  change ∃ x : ℝ, 0 < x ∧
    (restrictedJacobianMatrix ET FT ST k u).charpoly.IsRoot x ∧
    (((restrictedJacobianMatrix ET FT ST k u).map
      (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
    ∀ z : ℂ,
      z ∈ spectrum ℂ ((restrictedJacobianMatrix ET FT ST k u).map
        (algebraMap ℝ ℂ)) →
      z.re < 0 ∨ z = (x : ℂ)
  refine ⟨lam, hpos, hselected.1, hselected.2.1, ?_⟩
  intro z hz
  rcases hselected.2.2 z hz with heq | hleft
  · exact Or.inr heq
  · exact Or.inl (by linarith)

/-- Convert the same positive equilibrium's Hurwitz class Jacobian to
nonlinear local asymptotic stability in its positive compatibility
class. -/
theorem positiveClassEquilibrium_nonlinear_sink
    {n : ℕ} (hn : 1 ≤ n)
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (s : State n) (hs : s.Positive)
    (heq : Equilibrium k s)
    (hclass : InClass ET FT ST s)
    (hstable : IsLinearlyStable ET FT ST k
      (toCoordinateSpace (chart s))) :
    IsLocallyAsymptoticallyStableClass ET FT ST k
      (toCoordinateSpace (chart s)) := by
  let u := toCoordinateSpace (chart s)
  have hback : unChart ET FT ST (ofCoordinateSpace u) = s := by
    rw [of_toCoordinateSpace]
    exact unChart_chart_of_inClass ET FT ST s hclass
  have hfield : restrictedFieldEuclid ET FT ST k u = 0 := by
    apply (restrictedFieldEuclid_eq_zero_iff ET FT ST k u).2
    rw [hback]
    exact heq
  have hu : u ∈ classPolytopeStrict n ET FT ST := by
    have hp := positive_state_mem_classPolytopeStrict
      ET FT ST
      (unChart ET FT ST (ofCoordinateSpace u))
      (by rw [hback]; exact hs)
      (unChart_inClass ET FT ST _)
    simpa only [chart_unChart, to_ofCoordinateSpace] using hp
  exact isLinearlyStable_locally_asymptotically_stable
    hn ET FT ST hET k hk u hu hfield hstable

end

end PhosphorylationStableCapacity
