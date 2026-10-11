module
public import proofs.PhosphorylationStableCapacity.RatioResidualBijection
public import proofs.PhosphorylationStableCapacity.GeneralEquilibriumBudget

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The exact scalar residual has finitely many positive roots in a
positive compatibility class, with the same `2n` bound as the literal
positive equilibrium set. -/
theorem positive_ratio_residual_roots_finite_and_ncard_le_two_n {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST : ℝ) (hET : 0 < ET) (hFT : 0 < FT)
    (hST : 0 < ST) :
    let R : Set ℝ :=
      {u | 0 < u ∧ ratioEnzymeResidual k ET FT ST u = 0}
    R.Finite ∧ R.ncard ≤ 2*n := by
  classical
  let E : Set (State n) :=
    {x | x.Positive ∧ Equilibrium k x ∧ InClass ET FT ST x}
  let R : Set ℝ :=
    {u | 0 < u ∧ ratioEnzymeResidual k ET FT ST u = 0}
  have hE : E.Finite ∧ E.ncard ≤ 2*n :=
    positive_equilibria_finite_and_ncard_le_two_n
      k hn hk ET FT ST hET hFT
  have hbij : Set.BijOn (fun x : State n => x.E/x.F) E R :=
    positive_equilibria_bijOn_ratio_residual_roots
      hn k hk ET FT ST hFT hST
  change R.Finite ∧ R.ncard ≤ 2*n
  exact ⟨hbij.finite_iff_finite.mp hE.1,
    hbij.ncard_eq ▸ hE.2⟩

end
end PhosphorylationStableCapacity
