module
public import proofs.PhosphorylationStableCapacity.RatioResidualConverse

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Exact all-size scalar chart of the positive equilibrium set:
literal equilibria in one compatibility class correspond bijectively
to positive roots of the differentiable enzyme-total residual. -/
theorem positive_equilibria_bijOn_ratio_residual_roots {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST : ℝ) (hFT : 0 < FT) (hST : 0 < ST) :
    Set.BijOn (fun x : State n => x.E/x.F)
      {x | x.Positive ∧ Equilibrium k x ∧ InClass ET FT ST x}
      {u | 0 < u ∧ ratioEnzymeResidual k ET FT ST u = 0} := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact ⟨div_pos hx.1.2.1 hx.1.2.2.1,
      positive_equilibrium_ratioEnzymeResidual_zero
        hn k hk ET FT ST hFT hST x hx.1 hx.2.1 hx.2.2⟩
  · intro x hx y hy hxy
    exact positive_equilibria_enzyme_ratio_injective
      k x y hn hk hx.1 hy.1 hx.2.1 hy.2.1
      ((hx.2.2).2.1.trans (hy.2.2).2.1.symm)
      ((hx.2.2).2.2.trans (hy.2.2).2.2.symm)
      hxy
  · intro u hu
    obtain ⟨x, hx, heq, hclass, hratio⟩ :=
      positive_ratioEnzymeResidual_root_realizes_equilibrium
        hn k hk ET FT ST u hFT hST hu.1 hu.2
    exact ⟨x, ⟨hx, heq, hclass⟩, hratio⟩

end
end PhosphorylationStableCapacity
