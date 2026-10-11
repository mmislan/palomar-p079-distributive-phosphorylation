module
public import proofs.PhosphorylationStableCapacity.GeneralEquilibriumInjection

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The scalar elimination residual for arbitrary positive rate lists.
`A = ET-FT*u` and `Q = FT*B-ET*D` satisfy `A = s*Q` at a
positive equilibrium; the residual eliminates both `s` and `f`. -/
def equilibriumEliminationResidual {n : ℕ}
    (k : Rates n) (ET FT ST u : ℝ) : ℝ :=
  let T := freeSubstrateInventory k u
  let B := kinaseComplexInventory k u
  let D := phosphataseComplexInventory k u
  let A := ET-FT*u
  let Q := FT*B-ET*D
  ST*Q*(Q+A*D)-A*T*(Q+A*D)-FT*A*(B+D)*Q

/-- The kinase total has the same two-parameter profile as the
phosphatase and substrate totals. -/
theorem equilibrium_totalE_profile {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) :
    let u := x.E/x.F
    totalE x = x.F*(u+x.S 0*kinaseComplexInventory k u) := by
  dsimp
  let u := x.E/x.F
  have hF : x.F ≠ 0 := ne_of_gt hx.2.2.1
  have hE : x.E = u*x.F := by
    dsimp [u]
    field_simp
  have hCsum : (∑ i : Fin n, x.C i) =
      x.F*x.S 0*kinaseComplexInventory k u := by
    calc
      _ = ∑ i : Fin n, x.F*x.S 0 *
          (kinaseBindingRatio k i * equilibriumWeight k i.val *
            u^(i.val+1)) := by
            apply Finset.sum_congr rfl
            intro i _
            exact (equilibrium_complex_profile k x hk hx heq i).1
      _ = x.F*x.S 0*kinaseComplexInventory k u := by
            simp only [kinaseComplexInventory, Finset.mul_sum]
  dsimp [totalE]
  rw [hCsum]
  change x.E + x.F*x.S 0*kinaseComplexInventory k u =
    x.F*(u+x.S 0*kinaseComplexInventory k u)
  conv_lhs => rw [hE]
  ring

/-- Every positive literal equilibrium maps to a root of the
universal scalar elimination residual. No denominator exception is
excluded; `positive_equilibria_enzyme_ratio_injective` handles root
multiplicity versus state count separately. -/
theorem equilibrium_elimination_residual_zero {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) :
    equilibriumEliminationResidual k
      (totalE x) (totalF x) (totalS x) (x.E/x.F) = 0 := by
  let u := x.E/x.F
  let T := freeSubstrateInventory k u
  let B := kinaseComplexInventory k u
  let D := phosphataseComplexInventory k u
  let s := x.S 0
  let f := x.F
  have hE : totalE x = f*(u+s*B) :=
    equilibrium_totalE_profile k x hk hx heq
  obtain ⟨hF, hS⟩ := equilibrium_total_profiles k x hk hx heq
  change totalF x = f*(1+s*D) at hF
  change totalS x = s*T+f*s*(B+D) at hS
  change (let A := totalE x-totalF x*u
    let Q := totalF x*B-totalE x*D
    totalS x*Q*(Q+A*D)-A*T*(Q+A*D)-
      totalF x*A*(B+D)*Q) = 0
  rw [hE, hF, hS]
  dsimp
  ring

end
end PhosphorylationStableCapacity
