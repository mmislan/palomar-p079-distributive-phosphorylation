module
public import proofs.PhosphorylationStableCapacity.LoadedFastField

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- At every literal equilibrium, the kinase binding flux equals the total
unbinding and catalytic complex outflow. -/
theorem equilibrium_kinase_binding_balance {n : ℕ} (k : Rates n)
    (x : State n) (hx : Equilibrium k x) (i : Fin n) :
    k.a i * x.S i.castSucc * x.E = (k.b i + k.c i) * x.C i := by
  have h := hx.2.2.2.1 i
  dsimp [field, kinaseNet] at h
  linarith

theorem equilibrium_phosphatase_binding_balance {n : ℕ} (k : Rates n)
    (x : State n) (hx : Equilibrium k x) (i : Fin n) :
    k.alpha i * x.S i.succ * x.F =
      (k.beta i + k.gamma i) * x.D i := by
  have h := hx.2.2.2.2 i
  dsimp [field, phosphataseNet] at h
  linarith

/-- Both detailed-balance weights needed by the fast quadratic form are
strictly positive at a positive equilibrium. -/
theorem equilibrium_binding_fluxes_positive {n : ℕ} (k : Rates n)
    (x : State n) (hk : k.Positive) (hx : x.Positive) (i : Fin n) :
    0 < k.a i * x.S i.castSucc * x.E ∧
      0 < k.alpha i * x.S i.succ * x.F := by
  rcases hk i with ⟨ha, _, _, halpha, _, _⟩
  rcases hx with ⟨hS, hE, hF, _, _⟩
  exact ⟨mul_pos (mul_pos ha (hS _)) hE,
    mul_pos (mul_pos halpha (hS _)) hF⟩

end
end PhosphorylationStableCapacity
