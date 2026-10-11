module
public import proofs.PhosphorylationStableCapacity.LoadedReducedField

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The reversible binding manifold has zero kinase and phosphatase complex
velocities whenever its binding ratios match the literal rate list. -/
theorem bindingState_fast_balance {n : ℕ} (ET FT : ℝ)
    (p q : Fin (n + 1) → ℝ) (k : Rates n)
    (hp : ∀ i : Fin n, k.a i = (k.b i + k.c i) * p i.castSucc)
    (hq : ∀ i : Fin n, k.alpha i =
      (k.beta i + k.gamma i) * q i.succ)
    (S : Fin (n + 1) → ℝ) (i : Fin n) :
    (field k (bindingState ET FT p q S)).C i = 0 ∧
      (field k (bindingState ET FT p q S)).D i = 0 := by
  constructor
  · dsimp [field, kinaseNet, bindingState]
    rw [hp i]
    unfold bindingComplex
    ring
  · dsimp [field, phosphataseNet, bindingState]
    rw [hq i]
    unfold bindingComplex
    ring

end
end PhosphorylationStableCapacity
