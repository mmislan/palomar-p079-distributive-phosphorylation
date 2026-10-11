module
public import Mathlib.Tactic.LinearCombination
public import proofs.PhosphorylationSharpness.Source

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

def retune {n : ℕ} (k : Rates n) (l b β : Fin n → ℝ) : Rates n where
  a i := (b i+l i*k.c i)*k.a i/(k.b i+k.c i)
  b := b
  c i := l i*k.c i
  alpha i := (β i+l i*k.gamma i)*k.alpha i/(k.beta i+k.gamma i)
  beta := β
  gamma i := l i*k.gamma i

theorem retune_positive {n : ℕ} (k : Rates n) (l b β : Fin n → ℝ)
    (hk : k.Positive) (hl : ∀ i, 0 < l i) (hb : ∀ i, 0 < b i)
    (hβ : ∀ i, 0 < β i) : (retune k l b β).Positive := by
  intro i
  obtain ⟨ha, hb0, hc, hal, hbe, hg⟩ := hk i
  dsimp [retune]
  exact ⟨div_pos (mul_pos (add_pos (hb i) (mul_pos (hl i) hc)) ha)
      (add_pos hb0 hc), hb i, mul_pos (hl i) hc,
    div_pos (mul_pos (add_pos (hβ i) (mul_pos (hl i) hg)) hal)
      (add_pos hbe hg), hβ i, mul_pos (hl i) hg⟩

/-- Retuning is common to all balanced states of the original source. -/
theorem retune_equilibrium {n : ℕ} (k : Rates n) (x : State n)
    (l b β : Fin n → ℝ) (hk : k.Positive)
    (hE : ∀ i, k.a i*x.S i.castSucc*x.E=(k.b i+k.c i)*x.C i)
    (hF : ∀ i, k.alpha i*x.S i.succ*x.F=(k.beta i+k.gamma i)*x.D i)
    (hcat : ∀ i, k.c i*x.C i=k.gamma i*x.D i) :
    Equilibrium (retune k l b β) x := by
  apply equilibrium_of_currents
  · intro i
    have hd : k.b i+k.c i ≠ 0 := ne_of_gt (add_pos (hk i).2.1 (hk i).2.2.1)
    dsimp [kinaseNet, retune]
    field_simp [hd]
    linear_combination (b i+l i*k.c i)*(hE i)
  · intro i
    have hd : k.beta i+k.gamma i ≠ 0 :=
      ne_of_gt (add_pos (hk i).2.2.2.2.1 (hk i).2.2.2.2.2)
    dsimp [phosphataseNet, retune]
    field_simp [hd]
    linear_combination (β i+l i*k.gamma i)*(hF i)
  · intro i
    dsimp [retune]
    linear_combination l i*(hcat i)

end
end PhosphorylationStableCapacity
