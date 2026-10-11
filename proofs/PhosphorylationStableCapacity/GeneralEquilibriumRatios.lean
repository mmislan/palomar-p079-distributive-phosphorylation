module
public import proofs.PhosphorylationStableCapacity.BoundaryEquilibrium

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The two complex balances hold at every equilibrium of the literal
mass-action system, with no special choice of positive rates. -/
theorem equilibrium_complex_balances {n : ℕ}
    (k : Rates n) (x : State n) (heq : Equilibrium k x)
    (i : Fin n) :
    k.a i * x.S i.castSucc * x.E =
      (k.b i + k.c i) * x.C i ∧
    k.alpha i * x.S i.succ * x.F =
      (k.beta i + k.gamma i) * x.D i := by
  constructor
  · have h := heq.2.2.2.1 i
    dsimp [field, kinaseNet] at h
    nlinarith
  · have h := heq.2.2.2.2 i
    dsimp [field, phosphataseNet] at h
    nlinarith

/-- Universal adjacent-substrate cross ratio. This is the literal
equilibrium-to-one-variable reduction before introducing denominators. -/
theorem equilibrium_substrate_cross_ratio {n : ℕ}
    (k : Rates n) (x : State n) (heq : Equilibrium k x)
    (i : Fin n) :
    (k.a i * k.c i * (k.beta i + k.gamma i)) *
      x.S i.castSucc * x.E =
    (k.alpha i * k.gamma i * (k.b i + k.c i)) *
      x.S i.succ * x.F := by
  obtain ⟨hC, hD⟩ := equilibrium_complex_balances k x heq i
  have hcat := equilibrium_catalytic_balance k x heq i
  calc
    (k.a i * k.c i * (k.beta i + k.gamma i)) *
        x.S i.castSucc * x.E =
      ((k.b i + k.c i) * (k.beta i + k.gamma i)) *
        (k.c i * x.C i) := by
          nlinarith [congrArg
            (fun z : ℝ => k.c i * (k.beta i + k.gamma i) * z) hC]
    _ = ((k.b i + k.c i) * (k.beta i + k.gamma i)) *
        (k.gamma i * x.D i) := by rw [hcat]
    _ = (k.alpha i * k.gamma i * (k.b i + k.c i)) *
        x.S i.succ * x.F := by
          nlinarith [congrArg
            (fun z : ℝ => k.gamma i * (k.b i + k.c i) * z) hD]

/-- The positive rate factor in the universal ratio formula. -/
def equilibriumRatioFactor {n : ℕ} (k : Rates n) (i : Fin n) : ℝ :=
  (k.a i * k.c i * (k.beta i + k.gamma i)) /
    (k.alpha i * k.gamma i * (k.b i + k.c i))

theorem equilibriumRatioFactor_pos {n : ℕ}
    (k : Rates n) (hk : k.Positive) (i : Fin n) :
    0 < equilibriumRatioFactor k i := by
  dsimp [equilibriumRatioFactor]
  exact div_pos
    (mul_pos (mul_pos (hk i).1 (hk i).2.2.1)
      (add_pos (hk i).2.2.2.2.1 (hk i).2.2.2.2.2))
    (mul_pos (mul_pos (hk i).2.2.2.1 (hk i).2.2.2.2.2)
      (add_pos (hk i).2.1 (hk i).2.2.1))

/-- Every positive literal equilibrium follows the same adjacent-level
recurrence as a function of the free-enzyme ratio `E/F`. -/
theorem equilibrium_substrate_ratio {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) (i : Fin n) :
    x.S i.succ / x.S i.castSucc =
      equilibriumRatioFactor k i * (x.E / x.F) := by
  have h := equilibrium_substrate_cross_ratio k x heq i
  let A : ℝ := k.a i * k.c i * (k.beta i + k.gamma i)
  let D : ℝ := k.alpha i * k.gamma i * (k.b i + k.c i)
  have hcross : A * x.S i.castSucc * x.E =
      D * x.S i.succ * x.F := h
  have hs : x.S i.castSucc ≠ 0 := ne_of_gt (hx.1 i.castSucc)
  have hf : x.F ≠ 0 := ne_of_gt hx.2.2.1
  have hd : D ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (hk i).2.2.2.1 (hk i).2.2.2.2.2)
      (add_pos (hk i).2.1 (hk i).2.2.1))
  change x.S i.succ / x.S i.castSucc = (A / D) * (x.E / x.F)
  field_simp [hs, hf, hd]
  nlinarith [hcross]

/-- At fixed positive rates, the free-enzyme ratio and level-zero
substrate determine every free-substrate coordinate of an equilibrium. -/
theorem equilibrium_substrate_profile_unique {n : ℕ}
    (k : Rates n) (x y : State n)
    (hk : k.Positive) (hx : x.Positive) (hy : y.Positive)
    (heqx : Equilibrium k x) (heqy : Equilibrium k y)
    (hEF : x.E / x.F = y.E / y.F)
    (hS0 : x.S 0 = y.S 0) :
    ∀ j : Fin (n+1), x.S j = y.S j := by
  intro j
  induction j using Fin.induction with
  | zero => exact hS0
  | succ i ih =>
      have hrx := equilibrium_substrate_ratio k x hk hx heqx i
      have hry := equilibrium_substrate_ratio k y hk hy heqy i
      have hden : y.S i.castSucc ≠ 0 := ne_of_gt (hy.1 i.castSucc)
      have hratio : x.S i.succ / y.S i.castSucc =
          y.S i.succ / y.S i.castSucc := by
        rw [← ih]
        calc
          x.S i.succ / x.S i.castSucc =
              equilibriumRatioFactor k i * (x.E / x.F) := hrx
          _ = equilibriumRatioFactor k i * (y.E / y.F) := by rw [hEF]
          _ = y.S i.succ / x.S i.castSucc := by simpa only [ih] using hry.symm
      exact (div_left_inj' hden).mp hratio

end
end PhosphorylationStableCapacity
