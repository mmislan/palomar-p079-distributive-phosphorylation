module
public import proofs.PhosphorylationStableCapacity.StructuralAlgebra
public import proofs.PhosphorylationSharpness.Source

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- Speed reversible complex binding by `ε⁻¹` while preserving the net
catalytic rates and the complex-balance equation. -/
def relaxRates {n : ℕ} (k : Rates n) (ε : ℝ) : Rates n where
  a i := k.a i / ε
  b i := (k.b i + k.c i) / ε - k.c i
  c := k.c
  alpha i := k.alpha i / ε
  beta i := (k.beta i + k.gamma i) / ε - k.gamma i
  gamma := k.gamma

/-- The relaxed rates remain strictly positive for `0<ε≤1`. -/
theorem relaxRates_positive {n : ℕ} (k : Rates n)
    (hk : k.Positive) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (relaxRates k ε).Positive := by
  intro i
  rcases hk i with ⟨ha, hb, hc, halpha, hbeta, hgamma⟩
  exact ⟨div_pos ha hε,
    relaxation_positive (k.b i) (k.c i) ε hb hc hε hε1,
    hc, div_pos halpha hε,
    relaxation_positive (k.beta i) (k.gamma i) ε
      hbeta hgamma hε hε1, hgamma⟩

/-- At a state satisfying the original kinase complex balance, the relaxed
kinase net equals the same catalytic flux. -/
theorem relaxRates_kinaseNet_of_balance {n : ℕ}
    (k : Rates n) (x : State n) (i : Fin n) {ε : ℝ}
    (hε : ε ≠ 0)
    (hbal : kinaseNet k x i = k.c i * x.C i) :
    kinaseNet (relaxRates k ε) x i = k.c i * x.C i := by
  have h : k.a i * x.S i.castSucc * x.E =
      (k.b i + k.c i) * x.C i := by
    dsimp [kinaseNet] at hbal
    linarith
  have hrel := relaxation_balance
    (k.a i) (k.b i) (k.c i) (x.S i.castSucc) x.E (x.C i)
      ε hε h
  dsimp [kinaseNet, relaxRates]
  linarith

/-- The same balance preservation holds for phosphatase complexes. -/
theorem relaxRates_phosphataseNet_of_balance {n : ℕ}
    (k : Rates n) (x : State n) (i : Fin n) {ε : ℝ}
    (hε : ε ≠ 0)
    (hbal : phosphataseNet k x i = k.gamma i * x.D i) :
    phosphataseNet (relaxRates k ε) x i = k.gamma i * x.D i := by
  have h : k.alpha i * x.S i.succ * x.F =
      (k.beta i + k.gamma i) * x.D i := by
    dsimp [phosphataseNet] at hbal
    linarith
  have hrel := relaxation_balance
    (k.alpha i) (k.beta i) (k.gamma i) (x.S i.succ) x.F
      (x.D i) ε hε h
  dsimp [phosphataseNet, relaxRates]
  linarith

/-- Relaxation preserves every equilibrium of the literal mass-action
field. In particular it preserves the coalesced source state while making
binding arbitrarily fast. -/
theorem relaxRates_preserves_equilibrium {n : ℕ}
    (k : Rates n) (x : State n) {ε : ℝ} (hε : ε ≠ 0)
    (hx : Equilibrium k x) : Equilibrium (relaxRates k ε) x := by
  have hC (i : Fin n) : kinaseNet k x i = k.c i * x.C i := by
    have h := hx.2.2.2.1 i
    dsimp [field] at h
    linarith
  have hD (i : Fin n) : phosphataseNet k x i =
      k.gamma i * x.D i := by
    have h := hx.2.2.2.2 i
    dsimp [field] at h
    linarith
  have hnetC (i : Fin n) :
      kinaseNet (relaxRates k ε) x i = kinaseNet k x i := by
    rw [relaxRates_kinaseNet_of_balance k x i hε (hC i), hC]
  have hnetD (i : Fin n) :
      phosphataseNet (relaxRates k ε) x i =
        phosphataseNet k x i := by
    rw [relaxRates_phosphataseNet_of_balance k x i hε (hD i), hD]
  have hc (i : Fin n) : (relaxRates k ε).c i = k.c i := rfl
  have hg (i : Fin n) : (relaxRates k ε).gamma i = k.gamma i := rfl
  simpa [Equilibrium, field, hnetC, hnetD, hc, hg] using hx

end
end PhosphorylationStableCapacity
