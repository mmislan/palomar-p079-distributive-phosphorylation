module
public import proofs.PhosphorylationStableCapacity.GeneralEquilibriumProfile

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

def kinaseBindingRatio {n : ℕ} (k : Rates n) (i : Fin n) : ℝ :=
  k.a i / (k.b i + k.c i)

def phosphataseBindingRatio {n : ℕ} (k : Rates n) (i : Fin n) : ℝ :=
  k.alpha i / (k.beta i + k.gamma i)

theorem kinaseBindingRatio_pos {n : ℕ}
    (k : Rates n) (hk : k.Positive) (i : Fin n) :
    0 < kinaseBindingRatio k i :=
  div_pos (hk i).1 (add_pos (hk i).2.1 (hk i).2.2.1)

theorem phosphataseBindingRatio_pos {n : ℕ}
    (k : Rates n) (hk : k.Positive) (i : Fin n) :
    0 < phosphataseBindingRatio k i :=
  div_pos (hk i).2.2.2.1
    (add_pos (hk i).2.2.2.2.1 (hk i).2.2.2.2.2)

/-- Common substrate and complex-inventory coefficients at enzyme
ratio `u`. Their positivity is independent of any equilibrium. -/
def freeSubstrateInventory {n : ℕ} (k : Rates n) (u : ℝ) : ℝ :=
  ∑ j : Fin (n+1), equilibriumWeight k j.val * u^j.val

def kinaseComplexInventory {n : ℕ} (k : Rates n) (u : ℝ) : ℝ :=
  ∑ i : Fin n, kinaseBindingRatio k i *
    equilibriumWeight k i.val * u^(i.val+1)

def phosphataseComplexInventory {n : ℕ} (k : Rates n) (u : ℝ) : ℝ :=
  ∑ i : Fin n, phosphataseBindingRatio k i *
    equilibriumWeight k (i.val+1) * u^(i.val+1)

theorem freeSubstrateInventory_pos {n : ℕ}
    (k : Rates n) (hk : k.Positive) {u : ℝ} (hu : 0 < u) :
    0 < freeSubstrateInventory k u := by
  unfold freeSubstrateInventory
  apply Finset.sum_pos
  · intro j _
    exact mul_pos (equilibriumWeight_pos k hk j.val) (pow_pos hu _)
  · simp

theorem kinaseComplexInventory_pos {n : ℕ}
    (k : Rates n) (hk : k.Positive) {u : ℝ} (hu : 0 < u)
    (hn : 0 < n) :
    0 < kinaseComplexInventory k u := by
  unfold kinaseComplexInventory
  apply Finset.sum_pos
  · intro i _
    exact mul_pos
      (mul_pos (kinaseBindingRatio_pos k hk i)
        (equilibriumWeight_pos k hk i.val)) (pow_pos hu _)
  · let i : Fin n := ⟨0, hn⟩
    exact ⟨i, Finset.mem_univ i⟩

theorem phosphataseComplexInventory_pos {n : ℕ}
    (k : Rates n) (hk : k.Positive) {u : ℝ} (hu : 0 < u)
    (hn : 0 < n) :
    0 < phosphataseComplexInventory k u := by
  unfold phosphataseComplexInventory
  apply Finset.sum_pos
  · intro i _
    exact mul_pos
      (mul_pos (phosphataseBindingRatio_pos k hk i)
        (equilibriumWeight_pos k hk (i.val+1))) (pow_pos hu _)
  · let i : Fin n := ⟨0, hn⟩
    exact ⟨i, Finset.mem_univ i⟩

/-- Literal complex concentrations follow the same scalar profile. -/
theorem equilibrium_complex_profile {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) (i : Fin n) :
    let u := x.E/x.F
    x.C i = x.F*x.S 0 *
      (kinaseBindingRatio k i * equilibriumWeight k i.val *
        u^(i.val+1)) ∧
    x.D i = x.F*x.S 0 *
      (phosphataseBindingRatio k i * equilibriumWeight k (i.val+1) *
        u^(i.val+1)) := by
  dsimp
  let u := x.E/x.F
  have hF : x.F ≠ 0 := ne_of_gt hx.2.2.1
  have hE : x.E = u*x.F := by
    dsimp [u]
    field_simp
  obtain ⟨hC, hD⟩ := equilibrium_complex_balances k x heq i
  have hSprev := equilibrium_substrate_profile k x hk hx heq i.castSucc
  have hSnext := equilibrium_substrate_profile k x hk hx heq i.succ
  have hbc : k.b i + k.c i ≠ 0 :=
    ne_of_gt (add_pos (hk i).2.1 (hk i).2.2.1)
  have hbg : k.beta i + k.gamma i ≠ 0 :=
    ne_of_gt (add_pos (hk i).2.2.2.2.1 (hk i).2.2.2.2.2)
  constructor
  · have hdiv : x.C i =
        (k.a i*x.S i.castSucc*x.E)/(k.b i+k.c i) := by
      apply (eq_div_iff hbc).2
      nlinarith [hC]
    rw [hdiv, hSprev]
    change (k.a i * (equilibriumWeight k i.val * u^i.val * x.S 0) *
        x.E)/(k.b i+k.c i) =
      x.F*x.S 0 * (kinaseBindingRatio k i *
        equilibriumWeight k i.val * u^(i.val+1))
    conv_lhs => rw [hE]
    rw [pow_succ]
    dsimp [kinaseBindingRatio]
    ring
  · have hdiv : x.D i =
        (k.alpha i*x.S i.succ*x.F)/(k.beta i+k.gamma i) := by
      apply (eq_div_iff hbg).2
      nlinarith [hD]
    rw [hdiv, hSnext]
    change (k.alpha i * (equilibriumWeight k (i.val+1) *
        u^(i.val+1) * x.S 0) * x.F)/(k.beta i+k.gamma i) =
      x.F*x.S 0 * (phosphataseBindingRatio k i *
        equilibriumWeight k (i.val+1) * u^(i.val+1))
    dsimp [phosphataseBindingRatio]
    ring

/-- Universal conserved-total formulas at a positive literal
equilibrium. These reduce the fixed-ratio uniqueness question to the
strictly monotone scalar inventory in `FixedRatioTotals.lean`. -/
theorem equilibrium_total_profiles {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) :
    let u := x.E/x.F
    totalF x = x.F*(1+x.S 0*phosphataseComplexInventory k u) ∧
    totalS x = x.S 0*freeSubstrateInventory k u +
      x.F*x.S 0*(kinaseComplexInventory k u +
        phosphataseComplexInventory k u) := by
  dsimp
  let u := x.E/x.F
  have hSsum : (∑ j : Fin (n+1), x.S j) =
      x.S 0*freeSubstrateInventory k u := by
    calc
      _ = ∑ j : Fin (n+1),
          equilibriumWeight k j.val*u^j.val*x.S 0 := by
            apply Finset.sum_congr rfl
            intro j _
            exact equilibrium_substrate_profile k x hk hx heq j
      _ = x.S 0*freeSubstrateInventory k u := by
            simp only [freeSubstrateInventory, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
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
  have hDsum : (∑ i : Fin n, x.D i) =
      x.F*x.S 0*phosphataseComplexInventory k u := by
    calc
      _ = ∑ i : Fin n, x.F*x.S 0 *
          (phosphataseBindingRatio k i * equilibriumWeight k (i.val+1) *
            u^(i.val+1)) := by
            apply Finset.sum_congr rfl
            intro i _
            exact (equilibrium_complex_profile k x hk hx heq i).2
      _ = x.F*x.S 0*phosphataseComplexInventory k u := by
            simp only [phosphataseComplexInventory, Finset.mul_sum]
  constructor
  · dsimp [totalF]
    rw [hDsum]
    ring
  · dsimp [totalS]
    rw [hSsum, hCsum, hDsum]
    ring

end
end PhosphorylationStableCapacity
