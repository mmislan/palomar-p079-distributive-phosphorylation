module
public import proofs.PhosphorylationStableCapacity.SourceCurrentTriangular
public import proofs.PhosphorylationStableCapacity.SourceCurrentSchur
public import proofs.PhosphorylationStableCapacity.LoadedFastBalance

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Association to total complex-outflow ratios on the levels used by
the two directed binding reactions. Unused endpoint values are zero. -/
def sourceBindingP {n : ℕ} (k : Rates n) : Fin (n+1) → ℝ :=
  Fin.lastCases 0 (fun i : Fin n => k.a i / (k.b i + k.c i))

def sourceBindingQ {n : ℕ} (k : Rates n) : Fin (n+1) → ℝ :=
  Fin.cases 0 (fun i : Fin n => k.alpha i / (k.beta i + k.gamma i))

theorem sourceBindingP_castSucc {n : ℕ} (k : Rates n) (i : Fin n) :
    sourceBindingP k i.castSucc = k.a i / (k.b i + k.c i) := by
  simp [sourceBindingP]

theorem sourceBindingQ_succ {n : ℕ} (k : Rates n) (i : Fin n) :
    sourceBindingQ k i.succ = k.alpha i / (k.beta i + k.gamma i) := by
  simp [sourceBindingQ]

theorem sourceBindingRatios_positive {n : ℕ} (k : Rates n)
    (hk : k.Positive) (i : Fin n) :
    0 < sourceBindingP k i.castSucc ∧
      0 < sourceBindingQ k i.succ := by
  rw [sourceBindingP_castSucc, sourceBindingQ_succ]
  exact ⟨div_pos (hk i).1 (add_pos (hk i).2.1 (hk i).2.2.1),
    div_pos (hk i).2.2.2.1
      (add_pos (hk i).2.2.2.2.1 (hk i).2.2.2.2.2)⟩

theorem sourceBindingRatios_rate_identities {n : ℕ} (k : Rates n)
    (hk : k.Positive) :
    (∀ i : Fin n, k.a i = (k.b i + k.c i) * sourceBindingP k i.castSucc) ∧
    (∀ i : Fin n,
      k.alpha i = (k.beta i + k.gamma i) * sourceBindingQ k i.succ) := by
  constructor
  · intro i
    rw [sourceBindingP_castSucc]
    have hden : k.b i + k.c i ≠ 0 :=
      ne_of_gt (add_pos (hk i).2.1 (hk i).2.2.1)
    field_simp
  · intro i
    rw [sourceBindingQ_succ]
    have hden : k.beta i + k.gamma i ≠ 0 :=
      ne_of_gt (add_pos (hk i).2.2.2.2.1 (hk i).2.2.2.2.2)
    field_simp

theorem state_substrate_from_free {n : ℕ} (x : State n)
    (j : Fin (n+1)) :
    Fin.cases (x.S 0) (fun i : Fin n => x.S i.succ) j = x.S j := by
  cases j using Fin.cases with
  | zero => rfl
  | succ i => rfl

/-- On a binding-balanced state, the actual mass-action catalytic currents
are exactly the free-substrate current map used by the triangular pivot. -/
theorem loadedCatalyticCurrent_eq_bindingCurrentAtFree {n : ℕ}
    (k : Rates n) (p q : Fin (n+1) → ℝ) (x : State n)
    (hC : ∀ i : Fin n, x.C i = p i.castSucc * x.S i.castSucc * x.E)
    (hD : ∀ i : Fin n, x.D i = q i.succ * x.S i.succ * x.F) :
    loadedCatalyticCurrent k (x.C, x.D) =
      sourceBindingCurrentAtFree k p q (x.S 0) x.E x.F
        (fun i => x.S i.succ) := by
  funext i
  rw [loadedCatalyticCurrent, sourceBindingCurrentAtFree,
    state_substrate_from_free]
  change k.c i * x.C i - k.gamma i * x.D i = _
  rw [hC i, hD i]
  ring

/-- Complex balance in the literal source supplies the binding formulas
whenever `p,q` represent its positive association/outflow ratios. -/
theorem equilibrium_binding_complex_formulas {n : ℕ}
    (k : Rates n) (p q : Fin (n+1) → ℝ) (x : State n)
    (hk : k.Positive) (heq : Equilibrium k x)
    (hp : ∀ i : Fin n,
      k.a i = (k.b i + k.c i) * p i.castSucc)
    (hq : ∀ i : Fin n,
      k.alpha i = (k.beta i + k.gamma i) * q i.succ) :
    (∀ i : Fin n, x.C i = p i.castSucc * x.S i.castSucc * x.E) ∧
    (∀ i : Fin n, x.D i = q i.succ * x.S i.succ * x.F) := by
  constructor
  · intro i
    have hb := equilibrium_kinase_binding_balance k x heq i
    rw [hp i] at hb
    have hden : k.b i + k.c i ≠ 0 :=
      ne_of_gt (add_pos (hk i).2.1 (hk i).2.2.1)
    apply mul_left_cancel₀ hden
    simpa only [mul_assoc] using hb.symm
  · intro i
    have hb := equilibrium_phosphatase_binding_balance k x heq i
    rw [hq i] at hb
    have hden : k.beta i + k.gamma i ≠ 0 :=
      ne_of_gt (add_pos (hk i).2.2.2.2.1 (hk i).2.2.2.2.2)
    apply mul_left_cancel₀ hden
    simpa only [mul_assoc] using hb.symm

theorem equilibrium_loadedCatalyticCurrent_eq_bindingCurrentAtFree {n : ℕ}
    (k : Rates n) (p q : Fin (n+1) → ℝ) (x : State n)
    (hk : k.Positive) (heq : Equilibrium k x)
    (hp : ∀ i : Fin n,
      k.a i = (k.b i + k.c i) * p i.castSucc)
    (hq : ∀ i : Fin n,
      k.alpha i = (k.beta i + k.gamma i) * q i.succ) :
    loadedCatalyticCurrent k (x.C, x.D) =
      sourceBindingCurrentAtFree k p q (x.S 0) x.E x.F
        (fun i => x.S i.succ) := by
  obtain ⟨hC, hD⟩ := equilibrium_binding_complex_formulas
    k p q x hk heq hp hq
  exact loadedCatalyticCurrent_eq_bindingCurrentAtFree k p q x hC hD

theorem equilibrium_loadedCatalyticCurrent_eq_free_ratio_current {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (heq : Equilibrium k x) :
    loadedCatalyticCurrent k (x.C, x.D) =
      sourceBindingCurrentAtFree k (sourceBindingP k) (sourceBindingQ k)
        (x.S 0) x.E x.F (fun i => x.S i.succ) := by
  obtain ⟨hp, hq⟩ := sourceBindingRatios_rate_identities k hk
  exact equilibrium_loadedCatalyticCurrent_eq_bindingCurrentAtFree
    k (sourceBindingP k) (sourceBindingQ k) x hk heq hp hq

/-- The literal positive-rate binding ratios make the post-binding
free-substrate current pivot parity positive at every positive state. -/
theorem sourceBindingCurrentSubstrateJacobian_actual_parity_pos {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive) :
    0 < (-1 : ℝ)^n *
      (sourceBindingCurrentSubstrateJacobian k
        (sourceBindingP k) (sourceBindingQ k) x.E x.F).det := by
  apply sourceBindingCurrentSubstrateJacobian_parity_det_pos
    k (sourceBindingP k) (sourceBindingQ k) x.E x.F hk
  · intro i
    exact (sourceBindingRatios_positive k hk i).2
  · exact hx.2.2.1

end
end PhosphorylationStableCapacity
