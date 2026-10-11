module
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import proofs.PhosphorylationStableCapacity.FixedRatioTotals

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The universal positive adjacent-level factor, extended by one
beyond the physical chain so its finite product has a simple recursion. -/
def equilibriumNatFactor {n : ℕ} (k : Rates n) (m : ℕ) : ℝ :=
  if h : m < n then equilibriumRatioFactor k ⟨m, h⟩ else 1

theorem equilibriumNatFactor_pos {n : ℕ}
    (k : Rates n) (hk : k.Positive) (m : ℕ) :
    0 < equilibriumNatFactor k m := by
  unfold equilibriumNatFactor
  split_ifs with h
  · exact equilibriumRatioFactor_pos k hk ⟨m, h⟩
  · norm_num

/-- The substrate profile polynomial coefficient at level `m` for
an arbitrary positive rate list. -/
def equilibriumWeight {n : ℕ} (k : Rates n) (m : ℕ) : ℝ :=
  ∏ i ∈ Finset.range m, equilibriumNatFactor k i

theorem equilibriumWeight_pos {n : ℕ}
    (k : Rates n) (hk : k.Positive) (m : ℕ) :
    0 < equilibriumWeight k m := by
  unfold equilibriumWeight
  exact Finset.prod_pos fun i _ => equilibriumNatFactor_pos k hk i

theorem equilibriumWeight_succ {n : ℕ}
    (k : Rates n) (i : Fin n) :
    equilibriumWeight k (i.val+1) =
      equilibriumWeight k i.val * equilibriumRatioFactor k i := by
  simp only [equilibriumWeight, Finset.prod_range_succ]
  simp [equilibriumNatFactor, i.isLt]

/-- Every positive equilibrium, at arbitrary positive rates, has a
single-variable substrate profile controlled by `E/F` and `S₀`. -/
theorem equilibrium_substrate_profile {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) :
    ∀ j : Fin (n+1), x.S j =
      equilibriumWeight k j.val * (x.E/x.F)^j.val * x.S 0 := by
  intro j
  induction j using Fin.induction with
  | zero => simp [equilibriumWeight]
  | succ i ih =>
      have hr := equilibrium_substrate_ratio k x hk hx heq i
      have hs : x.S i.castSucc ≠ 0 := ne_of_gt (hx.1 i.castSucc)
      have hmul : x.S i.succ =
          (equilibriumRatioFactor k i * (x.E/x.F)) *
            x.S i.castSucc := (div_eq_iff hs).mp hr
      rw [hmul, ih]
      change equilibriumRatioFactor k i * (x.E/x.F) *
          (equilibriumWeight k i.val * (x.E/x.F)^i.val * x.S 0) =
        equilibriumWeight k (i.val+1) * (x.E/x.F)^(i.val+1) * x.S 0
      rw [equilibriumWeight_succ, pow_succ]
      ring

end
end PhosphorylationStableCapacity
