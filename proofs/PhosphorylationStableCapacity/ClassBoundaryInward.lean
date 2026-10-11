module
public import proofs.PhosphorylationStableCapacity.ClassPolytopeBounds

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The literal mass-action field points inward or tangent on every
active nonnegative face of a compatibility class. -/
theorem nonnegative_state_field_inward {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : NonnegativeState x) :
    (∀ j : Fin (n+1), x.S j = 0 → 0 ≤ (field k x).S j) ∧
      (x.E = 0 → 0 ≤ (field k x).E) ∧
      (x.F = 0 → 0 ≤ (field k x).F) ∧
      (∀ i : Fin n, x.C i = 0 → 0 ≤ (field k x).C i) ∧
      (∀ i : Fin n, x.D i = 0 → 0 ≤ (field k x).D i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    dsimp [field]
    apply Finset.sum_nonneg
    intro i _
    have hleft : 0 ≤
        (if i.castSucc = j then
          -kinaseNet k x i + k.gamma i*x.D i else 0) := by
      split_ifs with h
      · have hS : x.S i.castSucc = 0 := by rw [h]; exact hj
        have hC : 0 ≤ k.b i*x.C i :=
          mul_nonneg (hk i).2.1.le (hx.2.2.2.1 i)
        have hD : 0 ≤ k.gamma i*x.D i :=
          mul_nonneg (hk i).2.2.2.2.2.le (hx.2.2.2.2 i)
        simp [kinaseNet, hS]
        linarith
      · exact le_refl _
    have hright : 0 ≤
        (if i.succ = j then
          k.c i*x.C i - phosphataseNet k x i else 0) := by
      split_ifs with h
      · have hS : x.S i.succ = 0 := by rw [h]; exact hj
        have hC : 0 ≤ k.c i*x.C i :=
          mul_nonneg (hk i).2.2.1.le (hx.2.2.2.1 i)
        have hD : 0 ≤ k.beta i*x.D i :=
          mul_nonneg (hk i).2.2.2.2.1.le (hx.2.2.2.2 i)
        simp [phosphataseNet, hS]
        linarith
      · exact le_refl _
    exact add_nonneg hleft hright
  · intro hE
    dsimp [field]
    apply Finset.sum_nonneg
    intro i _
    have hb : 0 ≤ k.b i*x.C i :=
      mul_nonneg (hk i).2.1.le (hx.2.2.2.1 i)
    have hc : 0 ≤ k.c i*x.C i :=
      mul_nonneg (hk i).2.2.1.le (hx.2.2.2.1 i)
    simp [kinaseNet, hE]
    linarith
  · intro hF
    dsimp [field]
    apply Finset.sum_nonneg
    intro i _
    have hb : 0 ≤ k.beta i*x.D i :=
      mul_nonneg (hk i).2.2.2.2.1.le (hx.2.2.2.2 i)
    have hc : 0 ≤ k.gamma i*x.D i :=
      mul_nonneg (hk i).2.2.2.2.2.le (hx.2.2.2.2 i)
    simp [phosphataseNet, hF]
    linarith
  · intro i hC
    dsimp [field, kinaseNet]
    rw [hC]
    have hSE : 0 ≤ x.S i.castSucc*x.E :=
      mul_nonneg (hx.1 i.castSucc) hx.2.1
    simpa [mul_assoc] using mul_nonneg (hk i).1.le hSE
  · intro i hD
    dsimp [field, phosphataseNet]
    rw [hD]
    have hSF : 0 ≤ x.S i.succ*x.F :=
      mul_nonneg (hx.1 i.succ) hx.2.2.1
    simpa [mul_assoc] using mul_nonneg (hk i).2.2.2.1.le hSF

end
end PhosphorylationStableCapacity
