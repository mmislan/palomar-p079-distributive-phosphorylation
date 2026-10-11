module
public import Mathlib.Data.Fin.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section

/-- Any finite ordered tuple in the paper can be supplied to the sequence-based
construction; the auxiliary tail puts no additional restriction on its entries. -/
def extendFiniteOrderedOffsets {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) : ℕ → ℝ :=
  fun k => if hk : k < N then x ⟨k, hk⟩ else
    x ⟨N-1, by omega⟩ + (k : ℝ) - ((N-1 : ℕ) : ℝ)

theorem extendFiniteOrderedOffsets_agrees {N : ℕ} (hN : 0 < N)
    (x : Fin N → ℝ) (i : Fin N) :
    extendFiniteOrderedOffsets hN x i.val = x i := by
  simp only [extendFiniteOrderedOffsets, dite_eq_left i.isLt]

theorem extendFiniteOrderedOffsets_strictMono {N : ℕ} (hN : 0 < N)
    (x : Fin N → ℝ) (hx : StrictMono x) :
    StrictMono (extendFiniteOrderedOffsets hN x) := by
  intro k l hkl
  by_cases hk : k < N
  · by_cases hl : l < N
    · simp only [extendFiniteOrderedOffsets, dite_eq_left hk, dite_eq_left hl]
      exact hx hkl
    · simp only [extendFiniteOrderedOffsets, dite_eq_left hk, dite_eq_right hl]
      have hle : x ⟨k, hk⟩ ≤ x ⟨N-1, by omega⟩ :=
        hx.monotone (by change k ≤ N-1; omega)
      have hlast : N-1 < l := by omega
      have hcast : ((N-1 : ℕ) : ℝ) < (l : ℝ) := by exact_mod_cast hlast
      linarith
  · have hl : ¬ l < N := by omega
    simp only [extendFiniteOrderedOffsets, dite_eq_right hk, dite_eq_right hl]
    have hcast : (k : ℝ) < (l : ℝ) := by exact_mod_cast hkl
    linarith

theorem finite_ordered_offsets_extend {N : ℕ} (hN : 0 < N)
    (x : Fin N → ℝ) (hx : StrictMono x) :
    ∃ ξ : ℕ → ℝ, StrictMono ξ ∧ ∀ i : Fin N, ξ i.val = x i :=
  ⟨extendFiniteOrderedOffsets hN x,
    extendFiniteOrderedOffsets_strictMono hN x hx,
    extendFiniteOrderedOffsets_agrees hN x⟩

end
end PhosphorylationStableCapacity
