module
public import Mathlib.Data.Fintype.Basic
public import proofs.PhosphorylationStableCapacity.FiniteOrderedOffsetExtension
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The finite tuple version of the root-gap product printed in the paper. -/
def finiteOffsetGap {N : ℕ} (x : Fin N → ℝ) (j : Fin N) : ℝ :=
  ∏ i ∈ Finset.univ.erase j, (x j-x i)

theorem finiteOffsetGap_eq_sequence_gap {N : ℕ}
    (x : Fin N → ℝ) (ξ : ℕ → ℝ)
    (hagree : ∀ i : Fin N, ξ i.val = x i)
    (j : Fin N) :
    finiteOffsetGap x j =
      ∏ i ∈ (Finset.range N).erase j.val, (ξ j.val-ξ i) := by
  classical
  unfold finiteOffsetGap
  apply Finset.prod_bij (fun i hi => i.val)
  · intro i hi
    obtain ⟨hij, _⟩ := Finset.mem_erase.mp hi
    exact Finset.mem_erase.mpr
      ⟨fun h => hij (Fin.ext h), Finset.mem_range.mpr i.isLt⟩
  · intro i hi k hk h
    exact Fin.ext h
  · intro v hv
    obtain ⟨hneq, hvN⟩ := Finset.mem_erase.mp hv
    let i : Fin N := ⟨v, Finset.mem_range.mp hvN⟩
    have hi : i ∈ Finset.univ.erase j :=
      Finset.mem_erase.mpr
        ⟨fun heq => hneq (congrArg Fin.val heq), Finset.mem_univ _⟩
    exact ⟨i, hi, rfl⟩
  · intro i hi
    simp only [hagree j, hagree i]

end
end PhosphorylationStableCapacity
