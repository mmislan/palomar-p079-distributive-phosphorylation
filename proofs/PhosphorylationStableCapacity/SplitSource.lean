module
public import proofs.PhosphorylationStableCapacity.SplitRootFamily
public import proofs.PhosphorylationStableCapacity.CoalescedFiniteSource
public import proofs.PhosphorylationSharpness.Resolution

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

def splitRawD (m : ℕ) (r δ : ℝ) : ℝ[X] :=
  rawD (splitPair m δ).1 (splitPair m δ).2 r

def splitRawB (m : ℕ) (r δ : ℝ) : ℝ[X] :=
  rawB (splitPair m δ).1 (splitPair m δ).2 r

/-- One rate list shared by all split states. -/
def splitFiniteRates (m : ℕ) (r δ : ℝ) : Rates (m + 1) :=
  realize
    (fun i : Fin (m + 2) => ((1 + X) * splitRawD m r δ).coeff i)
    (fun i : Fin (m + 1) => (splitRawB m r δ).coeff i)
    (fun i : Fin (m + 1) => (splitRawD m r δ).coeff i)

/-- The state at the `j`th prescribed root, reconstructed with that same
rate list and the same total triple. -/
def splitFiniteState (m : ℕ) (r δ : ℝ) (j : Fin (2*m+1)) : State (m + 1) :=
  let x := splitRoot δ j.val
  reconstruct
    (fun i : Fin (m + 2) => ((1 + X) * splitRawD m r δ).coeff i)
    (fun i : Fin (m + 1) => (splitRawB m r δ).coeff i)
    (fun i : Fin (m + 1) => (splitRawD m r δ).coeff i)
    (ratio x) (rootS x ((splitRawD m r δ).eval (ratio x))) (rootF x)

theorem splitFiniteRates_zero_eq_coalesced (m : ℕ) (r : ℝ) :
    splitFiniteRates m r 0 = coalescedFiniteRates m r := by
  simp [splitFiniteRates, splitRawD, splitRawB,
    coalescedFiniteRates, coalescedRawD, coalescedRawB,
    splitPair_zero_eq_coalesced]

theorem splitFiniteState_zero_eq_coalesced (m : ℕ) (r : ℝ)
    (j : Fin (2*m+1)) :
    splitFiniteState m r 0 j = coalescedFiniteState m r := by
  simp [splitFiniteState, splitRawD, splitRawB,
    coalescedFiniteState, coalescedRawD, coalescedRawB,
    splitPair_zero_eq_coalesced, splitRoot]

theorem splitFiniteState_injective (m : ℕ) (r : ℝ) {δ : ℝ}
    (hδ : 0 < δ) : Function.Injective (splitFiniteState m r δ) := by
  intro i j hij
  let xx : Fin (2*m+1) → ℝ := fun a => splitRoot δ a.val
  have hx (a : Fin (2*m+1)) : 1 < xx a := by
    have hh : 0 ≤ δ * (a.val : ℝ) :=
      mul_nonneg hδ.le (Nat.cast_nonneg _)
    dsimp [xx, splitRoot]
    linarith
  have hf (a : Fin (2*m+1)) : rootF (xx a) ≠ 0 :=
    ne_of_gt (div_pos (by norm_num) (by have := hx a; linarith))
  have hrat := congrArg (fun w : State (m+1) => w.E/w.F) hij
  change (reconstruct _ _ _ (ratio (xx i)) _ (rootF (xx i))).E /
    (reconstruct _ _ _ (ratio (xx i)) _ (rootF (xx i))).F =
      (reconstruct _ _ _ (ratio (xx j)) _ (rootF (xx j))).E /
    (reconstruct _ _ _ (ratio (xx j)) _ (rootF (xx j))).F at hrat
  rw [reconstruct_ratio _ _ _ _ _ _ (hf i),
    reconstruct_ratio _ _ _ _ _ _ (hf j)] at hrat
  have he := ratio_injective (hx i) (hx j) hrat
  exact Fin.ext ((splitRoot_strictMono hδ).injective he)

/-- If conversion coefficients stay positive, the near-coalescent family
already supplies all `2m+1` distinct literal equilibria under one common
rate list and one total triple. Positivity near `δ=0` is a separate
continuity obligation. -/
theorem splitFiniteSource_attains_of_conversion_positive
    (m : ℕ) (r δ : ℝ)
    (hr : 0 < r) (hδ : 0 < δ)
    (hD : DensePositive (splitRawD m r δ) m)
    (hB : DensePositive (splitRawB m r δ) m) :
    Attains (m + 1) (2*m+1) := by
  let B := splitRawB m r δ
  let D := splitRawD m r δ
  let A : ℝ[X] := (1 + X) * D
  let t : Fin (m + 2) → ℝ := fun i => A.coeff i
  let b : Fin (m + 1) → ℝ := fun i => B.coeff i
  let d : Fin (m + 1) → ℝ := fun i => D.coeff i
  let xx : Fin (2*m+1) → ℝ := fun j => splitRoot δ j.val
  let z : Fin (2*m+1) → State (m+1) := fun j =>
    reconstruct t b d (ratio (xx j))
      (rootS (xx j) (D.eval (ratio (xx j)))) (rootF (xx j))
  have hx (j : Fin (2*m+1)) : 1 < xx j := by
    have hh : 0 ≤ δ * (j.val : ℝ) :=
      mul_nonneg hδ.le (Nat.cast_nonneg _)
    dsimp [xx, splitRoot]
    linarith
  have hrel (j : Fin (2*m+1)) :
      (xx j - 1) * (B.eval (ratio (xx j)) - r * D.eval (ratio (xx j))) =
        2 * (r - ratio (xx j)) * D.eval (ratio (xx j)) := by
    apply conversion_root (splitPair m δ).1 (splitPair m δ).2 r (xx j)
    exact splitPair_roots m j.val δ (by omega)
  have hA : DensePositive A (m+1) := dense_inventory_product hD
  have ht : ∀ i, 0 < t i := fun i => hA.1 i (by omega)
  have hb : ∀ i, 0 < b i := fun i => hB.1 i (by omega)
  have hd : ∀ i, 0 < d i := fun i => hD.1 i (by omega)
  refine ⟨splitFiniteRates m r δ, 2*r, 2, 2*(r+1),
    splitFiniteState m r δ,
    ?_, by positivity, by norm_num, by positivity, ?_, ?_⟩
  · exact realize_positive t b d ht hb hd
  · intro i j hij
    have hrat := congrArg (fun w : State (m+1) => w.E/w.F) hij
    have hf (k : Fin (2*m+1)) : rootF (xx k) ≠ 0 :=
      ne_of_gt (div_pos (by norm_num) (by have := hx k; linarith))
    change (z i).E/(z i).F = (z j).E/(z j).F at hrat
    rw [reconstruct_ratio _ _ _ _ _ _ (hf i),
      reconstruct_ratio _ _ _ _ _ _ (hf j)] at hrat
    have he := ratio_injective (hx i) (hx j) hrat
    have hindex : i.val = j.val :=
      (splitRoot_strictMono hδ).injective (by simpa [xx] using he)
    exact Fin.ext hindex
  · intro j
    exact source_from_coefficients B D hB hD r (xx j) (hx j) (hrel j)

end
end PhosphorylationStableCapacity
