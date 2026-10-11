module
public import proofs.PhosphorylationStableCapacity.LoadedDerivativeBlockScaling
public import proofs.PhosphorylationStableCapacity.FastBindingEnergy

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

abbrev SlowSpace (n : ℕ) := Fin n → ℝ

/-- The four literal Fréchet-derivative blocks in fixed loaded coordinates. -/
def loadedBlockA {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) : SlowSpace n →L[ℝ] SlowSpace n :=
  (ContinuousLinearMap.fst ℝ (SlowSpace n) (FastSpace n)).comp
    ((fderiv ℝ (loadedRestrictedField ET FT ST k) u).comp
      (ContinuousLinearMap.inl ℝ (SlowSpace n) (FastSpace n)))

def loadedBlockB {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) : FastSpace n →L[ℝ] SlowSpace n :=
  (ContinuousLinearMap.fst ℝ (SlowSpace n) (FastSpace n)).comp
    ((fderiv ℝ (loadedRestrictedField ET FT ST k) u).comp
      (ContinuousLinearMap.inr ℝ (SlowSpace n) (FastSpace n)))

def loadedBlockC {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) : SlowSpace n →L[ℝ] FastSpace n :=
  (ContinuousLinearMap.snd ℝ (SlowSpace n) (FastSpace n)).comp
    ((fderiv ℝ (loadedRestrictedField ET FT ST k) u).comp
      (ContinuousLinearMap.inl ℝ (SlowSpace n) (FastSpace n)))

def loadedBlockD {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) : FastSpace n →L[ℝ] FastSpace n :=
  (ContinuousLinearMap.snd ℝ (SlowSpace n) (FastSpace n)).comp
    ((fderiv ℝ (loadedRestrictedField ET FT ST k) u).comp
      (ContinuousLinearMap.inr ℝ (SlowSpace n) (FastSpace n)))

theorem loadedBlockA_relax {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) {ε : ℝ} (hε : ε ≠ 0) :
    loadedBlockA ET FT ST (relaxRates k ε) u =
      loadedBlockA ET FT ST k u := by
  apply ContinuousLinearMap.ext
  intro v
  simp [loadedBlockA, loadedFderiv_relax_blocks ET FT ST k u _ hε]

theorem loadedBlockB_relax {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) {ε : ℝ} (hε : ε ≠ 0) :
    loadedBlockB ET FT ST (relaxRates k ε) u =
      loadedBlockB ET FT ST k u := by
  apply ContinuousLinearMap.ext
  intro v
  simp [loadedBlockB, loadedFderiv_relax_blocks ET FT ST k u _ hε]

theorem loadedBlockC_relax {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) {ε : ℝ} (hε : ε ≠ 0) :
    loadedBlockC ET FT ST (relaxRates k ε) u =
      ε⁻¹ • loadedBlockC ET FT ST k u := by
  apply ContinuousLinearMap.ext
  intro v
  simp [loadedBlockC, loadedFderiv_relax_blocks ET FT ST k u _ hε]
  rfl

theorem loadedBlockD_relax {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) {ε : ℝ} (hε : ε ≠ 0) :
    loadedBlockD ET FT ST (relaxRates k ε) u =
      ε⁻¹ • loadedBlockD ET FT ST k u := by
  apply ContinuousLinearMap.ext
  intro v
  simp [loadedBlockD, loadedFderiv_relax_blocks ET FT ST k u _ hε]
  rfl

end
end PhosphorylationStableCapacity
