module
public import proofs.PhosphorylationStableCapacity.CoalescedFullMassLimit

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Algebraic loaded mass formula for free substrates and two families of
enzyme-bound complexes at fixed enzyme totals. -/
def loadedBindingMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S C Y : ι → ℝ) (ET FT : ℝ) : Matrix ι ι ℝ :=
  fun i j => (if i = j then S i + C i + Y i else 0) -
    C i * C j / ET - Y i * Y j / FT

/-- The mass matrix acts on logarithmic substrate variations by subtracting
the enzyme-total corrections from both bound-complex variations. -/
theorem loadedBindingMass_action {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S C Y σ : ι → ℝ) (ET FT : ℝ) (i : ι) :
    (loadedBindingMass S C Y ET FT).mulVec σ i =
      S i * σ i +
      C i * (σ i - (∑ j, C j * σ j) / ET) +
      Y i * (σ i - (∑ j, Y j * σ j) / FT) := by
  simp only [Matrix.mulVec, dotProduct, loadedBindingMass,
    sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul]
  have hdiag :
      (∑ j, if i = j then (S i + C i + Y i) * σ j else 0) =
        (S i + C i + Y i) * σ i := by
    simp
  rw [hdiag]
  have hC : (∑ j, C i * C j / ET * σ j) =
      C i / ET * (∑ j, C j * σ j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hY : (∑ j, Y i * Y j / FT * σ j) =
      Y i / FT * (∑ j, Y j * σ j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hC, hY]
  ring

/-- The coalesced finite-source candidate matrix is the generic loaded
binding formula evaluated on its literal concentrations and totals. -/
theorem coalescedFullMass_eq_loadedBindingMass (m : ℕ) (r : ℝ) :
    coalescedFullMass m r =
      loadedBindingMass (coalescedFiniteState (m + 1) r).S
        (coalescedFiniteCLevel m r) (coalescedFiniteYLevel m r)
        (2 * r) 2 := by
  rfl

theorem coalescedFullMass_action (m : ℕ) (r : ℝ)
    (σ : Fin (m + 3) → ℝ) (i : Fin (m + 3)) :
    (coalescedFullMass m r).mulVec σ i =
      (coalescedFiniteState (m + 1) r).S i * σ i +
      coalescedFiniteCLevel m r i *
        (σ i - (∑ j, coalescedFiniteCLevel m r j * σ j) / (2 * r)) +
      coalescedFiniteYLevel m r i *
        (σ i - (∑ j, coalescedFiniteYLevel m r j * σ j) / 2) := by
  rw [coalescedFullMass_eq_loadedBindingMass]
  exact loadedBindingMass_action _ _ _ σ (2 * r) 2 i

end
end PhosphorylationStableCapacity
