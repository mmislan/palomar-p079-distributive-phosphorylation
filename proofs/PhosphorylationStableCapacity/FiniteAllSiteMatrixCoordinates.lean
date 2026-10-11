module
public import proofs.PhosphorylationStableCapacity.FiniteAllSiteJacobianUnified

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Coordinate readout for the three consecutive blocks of the class chart. -/
def allSiteCoordinateRead {n : ℕ}
    (i : Fin n ⊕ (Fin n ⊕ Fin n)) (u : CoordinateSpace n) : ℝ :=
  match i with
  | .inl j => u.1 j
  | .inr (.inl j) => u.2.1 j
  | .inr (.inr j) => u.2.2 j

/-- The corresponding literal unit basis vector. -/
def allSiteCoordinateUnit {n : ℕ}
    (j : Fin n ⊕ (Fin n ⊕ Fin n)) : CoordinateSpace n :=
  match j with
  | .inl i => (Pi.single i 1, (0, 0))
  | .inr (.inl i) => (0, (Pi.single i 1, 0))
  | .inr (.inr i) => (0, (0, Pi.single i 1))

theorem allSiteCoordinateRead_eq_basis_repr {n : ℕ}
    (i : Fin n ⊕ (Fin n ⊕ Fin n)) (u : CoordinateSpace n) :
    (coordinateBasis n).repr u i = allSiteCoordinateRead i u := by
  rcases i with i | i
  · simp [allSiteCoordinateRead, coordinateBasis]
  rcases i with i | i
  · simp [allSiteCoordinateRead, coordinateBasis]
  · simp [allSiteCoordinateRead, coordinateBasis]

theorem allSiteCoordinateUnit_eq_basis {n : ℕ}
    (j : Fin n ⊕ (Fin n ⊕ Fin n)) :
    coordinateBasis n j = allSiteCoordinateUnit j := by
  rcases j with j | j
  · simp [allSiteCoordinateUnit, coordinateBasis, Prod.mk_zero_zero]
  rcases j with j | j
  · simp [allSiteCoordinateUnit, coordinateBasis]
  · simp [allSiteCoordinateUnit, coordinateBasis]

/-- A certificate entry is an explicit finite-sum row acting on one unit
vector. This statement remains uniform in the number of sites. -/
theorem allSiteExplicitFinMatrix_entry {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (i j : Fin (3 * n)) :
    allSiteExplicitFinMatrix ET FT ST k u i j =
      allSiteCoordinateRead ((allSiteIndexEquiv n).symm i)
        (allSiteJacobianCLM ET FT ST k u
          (allSiteCoordinateUnit ((allSiteIndexEquiv n).symm j))) := by
  rw [allSiteExplicitFinMatrix_apply,
    allSiteCoordinateRead_eq_basis_repr,
    allSiteCoordinateUnit_eq_basis]

end
end PhosphorylationStableCapacity
