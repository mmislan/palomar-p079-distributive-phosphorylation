module
public import proofs.PhosphorylationStableCapacity.GeneralEquilibriumNegativeRoot

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Polynomial

/-- At arbitrary positive rates and totals, any finite collection of
distinct positive literal equilibria in one class has at most `2n`
members. This is the equilibrium budget needed for the degree/index
ceiling; the sharper published `2n-1` bound is not used here. -/
theorem positive_equilibria_card_le_two_n {n : ℕ}
    (k : Rates n) (hn : 0 < n) (hk : k.Positive)
    (ET FT ST : ℝ) (hET : 0 < ET) (hFT : 0 < FT)
    (S : Finset (State n))
    (hS : ∀ x ∈ S, x.Positive ∧ Equilibrium k x ∧
      InClass ET FT ST x) :
    S.card ≤ 2*n := by
  classical
  let P := equilibriumEliminationPoly k ET FT ST
  let ratio : State n → ℝ := fun x => x.E/x.F
  let roots : Finset ℝ := P.roots.toFinset
  let image : Finset ℝ := S.image ratio
  obtain ⟨negative, hnegative, hnegativeRoot⟩ :=
    equilibriumEliminationPoly_negative_root
      k hn hk ET FT ST hET hFT
  have hzeroRoot : P.eval 0 = 0 :=
    equilibriumEliminationPoly_zero_root k ET FT ST
  have hPne : P ≠ 0 := by
    intro hP
    have hcoeff := equilibriumEliminationPoly_coeff_one_neg
      k hn hk ET FT ST hET hFT
    change P.coeff 1 < 0 at hcoeff
    rw [hP, coeff_zero] at hcoeff
    linarith
  have hmem (u : ℝ) (hu : P.eval u = 0) : u ∈ roots := by
    change u ∈ P.roots.toFinset
    rw [Multiset.mem_toFinset, mem_roots hPne]
    exact hu
  have hImageInj : (S : Set (State n)).InjOn ratio := by
    intro x hx y hy hratio
    obtain ⟨hxpos, hxeq, hxclass⟩ := hS x hx
    obtain ⟨hypos, hyeq, hyclass⟩ := hS y hy
    exact positive_equilibria_enzyme_ratio_injective
      k x y hn hk hxpos hypos hxeq hyeq
      (hxclass.2.1.trans hyclass.2.1.symm)
      (hxclass.2.2.trans hyclass.2.2.symm) hratio
  have hImageCard : image.card = S.card := by
    exact Finset.card_image_of_injOn hImageInj
  have hImageSub : image ⊆ roots := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hxpos, hxeq, hxclass⟩ := hS x hx
    apply hmem
    change (equilibriumEliminationPoly k ET FT ST).eval (x.E/x.F) = 0
    rw [← hxclass.1, ← hxclass.2.1, ← hxclass.2.2]
    exact positive_equilibrium_poly_root k x hk hxpos hxeq
  have hImagePos : ∀ u ∈ image, 0 < u := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    exact div_pos (hS x hx).1.2.1 (hS x hx).1.2.2.1
  let extras : Finset ℝ := {0, negative}
  have hExtrasCard : extras.card = 2 := by
    have hne : (0 : ℝ) ≠ negative := Ne.symm (ne_of_lt hnegative)
    simp [extras, hne]
  have hExtrasSub : extras ⊆ roots := by
    intro u hu
    simp only [extras, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with hu | hu
    · rw [hu]
      exact hmem 0 hzeroRoot
    · rw [hu]
      exact hmem negative hnegativeRoot
  have hDisj : Disjoint image extras := by
    apply Finset.disjoint_left.mpr
    intro u huimg huex
    have hpos := hImagePos u huimg
    simp only [extras, Finset.mem_insert, Finset.mem_singleton] at huex
    rcases huex with rfl | rfl <;> linarith
  have hUnionCard : S.card+2 = (image ∪ extras).card := by
    rw [Finset.card_union_of_disjoint hDisj, hImageCard,
      hExtrasCard]
  have hUnionSub : image ∪ extras ⊆ roots :=
    Finset.union_subset hImageSub hExtrasSub
  have hRootCard : roots.card ≤ P.natDegree := by
    exact (Multiset.toFinset_card_le P.roots).trans (card_roots' P)
  have hDegree := equilibriumEliminationPoly_natDegree_le k ET FT ST
  have hcard : (image ∪ extras).card ≤ 2*n+2 :=
    (Finset.card_le_card hUnionSub).trans (hRootCard.trans hDegree)
  omega

/-- The full set of positive literal equilibria in a fixed class is
finite, with the uniform `2n` cardinality bound. -/
theorem positive_equilibria_finite_and_ncard_le_two_n {n : ℕ}
    (k : Rates n) (hn : 0 < n) (hk : k.Positive)
    (ET FT ST : ℝ) (hET : 0 < ET) (hFT : 0 < FT) :
    let E : Set (State n) :=
      {x | x.Positive ∧ Equilibrium k x ∧ InClass ET FT ST x}
    E.Finite ∧ E.ncard ≤ 2*n := by
  classical
  dsimp
  let E : Set (State n) :=
    {x | x.Positive ∧ Equilibrium k x ∧ InClass ET FT ST x}
  let P := equilibriumEliminationPoly k ET FT ST
  let ratio : State n → ℝ := fun x => x.E/x.F
  have hPne : P ≠ 0 := by
    intro hP
    have hcoeff := equilibriumEliminationPoly_coeff_one_neg
      k hn hk ET FT ST hET hFT
    change P.coeff 1 < 0 at hcoeff
    rw [hP, coeff_zero] at hcoeff
    linarith
  have hMaps : Set.MapsTo ratio E (P.roots.toFinset : Set ℝ) := by
    intro x hx
    obtain ⟨hxpos, hxeq, hxclass⟩ := hx
    change ratio x ∈ P.roots.toFinset
    rw [Multiset.mem_toFinset, mem_roots hPne]
    change (equilibriumEliminationPoly k ET FT ST).eval (x.E/x.F) = 0
    rw [← hxclass.1, ← hxclass.2.1, ← hxclass.2.2]
    exact positive_equilibrium_poly_root k x hk hxpos hxeq
  have hInj : E.InjOn ratio := by
    intro x hx y hy hratio
    obtain ⟨hxpos, hxeq, hxclass⟩ := hx
    obtain ⟨hypos, hyeq, hyclass⟩ := hy
    exact positive_equilibria_enzyme_ratio_injective
      k x y hn hk hxpos hypos hxeq hyeq
      (hxclass.2.1.trans hyclass.2.1.symm)
      (hxclass.2.2.trans hyclass.2.2.symm) hratio
  have hfin : E.Finite :=
    Set.Finite.of_injOn hMaps hInj (Finset.finite_toSet _)
  refine ⟨hfin, ?_⟩
  have hcard := positive_equilibria_card_le_two_n
    k hn hk ET FT ST hET hFT hfin.toFinset (by
      intro x hx
      exact hfin.mem_toFinset.mp hx)
  change E.ncard ≤ 2*n
  rw [Set.ncard_eq_toFinset_card E hfin]
  exact hcard

end
end PhosphorylationStableCapacity
