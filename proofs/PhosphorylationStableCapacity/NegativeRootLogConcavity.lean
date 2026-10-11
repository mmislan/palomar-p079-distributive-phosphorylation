module
public import proofs.PhosphorylationStableCapacity.PositiveFactorListProduct

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial

noncomputable section

def negativeRootFactorList (s : Multiset ℝ) : List ℝ :=
  s.toList.map fun r => -r

theorem negativeRootFactorList_pos (s : Multiset ℝ)
    (hs : ∀ r ∈ s, r < 0) :
    ∀ a ∈ negativeRootFactorList s, 0 < a := by
  intro a ha
  rcases List.mem_map.mp ha with ⟨r, hr, rfl⟩
  exact neg_pos.mpr (hs r (Multiset.mem_toList.mp hr))

theorem negativeRootFactorList_length (s : Multiset ℝ) :
    (negativeRootFactorList s).length = s.card := by
  simp [negativeRootFactorList]

theorem negativeRootFactorList_prod (s : Multiset ℝ) :
    positiveFactorProduct (negativeRootFactorList s) =
      (s.map fun r : ℝ => X - C r).prod := by
  rw [positiveFactorProduct_eq_list_prod]
  unfold negativeRootFactorList
  have hlist :
      (s.toList.map fun r : ℝ => -r).map (fun r => X + C r) =
        s.toList.map (fun r : ℝ => X - C r) := by
    simp [List.map_map, sub_eq_add_neg]
  rw [hlist]
  have hmap :
      (((s.toList.map fun r : ℝ => X - C r) : List ℝ[X]) : Multiset ℝ[X]) =
        s.map (fun r : ℝ => X - C r) := by
    change (s.toList : Multiset ℝ).map (fun r : ℝ => X - C r) = _
    rw [Multiset.coe_toList]
  change (((s.toList.map fun r : ℝ => X - C r) : List ℝ[X]) :
    Multiset ℝ[X]).prod = (s.map fun r : ℝ => X - C r).prod
  rw [hmap]

/-- A polynomial with a full multiset of negative real roots has
log-concave coefficients on its degree support. -/
theorem coeffLogConcave_of_negative_roots {p : ℝ[X]}
    (hcard : p.roots.card = p.natDegree)
    (hneg : ∀ r ∈ p.roots, r < 0) :
    CoeffLogConcave p p.natDegree := by
  have hpos := negativeRootFactorList_pos p.roots hneg
  have hlc := positiveFactorProduct_logconcave
    (negativeRootFactorList p.roots) hpos
  rw [negativeRootFactorList_length, hcard] at hlc
  have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  rw [← negativeRootFactorList_prod] at hfac
  have hscaled := coeffLogConcave_C_mul hlc p.leadingCoeff
  rw [hfac] at hscaled
  exact hscaled

end
end PhosphorylationStableCapacity
