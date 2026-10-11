module
public import proofs.PhosphorylationStableCapacity.PositiveFactorPairRatioOrder

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial

noncomputable section

/-- Turn a list of factors indexed by a finite set into the corresponding
multiset product. Injectivity ensures image removes no factor. -/
theorem positiveFactorProduct_finset
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ)
    (hinj : Set.InjOn f s) :
    positiveFactorProduct (s.val.toList.map fun i => -f i) =
      ((s.image f).val.map fun r : ℝ => X - C r).prod := by
  classical
  rw [positiveFactorProduct_eq_list_prod]
  have hlist :
      ((s.val.toList.map fun i => -f i).map fun r : ℝ => X + C r) =
        s.val.toList.map (fun i => X - C (f i)) := by
    simp [List.map_map, sub_eq_add_neg]
  rw [hlist]
  have hmap :
      (((s.val.toList.map fun i => X - C (f i)) : List ℝ[X]) :
        Multiset ℝ[X]) =
      s.val.map (fun i => X - C (f i)) := by
    change (s.val.toList : Multiset α).map (fun i => X - C (f i)) = _
    rw [Multiset.coe_toList]
  change (((s.val.toList.map fun i => X - C (f i)) : List ℝ[X]) :
    Multiset ℝ[X]).prod = _
  rw [hmap, Finset.image_val_of_injOn hinj]
  simp [Multiset.map_map]

end
end PhosphorylationStableCapacity
