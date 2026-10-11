module
public import proofs.PhosphorylationStableCapacity.BindingIncidenceAffinity
public import proofs.PhosphorylationStableCapacity.FastBindingRateDiagonal
public import proofs.PhosphorylationStableCapacity.LoadedBindingMassOrientation

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Matrix
open scoped BigOperators

theorem source_fastAffinity_eq_complementary {n : ℕ}
    (x : State n) (hx : x.Positive) :
    let K := bindingFreeIncidence (Fin.castSucc : Fin n → Fin (n+1)) Fin.succ
    let Df := diagonal (Sum.elim x.S ![x.E, x.F])
    let Dc := diagonal (Sum.elim x.C x.D)
    fastAffinityMatrix n x = Dc⁻¹ + K.transpose * Df⁻¹ * K := by
  dsimp only
  have hdc : ∀ a : Fin n ⊕ Fin n, Sum.elim x.C x.D a ≠ 0 := by
    intro a
    cases a with
    | inl i => exact ne_of_gt (hx.2.2.2.1 i)
    | inr i => exact ne_of_gt (hx.2.2.2.2 i)
  have hdf : ∀ a : Fin (n+1) ⊕ Fin 2, Sum.elim x.S ![x.E, x.F] a ≠ 0 := by
    intro a
    cases a with
    | inl i => exact ne_of_gt (hx.1 i)
    | inr i => fin_cases i <;> simp [ne_of_gt hx.2.1, ne_of_gt hx.2.2.1]
  rw [inverse_diagonal_of_entries_ne_zero _ hdc,
    inverse_diagonal_of_entries_ne_zero _ hdf]
  have hrepr (v : FastSpace n) :
      (fastBasis n).repr v = Sum.elim v.1 v.2 := by
    ext a
    cases a with
    | inl i => exact fastBasis_repr_inl v i
    | inr i => exact fastBasis_repr_inr v i
  have haction (v : FastSpace n) := binding_affinity_action
    (Fin.castSucc : Fin n → Fin (n+1)) Fin.succ x.S x.C x.D x.E x.F v.1 v.2
  have heq (v : FastSpace n) :
      (diagonal (fun a => (Sum.elim x.C x.D a)⁻¹) +
        (bindingFreeIncidence (Fin.castSucc : Fin n → Fin (n+1)) Fin.succ).transpose *
          diagonal (fun a => (Sum.elim x.S ![x.E, x.F] a)⁻¹) *
            bindingFreeIncidence (Fin.castSucc : Fin n → Fin (n+1)) Fin.succ) *ᵥ (fastBasis n).repr v =
        (fastBasis n).repr (fastAffinityLinear n x v) := by
    rw [hrepr]
    dsimp only at haction
    rw [haction]
    ext a
    cases a with
    | inl i =>
      simp [fastBasis_repr_inl, fastAffinityLinear, fastAffinityC,
        boundComplexAt, bindingLevelInventory]
    | inr i =>
      simp [fastBasis_repr_inr, fastAffinityLinear, fastAffinityD,
        boundComplexAt, bindingLevelInventory]
  ext i j
  let v := (fastBasis n).equivFun.symm (Pi.single j (1 : ℝ))
  have hv : ⇑((fastBasis n).repr v) = Pi.single j (1 : ℝ) := by
    simpa only [← Module.Basis.equivFun_apply] using
      (fastBasis n).equivFun.apply_symm_apply (Pi.single j (1 : ℝ))
  have hmatrix := congrArg (fun u => u i) (heq v)
  rw [← LinearMap.toMatrix_mulVec_repr (fastBasis n) (fastBasis n)
    (fastAffinityLinear n x) v] at hmatrix
  change _ = (fastAffinityMatrix n x *ᵥ (fastBasis n).repr v) i at hmatrix
  rw [hv, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hmatrix
  exact hmatrix.symm

/-- Exact physical affinity/inventory determinant relation, including
every free and bound concentration factor. -/
theorem source_fastAffinity_bindingMass_determinant {n : ℕ}
    (x : State n) (hx : x.Positive) :
    (fastAffinityMatrix n x).det *
        ((∏ j, x.S j) * x.E * x.F) * ((∏ i, x.C i) * ∏ i, x.D i) =
      totalE x * totalF x *
        (loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
          (totalE x) (totalF x)).det := by
  rw [source_fastAffinity_eq_complementary x hx]
  have hET : 0 < totalE x :=
    add_pos_of_pos_of_nonneg hx.2.1
      (Finset.sum_nonneg (fun i _ => (hx.2.2.2.1 i).le))
  have hFT : 0 < totalF x :=
    add_pos_of_pos_of_nonneg hx.2.2.1
      (Finset.sum_nonneg (fun i _ => (hx.2.2.2.2 i).le))
  have h := binding_affinity_inventory_determinant
    (Fin.castSucc : Fin n → Fin (n+1)) Fin.succ x.S x.C x.D x.E x.F
    (fun j => ne_of_gt (hx.1 j)) (fun i => ne_of_gt (hx.2.2.2.1 i))
    (fun i => ne_of_gt (hx.2.2.2.2 i)) (ne_of_gt hx.2.1) (ne_of_gt hx.2.2.1)
    (ne_of_gt hET) (ne_of_gt hFT)
  convert h using 1
  congr 2

theorem fastBindingMatrix_det_magnitude {n : ℕ} (x : State n)
    (ρ σ : Fin n → ℝ) :
    (fastBindingMatrix n x ρ σ).det =
      (∏ i, ρ i) * (∏ i, σ i) * (fastAffinityMatrix n x).det := by
  have hsign : (-1 : ℝ)^(n+n) = 1 := by
    rw [pow_add, ← mul_pow]
    simp
  rw [fastBindingMatrix_factorization, Matrix.det_neg, Matrix.det_mul,
    fastRateMatrix_eq_diagonal, Matrix.det_diagonal,
    Fintype.card_sum, Fintype.card_fin, hsign, one_mul]
  simp [fastRateWeights, Fintype.prod_sum_type]

/-- Eliminating all bound concentrations leaves exactly the two
enzyme totals and the manuscript's physical binding-rate product. -/
theorem source_fastBinding_bindingMass_determinant {n : ℕ}
    (k : Rates n) (x : State n) (hx : x.Positive) :
    (fastBindingMatrix n x
      (fun i => (k.b i + k.c i) * x.C i)
      (fun i => (k.beta i + k.gamma i) * x.D i)).det *
        ((∏ j, x.S j) * x.E * x.F) =
      ((∏ i : Fin n, (k.b i + k.c i)) * ∏ i : Fin n, (k.beta i + k.gamma i)) *
        (totalE x * totalF x *
          (loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
            (totalE x) (totalF x)).det) := by
  rw [fastBindingMatrix_det_magnitude, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib]
  calc
    _ = ((∏ i : Fin n, (k.b i + k.c i)) * ∏ i : Fin n, (k.beta i + k.gamma i)) *
        ((fastAffinityMatrix n x).det * ((∏ j, x.S j) * x.E * x.F) *
          ((∏ i, x.C i) * ∏ i, x.D i)) := by ring
    _ = _ := by rw [source_fastAffinity_bindingMass_determinant x hx]

end
end PhosphorylationStableCapacity
