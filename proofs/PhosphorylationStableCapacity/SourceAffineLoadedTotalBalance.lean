module
public import proofs.PhosphorylationStableCapacity.SourceAffineEnzymeBalance

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Matrix

private theorem balanced_complex_total (E C T U v : ℝ)
    (hT : T = E + C) (hT0 : T ≠ 0) (hbal : T*v + U = 0) :
    U + C*v = U*E/T := by
  apply (eq_div_iff hT0).2
  linear_combination C*hbal + U*hT

/-- Under the two fixed-enzyme-total tangent balances, the literal
species-total derivative equals the loaded binding-mass total-row
action on the free-substrate logarithmic tangent. -/
theorem source_affine_species_total_eq_loaded_action {n : ℕ}
    (x : State n) (hx : x.Positive) (a b z : ℝ)
    (hE : totalE x * (b + z) +
      ∑ i : Fin n, x.C i * sourceAffineLogTangent a b i.castSucc = 0)
    (hF : totalF x * z +
      ∑ i : Fin n, x.D i * sourceAffineLogTangent a b i.succ = 0) :
    (∑ j : Fin (n+1), x.S j * sourceAffineLogTangent a b j) +
      (∑ i : Fin n, x.C i *
        (sourceAffineLogTangent a b i.succ + z)) +
      (∑ i : Fin n, x.D i *
        (sourceAffineLogTangent a b i.succ + z)) =
    sourceAugmentedTotalRow x ⬝ᵥ sourceAffineLogTangent a b := by
  let σ : Fin (n+1) → ℝ := sourceAffineLogTangent a b
  let CU := ∑ i : Fin n, x.C i * σ i.castSucc
  let DU := ∑ i : Fin n, x.D i * σ i.succ
  let CS := ∑ i : Fin n, x.C i
  let DS := ∑ i : Fin n, x.D i
  have hET : totalE x = x.E + CS := rfl
  have hFT : totalF x = x.F + DS := rfl
  have hET0 : totalE x ≠ 0 := by
    apply ne_of_gt
    rw [hET]
    exact add_pos_of_pos_of_nonneg hx.2.1
      (Finset.sum_nonneg fun i _ => (hx.2.2.2.1 i).le)
  have hFT0 : totalF x ≠ 0 := by
    apply ne_of_gt
    rw [hFT]
    exact add_pos_of_pos_of_nonneg hx.2.2.1
      (Finset.sum_nonneg fun i _ => (hx.2.2.2.2 i).le)
  have hCbal : CU + CS*(b+z) = CU*x.E/totalE x := by
    exact balanced_complex_total x.E CS (totalE x) CU (b+z)
      hET hET0 hE
  have hDbal : DU + DS*z = DU*x.F/totalF x := by
    exact balanced_complex_total x.F DS (totalF x) DU z
      hFT hFT0 hF
  have hshift (i : Fin n) : σ i.succ = σ i.castSucc + b := by
    simp [σ, sourceAffineLogTangent]
    ring
  have hCvar :
      (∑ i : Fin n, x.C i * (σ i.succ + z)) = CU + CS*(b+z) := by
    simp_rw [hshift]
    simp only [← add_assoc, mul_add, Finset.sum_add_distrib,
      ← Finset.sum_mul]
    dsimp [CU, CS]
  have hDvar :
      (∑ i : Fin n, x.D i * (σ i.succ + z)) = DU + DS*z := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    rfl
  have hrow (j : Fin (n+1)) :
      sourceAugmentedTotalRow x j =
        x.S j + sourceLevelC x j * x.E / totalE x +
          sourceLevelD x j * x.F / totalF x := by
    simpa [sourceAugmentedTotalRow, totalAndLevelOutputMatrix,
      Matrix.mul_apply] using
      loadedBindingMass_column_sum_general x.S (sourceLevelC x)
        (sourceLevelD x) (totalE x) (totalF x) x.E x.F
        (by simp [totalE, sourceLevelC_sum])
        (by simp [totalF, sourceLevelD_sum]) hET0 hFT0 j
  have hloaded : sourceAugmentedTotalRow x ⬝ᵥ σ =
      (∑ j : Fin (n+1), x.S j * σ j) +
        CU*x.E/totalE x + DU*x.F/totalF x := by
    simp only [dotProduct]
    simp_rw [hrow]
    simp only [add_mul, Finset.sum_add_distrib]
    have hcw :
        (∑ j : Fin (n+1), sourceLevelC x j * x.E / totalE x * σ j) =
          CU*x.E/totalE x := by
      calc
        _ = (∑ j : Fin (n+1), sourceLevelC x j * σ j) *
            (x.E / totalE x) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = _ := by rw [sourceLevelC_weighted_sum]; dsimp [CU]; ring
    have hdw :
        (∑ j : Fin (n+1), sourceLevelD x j * x.F / totalF x * σ j) =
          DU*x.F/totalF x := by
      calc
        _ = (∑ j : Fin (n+1), sourceLevelD x j * σ j) *
            (x.F / totalF x) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = _ := by rw [sourceLevelD_weighted_sum]; dsimp [DU]; ring
    rw [hcw, hdw]
  change (∑ j, x.S j * σ j) +
    (∑ i, x.C i * (σ i.succ + z)) +
    (∑ i, x.D i * (σ i.succ + z)) =
      sourceAugmentedTotalRow x ⬝ᵥ σ
  rw [hCvar, hDvar, hCbal, hDbal, hloaded]

end
end PhosphorylationStableCapacity
