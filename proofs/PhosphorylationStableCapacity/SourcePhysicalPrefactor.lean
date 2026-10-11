module
public import proofs.PhosphorylationStableCapacity.SourceBindingDeterminantMagnitude
public import proofs.PhosphorylationStableCapacity.GeneralEquilibriumRatios
public import proofs.PhosphorylationStableCapacity.SourceAugmentedRankOne
public import proofs.PhosphorylationStableCapacity.LoadedJacobianBlockMatrix
public import proofs.PhosphorylationStableCapacity.LoadedStateChartBridge

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Matrix
open scoped BigOperators

theorem source_bindingMass_eq_pivot_constrained {n : ℕ}
    (k : Rates n) (x : State n) (hx : x.Positive) :
    (loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
      (totalE x) (totalF x)).det =
        sourceAugmentedCurrentMatrix k x 0 0 *
          (sourceConstrainedBindingMass x).det := by
  let A := totalAndLevelOutputMatrix n *
    loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
      (totalE x) (totalF x)
  have hp : A 0 0 ≠ 0 :=
    ne_of_gt (sourceAugmentedCurrentMatrix_pivot_pos k x hx)
  have h := det_eq_first_pivot_mul_schur A hp
  simpa only [A, Matrix.det_mul, totalAndLevelOutputMatrix_det, one_mul,
    sourceAugmentedCurrentMatrix_zero, sourceConstrainedBindingMass] using h

/-- The literal fast determinant and catalytic row product cancel all bound
concentrations. This is valid at every positive equilibrium. -/
theorem equilibrium_fast_binding_physical_prefactor {n : ℕ}
    (k : Rates n) (x : State n) (hx : x.Positive)
    (heq : Equilibrium k x) :
    (fastBindingMatrix n x
      (fun i => k.a i * x.S i.castSucc * x.E)
      (fun i => k.alpha i * x.S i.succ * x.F)).det *
      (∏ i : Fin (n+1), sourceAugmentedRowWeight k x i) *
        (x.S 0 * x.E * x.F) =
    totalE x * totalF x * x.F^n *
      (loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
        (totalE x) (totalF x)).det *
          (∏ i : Fin n, (k.b i + k.c i) * k.alpha i * k.gamma i) := by
  have hC : (fun i => k.a i * x.S i.castSucc * x.E) =
      (fun i => (k.b i + k.c i) * x.C i) := by
    funext i
    exact (equilibrium_complex_balances k x heq i).1
  have hD : (fun i => k.alpha i * x.S i.succ * x.F) =
      (fun i => (k.beta i + k.gamma i) * x.D i) := by
    funext i
    exact (equilibrium_complex_balances k x heq i).2
  have hflux (i : Fin n) :
      (k.beta i + k.gamma i) * (k.c i * x.C i) =
        k.alpha i * k.gamma i * x.S i.succ * x.F := by
    rw [equilibrium_catalytic_balance k x heq i]
    have hi := (equilibrium_complex_balances k x heq i).2
    calc
      _ = k.gamma i * ((k.beta i + k.gamma i) * x.D i) := by ring
      _ = k.gamma i * (k.alpha i * x.S i.succ * x.F) := by rw [← hi]
      _ = _ := by ring
  have hprod :
      (∏ i : Fin n, (k.beta i + k.gamma i)) * (∏ i : Fin n, k.c i * x.C i) =
      (∏ i : Fin n, k.alpha i * k.gamma i) *
        (∏ i : Fin n, x.S i.succ) * x.F^n := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [hflux]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hbase := source_fastBinding_bindingMass_determinant k x hx
  rw [hC, hD]
  rw [Fin.prod_univ_succ]
  simp only [sourceAugmentedRowWeight, Fin.cases_zero, Fin.cases_succ, one_mul]
  have hs : (∏ j : Fin (n+1), x.S j) = x.S 0 * ∏ i : Fin n, x.S i.succ :=
    Fin.prod_univ_succ x.S
  have hS : (∏ i : Fin n, x.S i.succ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => ne_of_gt (hx.1 i.succ))
  apply mul_right_cancel₀ hS
  calc
    _ = ((fastBindingMatrix n x
        (fun i => (k.b i + k.c i) * x.C i)
        (fun i => (k.beta i + k.gamma i) * x.D i)).det *
          ((∏ j : Fin (n+1), x.S j) * x.E * x.F)) *
            (∏ i : Fin n, k.c i * x.C i) := by rw [hs]; ring
    _ = _ := by
      rw [hbase]
      simp_rw [show ∀ i : Fin n, (k.b i + k.c i) * k.alpha i * k.gamma i =
        (k.b i + k.c i) * (k.alpha i * k.gamma i) from fun i => by ring]
      have hrates : (∏ i : Fin n, (k.b i + k.c i) * (k.alpha i * k.gamma i)) =
          (∏ i : Fin n, (k.b i + k.c i)) * (∏ i : Fin n, k.alpha i * k.gamma i) :=
        Finset.prod_mul_distrib
      rw [hrates]
      calc
        _ = totalE x * totalF x *
            (loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
              (totalE x) (totalF x)).det * (∏ i : Fin n, (k.b i + k.c i)) *
                ((∏ i : Fin n, (k.beta i + k.gamma i)) *
                  (∏ i : Fin n, k.c i * x.C i)) := by ring
        _ = _ := by rw [hprod]; ring

theorem equilibrium_loaded_fast_physical_prefactor {n : ℕ}
    (k : Rates n) (x : State n) (hx : x.Positive)
    (heq : Equilibrium k x) :
    let D := LinearMap.toMatrix (fastBasis n) (fastBasis n)
      (loadedBlockD (totalE x) (totalF x) (totalS x) k
        (loadedCoordOfState x)).toLinearMap
    D.det * (∏ i : Fin (n+1), sourceAugmentedRowWeight k x i) *
      (x.S 0 * x.E * x.F) =
    totalE x * totalF x * x.F^n *
      (sourceConstrainedBindingMass x).det *
        sourceAugmentedCurrentMatrix k x 0 0 *
          (∏ i : Fin n, (k.b i + k.c i) * k.alpha i * k.gamma i) := by
  dsimp only
  have hback : stateFromLoaded (totalE x) (totalF x) (totalS x)
      (loadedCoordOfState x) = x :=
    stateFromLoaded_loadedCoordOfState _ _ _ x ⟨rfl, rfl, rfl⟩
  have hD := loadedBlockD_toMatrix_eq_fastBinding
    (totalE x) (totalF x) (totalS x) k (loadedCoordOfState x)
    (show (stateFromLoaded (totalE x) (totalF x) (totalS x)
      (loadedCoordOfState x)).Positive from hback.symm ▸ hx)
    (show Equilibrium k (stateFromLoaded (totalE x) (totalF x) (totalS x)
      (loadedCoordOfState x)) from hback.symm ▸ heq)
  rw [hback] at hD
  rw [hD]
  rw [equilibrium_fast_binding_physical_prefactor k x hx heq,
    source_bindingMass_eq_pivot_constrained k x hx]
  ring

/-- The prefactor quotient contains no derivatives or bound concentrations. -/
theorem equilibrium_loaded_fast_prefactor_quotient {n : ℕ}
    (k : Rates n) (x : State n) (hx : x.Positive)
    (heq : Equilibrium k x) :
    let D := LinearMap.toMatrix (fastBasis n) (fastBasis n)
      (loadedBlockD (totalE x) (totalF x) (totalS x) k
        (loadedCoordOfState x)).toLinearMap
    D.det * (∏ i : Fin (n+1), sourceAugmentedRowWeight k x i) /
      ((sourceConstrainedBindingMass x).det * sourceAugmentedCurrentMatrix k x 0 0) =
    totalE x * totalF x * x.F^n /
      (x.S 0 * x.E * x.F) *
        (∏ i : Fin n, (k.b i + k.c i) * k.alpha i * k.gamma i) := by
  dsimp only
  have h := equilibrium_loaded_fast_physical_prefactor k x hx heq
  dsimp only at h
  have hm := ne_of_gt (sourceConstrainedBindingMass_det_pos x hx)
  have hp := ne_of_gt (sourceAugmentedCurrentMatrix_pivot_pos k x hx)
  have hs := ne_of_gt (hx.1 0)
  have he := ne_of_gt hx.2.1
  have hf := ne_of_gt hx.2.2.1
  apply (div_eq_iff (mul_ne_zero hm hp)).mpr
  apply (mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hs he) hf))
  calc
    _ = totalE x * totalF x * x.F^n *
        (sourceConstrainedBindingMass x).det *
          sourceAugmentedCurrentMatrix k x 0 0 *
            (∏ i : Fin n, (k.b i + k.c i) * k.alpha i * k.gamma i) := h
    _ = _ := by field_simp [hs, he, hf]

end
end PhosphorylationStableCapacity
