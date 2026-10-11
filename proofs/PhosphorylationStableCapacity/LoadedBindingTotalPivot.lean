module
public import proofs.PhosphorylationStableCapacity.LoadedBindingMassDerivativeSource

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The total-inventory derivative along a logarithmic variation of one
free substrate has a positive formula in physical coordinates. -/
theorem loadedBindingMass_column_sum_general {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (S C Y : ι → ℝ) (ET FT E F : ℝ)
    (hET : ET = E + ∑ i, C i)
    (hFT : FT = F + ∑ i, Y i)
    (hET0 : ET ≠ 0) (hFT0 : FT ≠ 0) (j : ι) :
    (∑ i, loadedBindingMass S C Y ET FT i j) =
      S j + C j * E / ET + Y j * F / FT := by
  have hdiag :
      (∑ i, if i = j then S i + C i + Y i else 0) =
        S j + C j + Y j := by simp
  simp only [loadedBindingMass, Finset.sum_sub_distrib]
  rw [hdiag]
  have hC :
      (∑ i, C i * C j / ET) = (∑ i, C i) * C j / ET := by
    rw [← Finset.sum_div, ← Finset.sum_mul]
  have hY :
      (∑ i, Y i * Y j / FT) = (∑ i, Y i) * Y j / FT := by
    rw [← Finset.sum_div, ← Finset.sum_mul]
  have hET' : E + ∑ i, C i ≠ 0 := by
    rw [← hET]
    exact hET0
  have hFT' : F + ∑ i, Y i ≠ 0 := by
    rw [← hFT]
    exact hFT0
  rw [hC, hY, hET, hFT]
  field_simp [hET', hFT']
  ring

/-- Total loaded-inventory variation is the weighted sum of logarithmic
substrate variations, with the physical free-enzyme shares. -/
theorem loadedBindingMass_total_action_general {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (S C Y σ : ι → ℝ) (ET FT E F : ℝ)
    (hET : ET = E + ∑ i, C i)
    (hFT : FT = F + ∑ i, Y i)
    (hET0 : ET ≠ 0) (hFT0 : FT ≠ 0) :
    (∑ i, (loadedBindingMass S C Y ET FT).mulVec σ i) =
      ∑ j, (S j + C j * E / ET + Y j * F / FT) * σ j := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  simp_rw [loadedBindingMass_column_sum_general S C Y ET FT E F
    hET hFT hET0 hFT0]

/-- The first total-inventory pivot is strictly positive at every
positive literal state, for each possible pivot substrate. -/
theorem source_loadedBindingMass_column_sum_pos {n : ℕ}
    (x : State n) (hx : x.Positive) (j : Fin (n+1)) :
    0 < ∑ i, loadedBindingMass x.S (sourceLevelC x)
      (sourceLevelD x) (totalE x) (totalF x) i j := by
  have hET : 0 < totalE x := by
    simp [totalE]
    exact add_pos_of_pos_of_nonneg hx.2.1
      (Finset.sum_nonneg fun i _ => (hx.2.2.2.1 i).le)
  have hFT : 0 < totalF x := by
    simp [totalF]
    exact add_pos_of_pos_of_nonneg hx.2.2.1
      (Finset.sum_nonneg fun i _ => (hx.2.2.2.2 i).le)
  rw [loadedBindingMass_column_sum_general x.S (sourceLevelC x)
    (sourceLevelD x) (totalE x) (totalF x) x.E x.F
    (by simp [totalE, sourceLevelC_sum])
    (by simp [totalF, sourceLevelD_sum])
    (ne_of_gt hET) (ne_of_gt hFT)]
  have hC : 0 ≤ sourceLevelC x j :=
    sourceLevelC_nonneg x (fun i => (hx.2.2.2.1 i).le) j
  have hY : 0 ≤ sourceLevelD x j :=
    sourceLevelD_nonneg x (fun i => (hx.2.2.2.2 i).le) j
  have hpC : 0 ≤ sourceLevelC x j * x.E / totalE x :=
    div_nonneg (mul_nonneg hC hx.2.1.le) hET.le
  have hpY : 0 ≤ sourceLevelD x j * x.F / totalF x :=
    div_nonneg (mul_nonneg hY hx.2.2.1.le) hFT.le
  linarith [hx.1 j]

/-- At a positive literal equilibrium, the derivative of total binding
inventory has the physical positive weights for every logarithmic
substrate direction. -/
theorem equilibrium_source_total_binding_inventory_hasDerivAt_kinetic
    {n : ℕ} (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) (σ : Fin (n+1) → ℝ) :
    HasDerivAt (fun t : ℝ =>
      ∑ i, bindingLoadedLevel (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k)
        (bindingLinearPath x.S σ t) i)
      (∑ j, (x.S j + sourceLevelC x j * x.E / totalE x +
        sourceLevelD x j * x.F / totalF x) * σ j) 0 := by
  have hsum : HasDerivAt (fun t : ℝ =>
      ∑ i, bindingLoadedLevel (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k)
        (bindingLinearPath x.S σ t) i)
      (∑ i, (loadedBindingMass x.S (sourceLevelC x)
        (sourceLevelD x) (totalE x) (totalF x)).mulVec σ i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    exact equilibrium_source_loadedBindingMass_hasDerivAt_kinetic
      k x hk hx heq σ i
  have hET : 0 < totalE x := by
    simp [totalE]
    exact add_pos_of_pos_of_nonneg hx.2.1
      (Finset.sum_nonneg fun i _ => (hx.2.2.2.1 i).le)
  have hFT : 0 < totalF x := by
    simp [totalF]
    exact add_pos_of_pos_of_nonneg hx.2.2.1
      (Finset.sum_nonneg fun i _ => (hx.2.2.2.2 i).le)
  rw [loadedBindingMass_total_action_general x.S (sourceLevelC x)
    (sourceLevelD x) σ (totalE x) (totalF x) x.E x.F
    (by simp [totalE, sourceLevelC_sum])
    (by simp [totalF, sourceLevelD_sum])
    (ne_of_gt hET) (ne_of_gt hFT)] at hsum
  exact hsum

/-- At a positive literal state, total inventory together with levels
`1,...,n` are locally independent binding coordinates. This is the
linear kernel statement behind the constrained chart. -/
theorem source_loadedBindingMass_total_and_levels_kernel {n : ℕ}
    (x : State n) (hx : x.Positive)
    (σ : Fin (n+1) → ℝ)
    (htotal : ∑ j, (loadedBindingMass x.S (sourceLevelC x)
      (sourceLevelD x) (totalE x) (totalF x)).mulVec σ j = 0)
    (hlevels : ∀ i : Fin n,
      (loadedBindingMass x.S (sourceLevelC x)
        (sourceLevelD x) (totalE x) (totalF x)).mulVec σ i.succ = 0) :
    σ = 0 := by
  let M := loadedBindingMass x.S (sourceLevelC x)
    (sourceLevelD x) (totalE x) (totalF x)
  have htotal' : ∑ j, M.mulVec σ j = 0 := htotal
  rw [Fin.sum_univ_succ] at htotal'
  have htail : (∑ i : Fin n, M.mulVec σ i.succ) = 0 :=
    Finset.sum_eq_zero (fun i _ => hlevels i)
  rw [htail, add_zero] at htotal'
  have hzero : M.mulVec σ = 0 := by
    funext j
    cases j using Fin.cases with
    | zero => exact htotal'
    | succ i => exact hlevels i
  exact Matrix.eq_zero_of_mulVec_eq_zero
    (ne_of_gt (source_loadedBindingMass_det_pos x hx)) hzero

end
end PhosphorylationStableCapacity
