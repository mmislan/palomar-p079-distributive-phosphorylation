module
public import proofs.PhosphorylationStableCapacity.CoalescedPhysicalPrefactor
public import proofs.PhosphorylationStableCapacity.CoalescedSourceSubstrateLimit

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- At the coalesced source, the unnormalized polynomial inventories
satisfy `B_raw(1)=(2r−1)D_raw(1)`. The manuscript subsequently divides
both by the constant coefficient `D_raw(0)`. -/
theorem coalesced_raw_inventory_difference_eval_one
    (m : ℕ) (r : ℝ) :
    (coalescedRawB m r).eval 1 - (coalescedRawD m r).eval 1 =
      2*(r-1)*(coalescedRawD m r).eval 1 := by
  let p := (coalescedPair m).1
  let q := (coalescedPair m).2
  have hpq : p.eval 1 = q.eval 1 := by
    simpa only [p, q] using
      (coalescedPair_eval_one m).1.trans
        (coalescedPair_eval_one m).2.symm
  have hquot : (1-r)*(quotient p q r).eval 1 =
      q.eval r*p.eval 1-r*p.eval r*q.eval 1 := by
    have h := congrArg (fun P : ℝ[X] => P.eval 1)
      (quotient_identity p q r)
    simpa [conversionNumerator] using h
  have hD : (rawD p q r).eval 1 =
      4*(quotient p q r).eval 1 := by
    simp [rawD]
  have hB : (rawB p q r).eval 1 =
      r*(rawD p q r).eval 1+
        4*(r*p.eval r-q.eval r)*p.eval 1 := by
    simp [rawB, hpq]
    ring
  change (rawB p q r).eval 1 - (rawD p q r).eval 1 =
    2*(r-1)*(rawD p q r).eval 1
  rw [hB, hD]
  rw [hpq] at hquot
  rw [hpq]
  linear_combination 4*hquot

/-- The first free substrate is `D_raw(0)/D_raw(1)`, because the
reconstruction has unnormalized first weight `T₀=D_raw(0)`. -/
theorem coalesced_first_free_substrate_eq_raw_ratio
    (m : ℕ) (r : ℝ) :
    (coalescedFiniteState m r).S 0 =
      (coalescedRawD m r).coeff 0 /
        (coalescedRawD m r).eval 1 := by
  have h := coalescedFiniteState_S_eq m r (0 : Fin (m+2))
  simpa only [Fin.val_zero, ite_true, add_zero,
    finiteD, coalescedRawD] using h

/-- The kinetic inventory factor used by the physical determinant is
exactly the manuscript's *normalized* `M(1)=B(1)-D(1)`, where
`B=B_raw/D_raw(0)` and `D=D_raw/D_raw(0)`. -/
theorem coalesced_inventory_difference_eq_published_M_one
    (m : ℕ) (r : ℝ) (k : Rates (m+1))
    (_hr : 1 < r)
    (hD : DensePositive (coalescedRawD m r) m)
    (hk : k.Positive)
    (hx : (coalescedFiniteState m r).Positive)
    (heq : Equilibrium k (coalescedFiniteState m r))
    (hET : totalE (coalescedFiniteState m r) = 2*r)
    (hFT : totalF (coalescedFiniteState m r) = 2) :
    kinaseComplexInventory k 1 - phosphataseComplexInventory k 1 =
      ((coalescedRawB m r).eval 1 -
        (coalescedRawD m r).eval 1) /
        (coalescedRawD m r).coeff 0 := by
  let x := coalescedFiniteState m r
  let d := coalescedRawD m r
  let M := kinaseComplexInventory k 1-phosphataseComplexInventory k 1
  have hEF := coalescedFiniteState_EF m r
  have hM : x.S 0*M = 2*(r-1) :=
    equilibrium_unit_enzymes_inventory_difference k x r hk hx heq
      hEF.1 hEF.2 hET hFT
  have hs : x.S 0 = d.coeff 0/d.eval 1 :=
    coalesced_first_free_substrate_eq_raw_ratio m r
  have hd0 : d.coeff 0 ≠ 0 :=
    ne_of_gt (hD.1 0 (by omega))
  have hd1 : d.eval 1 ≠ 0 :=
    ne_of_gt (hD.eval_pos (by norm_num))
  have hraw := coalesced_raw_inventory_difference_eval_one m r
  change M = ((coalescedRawB m r).eval 1-d.eval 1)/d.coeff 0
  rw [hraw]
  rw [hs] at hM
  field_simp [hd0, hd1] at hM ⊢
  nlinarith [hM]

end
end PhosphorylationStableCapacity
