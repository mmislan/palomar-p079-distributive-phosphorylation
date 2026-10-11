module
public import proofs.PhosphorylationStableCapacity.RatioSubstrateDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Explicit positive root of the substrate-total equation. This
formula avoids dividing by the enzyme-total pivot and is smooth
where the model coefficients and totals are positive. -/
def ratioSubstrateFormula (FT ST T K D : ℝ) : ℝ :=
  let B := T + FT*K - ST*D
  (Real.sqrt (B^2 + 4*T*D*ST) - B)/(2*T*D)

theorem ratioSubstrateFormula_pos_and_inventory
    (FT ST T K D : ℝ)
    (hST : 0 < ST) (hT : 0 < T) (hD : 0 < D) :
    0 < ratioSubstrateFormula FT ST T K D ∧
      ratioSubstrateInventory FT T K D
        (ratioSubstrateFormula FT ST T K D) = ST := by
  let A := T*D
  let B := T+FT*K-ST*D
  let disc := B^2+4*A*ST
  let q := Real.sqrt disc
  let s := ratioSubstrateFormula FT ST T K D
  have hA : 0 < A := mul_pos hT hD
  have hdisc : 0 < disc := by dsimp [disc]; positivity
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hqsq : q^2 = disc := Real.sq_sqrt hdisc.le
  have hnum : 0 < q-B := by
    dsimp [disc] at hqsq
    nlinarith
  have hsdef : s = (q-B)/(2*A) := by
    dsimp [s, ratioSubstrateFormula, q, disc, B, A]
    ring
  have hs : 0 < s := by rw [hsdef]; exact div_pos hnum (by positivity)
  have hlin : q = B+2*A*s := by
    rw [hsdef]
    have hne : 2*A ≠ 0 := ne_of_gt (by positivity)
    field_simp
    ring
  have hquad : A*s^2+B*s-ST=0 := by
    have hfact : 4*A*(A*s^2+B*s-ST)=0 := by
      calc
        4*A*(A*s^2+B*s-ST) = (B+2*A*s)^2-disc := by
          dsimp [disc]
          ring
        _ = 0 := by rw [←hlin, hqsq]; ring
    have hnonzero : 4*A ≠ 0 := ne_of_gt (by positivity)
    exact (mul_eq_zero.mp hfact).resolve_left hnonzero
  have hden : 1+D*s ≠ 0 := ne_of_gt (by nlinarith [mul_pos hD hs])
  have hvalue : ratioSubstrateInventory FT T K D s = ST := by
    dsimp [ratioSubstrateInventory]
    field_simp
    dsimp [A, B] at hquad
    nlinarith [hquad]
  exact ⟨hs, hvalue⟩

end
end PhosphorylationStableCapacity
