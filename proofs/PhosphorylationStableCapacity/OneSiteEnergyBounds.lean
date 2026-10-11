module
public import proofs.PhosphorylationStableCapacity.OneSiteEnergyAlongCurve

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Exact coercivity and upper bound for the rational quadratic
one-site energy in Euclidean squared coordinates. The lower bound is
a sum-of-squares certificate for `P-(1/100)I`. -/
theorem oneSiteEnergyPoly_bounds (a b c : ℝ) :
    (a^2+b^2+c^2)/100 ≤ oneSiteEnergyPoly a b c ∧
      oneSiteEnergyPoly a b c ≤ 3*(a^2+b^2+c^2) := by
  have hSOS : oneSiteEnergyPoly a b c - (a^2+b^2+c^2)/100 =
      (321/400 : ℝ) * (a+(1000/5457)*b+(3125/5457)*c)^2 +
      (578953/4638450 : ℝ) * (b+(12775/4631624)*c)^2 +
      (318065679/1852649600 : ℝ) * c^2 := by
    unfold oneSiteEnergyPoly
    ring
  have hLower : (a^2+b^2+c^2)/100 ≤
      oneSiteEnergyPoly a b c := by
    rw [← sub_nonneg]
    rw [hSOS]
    positivity
  have hab : 2*a*b ≤ a^2+b^2 := by
    nlinarith only [sq_nonneg (a-b)]
  have hac : 2*a*c ≤ a^2+c^2 := by
    nlinarith only [sq_nonneg (a-c)]
  have hbc : 2*b*c ≤ b^2+c^2 := by
    nlinarith only [sq_nonneg (b-c)]
  refine ⟨hLower, ?_⟩
  unfold oneSiteEnergyPoly
  linarith only [hab, hac, hbc,
    sq_nonneg a, sq_nonneg b, sq_nonneg c]

end
end PhosphorylationStableCapacity
