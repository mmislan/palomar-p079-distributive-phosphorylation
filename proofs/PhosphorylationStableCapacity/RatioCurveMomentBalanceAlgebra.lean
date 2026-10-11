module
public import proofs.PhosphorylationStableCapacity.SourceTotalRowMoments

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Algebraic elimination of the common free-phosphatase log slope
from the exact kinase, phosphatase and substrate inventory balances. -/
theorem total_log_balances_imply_moment_identities
    (E F C D ET FT SS SC SD b u dET : ℝ)
    (hET : ET = E+C) (hFT : FT = F+D)
    (hET0 : ET ≠ 0) (hFT0 : FT ≠ 0)
    (hkinase : u*dET = E*(1+b)+SC+(b+1)*C)
    (hphosphatase : F*b+SD+b*D=0)
    (hsubstrate : SS+SC+(b+1)*C+SD+b*D=0) :
    ET*(1-(SD/FT-SC/ET)) = u*dET ∧
    ET*(SS+E/ET*SC+F/FT*SD)+C*u*dET=0 := by
  have hp : SD = -FT*b := by rw [hFT]; linarith [hphosphatase]
  have hpdiv : SD/FT = -b := by
    rw [hp]
    field_simp [hFT0]
  have hk : u*dET = ET*(1+b)+SC := by
    rw [hET]
    linarith [hkinase]
  have hbase : SS+SC+C*(1+b)-F*b=0 := by
    linarith [hsubstrate, hphosphatase]
  have hFterm : F/FT*SD = -F*b := by
    calc
      F/FT*SD = F*(SD/FT) := by ring
      _ = -F*b := by rw [hpdiv]; ring
  have hEterm : ET*(E/ET*SC)=E*SC := by
    field_simp [hET0]
  constructor
  · rw [hpdiv]
    calc
      ET*(1-(-b-SC/ET)) = ET*(1+b)+SC := by
        field_simp [hET0]
        ring
      _ = u*dET := hk.symm
  · calc
      ET*(SS+E/ET*SC+F/FT*SD)+C*u*dET =
          ET*SS+E*SC-ET*F*b+C*u*dET := by
            rw [hFterm]
            linear_combination hEterm
      _ = ET*(SS+SC+C*(1+b)-F*b) +
          C*(u*dET-ET*(1+b)-SC) := by
            rw [hET]
            ring
      _ = 0 := by rw [hbase, hk]; ring

end
end PhosphorylationStableCapacity
