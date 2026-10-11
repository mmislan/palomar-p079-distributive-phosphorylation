module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J5Data
public import proofs.PhosphorylationStableCapacity.FiniteUniformSmallGainCertificate
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Kernel integer arithmetic checks this proposed similarity and every
small-gain bound. The numerical basis producer supplies no evidence. -/
def uniformPilotN7J5Certificate : UniformSmallGainCertificate 20 where
  A := uniformPilotN7J5A
  T := uniformPilotN7J5T
  U := uniformPilotN7J5U
  B := uniformPilotN7J5B
  positiveA := by decide +kernel
  positiveT := by decide +kernel
  positiveU := by decide +kernel
  positiveB := by decide +kernel
  inverse := by decide +kernel
  intertwine := by decide +kernel
  row i := by fin_cases i <;> decide +kernel
  column i := by fin_cases i <;> decide +kernel
  feedback := by decide +kernel

end
end PhosphorylationStableCapacity
