module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN6J1Data
public import proofs.PhosphorylationStableCapacity.FiniteUniformSmallGainCertificate
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Kernel integer arithmetic checks this proposed similarity and every
small-gain bound. The numerical basis producer supplies no evidence. -/
def uniformPilotN6J1Certificate : UniformSmallGainCertificate 17 where
  A := uniformPilotN6J1A
  T := uniformPilotN6J1T
  U := uniformPilotN6J1U
  B := uniformPilotN6J1B
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
