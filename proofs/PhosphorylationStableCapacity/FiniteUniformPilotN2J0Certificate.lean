module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN2J0Data
public import proofs.PhosphorylationStableCapacity.FiniteUniformSmallGainCertificate
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Trusted integer checks of one exact similarity and its uniform row margins. -/
def uniformPilotN2J0Certificate : UniformSmallGainCertificate 5 where
  A := uniformPilotN2J0A
  T := uniformPilotN2J0T
  U := uniformPilotN2J0U
  B := uniformPilotN2J0B
  positiveA := by decide
  positiveT := by decide
  positiveU := by decide
  positiveB := by decide
  inverse := by decide +kernel
  intertwine := by decide +kernel
  row := by intro i; fin_cases i <;> decide +kernel
  column := by intro i; fin_cases i <;> decide +kernel
  feedback := by decide +kernel

end
end PhosphorylationStableCapacity
