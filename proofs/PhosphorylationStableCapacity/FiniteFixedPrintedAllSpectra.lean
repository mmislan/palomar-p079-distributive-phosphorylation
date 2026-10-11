module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN2J0Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN2J1Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN2J2Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN3J0Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN3J1Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN3J2Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN3J3Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN3J4Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN4J0Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN4J1Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN4J2Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN4J3Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN4J4Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN4J5Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN4J6Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN5J0Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN5J1Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN5J2Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN5J3Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN5J4Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN5J5Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN5J6Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN5J7Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN5J8Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN6J0Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN6J1Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN6J2Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN6J3Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN6J4Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN6J5Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN6J6Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN6J7Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN6J8Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN6J9Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN6J10Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J0Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J1Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J2Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J3Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J4Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J5Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J6Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J7Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J8Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J9Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J10Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J11Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J12Spectrum
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedFamily
public import Mathlib.Tactic.FinCases
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

/-- Every literal printed state in the n=2 family has its claimed spectral type.
All endpoint lemmas use the same printed rate vector and class totals. -/
private theorem finiteFixedPrinted_spectra_n2
    (j : Fin 3) :
    if Even j.val then
      IsLinearlyStable (2*finiteFixedRadius 1) 2
        (2*(finiteFixedRadius 1+1)) (finiteFixedPrintedRates 1)
        (toCoordinateSpace (chart (finiteFixedPrintedState 1 j))) ∧
      IsLocallyAsymptoticallyStableClass (2*finiteFixedRadius 1) 2
        (2*(finiteFixedRadius 1+1)) (finiteFixedPrintedRates 1)
        (toCoordinateSpace (chart (finiteFixedPrintedState 1 j)))
    else
      IsOneUnstableSaddle (2*finiteFixedRadius 1) 2
        (2*(finiteFixedRadius 1+1)) (finiteFixedPrintedRates 1)
        (toCoordinateSpace (chart (finiteFixedPrintedState 1 j))) := by
  fin_cases j
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN2J0actual_linearlyStable
      uniformPilotN2J0actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN2J1actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN2J2actual_linearlyStable
      uniformPilotN2J2actual_nonlinearSink)

/-- Every literal printed state in the n=3 family has its claimed spectral type.
All endpoint lemmas use the same printed rate vector and class totals. -/
private theorem finiteFixedPrinted_spectra_n3
    (j : Fin 5) :
    if Even j.val then
      IsLinearlyStable (2*finiteFixedRadius 2) 2
        (2*(finiteFixedRadius 2+1)) (finiteFixedPrintedRates 2)
        (toCoordinateSpace (chart (finiteFixedPrintedState 2 j))) ∧
      IsLocallyAsymptoticallyStableClass (2*finiteFixedRadius 2) 2
        (2*(finiteFixedRadius 2+1)) (finiteFixedPrintedRates 2)
        (toCoordinateSpace (chart (finiteFixedPrintedState 2 j)))
    else
      IsOneUnstableSaddle (2*finiteFixedRadius 2) 2
        (2*(finiteFixedRadius 2+1)) (finiteFixedPrintedRates 2)
        (toCoordinateSpace (chart (finiteFixedPrintedState 2 j))) := by
  fin_cases j
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN3J0actual_linearlyStable
      uniformPilotN3J0actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN3J1actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN3J2actual_linearlyStable
      uniformPilotN3J2actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN3J3actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN3J4actual_linearlyStable
      uniformPilotN3J4actual_nonlinearSink)

/-- Every literal printed state in the n=4 family has its claimed spectral type.
All endpoint lemmas use the same printed rate vector and class totals. -/
private theorem finiteFixedPrinted_spectra_n4
    (j : Fin 7) :
    if Even j.val then
      IsLinearlyStable (2*finiteFixedRadius 3) 2
        (2*(finiteFixedRadius 3+1)) (finiteFixedPrintedRates 3)
        (toCoordinateSpace (chart (finiteFixedPrintedState 3 j))) ∧
      IsLocallyAsymptoticallyStableClass (2*finiteFixedRadius 3) 2
        (2*(finiteFixedRadius 3+1)) (finiteFixedPrintedRates 3)
        (toCoordinateSpace (chart (finiteFixedPrintedState 3 j)))
    else
      IsOneUnstableSaddle (2*finiteFixedRadius 3) 2
        (2*(finiteFixedRadius 3+1)) (finiteFixedPrintedRates 3)
        (toCoordinateSpace (chart (finiteFixedPrintedState 3 j))) := by
  fin_cases j
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN4J0actual_linearlyStable
      uniformPilotN4J0actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN4J1actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN4J2actual_linearlyStable
      uniformPilotN4J2actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN4J3actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN4J4actual_linearlyStable
      uniformPilotN4J4actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN4J5actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN4J6actual_linearlyStable
      uniformPilotN4J6actual_nonlinearSink)

/-- Every literal printed state in the n=5 family has its claimed spectral type.
All endpoint lemmas use the same printed rate vector and class totals. -/
private theorem finiteFixedPrinted_spectra_n5
    (j : Fin 9) :
    if Even j.val then
      IsLinearlyStable (2*finiteFixedRadius 4) 2
        (2*(finiteFixedRadius 4+1)) (finiteFixedPrintedRates 4)
        (toCoordinateSpace (chart (finiteFixedPrintedState 4 j))) ∧
      IsLocallyAsymptoticallyStableClass (2*finiteFixedRadius 4) 2
        (2*(finiteFixedRadius 4+1)) (finiteFixedPrintedRates 4)
        (toCoordinateSpace (chart (finiteFixedPrintedState 4 j)))
    else
      IsOneUnstableSaddle (2*finiteFixedRadius 4) 2
        (2*(finiteFixedRadius 4+1)) (finiteFixedPrintedRates 4)
        (toCoordinateSpace (chart (finiteFixedPrintedState 4 j))) := by
  fin_cases j
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN5J0actual_linearlyStable
      uniformPilotN5J0actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN5J1actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN5J2actual_linearlyStable
      uniformPilotN5J2actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN5J3actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN5J4actual_linearlyStable
      uniformPilotN5J4actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN5J5actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN5J6actual_linearlyStable
      uniformPilotN5J6actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN5J7actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN5J8actual_linearlyStable
      uniformPilotN5J8actual_nonlinearSink)

/-- Every literal printed state in the n=6 family has its claimed spectral type.
All endpoint lemmas use the same printed rate vector and class totals. -/
private theorem finiteFixedPrinted_spectra_n6
    (j : Fin 11) :
    if Even j.val then
      IsLinearlyStable (2*finiteFixedRadius 5) 2
        (2*(finiteFixedRadius 5+1)) (finiteFixedPrintedRates 5)
        (toCoordinateSpace (chart (finiteFixedPrintedState 5 j))) ∧
      IsLocallyAsymptoticallyStableClass (2*finiteFixedRadius 5) 2
        (2*(finiteFixedRadius 5+1)) (finiteFixedPrintedRates 5)
        (toCoordinateSpace (chart (finiteFixedPrintedState 5 j)))
    else
      IsOneUnstableSaddle (2*finiteFixedRadius 5) 2
        (2*(finiteFixedRadius 5+1)) (finiteFixedPrintedRates 5)
        (toCoordinateSpace (chart (finiteFixedPrintedState 5 j))) := by
  fin_cases j
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN6J0actual_linearlyStable
      uniformPilotN6J0actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN6J1actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN6J2actual_linearlyStable
      uniformPilotN6J2actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN6J3actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN6J4actual_linearlyStable
      uniformPilotN6J4actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN6J5actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN6J6actual_linearlyStable
      uniformPilotN6J6actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN6J7actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN6J8actual_linearlyStable
      uniformPilotN6J8actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN6J9actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN6J10actual_linearlyStable
      uniformPilotN6J10actual_nonlinearSink)

/-- Every literal printed state in the n=7 family has its claimed spectral type.
All endpoint lemmas use the same printed rate vector and class totals. -/
private theorem finiteFixedPrinted_spectra_n7
    (j : Fin 13) :
    if Even j.val then
      IsLinearlyStable (2*finiteFixedRadius 6) 2
        (2*(finiteFixedRadius 6+1)) (finiteFixedPrintedRates 6)
        (toCoordinateSpace (chart (finiteFixedPrintedState 6 j))) ∧
      IsLocallyAsymptoticallyStableClass (2*finiteFixedRadius 6) 2
        (2*(finiteFixedRadius 6+1)) (finiteFixedPrintedRates 6)
        (toCoordinateSpace (chart (finiteFixedPrintedState 6 j)))
    else
      IsOneUnstableSaddle (2*finiteFixedRadius 6) 2
        (2*(finiteFixedRadius 6+1)) (finiteFixedPrintedRates 6)
        (toCoordinateSpace (chart (finiteFixedPrintedState 6 j))) := by
  fin_cases j
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN7J0actual_linearlyStable
      uniformPilotN7J0actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN7J1actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN7J2actual_linearlyStable
      uniformPilotN7J2actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN7J3actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN7J4actual_linearlyStable
      uniformPilotN7J4actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN7J5actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN7J6actual_linearlyStable
      uniformPilotN7J6actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN7J7actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN7J8actual_linearlyStable
      uniformPilotN7J8actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN7J9actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN7J10actual_linearlyStable
      uniformPilotN7J10actual_nonlinearSink)
  · norm_num [finiteFixedRadius]
    exact
      uniformPilotN7J11actual_oneUnstableSaddle
  · norm_num [finiteFixedRadius]
    exact (And.intro
      uniformPilotN7J12actual_linearlyStable
      uniformPilotN7J12actual_nonlinearSink)

/-- Complete printed finite table spectral classification, with the class
Jacobian and nonlinear sink property on each literal common-family witness. -/
theorem finiteFixedPrinted_all_spectra
    (m : ℕ) (hm : 1 ≤ m) (hm6 : m ≤ 6)
    (j : Fin (2*m+1)) :
    if Even j.val then
      IsLinearlyStable (2*finiteFixedRadius m) 2
        (2*(finiteFixedRadius m+1)) (finiteFixedPrintedRates m)
        (toCoordinateSpace (chart (finiteFixedPrintedState m j))) ∧
      IsLocallyAsymptoticallyStableClass (2*finiteFixedRadius m) 2
        (2*(finiteFixedRadius m+1)) (finiteFixedPrintedRates m)
        (toCoordinateSpace (chart (finiteFixedPrintedState m j)))
    else
      IsOneUnstableSaddle (2*finiteFixedRadius m) 2
        (2*(finiteFixedRadius m+1)) (finiteFixedPrintedRates m)
        (toCoordinateSpace (chart (finiteFixedPrintedState m j))) := by
  have hcases : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 := by omega
  rcases hcases with h | h | h | h | h | h
  · subst m
    exact finiteFixedPrinted_spectra_n2 j
  · subst m
    exact finiteFixedPrinted_spectra_n3 j
  · subst m
    exact finiteFixedPrinted_spectra_n4 j
  · subst m
    exact finiteFixedPrinted_spectra_n5 j
  · subst m
    exact finiteFixedPrinted_spectra_n6 j
  · subst m
    exact finiteFixedPrinted_spectra_n7 j

end
end PhosphorylationStableCapacity

