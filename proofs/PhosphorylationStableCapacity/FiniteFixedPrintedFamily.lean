module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitSource
public import proofs.PhosphorylationStableCapacity.CoalescedFiniteSource
public import proofs.PhosphorylationStableCapacity.KineticFreedom

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Proposition 9.1's six fixed parameter choices are indexed by `m=n-1`.
The intended range is `1 ≤ m ≤ 6`, corresponding to `2 ≤ n ≤ 7`. -/
def finiteFixedRadius (m : ℕ) : ℝ :=
  if m = 1 then 2 else if m ≤ 3 then 4 else 8

def finiteFixedSpacing (m : ℕ) : ℝ :=
  if m ≤ 3 then 1 / 2 else 1 / 4

def finiteFixedOffset (m j : ℕ) : ℝ := (j : ℝ) - m

/-- One exact rate vector, shared by all `2n-1` printed states. The retuning
uses `1/Y_i(X∘)` from the coalesced state and fixes `b_i=β_i=1`; it performs
none of the asymptotic relaxation used for the all-size theorem. -/
def finiteFixedPrintedRates (m : ℕ) : Rates (m + 1) :=
  retune
    (arbitrarySplitFiniteRates m (finiteFixedOffset m)
      (finiteFixedRadius m) (finiteFixedSpacing m))
    (fun i => 1 / (coalescedFiniteState m (finiteFixedRadius m)).D i)
    (fun _ => 1) (fun _ => 1)

def finiteFixedPrintedState (m : ℕ) (j : Fin (2 * m + 1)) : State (m + 1) :=
  arbitrarySplitFiniteState m (finiteFixedOffset m)
    (finiteFixedRadius m) (finiteFixedSpacing m) j

end
end PhosphorylationStableCapacity
