module
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedEndpoint
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedContractBridge

@[expose] public section

namespace PhosphorylationStableCapacity.P079PrintedContract
noncomputable section
open PhosphorylationSharpness

/-- Internal docking lemma: exact coefficient certificates and the actual
per-state spectra transfer to the independent literal manuscript contract.
The final endpoint must discharge both inputs for every printed size. -/
theorem finiteFixedPrinted_contract_of_coefficients_and_spectra
    (hcoeff : ∀ m : ℕ, 1 ≤ m → m ≤ 6 →
      DensePositive
        (arbitrarySplitRawD m (finiteFixedOffset m)
          (finiteFixedRadius m) (finiteFixedSpacing m)) m ∧
      DensePositive
        (arbitrarySplitRawB m (finiteFixedOffset m)
          (finiteFixedRadius m) (finiteFixedSpacing m)) m ∧
      ∀ i : Fin (m+1),
        0 < (coalescedFiniteState m (finiteFixedRadius m)).D i)
    (hspec : ∀ m : ℕ, 1 ≤ m → m ≤ 6 →
      ∀ j : Fin (2*m+1),
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
            (toCoordinateSpace (chart (finiteFixedPrintedState m j)))) :
    PaperFixedFiniteTable := by
  intro m hm hm6
  obtain ⟨hD, hB, hcoalD⟩ := hcoeff m hm hm6
  have hsource := finiteFixedPrinted_complete_source_of_coeff_positive
    m hm hm6 hD hB hcoalD
  dsimp only
  simp only [paperFixedRates_eq, paperFixedState_fun_eq, paperFixedRadius_eq]
  exact ⟨hsource.1, hsource.2.1, hsource.2.2.1,
    hsource.2.2.2.1, hsource.2.2.2.2.1,
    hsource.2.2.2.2.2, hspec m hm hm6⟩

end
end PhosphorylationStableCapacity.P079PrintedContract
