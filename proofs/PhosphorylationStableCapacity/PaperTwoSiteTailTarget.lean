module
public import proofs.PhosphorylationStableCapacity.FiniteTwoSitePaperTailGap

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

def PaperTwoSiteTailLaw : Prop :=
  ∀ j : Fin 3, OneDominantTailGap
    (restrictedJacobianMatrix 4 2 6 manuscriptTwoSiteRates
      (toCoordinateSpace (chart (manuscriptTwoSiteStates j))))

theorem two_site_literal_dominant_tail_gap : PaperTwoSiteTailLaw :=
  manuscriptTwoSite_literal_all_tail_gap

end
end PhosphorylationStableCapacity
