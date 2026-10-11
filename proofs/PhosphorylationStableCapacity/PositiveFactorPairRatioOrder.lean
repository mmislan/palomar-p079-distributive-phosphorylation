module
public import proofs.PhosphorylationStableCapacity.CommonFactorRatioOrder

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Coordinatewise decrease of positive linear-factor magnitudes makes the
coefficient ratio of the resulting products nondecreasing in degree. -/
theorem positiveFactorProduct_ratio_mono
    (as bs : List ℝ)
    (hpair : List.Forall₂ (fun a b => b ≤ a) as bs)
    (ha : ∀ a ∈ as, 0 < a) (hb : ∀ b ∈ bs, 0 < b) :
    CoeffRatioMono (positiveFactorProduct as)
      (positiveFactorProduct bs) as.length := by
  induction as generalizing bs with
  | nil =>
      cases bs with
      | nil =>
          intro i hi
          simp at hi
      | cons b bs => cases hpair
  | cons a as ih =>
      cases bs with
      | nil => cases hpair
      | cons b bs =>
          cases hpair with
          | cons hba htail =>
              have haHead : 0 < a := ha a (by simp)
              have hbHead : 0 < b := hb b (by simp)
              have haTail : ∀ x ∈ as, 0 < x := by
                intro x hx
                exact ha x (by simp [hx])
              have hbTail : ∀ x ∈ bs, 0 < x := by
                intro x hx
                exact hb x (by simp [hx])
              have hlen : as.length = bs.length :=
                List.Forall₂.length_eq htail
              have hp := positiveFactorProduct_dense as haTail
              have hq := positiveFactorProduct_dense bs hbTail
              rw [← hlen] at hq
              have hlc := positiveFactorProduct_logconcave as haTail
              have htailRatio := ih bs htail haTail hbTail
              have hreplace := factorReplacement_coeffRatioMono
                hp hlc haHead hba
              have hcommon := commonFactor_coeffRatioMono
                hp hq htailRatio hbHead
              have hcomp := coeffRatioMono_compose
                (positiveLinearStep_dense hp haHead)
                (positiveLinearStep_dense hp hbHead)
                (positiveLinearStep_dense hq hbHead)
                hreplace hcommon
              simpa [positiveFactorProduct] using hcomp

end
end PhosphorylationStableCapacity
