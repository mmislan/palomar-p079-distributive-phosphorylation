module
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteRationalCertificate
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open scoped Matrix
set_option maxHeartbeats 2000000

def twoSiteQ2Real : Matrix (Fin 6) (Fin 6) ℝ :=
  manuscriptTwoSiteQ2Candidate.map (fun q : ℚ => (q : ℝ))

private def twoSitePairSet2 : Finset (Fin 6 × Fin 6) :=
  {(0,1), (0,2), (0,3), (0,4), (0,5),
   (1,2), (1,3), (1,4), (1,5),
   (2,3), (2,4), (2,5),
   (3,4), (3,5), (4,5)}

private def twoSiteQ2Sign (p : Fin 6 × Fin 6) : ℝ :=
  if 0 ≤ twoSiteQ2Real p.1 p.2 then 1 else -1

private def twoSiteSignedDiff (p : Fin 6 × Fin 6) : Fin 6 → ℝ :=
  fun k => if k = p.1 then 1 else if k = p.2 then twoSiteQ2Sign p else 0

private def twoSiteQ2Weight (p : Fin 6 × Fin 6) : ℝ :=
  |twoSiteQ2Real p.1 p.2|

private def twoSiteQ2Margin (i : Fin 6) : ℝ :=
  ![601369735894712663/602073615000000000,
    199841549957544423/200691205000000000,
    10921079270959723/10946793000000000,
    7208002028594280499/7224883380000000000,
    3603609975230740927/3612441690000000000,
    7204077244674863609/7224883380000000000] i

private def twoSiteQ2PairSum : Matrix (Fin 6) (Fin 6) ℝ :=
  ∑ p ∈ twoSitePairSet2,
    twoSiteQ2Weight p • Matrix.vecMulVec
      (twoSiteSignedDiff p) (twoSiteSignedDiff p)

private theorem twoSiteQ2Weight_pos (p : Fin 6 × Fin 6)
    (hp : p ∈ twoSitePairSet2) : 0 < twoSiteQ2Weight p := by
  rcases p with ⟨i, j⟩
  simp only [twoSitePairSet2, Finset.mem_insert, Finset.mem_singleton] at hp
  fin_cases i <;> fin_cases j
  all_goals norm_num at hp
  all_goals norm_num [twoSiteQ2Weight, twoSiteQ2Real,
    manuscriptTwoSiteQ2Candidate]

private theorem twoSiteQ2Margin_pos (i : Fin 6) :
    0 < twoSiteQ2Margin i := by
  fin_cases i <;> norm_num [twoSiteQ2Margin]

private theorem twoSiteQ2_decomposition :
    twoSiteQ2Real =
      Matrix.diagonal twoSiteQ2Margin + twoSiteQ2PairSum := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoSiteQ2Real, twoSiteQ2PairSum, twoSitePairSet2,
      twoSiteQ2Weight, twoSiteQ2Margin, twoSiteSignedDiff, twoSiteQ2Sign,
      manuscriptTwoSiteQ2Candidate, Matrix.vecMulVec, Matrix.diagonal,
      Finset.sum_insert]

theorem twoSiteQ2Real_posDef : twoSiteQ2Real.PosDef := by
  rw [twoSiteQ2_decomposition]
  apply Matrix.PosDef.add_posSemidef
  · exact Matrix.PosDef.diagonal twoSiteQ2Margin_pos
  · unfold twoSiteQ2PairSum
    apply Matrix.posSemidef_sum
    intro p hp
    have hv :
        (Matrix.vecMulVec (twoSiteSignedDiff p)
          (twoSiteSignedDiff p)).PosSemidef := by
      simpa using Matrix.posSemidef_vecMulVec_self_star
        (twoSiteSignedDiff p)
    exact hv.smul (twoSiteQ2Weight_pos p hp).le

end
end PhosphorylationStableCapacity
