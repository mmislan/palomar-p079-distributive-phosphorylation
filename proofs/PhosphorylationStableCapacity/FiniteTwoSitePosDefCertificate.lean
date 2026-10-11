module
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteRationalCertificate
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open scoped Matrix
set_option maxHeartbeats 2000000

def twoSiteQ0Real : Matrix (Fin 6) (Fin 6) ℝ :=
  manuscriptTwoSiteQ0Candidate.map (fun q : ℚ => (q : ℝ))

private def twoSitePairSet : Finset (Fin 6 × Fin 6) :=
  {(0,1), (0,2), (0,3), (0,4), (0,5),
   (1,2), (1,3), (1,4), (1,5),
   (2,3), (2,4), (2,5),
   (3,4), (3,5), (4,5)}

private def twoSiteDiff (i j : Fin 6) : Fin 6 → ℝ :=
  fun k => if k = i then 1 else if k = j then -1 else 0

private def twoSiteQ0Weight (p : Fin 6 × Fin 6) : ℝ :=
  -twoSiteQ0Real p.1 p.2

private def twoSiteQ0Margin (i : Fin 6) : ℝ :=
  ![51680874998722951/52813475000000000,
    852185877889506037/887266380000000000,
    21702077166868759/22181659500000000,
    304407047840822191/316880850000000000,
    1029765927797879333/1043842800000000000,
    17162455307822254643/17745327600000000000] i

private def twoSiteQ0Laplacian : Matrix (Fin 6) (Fin 6) ℝ :=
  ∑ p ∈ twoSitePairSet,
    twoSiteQ0Weight p • Matrix.vecMulVec
      (twoSiteDiff p.1 p.2) (twoSiteDiff p.1 p.2)

private theorem twoSiteQ0Weight_pos (p : Fin 6 × Fin 6)
    (hp : p ∈ twoSitePairSet) : 0 < twoSiteQ0Weight p := by
  rcases p with ⟨i, j⟩
  simp only [twoSitePairSet, Finset.mem_insert, Finset.mem_singleton] at hp
  fin_cases i <;> fin_cases j
  all_goals norm_num at hp
  all_goals norm_num [twoSiteQ0Weight, twoSiteQ0Real,
    manuscriptTwoSiteQ0Candidate]

private theorem twoSiteQ0Margin_pos (i : Fin 6) :
    0 < twoSiteQ0Margin i := by
  fin_cases i <;> norm_num [twoSiteQ0Margin]

private theorem twoSiteQ0_decomposition :
    twoSiteQ0Real =
      Matrix.diagonal twoSiteQ0Margin + twoSiteQ0Laplacian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoSiteQ0Real, twoSiteQ0Laplacian, twoSitePairSet,
      twoSiteQ0Weight, twoSiteQ0Margin, twoSiteDiff,
      manuscriptTwoSiteQ0Candidate, Matrix.vecMulVec, Matrix.diagonal,
      Finset.sum_insert]

theorem twoSiteQ0Real_posDef : twoSiteQ0Real.PosDef := by
  rw [twoSiteQ0_decomposition]
  apply Matrix.PosDef.add_posSemidef
  · exact Matrix.PosDef.diagonal twoSiteQ0Margin_pos
  · unfold twoSiteQ0Laplacian
    apply Matrix.posSemidef_sum
    intro p hp
    have hv :
        (Matrix.vecMulVec (twoSiteDiff p.1 p.2)
          (twoSiteDiff p.1 p.2)).PosSemidef := by
      simpa using Matrix.posSemidef_vecMulVec_self_star
        (twoSiteDiff p.1 p.2)
    exact hv.smul (twoSiteQ0Weight_pos p hp).le

end
end PhosphorylationStableCapacity
