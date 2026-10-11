module
public import proofs.PhosphorylationStableCapacity.FiniteAllSiteMatrixCoordinates

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The class-chart perturbation of the eliminated substrate and free enzymes. -/
def allSiteDirectionS {n : ℕ} (v : CoordinateSpace n) : Fin (n + 1) → ℝ :=
  Fin.cases (-(∑ i, v.1 i) - (∑ i, v.2.1 i) - (∑ i, v.2.2 i)) v.1

def allSiteDirectionE {n : ℕ} (v : CoordinateSpace n) : ℝ :=
  -(∑ i, v.2.1 i)

def allSiteDirectionF {n : ℕ} (v : CoordinateSpace n) : ℝ :=
  -(∑ i, v.2.2 i)

def allSiteKinaseDirection {n : ℕ} (ET ST : ℝ) (k : Rates n)
    (u v : CoordinateSpace n) (i : Fin n) : ℝ :=
  k.a i *
    (allSiteClassE ET u * allSiteDirectionS v i.castSucc +
      allSiteClassS ST u i.castSucc * allSiteDirectionE v) -
    k.b i * v.2.1 i

def allSitePhosphataseDirection {n : ℕ} (FT ST : ℝ) (k : Rates n)
    (u v : CoordinateSpace n) (i : Fin n) : ℝ :=
  k.alpha i *
    (allSiteClassF FT u * allSiteDirectionS v i.succ +
      allSiteClassS ST u i.succ * allSiteDirectionF v) -
    k.beta i * v.2.2 i

/-- A scalar finite-sum presentation of the literal arbitrary-site class
Jacobian action. It has the same coordinate order as the printed matrices. -/
def allSiteJacobianActionFormula {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u v : CoordinateSpace n) : CoordinateSpace n :=
  ((fun j => ∑ i : Fin n, (
      (if i.castSucc = j.succ then
        -allSiteKinaseDirection ET ST k u v i + k.gamma i * v.2.2 i else 0) +
      (if i.succ = j.succ then
        k.c i * v.2.1 i - allSitePhosphataseDirection FT ST k u v i else 0))),
    (fun i => allSiteKinaseDirection ET ST k u v i - k.c i * v.2.1 i),
    (fun i => allSitePhosphataseDirection FT ST k u v i - k.gamma i * v.2.2 i))

private theorem allSiteSLinear_apply_eq_direction {n : ℕ}
    (v : CoordinateSpace n) (j : Fin (n + 1)) :
    allSiteSLinear j v = allSiteDirectionS v j := by
  cases j using Fin.cases with
  | zero => simp [allSiteSLinear, allSiteDirectionS]
  | succ j => rfl

theorem allSiteKinaseRow_apply_eq_direction {n : ℕ} (ET ST : ℝ)
    (k : Rates n) (u v : CoordinateSpace n) (i : Fin n) :
    allSiteKinaseRow ET ST k u i v =
      allSiteKinaseDirection ET ST k u v i := by
  simp [allSiteKinaseRow, allSiteKinaseDirection, allSiteDirectionE,
    allSiteSLinear_apply_eq_direction, allSiteELinear_apply]; ring

theorem allSitePhosphataseRow_apply_eq_direction {n : ℕ} (FT ST : ℝ)
    (k : Rates n) (u v : CoordinateSpace n) (i : Fin n) :
    allSitePhosphataseRow FT ST k u i v =
      allSitePhosphataseDirection FT ST k u v i := by
  simp [allSitePhosphataseRow, allSitePhosphataseDirection,
    allSiteDirectionF, allSiteSLinear_apply_eq_direction,
    allSiteFLinear_apply]; ring

theorem allSiteJacobianCLM_apply_eq_actionFormula {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u v : CoordinateSpace n) :
    allSiteJacobianCLM ET FT ST k u v =
      allSiteJacobianActionFormula ET FT ST k u v := by
  apply Prod.ext
  · funext j
    simp [allSiteJacobianCLM, allSiteJacobianActionFormula, allSiteRowS]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h1 : x.castSucc = j.succ
    · by_cases h2 : x = j
      · subst x
        by_cases hk : j.castSucc = j.succ <;>
          simp [hk, allSiteKinaseRow_apply_eq_direction,
            allSitePhosphataseRow_apply_eq_direction]
      · simp [h1, h2, allSiteKinaseRow_apply_eq_direction]
    · by_cases h2 : x = j
      · subst x
        by_cases hk : j.castSucc = j.succ <;>
          simp [hk, allSiteKinaseRow_apply_eq_direction,
            allSitePhosphataseRow_apply_eq_direction]
      · simp [h1, h2]
  · apply Prod.ext
    · funext i
      simp [allSiteJacobianCLM, allSiteJacobianActionFormula, allSiteRowC,
        allSiteKinaseRow_apply_eq_direction]
    · funext i
      simp [allSiteJacobianCLM, allSiteJacobianActionFormula, allSiteRowD,
        allSitePhosphataseRow_apply_eq_direction]

theorem allSiteExplicitFinMatrix_entry_actionFormula {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    (i j : Fin (3 * n)) :
    allSiteExplicitFinMatrix ET FT ST k u i j =
      allSiteCoordinateRead ((allSiteIndexEquiv n).symm i)
        (allSiteJacobianActionFormula ET FT ST k u
          (allSiteCoordinateUnit ((allSiteIndexEquiv n).symm j))) := by
  rw [allSiteExplicitFinMatrix_entry,
    allSiteJacobianCLM_apply_eq_actionFormula]

end
end PhosphorylationStableCapacity
