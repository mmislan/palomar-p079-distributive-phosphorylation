module
public import proofs.PhosphorylationStableCapacity.RatioCurveClassLift

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Response of the free class coordinates to a unit change in free
kinase concentration at a fixed literal state. -/
def kinaseInputDirection {n : ℕ} (k : Rates n) (x : State n) :
    CoordinateSpace n :=
  (fun j => ∑ i : Fin n,
      if i.castSucc = j.succ then -(k.a i*x.S i.castSucc) else 0,
    fun i => k.a i*x.S i.castSucc,
    fun _ => 0)

theorem equilibrium_free_kinase_shift_field_chart {n : ℕ}
    (k : Rates n) (x : State n) (heq : Equilibrium k x)
    (d : ℝ) :
    toCoordinateSpace (chart (field k {x with E := x.E+d})) =
      d • kinaseInputDirection k x := by
  apply Prod.ext
  · funext j
    dsimp [toCoordinateSpace, chart, kinaseInputDirection,
      field, smul_eq_mul]
    have hzero := heq.1 j.succ
    dsimp [field] at hzero
    calc
      (∑ i : Fin n,
          ((if i.castSucc = j.succ then
              -kinaseNet k {x with E := x.E+d} i+k.gamma i*x.D i else 0) +
            (if i.succ = j.succ then
              k.c i*x.C i-phosphataseNet k {x with E := x.E+d} i else 0))) =
        (∑ i : Fin n,
          ((if i.castSucc = j.succ then
              -kinaseNet k x i+k.gamma i*x.D i else 0) +
            (if i.succ = j.succ then
              k.c i*x.C i-phosphataseNet k x i else 0))) +
        d * (∑ i : Fin n,
          if i.castSucc = j.succ then -(k.a i*x.S i.castSucc) else 0) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> (try dsimp [kinaseNet, phosphataseNet]) <;> ring
      _ = d * (∑ i : Fin n,
          if i.castSucc = j.succ then -(k.a i*x.S i.castSucc) else 0) := by
        rw [hzero, zero_add]
  · apply Prod.ext
    · funext i
      dsimp [toCoordinateSpace, chart, kinaseInputDirection,
        field, smul_eq_mul]
      have hzero := heq.2.2.2.1 i
      dsimp [field, kinaseNet] at hzero ⊢
      nlinarith
    · funext i
      dsimp [toCoordinateSpace, chart, kinaseInputDirection,
        field, smul_eq_mul]
      simpa [field, phosphataseNet] using heq.2.2.2.2 i

/-- On the exact positive equilibrium curve, the fixed-class field
has rank-one form: the remaining kinase-total gap times the explicit
kinase-input direction. -/
theorem restrictedField_on_ratioEquilibriumCurveChart {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u) :
    restrictedFieldEuclid ET FT ST k
      (ratioEquilibriumCurveChart k FT ST u) =
      (ET - ratioCurveKinaseTotal k FT ST u) •
        kinaseInputDirection k (ratioEquilibriumCurve k FT ST u) := by
  let x := ratioEquilibriumCurve k FT ST u
  have heq : Equilibrium k x :=
    (ratioEquilibriumCurve_positive_equilibrium_and_totals
      hn k hk FT ST u hFT hST hu).2.1
  change toCoordinateSpace (chart (field k
      (unChart ET FT ST (chart x)))) = _
  rw [ratioEquilibriumCurve_class_lift hn k hk ET FT ST u hFT hST hu]
  exact equilibrium_free_kinase_shift_field_chart k x heq
    (ET - ratioCurveKinaseTotal k FT ST u)

end
end PhosphorylationStableCapacity
