module
public import proofs.PhosphorylationStableCapacity.RatioCurveChart

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Changing only the kinase total in the class chart changes only
free kinase in the reconstructed literal state. -/
theorem unChart_chart_change_kinase_total {n : ℕ}
    (ET FT ST : ℝ) (x : State n)
    (hF : totalF x = FT) (hS : totalS x = ST) :
    unChart ET FT ST (chart x) =
      {x with E := x.E + (ET - totalE x)} := by
  have hbase : unChart (totalE x) FT ST (chart x) = x :=
    unChart_chart_of_inClass (totalE x) FT ST x
      ⟨rfl, hF, hS⟩
  have hshift : unChart ET FT ST (chart x) =
      {(unChart (totalE x) FT ST (chart x)) with
        E := (unChart (totalE x) FT ST (chart x)).E +
          (ET - totalE x)} := by
    dsimp [unChart, chart]
    congr 1
    ring
  rw [hshift, hbase]

/-- The fixed-class lift of the positive equilibrium curve is the
same literal state except for its free kinase concentration. -/
theorem ratioEquilibriumCurve_class_lift {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u) :
    unChart ET FT ST (chart (ratioEquilibriumCurve k FT ST u)) =
      {ratioEquilibriumCurve k FT ST u with
        E := (ratioEquilibriumCurve k FT ST u).E +
          (ET - ratioCurveKinaseTotal k FT ST u)} := by
  obtain ⟨_hx, _heq, hF, hS, hE, _hratio⟩ :=
    ratioEquilibriumCurve_positive_equilibrium_and_totals
      hn k hk FT ST u hFT hST hu
  rw [unChart_chart_change_kinase_total ET FT ST
      (ratioEquilibriumCurve k FT ST u) hF hS, hE]

end
end PhosphorylationStableCapacity
