module
public import proofs.PhosphorylationStableCapacity.Compatibility

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- Literal substrate inventory at one phosphorylation level, including the
kinase complex bound on the outgoing edge and the phosphatase complex bound on
the incoming edge. -/
def loadedLevel {n : ℕ} (x : State n) (j : Fin (n + 1)) : ℝ :=
  x.S j +
    (∑ i : Fin n, if i.castSucc = j then x.C i else 0) +
    (∑ i : Fin n, if i.succ = j then x.D i else 0)

/-- The exact full mass-action field changes each loaded level only by the
incoming and outgoing catalytic currents. -/
theorem loadedLevel_field_eq_catalytic_flux {n : ℕ}
    (k : Rates n) (x : State n) (j : Fin (n + 1)) :
    loadedLevel (field k x) j =
      ∑ i : Fin n, (
        (if i.succ = j then k.c i * x.C i - k.gamma i * x.D i else 0) -
        (if i.castSucc = j then k.c i * x.C i - k.gamma i * x.D i else 0)) := by
  simp only [loadedLevel, field, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [kinaseNet, phosphataseNet] <;> ring

end
end PhosphorylationStableCapacity
