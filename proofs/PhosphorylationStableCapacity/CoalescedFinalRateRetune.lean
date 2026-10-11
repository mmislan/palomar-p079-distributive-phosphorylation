module
public import proofs.PhosphorylationStableCapacity.CoalescedFinalCurrentWeight
public import proofs.PhosphorylationStableCapacity.CoalescedFiniteSource
public import proofs.PhosphorylationStableCapacity.LoadedCurrentDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- Multiply all six literal rates on each edge by the same factor. -/
def edgeScaledRates {n : ℕ} (w : Fin n → ℝ) (k : Rates n) : Rates n where
  a i := w i * k.a i
  b i := w i * k.b i
  c i := w i * k.c i
  alpha i := w i * k.alpha i
  beta i := w i * k.beta i
  gamma i := w i * k.gamma i

theorem edgeScaledRates_positive {n : ℕ} (w : Fin n → ℝ) (k : Rates n)
    (hw : ∀ i, 0 < w i) (hk : k.Positive) :
    (edgeScaledRates w k).Positive := by
  intro i
  obtain ⟨ha, hb, hc, halpha, hbeta, hgamma⟩ := hk i
  exact ⟨mul_pos (hw i) ha, mul_pos (hw i) hb,
    mul_pos (hw i) hc, mul_pos (hw i) halpha,
    mul_pos (hw i) hbeta, mul_pos (hw i) hgamma⟩

/-- Per-edge scaling preserves any state with separately balanced
binding and catalytic currents. -/
theorem edgeScaledRates_equilibrium {n : ℕ} (w : Fin n → ℝ)
    (k : Rates n) (x : State n)
    (hE : ∀ i, kinaseNet k x i = k.c i * x.C i)
    (hF : ∀ i, phosphataseNet k x i = k.gamma i * x.D i)
    (hcat : ∀ i, k.c i * x.C i = k.gamma i * x.D i) :
    Equilibrium (edgeScaledRates w k) x := by
  apply equilibrium_of_currents
  · intro i
    calc
      kinaseNet (edgeScaledRates w k) x i =
          w i * kinaseNet k x i := by
            simp only [edgeScaledRates, kinaseNet]
            ring
      _ = w i * (k.c i * x.C i) := by rw [hE i]
      _ = (edgeScaledRates w k).c i * x.C i := by
        simp only [edgeScaledRates]
        ring
  · intro i
    calc
      phosphataseNet (edgeScaledRates w k) x i =
          w i * phosphataseNet k x i := by
            simp only [edgeScaledRates, phosphataseNet]
            ring
      _ = w i * (k.gamma i * x.D i) := by rw [hF i]
      _ = (edgeScaledRates w k).gamma i * x.D i := by
        simp only [edgeScaledRates]
        ring
  · intro i
    simpa only [edgeScaledRates, mul_assoc] using
      congrArg (fun t : ℝ => w i * t) (hcat i)

def coalescedFinalScaledRates (m : ℕ) (r τ : ℝ) : Rates (m + 2) :=
  edgeScaledRates (coalescedFinalCurrentWeights m τ)
    (coalescedFiniteRates (m + 1) r)

/-- A positive final catalytic weight has a literal positive rate
realization sharing the exact coalesced equilibrium and conserved totals. -/
theorem coalescedFinalScaledRates_eventually_source (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ τ : ℝ, 0 < τ →
        (coalescedFinalScaledRates m r τ).Positive ∧
          Equilibrium (coalescedFinalScaledRates m r τ)
            (coalescedFiniteState (m + 1) r) := by
  have hdense := coalescedPair_dense (m + 1)
  filter_upwards [coalescedFiniteState_eventually_equilibrium (m + 1),
    conversion_eventually_positive hdense.1 hdense.2]
    with r hsource hBD
  obtain ⟨hk, _, heq, _, _, _⟩ := hsource
  intro τ hτ
  have hw : ∀ i : Fin (m + 2),
      0 < coalescedFinalCurrentWeights m τ i := by
    intro i
    by_cases hi : i = Fin.last (m + 1)
    · simp [coalescedFinalCurrentWeights, hi, hτ]
    · simp [coalescedFinalCurrentWeights, hi]
  refine ⟨edgeScaledRates_positive _ _ hw hk, ?_⟩
  apply edgeScaledRates_equilibrium
  · intro i
    have h := heq.2.2.2.1 i
    change kinaseNet (coalescedFiniteRates (m + 1) r)
      (coalescedFiniteState (m + 1) r) i -
      (coalescedFiniteRates (m + 1) r).c i *
        (coalescedFiniteState (m + 1) r).C i = 0 at h
    exact sub_eq_zero.mp h
  · intro i
    have h := heq.2.2.2.2 i
    change phosphataseNet (coalescedFiniteRates (m + 1) r)
      (coalescedFiniteState (m + 1) r) i -
      (coalescedFiniteRates (m + 1) r).gamma i *
        (coalescedFiniteState (m + 1) r).D i = 0 at h
    exact sub_eq_zero.mp h
  · intro i
    exact realize_reconstruct_catalytic_balance
      (fun j : Fin (m + 3) =>
        ((1 + Polynomial.X) * coalescedRawD (m + 1) r).coeff j)
      (fun j : Fin (m + 2) => (coalescedRawB (m + 1) r).coeff j)
      (fun j : Fin (m + 2) => (coalescedRawD (m + 1) r).coeff j)
      (ratio 3)
      (rootS 3 ((coalescedRawD (m + 1) r).eval (ratio 3)))
      (rootF 3) i
      (ne_of_gt (hBD.2.1 i (by omega)))

end
end PhosphorylationStableCapacity
