module
public import proofs.PhosphorylationStableCapacity.PaperCompactActualCurrentIndependent435
public import proofs.PhosphorylationStableCapacity.LiteralPhosphorylationFlux435
public import proofs.PhosphorylationStableCapacity.ReadoutDerivative435
public import Mathlib.Topology.Order.LeftRightNhds

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Filter
open scoped Topology BigOperators

/-- The actual-current splitting law holds on one common closed positive
interval, with the same rates, slow branches and quantitative constants.
The positive physical readout derivative is asserted even for an empty K.
Every listed equilibrium has positive total phosphorylation flux. -/
def PaperCompactActualCurrentIntervalLaw
    (m : ℕ) (x : Fin (2*(m+1)+1) → ℝ) : Prop :=
  StrictMono x →
    ∃ ξ : ℕ → ℝ, StrictMono ξ ∧ (∀ j, ξ j.val = x j) ∧
      ∀ᶠ r : ℝ in atTop,
        ∀ K : Set (PaperPositivePrefixCurrents m), IsCompact K →
          ∃ t ε α Kerr Cread : ℝ,
            0 < t ∧ 0 < ε ∧ ε ≤ 1 ∧ 0 < α ∧ 0 < Kerr ∧ 0 < Cread ∧
            0 < deriv (paperReadoutScalar m (paperCoalescedD (m+1) r)) 3 ∧
            let X₀ := paperCoalescedState m r
            let z := fun δ => paperSourceState m ξ r δ
            let w := fun ω : PaperPositivePrefixCurrents m =>
              Fin.lastCases (t/X₀.D (Fin.last (m+1)))
                (fun i => ω.val i/X₀.D i.castSucc)
            let k := fun ω δ => paperRates m ξ r δ ε (w ω)
            ∃ lam : PaperPositivePrefixCurrents m → Fin (2*(m+1)+1) → ℝ → ℝ,
              ∃ A : PaperPositivePrefixCurrents m → ℝ,
                (∀ ω ∈ K, 0 < A ω ∧
                  (∀ j, AnalyticAt ℝ (lam ω j) 0 ∧ lam ω j 0 = 0) ∧
                  (∀ i, (k ω 0).gamma i.castSucc*X₀.D i.castSucc = ω.val i) ∧
                  (k ω 0).gamma (Fin.last (m+1))*X₀.D (Fin.last (m+1)) = t ∧
                  (A ω =
                    let J₀ := restrictedJacobianMatrix (2*r) 2 (2*(r+1)) (k ω 0)
                      (toCoordinateSpace (chart X₀))
                    let Θ₀ : ℂ :=
                      ((J₀.map (algebraMap ℝ ℂ)).charpoly.roots.erase 0).prod
                    let P := paperCoalescedPair (m+1)
                    let D := paperCoalescedD (m+1) r
                    let B := paperCoalescedB (m+1) r
                    let C := 2*r*P.1.eval r+P.2.eval r
                    let M := (B.eval 1-D.eval 1)/D.coeff 0
                    (4*C*M/((r-1)*D.eval 1*‖Θ₀‖))*
                      (∏ i : Fin (m+2),
                        ((k ω 0).b i+(k ω 0).c i)*(k ω 0).alpha i*(k ω 0).gamma i))) ∧
                ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
                  (∀ j l : Fin (2*(m+1)+1),
                    |(paperReadout m (z δ j)-paperReadout m (z δ l)) -
                      (x j-x l)*deriv (paperReadoutScalar m (paperCoalescedD (m+1) r)) 3*δ|
                      ≤ Cread*δ^2) ∧
                  StrictMono (fun j => paperReadout m (z δ j)) ∧
                  ∀ ω ∈ K,
                    (k ω δ).Positive ∧ Function.Injective (z δ) ∧
                    {s : State (m+2) | s.Positive ∧ Equilibrium (k ω δ) s ∧
                      InClass (2*r) 2 (2*(r+1)) s} = Set.range (z δ) ∧
                    {s : State (m+2) | s.Positive ∧ Equilibrium (k ω δ) s ∧
                      InClass (2*r) 2 (2*(r+1)) s}.ncard = 2*(m+1)+1 ∧
                    ∀ j : Fin (2*(m+1)+1),
                      let s := z δ j
                      let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1)) (k ω δ)
                        (toCoordinateSpace (chart s))
                      s.Positive ∧
                      0 < ∑ i : Fin (m+2), (k ω δ).gamma i*s.D i ∧
                      Equilibrium (k ω δ) s ∧
                      InClass (2*r) 2 (2*(r+1)) s ∧
                      Real.sqrt (1+8*s.E/s.F) = 3+δ*x j ∧
                      J.charpoly.IsRoot (lam ω j δ) ∧
                      ((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
                        ((lam ω j δ) : ℂ) ≠ 0 ∧
                      (∀ ζ : ℂ, ζ ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
                        ζ = ((lam ω j δ) : ℂ) ∨ ζ.re ≤ -α) ∧
                      |lam ω j δ/(-A ω*δ^(2*(m+1))*paperFiniteGap x j)-1| ≤ Kerr*|δ| ∧
                      (∃ err : ℝ, |err| ≤ 2*Kerr*|δ| ∧
                        1/|lam ω j δ| = (1+err)/
                          (A ω*|paperFiniteGap x j| *δ^(2*(m+1)))) ∧
                      (Even j.val → lam ω j δ < 0) ∧
                      (Odd j.val → 0 < lam ω j δ) ∧
                      (Even j.val → IsLinearlyStable (2*r) 2 (2*(r+1)) (k ω δ)
                        (toCoordinateSpace (chart s)) ∧
                        IsLocallyAsymptoticallyStableClass (2*r) 2 (2*(r+1)) (k ω δ)
                          (toCoordinateSpace (chart s))) ∧
                      (Odd j.val → IsOneUnstableSaddle (2*r) 2 (2*(r+1)) (k ω δ)
                        (toCoordinateSpace (chart s)))

/-- Select a single closed positive split interval from the actual-current
law. The interval is chosen after the whole compact set and before the
individual current; every original witness and error constant is retained. -/
theorem paper_compact_actual_current_interval_law
    (m : ℕ) (x : Fin (2*(m+1)+1) → ℝ) :
    PaperCompactActualCurrentIntervalLaw m x := by
  intro hx
  obtain ⟨ξ, hξ, hagree, hfamily⟩ := paper_compact_actual_current_law m x hx
  refine ⟨ξ, hξ, hagree, ?_⟩
  obtain ⟨hp, hq⟩ := coalescedPair_dense (m+1)
  filter_upwards [hfamily, conversion_eventually_positive hp hq]
    with r hfamilyr hconv
  intro K hK
  obtain ⟨t, ε, α, Kerr, Cread, ht, hε, hε1, hα, hKerr, hCread,
    lam, A, hcommon, hδ⟩ := hfamilyr K hK
  have hreadpos :
      0 < deriv (paperReadoutScalar m (paperCoalescedD (m+1) r)) 3 := by
    rw [paperCoalescedD_eq_coalescedRawD]
    have hscalar : paperReadoutScalar m (coalescedRawD (m+1) r) =
        splitReadoutScalar (m+1) (coalescedRawD (m+1) r) := by
      funext u
      rfl
    rw [hscalar]
    exact splitReadoutScalar_deriv_three_pos (m+1) _ hconv.1
  obtain ⟨δ₀, hδ₀, hinterval⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hδ
  refine ⟨t, ε, α, Kerr, Cread, ht, hε, hε1, hα, hKerr, hCread,
    hreadpos, lam, A, hcommon, δ₀, hδ₀, ?_⟩
  intro δ hδpos hδle
  obtain ⟨hread, horder, hcurrents⟩ := hinterval ⟨hδpos, hδle⟩
  refine ⟨hread, horder, ?_⟩
  intro ω hω
  obtain ⟨hk, hinj, hset, hcard, hstates⟩ := hcurrents ω hω
  refine ⟨hk, hinj, hset, hcard, ?_⟩
  intro j
  obtain ⟨hs, hremaining⟩ := hstates j
  exact ⟨hs, positive_total_phosphorylation_flux (m+1) _ _ hk hs, hremaining⟩

end

end PhosphorylationStableCapacity
